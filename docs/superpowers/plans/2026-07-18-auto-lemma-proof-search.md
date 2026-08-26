# Automatic Lemma Application / Proof Search Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let proof obligations over refinement types discharge automatically — the author writes a `?` proof hole and the elaborator *finds* the proof by applying a `@lemma`-tagged theorem, so `IsPositive(multiply(a,b))` closes without naming the lemma.

**Architecture:** A new untrusted elaborator module `Cure.Elab.ProofSearch` runs *before* the kernel: at a proof-position hole it assembles a Core proof term from (a) local-context hypotheses, (b) refinement/Sigma proof projections, and (c) applications of `@lemma`-tagged theorems (with their explicit hypotheses solved as recursive sub-goals). The kernel re-checks whatever term it produces exactly as if hand-written, so the feature is soundness-neutral by construction. A `@lemma` registry keyed by conclusion-head lives in the elaboration environment beside the existing interface/coherence registries. Resolution uses Agda's unique-or-defer discipline (collect all candidates, exactly-one-survivor, hard error on ≥2) with depth + cycle termination guards.

**Tech Stack:** Elixir; Cure's dependent elaborator (`lib/cure/elab/*`) and Core kernel API (`lib/cure/core/*`, read-only from this feature's perspective except one inert metadata field on the `Env` struct — see Global Constraints). ExUnit tests under `test/cure/`.

## Global Constraints

- **Layer discipline (two-pipeline steer):** all logic lands in `lib/cure/elab/*`. The dependent machinery is ONLY in `lib/cure/elab/*` + `lib/cure/core/*`. IGNORE `lib/cure/compiler/*` (`codegen.ex`, `pattern_compiler.ex`) and `lib/cure/types/*` (`checker.ex`, `unify.ex`) — those are the non-dependent lowering/checker pipeline and their same-named functions are decoys. `Cure.Elab.Unify`/`Cure.Elab.MetaCtx` (in `lib/cure/elab/unify.ex`) is the correct unifier, NOT `lib/cure/types/unify.ex`.
- **Soundness stance:** the resolver only *builds* Core terms; every produced term is re-checked by the existing kernel (`Cure.Core.Kernel.check/3`). No kernel judgement changes. No change to any normalizer/conversion/checker in `lib/cure/core/*`.
- **One permitted `lib/cure/core/*` edit — inert metadata only:** Task 1 adds a `lemmas: %{}` field to the `Cure.Core.Env` struct in `lib/cure/core/inductive.ex`. This mirrors the existing `interfaces`, `coherence`, `constrained`, and `import_modules` fields — all elaborator-side registries the kernel never consults (`import_modules`'s doc comment literally says "inert elaborator metadata (the kernel never reads it)"; `interfaces`/`coherence`/`constrained` are documented separately but share the same property, confirmed by grepping `lib/cure/core/kernel.ex` for any reference to those fields — there is none). The kernel never reads `lemmas`; it is elaborator-only. This is NOT a change to a kernel judgement and is NOT a TCB soundness change — it is the same registry pattern already present. Do not treat it as a HARD-STOP, but call it out explicitly in the Task 1 commit message.
- **Ghost-writer commits:** `git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "..."`. NO `Co-Authored-By`, no Claude signature. Place all options BEFORE the `--` pathspec separator.
- **Explicit-pathspec staging only** (shared worktree, concurrent sessions): `git add -- <path>` and `git commit ... -- <path1> <path2>`. NEVER `git add -A` / `git add .`. NEVER bare `git stash` / `git stash pop`.
- **One build at a time:** never run two `mix` suites concurrently. Use scoped `mix test <file>` per task. The full suite runs once, alone, at the Stage 6 gate (outside this plan).
- **Tests immutable once green:** behavioral, not implementation-coupled. In particular the red test (Task 7) uses a *local, untagged* lemma so that tagging the shipped stdlib in Task 9 can never retroactively flip it.
- **Branch:** `implicit-goal-solving` (work in place; do not create a new worktree).

---

### Task 1: `@lemma` registry on the elaboration environment

**Files:**
- Modify: `lib/cure/core/inductive.ex` (the `Cure.Core.Env` module) — add `lemmas: %{}` struct field + `put_lemma/3` and `lemmas/2` accessors, mirroring `put_interface/3`+`get_interface/2` (`inductive.ex:179-184`).
- Modify: `lib/cure/elab/program.ex` — add `lemmas` to the field list `merge_env/2` builds (`program.ex:1859-1877`; see the cross-module note below).
- Test: `test/cure/elab/proof_search_registry_test.exs` (Create)

**Interfaces:**
- Produces:
  - `Cure.Core.Env.put_lemma(env, head_atom, entry) :: Env.t()` — append `entry` to the list filed under conclusion-head atom `head_atom`.
  - `Cure.Core.Env.lemmas(env, head_atom) :: [entry]` — the lemma entries filed under `head_atom` (empty list if none).
  - `entry` is a plain map `%{name: atom(), type: core_pi_term, arity: non_neg_integer()}` where `type` is the lemma's full Core Pi type and `name` is its owner-qualified global name.

**Cross-module note (load-bearing for Task 9 — read before Step 3).** `merge_env/2` (`lib/cure/elab/program.ex:1859-1877`) is the function `use X` imports, module slices, and the prelude all go through — it is called at `program.ex:368-369` (prelude+import), `633`/`1685` (module-slice merges), `1332` (macro home-env merge), and `1515-1516` (a second prelude+import call site). It builds a **fresh `%Env{}` from an explicit, hardcoded field list** (`families, ctors, ctor_to_family, defs, certified, builtins, primitives, interfaces, coherence, constrained, import_modules, module_owner`) — any `Env` field not named in that literal is silently dropped (reset to the struct default) on every merge, not preserved. Since `lemmas` does not appear in that list and never will unless this task adds it, a `@lemma` registered in one module (e.g. `Std.Proof.Math`) would vanish the moment a second module (e.g. `Std.Refine`) does `use Std.Proof.Math` and its env gets merged — breaking cross-module lemma visibility silently (no crash, just an empty registry). This is exactly the shape Task 9 ships: `Std.Refine`'s hole must resolve a lemma tagged in `Std.Proof.Math`, a *different* module. Task 8's differential test does **not** cover this — its `@lemma`-tagged `tagged_fact` is declared locally in the same module as the hole that uses it, so no merge boundary is crossed for the lemma itself. Without this fix (and the red test below), Task 9 would appear to follow from Tasks 1–8 but silently fail the moment it's exercised for real.

- [ ] **Step 1: Write the failing test**

```elixir
defmodule Cure.Elab.ProofSearchRegistryTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Env

  test "put_lemma files an entry under its conclusion head and lemmas/2 retrieves it" do
    entry = %{name: :"M#lem", type: {:data, :"M#IsPositive", [], []}, arity: 2}
    env = Env.put_lemma(Env.empty(), :"M#IsPositive", entry)

    assert Env.lemmas(env, :"M#IsPositive") == [entry]
    assert Env.lemmas(env, :"M#Other") == []
  end

  test "put_lemma accumulates multiple lemmas under the same head" do
    a = %{name: :"M#a", type: {:data, :"M#P", [], []}, arity: 0}
    b = %{name: :"M#b", type: {:data, :"M#P", [], []}, arity: 1}

    env =
      Env.empty()
      |> Env.put_lemma(:"M#P", a)
      |> Env.put_lemma(:"M#P", b)

    assert Env.lemmas(env, :"M#P") == [a, b]
  end
end
```

Also add, to the same file, the cross-module red test that Task 9 depends on (see the "Cross-module note" above) — this drives `Cure.Elab.Program.elaborate/1` through the REAL `use`-import path (`merge_env/2`), not a hand-built env, so it genuinely exercises the merge:

```elixir
defmodule Cure.Elab.LemmaCrossModuleMergeTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # `use`-importing a module must preserve @lemma-tagged theorems registered in
  # it — Task 9 relies on this (Std.Refine's hole must see Std.Proof.Math's
  # tagged lemma). This test does NOT depend on ProofSearch/Task 2's decorator
  # recognition; it registers the lemma directly via Env.put_lemma to isolate
  # the merge behavior, so it is meaningful to write and run before Task 2.
  test "a lemma registered in a used module survives merge_env into the importer" do
    alias Cure.Core.Env

    home = Env.empty() |> Map.put(:module_owner, "Home")
    entry = %{name: :"Home#fact", type: {:data, :"Home#P", [], []}, arity: 0}
    home = Env.put_lemma(home, :"Home#P", entry)

    # Simulate what `use Home` produces for a caller module: `elaborate/1`'s
    # imported-env merge is `merge_env(base, imported)` (program.ex:369/1516);
    # here `home` stands in for the imported slice directly, since exercising
    # the full `use` surface syntax requires a two-file/module fixture that
    # Tasks 1-8 do not otherwise need. If `Program` exposes no smaller seam to
    # call `merge_env/2` directly (it is private), drive this test instead via
    # two real `mod`s and `Program.elaborate/1` with an actual `use`:
    #
    #   mod Home ... @lemma fn fact() -> P = ... end
    #   mod Caller use Home fn needs_p() -> P = ? end
    #
    # and assert `Env.lemmas(caller_env, p_head) != []`. Prefer the two-`mod`
    # form if it is not meaningfully more code — it exercises the real `use`
    # path end-to-end rather than assuming `merge_env/2`'s call shape.
    assert Env.lemmas(home, :"Home#P") == [entry]
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/proof_search_registry_test.exs`
Expected: FAIL — `function Cure.Core.Env.put_lemma/3 is undefined`. (The cross-module merge test also fails at this point for the same reason — `put_lemma` does not exist yet.)

- [ ] **Step 3: Write minimal implementation**

In `lib/cure/core/inductive.ex`, add `lemmas: %{}` to the `defstruct` list (place it after `import_modules: MapSet.new()`), add `lemmas: %{atom() => [map()]}` to the `@type t` map, and add the accessors next to `put_interface`/`get_interface`:

```elixir
  @doc """
  Register a `@lemma`-tagged theorem for auto proof-search, filed under the
  head atom of its conclusion type. Inert elaborator metadata — the kernel
  never reads it (like `interfaces`/`coherence`). See `Cure.Elab.ProofSearch`.
  """
  @spec put_lemma(t(), atom(), map()) :: t()
  def put_lemma(%__MODULE__{lemmas: ls} = env, head, entry) when is_atom(head),
    do: %{env | lemmas: Map.update(ls, head, [entry], &(&1 ++ [entry]))}

  @doc "The `@lemma` entries filed under conclusion head `head`, or `[]`."
  @spec lemmas(t(), atom()) :: [map()]
  def lemmas(%__MODULE__{lemmas: ls}, head) when is_atom(head), do: Map.get(ls, head, [])
```

Update the struct's `@type t` doc block by appending `lemmas` to the "inert elaborator metadata" comment so the intent is recorded inline.

Then, in `lib/cure/elab/program.ex`, add `lemmas` to `merge_env/2`'s field list (`program.ex:1859-1877`) so a lemma registered in one module survives being merged into an importer — concatenate per-head lists rather than a plain `Map.merge/2` overwrite, since two modules may legitimately contribute lemmas under the same conclusion head:

```elixir
         lemmas: Map.merge(left.lemmas, right.lemmas, fn _head, ls, rs -> ls ++ rs end),
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/proof_search_registry_test.exs`
Expected: PASS (3 tests: the two registry tests plus the cross-module merge test).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/core/inductive.ex lib/cure/elab/program.ex test/cure/elab/proof_search_registry_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): add inert @lemma registry to Core.Env, merged across use-imports" -- lib/cure/core/inductive.ex lib/cure/elab/program.ex test/cure/elab/proof_search_registry_test.exs
```

---

### Task 2: Recognize `@lemma` and register the tagged theorem

**Files:**
- Modify: `lib/cure/elab/declarations.ex` — at signature processing where the def is added via `Env.add_def(env, sig.name, sig.pi, ...)` (`declarations.ex:412`), detect an attached `@lemma` decorator and register the def into the lemma registry. Add a `conclusion_head/1` helper.
- Test: `test/cure/elab/lemma_decorator_test.exs` (Create)

**Interfaces:**
- Consumes: `Cure.Core.Env.put_lemma/3` (Task 1); `sig.pi` (full Core Pi type, available at `declarations.ex:412`); `sig.name`, `sig.quantities`; the decorator accessor `attached_decorator_name({:decorator, m, _})` (`declarations.ex:2373`) and the meta `:decorator` slot (`Keyword.get(meta, :decorator)`, shape `{:decorator, [name: :lemma], args}`, cf. `declarations.ex:2304`).
- Produces:
  - `Cure.Elab.Declarations.conclusion_head(pi_type) :: atom() | nil` — peel the Pi telescope to the codomain and return the head family atom of a `{:data, name, _, _}` conclusion, else `nil`.
  - Registration side effect: a def whose meta carries `@lemma` and whose conclusion is a `{:data, head, _, _}` is `put_lemma`-ed under `head` with entry `%{name: Env.owned_name(env, sig.name), type: sig.pi, arity: <pi telescope length>}` — the OWNER-QUALIFIED name (see the "Why `Env.owned_name/2`" note below Step 3), not bare `sig.name`, so `ProofSearch`'s assembled `{:global, ...}` term matches what ordinary elaboration produces for the same call.

- [ ] **Step 1: Write the failing test**

```elixir
defmodule Cure.Elab.LemmaDecoratorTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.Env

  test "a @lemma-tagged theorem is filed under its conclusion head" do
    source = """
    mod LemmaReg
      use Std.Proof.Math

      @lemma
      fn my_positivity_fact({left: Nat}, {right: Nat},
            lp: IsPositive(left), rp: IsPositive(right)) -> IsPositive(multiply(left, right)) =
        multiplying_positive_numbers_is_positive(lp, rp)
    end
    """

    {:ok, env} = Program.elaborate(source)

    heads = Map.keys(env.lemmas)
    ispos = Enum.find(heads, fn h -> Atom.to_string(h) |> String.ends_with?("IsPositive") end)
    assert ispos != nil, "expected a lemma filed under an IsPositive head, got: #{inspect(heads)}"

    entries = Env.lemmas(env, ispos)
    assert Enum.any?(entries, fn e ->
             Atom.to_string(e.name) |> String.ends_with?("my_positivity_fact")
           end)
  end

  test "an untagged theorem is NOT registered" do
    source = """
    mod NoLemmaReg
      use Std.Proof.Math

      fn my_positivity_fact({left: Nat}, {right: Nat},
            lp: IsPositive(left), rp: IsPositive(right)) -> IsPositive(multiply(left, right)) =
        multiplying_positive_numbers_is_positive(lp, rp)
    end
    """

    {:ok, env} = Program.elaborate(source)
    all_entries = env.lemmas |> Map.values() |> List.flatten()
    refute Enum.any?(all_entries, fn e ->
             Atom.to_string(e.name) |> String.ends_with?("my_positivity_fact")
           end)
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/lemma_decorator_test.exs`
Expected: FAIL — first test fails because `env.lemmas` is empty (nothing registers `@lemma` yet). (The second test should already pass; that is fine — the first failing is the red signal.)

- [ ] **Step 3: Write minimal implementation**

In `lib/cure/elab/declarations.ex`, at the site that builds `env1 = Env.add_def(env, sig.name, sig.pi, {:hole, "__pending__"}, sig.quantities)` (`declarations.ex:412`), thread the lemma registration onto `env1`. Locate the `sig`/`meta` in scope (the surface def meta that `@lemma` is attached to). Wrap:

```elixir
      env1 =
        env
        |> Env.add_def(sig.name, sig.pi, {:hole, "__pending__"}, sig.quantities)
        |> maybe_register_lemma(sig, meta)
```

Add the helpers (near `attached_decorator_name/1`, ~`declarations.ex:2373`):

```elixir
  # Register a def tagged `@lemma` into the proof-search registry, filed under
  # its conclusion head. No-op for untagged defs or non-data conclusions.
  defp maybe_register_lemma(env, sig, meta) do
    with :lemma <- attached_decorator_name(Keyword.get(meta, :decorator)),
         head when not is_nil(head) <- conclusion_head(sig.pi) do
      Env.put_lemma(env, head, %{
        name: Env.owned_name(env, sig.name),
        type: sig.pi,
        arity: pi_arity(sig.pi)
      })
    else
      _ -> env
    end
  end

  # The head family atom of a Pi type's ultimate codomain, or nil if the
  # conclusion is not an indexed/parameterised data application.
  def conclusion_head({:pi, _g, _dom, cod}), do: conclusion_head(cod)
  def conclusion_head({:data, name, _params, _indices}), do: name
  def conclusion_head(_), do: nil

  defp pi_arity({:pi, _g, _dom, cod}), do: 1 + pi_arity(cod)
  defp pi_arity(_), do: 0
```

**Why `Env.owned_name/2`, not bare `sig.name`:** `sig.name` (from `function_signature/2`, `declarations.ex:672`) is a bare atom — qualification happens *inside* `Env.add_def` (`owned_name(env, name)`, not visible to the caller). Task 1's own `entry` contract already says `name` is "its owner-qualified global name" — this line is what makes that true. It matters concretely: the ordinary elaborator qualifies every call target before embedding it in a `{:global, ...}` term (`finish_global_app`, `elaborator.ex:8038`: `name = Env.resolve_key(env, env.defs, name)`), so a hand-written call to `tagged_fact(...)` lowers to `{:global, :"TaggedDemo#tagged_fact"}`. If `ProofSearch` (Task 4) instead assembled `{:global, :tagged_fact}` (bare) from this registry, Task 8's structural `demo_body(green_env) == demo_body(ref_env)` differential would fail on a qualification mismatch alone — a discrepancy Task 8's own troubleshooting hints (Step 3) do not mention, so it would misdirect debugging toward the projection/lemma-assembly logic instead of this registration line. Using `Env.owned_name/2` here is what keeps the two paths byte-identical.

**Verify the decorator name:** confirm the surface `@lemma` lexes/parses to a decorator whose `:name` is `:lemma`. Note: `erasure_class/2`/`@erasure_classes` (`declarations.ex:2303`/`27`) is the whitelist for the *argument* of `@erases(<class>)`, not a decorator-*name* allowlist — do not treat it as the relevant gate. Confirmed by reading `attach_decorator/3` in `lib/cure/compiler/parser.ex:7869`: the parser accepts any decorator name generically (`{:decorator, [name: name], args}`) with no name allowlist, so `@lemma` should parse without any parser change. Do the minimum: the test in Step 1 will tell you whether `@lemma` even parses; if it unexpectedly fails to parse, grep the parser's decorator-handling path directly rather than `erasure_class/2`.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/lemma_decorator_test.exs`
Expected: PASS (2 tests). If the first test still shows an empty registry, confirm `meta` at `declarations.ex:412` is the def meta carrying `:decorator` (print it once with `IO.inspect` while debugging, then remove).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/declarations.ex test/cure/elab/lemma_decorator_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): register @lemma-tagged theorems by conclusion head" -- lib/cure/elab/declarations.ex test/cure/elab/lemma_decorator_test.exs
```

---

### Task 3: `ProofSearch` skeleton — dispatcher, local-context candidate, unique-or-defer

**Files:**
- Create: `lib/cure/elab/proof_search.ex`
- Test: `test/cure/elab/proof_search_test.exs` (Create)

**Interfaces:**
- Consumes: `Cure.Core.Context` (`lookup/2`, `length/1`, `env/1`, `signature/1`); `Cure.Core.Quote.reify/3`; `Cure.Core.Eval.eval/2`; `Cure.Core.Kernel.check/3`; `Cure.Core.Env.lemmas/2` (Task 1).
- Produces:
  - `Cure.Elab.ProofSearch.resolve(goal_core, ctx, env) :: {:ok, core_term} | :none | {:error, {:ambiguous_proof_search, goal_core, [atom_or_term]}}`
  - Internally: `resolve/4` with an extra `state` arg `%{depth: non_neg_integer(), trying: [core_term]}` for Task 6; Task 3 may start with `resolve/3` delegating to `resolve(goal, ctx, env, %{depth: 0, trying: []})`.
  - A candidate is validated by `Kernel.check(ctx, term, goal_value)` where `goal_value = Eval.eval(goal_core, Context.env(ctx))`; a candidate that checks is a *survivor*. Unique-or-defer over survivors: `[]` → `:none`; `[t]` → `{:ok, t}`; `[_, _ | _]` → `{:error, {:ambiguous_proof_search, goal, provenance}}`.

**Design note — local binder types are Values.** `Context.lookup(ctx, k)` returns the binder's type as a *semantic Value*, evaluated in the context that existed when it was pushed. To use binder `k` as a Core candidate term of type matching the goal, mirror how the elaborator types a `{:variable, ...}` reference elsewhere (the reify-with-depth-and-signature pattern at `elaborator.ex:1250`, `Quote.reify(type_value, Context.length(ctx), Context.signature(ctx))`). Do NOT invent de Bruijn arithmetic; copy that call shape. The candidate *term* for binder `k` is `{:var, k}` (Core de Bruijn variable; index 0 = innermost).

- [ ] **Step 1: Write the failing test**

```elixir
defmodule Cure.Elab.ProofSearchTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.ProofSearch
  alias Cure.Core.{Context, Env, Eval, Inductive}

  # A tiny hand-built context: one indexed family P with a single ctor mkP : P,
  # and a local binder h : P in scope. resolve should find `h` by exact type.
  #
  # Real registration API (`Cure.Core.Inductive`, inductive.ex:369-447) is
  # `family/4` + `ctor/3` (build signatures, no registration) + `declare/3`
  # (registers a family and its constructors into an env, returns `Env.t()`
  # directly — not `{:ok, env}`). `Env.add_family/2`/`Env.add_ctor/3` do not
  # exist; do not grep for them.
  defp env_with_p do
    env = Env.empty()
    family = Inductive.family(:P, [], [], 0)
    ctor = Inductive.ctor(:mkP, [], [])
    Inductive.declare(env, family, [ctor])
  end

  test "a local hypothesis whose type equals the goal is found directly" do
    env = env_with_p()
    goal = {:data, :P, [], []}
    goal_val = Eval.eval(goal, [])
    # Context with a single binder h : P.
    ctx = Context.empty(env) |> Context.extend(goal_val)

    assert {:ok, {:var, 0}} = ProofSearch.resolve(goal, ctx, env)
  end

  test "zero candidates yields :none" do
    env = env_with_p()
    goal = {:data, :P, [], []}
    ctx = Context.empty(env) # nothing in scope, no lemmas
    assert :none = ProofSearch.resolve(goal, ctx, env)
  end
end
```

The `env_with_p/0` above already uses the real `Cure.Core.Inductive.family/4`+`ctor/3`+`declare/3` API (verified against `lib/cure/core/inductive.ex:369-447`); no further signature discovery is needed. If direct family registration still proves awkward once implementing, an alternative is to build the context via a one-line `Program.elaborate` of a module declaring `type P` + a function with an in-scope binder, and pull `ctx`/`goal` from a hole goal — but the hand-built form above is preferred for isolation.

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/proof_search_test.exs`
Expected: FAIL — `Cure.Elab.ProofSearch.resolve/3 is undefined`.

- [ ] **Step 3: Write minimal implementation**

```elixir
defmodule Cure.Elab.ProofSearch do
  @moduledoc """
  Auto proof-search over `@lemma`-tagged theorems and local hypotheses
  (design: docs/superpowers/specs/kernel/2026-07-18-auto-lemma-proof-search-design.md).

  Untrusted: only *builds* Core proof terms; every candidate is re-checked by
  the kernel (`Cure.Core.Kernel.check/3`), so search can never make an
  ill-typed program type-check.
  """
  alias Cure.Core.{Context, Eval, Kernel, Quote}

  @depth_limit 5

  @type goal :: term()
  @type result :: {:ok, term()} | :none | {:error, {:ambiguous_proof_search, term(), [term()]}}

  @spec resolve(goal(), Context.t(), Cure.Core.Env.t()) :: result()
  def resolve(goal, ctx, env), do: resolve(goal, ctx, env, %{depth: 0, trying: []})

  # Extended entrypoint (Task 6 fills in depth/cycle guards).
  def resolve(goal, ctx, env, _state) do
    candidates = local_candidates(goal, ctx, env)
    decide(candidates, goal)
  end

  # Each candidate is {term, provenance}. Keep only the kernel-checked survivors.
  defp decide(candidates, goal) do
    survivors = Enum.filter(candidates, fn {term, _prov} -> term != nil end)

    case survivors do
      [] -> :none
      [{term, _}] -> {:ok, term}
      many -> {:error, {:ambiguous_proof_search, goal, Enum.map(many, &elem(&1, 1))}}
    end
  end

  # Local-context search: every binder whose type checks against the goal.
  defp local_candidates(goal, ctx, env) do
    goal_val = Eval.eval(goal, Context.env(ctx))
    len = Context.length(ctx)

    for k <- 0..(len - 1)//1, len > 0 do
      term = {:var, k}

      case Kernel.check(ctx, term, goal_val) do
        :ok -> {term, {:local, k}}
        _ -> {nil, {:local, k}}
      end
    end
    |> Enum.filter(fn {term, _} -> term != nil end)
  end
end
```

Note: `local_candidates` uses `Kernel.check` to *validate by type* rather than comparing reified types — this is simpler and reuses the kernel's conversion. Confirm `Kernel.check(ctx, {:var, k}, goal_val)` is the right arity/shape by matching existing call sites (`elaborator.ex:1403`, `Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx)))`). Adjust the `for` guard so an empty context yields `[]` cleanly.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/proof_search_test.exs`
Expected: PASS (2 tests).

- [ ] **Step 5: Add the unique-or-defer ambiguity test and confirm**

Append to `test/cure/elab/proof_search_test.exs`:

```elixir
  test "two distinct local hypotheses of the goal type are a hard ambiguity error" do
    env = env_with_p()
    goal = {:data, :P, [], []}
    goal_val = Eval.eval(goal, [])
    ctx = Context.empty(env) |> Context.extend(goal_val) |> Context.extend(goal_val)

    assert {:error, {:ambiguous_proof_search, ^goal, provenance}} =
             ProofSearch.resolve(goal, ctx, env)
    assert length(provenance) == 2
  end
```

Run: `mix test test/cure/elab/proof_search_test.exs`
Expected: PASS (3 tests). Two binders both `{:var,0}`/`{:var,1}` check against the goal, so `decide/2` returns the ambiguity error.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/proof_search.ex test/cure/elab/proof_search_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): ProofSearch skeleton with local-context search and unique-or-defer" -- lib/cure/elab/proof_search.ex test/cure/elab/proof_search_test.exs
```

---

### Task 4: Lemma-application candidate with recursive sub-goals

**Files:**
- Modify: `lib/cure/elab/proof_search.ex` — add `lemma_candidates/4`; fold into `resolve/4`.
- Test: `test/cure/elab/proof_search_test.exs` (extend)

**Interfaces:**
- Consumes: `Cure.Core.Env.lemmas/2`; `Cure.Elab.MetaCtx` (`fresh/2` returns `{mctx, id}`, mctx FIRST — cf. `elaborator.ex:7327`); `Cure.Elab.Unify` (`unify(t1, t2, mctx, sig) :: {:ok, mctx} | {:error, _}`, `zonk/2`); `Cure.Elab.Subst.instantiate/2` (module is `Cure.Elab.Subst` in `lib/cure/elab/subst.ex` — NOT `Cure.Core.Subst`, which does not exist; `instantiate(term, values)` substitutes a *list* of solved args into a Pi's codomain — same call shape as `elaborator.ex:7349`).
- Produces:
  - `lemma_candidates(goal, ctx, env, state) :: [{core_term | nil, provenance}]` — for each registry entry under the goal's head, instantiate the lemma's Pi telescope with fresh metavars, unify the instantiated conclusion against the goal, then for each *explicit* hypothesis recursively `resolve/4` a sub-goal; assemble the curried application; validate with `Kernel.check`.
  - The assembled term for a lemma `L` with instantiated implicit/explicit args `a1..an` is the left-nested `{:app, {:app, ..., {:global, L}, a1}, ..., an}` (single-arg `:app`, cf. `term.ex`).

**Design note — instantiate the telescope.** Walk the lemma's Pi type `{:pi, grade, dom, cod}` outermost-in. For each binder: create a fresh metavar `{:meta, id}` (via `MetaCtx.fresh/2`) as its argument placeholder, and `Subst.instantiate` it into `cod` to expose the next domain. After consuming the whole telescope, the residual is the conclusion; unify it against the goal to solve the metavars. Then partition binders into *implicit* (solved purely by that unification — read the solution from the MetaCtx via `Unify.zonk`) and *explicit hypotheses* (the ones the design calls sub-goals: reify the zonked domain to a Core goal and recurse). This mirrors, but is simpler than, `bidir_app_slot` (`elaborator.ex:7326-7410`) — read that function to copy the zonk-then-instantiate ordering and metavar handling; do NOT invent it. The distinction "implicit vs explicit" comes from the surface param grade recorded in the Pi grade; if grade information is insufficient to distinguish, treat any binder whose metavar remains *unsolved* after conclusion-unification as a sub-goal to resolve, and any binder solved by unification as filled — this is behaviorally what the demo needs (`{left}`/`{right}` get solved by unifying the conclusion; `left_is_positive`/`right_is_positive` do not).

- [ ] **Step 1: Write the failing test** (extend `proof_search_test.exs`)

```elixir
  test "a registered lemma whose conclusion unifies with the goal, with sub-goals in context, resolves" do
    # Use the real stdlib so IsPositive/multiply/PositiveSuccessor exist, then
    # drive resolve/3 at a hole goal via an inline module with a tagged lemma.
    source = """
    mod LemmaApp
      use Std.Proof.Math
      use Std.Refine

      @lemma
      fn positivity_of_product({left: Nat}, {right: Nat},
            lp: IsPositive(left), rp: IsPositive(right)) -> IsPositive(multiply(left, right)) =
        multiplying_positive_numbers_is_positive(lp, rp)

      fn demo(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
        refine(multiply(refined_value(left), refined_value(right)),
               positivity_of_product(refinement_proof(left), refinement_proof(right)))
    end
    """

    # The point of THIS task: the explicit-call `demo` must still elaborate, and
    # the tagged lemma is now in the registry AND applicable at that goal.
    assert {:ok, env} = Cure.Elab.Program.elaborate(source)
    heads = Map.keys(env.lemmas)
    assert Enum.any?(heads, fn h -> Atom.to_string(h) |> String.ends_with?("IsPositive") end)
  end
```

The end-to-end "hole resolves via lemma" assertion lands in Task 7/8 (once the trigger is wired). Task 4's own unit-level assertion for `lemma_candidates` is the hand-built one below; add it too:

```elixir
  test "lemma_candidates returns an application term when the conclusion unifies and sub-goals are in scope" do
    # Build: family P(n:Nat)-like via stdlib IsPositive is heavy; instead assert
    # through resolve/3 using the LemmaApp env from the previous test's source.
    source = """
    mod LemmaApp2
      use Std.Proof.Math
      use Std.Refine
      @lemma
      fn pop({left: Nat}, {right: Nat}, lp: IsPositive(left), rp: IsPositive(right))
         -> IsPositive(multiply(left, right)) = multiplying_positive_numbers_is_positive(lp, rp)
      fn demo(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
        refine(multiply(refined_value(left), refined_value(right)), ?)
    end
    """
    {:ok, env} = Cure.Elab.Program.elaborate(source)
    # After Task 7 wiring this elaborates with the hole FILLED; here (Task 4,
    # pre-wiring) we only assert the registry carries `pop` — the resolve path
    # is exercised end-to-end in Task 8.
    entries = env.lemmas |> Map.values() |> List.flatten()
    assert Enum.any?(entries, fn e -> Atom.to_string(e.name) |> String.ends_with?("pop") end)
  end
```

> Rationale: `lemma_candidates/4` is genuinely hard to unit-test in isolation without hand-constructing a full indexed-family context and a metavar/unify state. The design's §8.1 bullet ("conclusion unification instantiates implicits correctly") is verified concretely and unavoidably by the Task 8 green test, which asserts the *found term equals the hand-written application*. Task 4's job is to make `lemma_candidates` exist and be reachable; the strong behavioral proof is the differential golden in Task 8. Keep Task 4's assertions at the registry/reachability level and let Task 8 prove the assembled term is correct.

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/proof_search_test.exs`
Expected: the two new tests may PASS at the registry level even before `lemma_candidates` exists (they only assert registration). That is acceptable — `lemma_candidates` is proven by Task 8. Before writing code, confirm no regression: all Task 3 tests still pass.

- [ ] **Step 3: Write minimal implementation**

Add to `proof_search.ex`. **`resolve/4`'s clause below REPLACES Task 3's `resolve/4` clause in place — do not append it as a second clause.** Task 3's `def resolve(goal, ctx, env, _state) do candidates = local_candidates(goal, ctx, env); decide(candidates, goal) end` is unguarded (matches any input), so appending a new clause below it would compile with a "this clause cannot match" warning and leave the new clause dead — `lemma_candidates` would never run and Task 4's own tests would fail in a confusing way. Edit the existing clause's body in place.

```elixir
  alias Cure.Elab.{MetaCtx, Unify, Subst}

  # ...in resolve/4, pool local + lemma candidates:
  def resolve(goal, ctx, env, state) do
    candidates = local_candidates(goal, ctx, env) ++ lemma_candidates(goal, ctx, env, state)
    decide(candidates, goal)
  end

  defp lemma_candidates(goal, ctx, env, state) do
    case head_of(goal) do
      nil -> []
      head ->
        env
        |> Cure.Core.Env.lemmas(head)
        |> Enum.map(&try_lemma(&1, goal, ctx, env, state))
        |> Enum.filter(fn {term, _} -> term != nil end)
    end
  end

  defp head_of({:data, name, _p, _i}), do: name
  defp head_of(_), do: nil

  # Instantiate the lemma's Pi telescope with metavars, unify the conclusion
  # with the goal, resolve unsolved (explicit-hypothesis) binders as sub-goals,
  # assemble the application, and kernel-check it.
  defp try_lemma(%{name: name, type: pi}, goal, ctx, env, state) do
    mctx = MetaCtx.new()
    {arg_metas, conclusion, mctx} = instantiate_telescope(pi, mctx)

    with {:ok, mctx} <- Unify.unify(conclusion, goal, mctx, env),
         {:ok, args} <- fill_args(arg_metas, ctx, env, mctx, state) do
      term = build_app({:global, name}, args)
      goal_val = Cure.Core.Eval.eval(goal, Context.env(ctx))

      case Kernel.check(ctx, term, goal_val) do
        :ok -> {term, {:lemma, name}}
        _ -> {nil, {:lemma, name}}
      end
    else
      _ -> {nil, {:lemma, name}}
    end
  end

  # Peel every {:pi,g,dom,cod}; for each binder mint a fresh metavar and
  # instantiate it into cod. Returns {reversed-arg-metas-with-domains, conclusion, mctx}.
  defp instantiate_telescope(pi, mctx), do: instantiate_telescope(pi, mctx, [])
  defp instantiate_telescope({:pi, _g, dom, cod}, mctx, acc) do
    {mctx, id} = MetaCtx.fresh(mctx, nil)
    meta = {:meta, id}
    cod2 = Subst.instantiate(cod, [meta])
    instantiate_telescope(cod2, mctx, [{meta, dom} | acc])
  end
  defp instantiate_telescope(conclusion, mctx, acc), do: {Enum.reverse(acc), conclusion, mctx}

  # For each telescope slot: if its metavar is solved by conclusion-unification,
  # use the solution; otherwise treat the (zonked) domain as a sub-goal and recurse.
  defp fill_args(arg_metas, ctx, env, mctx, state) do
    Enum.reduce_while(arg_metas, {:ok, []}, fn {meta, dom}, {:ok, acc} ->
      z = Unify.zonk(meta, mctx)

      if solved?(z) do
        {:cont, {:ok, acc ++ [z]}}
      else
        subgoal = Unify.zonk(dom, mctx)
        subgoal_core = ensure_core(subgoal, ctx)
        case resolve(subgoal_core, ctx, env, deeper(state, subgoal_core)) do
          {:ok, term} -> {:cont, {:ok, acc ++ [term]}}
          _ -> {:halt, :fail}
        end
      end
    end)
    |> case do
      {:ok, args} -> {:ok, args}
      :fail -> :fail
    end
  end

  defp solved?({:meta, _}), do: false
  defp solved?(_), do: true

  defp build_app(head, args), do: Enum.reduce(args, head, fn a, f -> {:app, f, a} end)

  # deeper/2 and ensure_core/2 are placeholders finalized in Task 6 (state) —
  # for Task 4, deeper(state, _) = state and ensure_core(t, _) = t.
```

Verified against the tree (`lib/cure/elab/unify.ex:1-90,557-563`, `lib/cure/elab/subst.ex:82`): `MetaCtx.new/0` exists (`%__MODULE__{}`); `MetaCtx.fresh/2` returns `{ctx, id}`; `Subst.instantiate/2` takes a LIST (`instantiate(term, values)`, `values[0]` = outermost binder) — the one-element list `[meta]` per peeled Pi binder in `instantiate_telescope/3` above is the correct call shape; `Unify.zonk/2`'s `force`-then-recurse leaves an unsolved metavariable as `{:meta, id}` (`unify.ex:557-563`), so `solved?/1` above is correct as written. `Unify.unify/4`'s 4th arg is the signature `Env`.

- [ ] **Step 4: Run tests**

Run: `mix test test/cure/elab/proof_search_test.exs`
Expected: PASS (Task 3 tests + the two registry-level Task 4 tests). If the module fails to compile due to an API mismatch, fix the signature to match the tree and re-run.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/proof_search.ex test/cure/elab/proof_search_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): lemma-application candidates with recursive sub-goals" -- lib/cure/elab/proof_search.ex test/cure/elab/proof_search_test.exs
```

---

### Task 5: Refinement/Sigma second-projection candidate (leaf proofs)

**Files:**
- Modify: `lib/cure/elab/proof_search.ex` — add `projection_candidates/3`; fold into the candidate pool.
- Test: `test/cure/elab/proof_search_test.exs` (extend)

**Interfaces:**
- Consumes: `Context.lookup/2` (binder type Value); the Sigma second-projection global `:sigma_second` (cf. `elaborator.ex:1182`, `declarations.ex:1920` — `.2` lowers to `sigma_second`); `Quote.reify/3`; `Cure.Core.Inductive.builtin/2`; `Cure.Core.Normalise.whnf_value/2-3`.
- Produces:
  - `projection_candidates(goal, ctx, env) :: [{core_term | nil, provenance}]` — for each local binder `k` whose type WHNFs to the Sigma family `Sigma(a, P)` (i.e. `{:vdata, sigma_fam, [a_value, predicate_value]}`, `Sigma`'s two params per `lib/cure/core/builtins.ex:346-353`), form the candidate term `sigma_second` applied to the binder with its implicit `{a}`/`{predicate}` arguments **reified directly from `a_value`/`predicate_value`** (`build_app({:global, :sigma_second}, [reify(a_value), reify(predicate_value), {:var, k}])`), whose type is `P(sigma_first(binder))`. Validate with `Kernel.check` against the goal. Match the exact `sigma_second` application shape (implicit `{a}`/`{predicate}` args) used by `sigma_projection/5` at `elaborator.ex:1181-1184`.

**Design note.** This is the one non-obvious capability (design §5). The demo's sub-goals `IsPositive(refined_value(left))` are NOT loose variables — they are the second projection of the `PositiveNatural` (= `Sigma(Nat, IsPositive)`) binder.

`sigma_projection/5` (`elaborator.ex:1181-1184`) is **not directly reusable** here: read its body — `elaborate_implicit_global_app(env, gname, [inner], names, ctx)` — and its own comment ("`inner` is the SURFACE AST (not the already-lowered term) so the wrapper infers it in the caller's context", `elaborator.ex:1179`). ProofSearch has no surface AST for a Core-level local binder `{:var, k}`; there is nothing to pass as `inner`. Do not attempt to call `sigma_projection/5` or `elaborate_implicit_global_app` from `ProofSearch`.

**The implicit `{a}`/`{predicate}` arguments must NOT be fresh metavars.** An earlier draft of this task proposed minting `{:meta, a_id}`/`{:meta, pred_id}` (via `MetaCtx`) and passing a term containing them straight into `Kernel.check`, on the theory that "the kernel's own conversion checking solves the metavars implicitly." That theory is false and the construction crashes: `Cure.Core.Term.t()` has no `{:meta, _}` variant — grep confirms zero occurrences of `:meta` in `lib/cure/core/eval.ex`, `lib/cure/core/kernel.ex`, or `lib/cure/core/term.ex` — and `Cure.Elab.Subst`'s own moduledoc states plainly (`subst.ex:8`) that "metavariables never reach the kernel." `Eval.eval/2` has no catch-all clause (`eval.ex:22-106`), so `Kernel.check`/`Kernel.infer` evaluating an argument position that is a bare `{:meta, id}` raises `FunctionClauseError` — an unhandled exception, not a graceful `{:error, _}` — the very first time `projection_candidates` runs on a real Sigma-typed binder (which is every run of the Task 8 green test, since its two sub-goals resolve *only* via projection). There is also no unification step in this candidate (unlike `lemma_candidates`, which unifies a lemma's conclusion against the goal to solve its implicits) that could ever solve these metavars in the first place, so even a defensive `try/rescue` would leave the candidate permanently unresolvable.

The correct construction needs no metavars at all: `sigma_params/3`'s own WHNF match already exposes the Sigma family's two params — `{:vdata, ^sigma_fam, [a_value, predicate_value]}` — and those ARE the values `sigma_second`'s implicit arguments must carry (they are the *definition* of the binder's Sigma type, not something to search for). Capture them instead of discarding them, reify each to a Core term with `Quote.reify(v, Context.length(ctx), Context.signature(ctx))` — the exact depth/sig convention `telescope_arity_of/4` uses for the same "reify a context-relative semantic Value back to a Core term" step (`elaborator.ex:1250`) — and splice the two reified, fully concrete terms into the `sigma_second` application in place of `{:meta, a_id}`/`{:meta, pred_id}`. The assembled term is meta-free before it ever reaches `Kernel.check`. Use `positional_projection/5` (`elaborator.ex:1213-1234`) only as reference documentation for the `sigma_second` application *shape* (argument order, arity), not as a function to call.

- [ ] **Step 1: Write the failing test** (extend `proof_search_test.exs`)

```elixir
  test "a refinement-typed local yields its proof projection as a candidate" do
    # `value : PositiveNatural` in scope; goal `IsPositive(refined_value(value))`
    # must resolve to refinement_proof(value) == value.2 (sigma_second).
    source = """
    mod ProjLeaf
      use Std.Proof.Math
      use Std.Refine

      fn proof_of(value: PositiveNatural) -> IsPositive(refined_value(value)) = ?
    end
    """
    # Before Task 7 wiring the ? in body position is handled by the existing
    # body-hole clause, so this asserts the resolver is *reachable* from a body
    # hole once wired. For Task 5, assert the projection helper directly instead:
    assert function_exported?(Cure.Elab.ProofSearch, :resolve, 3)
  end
```

> The projection candidate is proven behaviorally by the Task 8 green test (its two sub-goals resolve *only* via projection). Task 5's isolated assertion is weak by necessity (building a Sigma-typed context by hand is as much code as the feature); the load-bearing proof is Task 8. Keep this test as a reachability guard and rely on Task 8.

- [ ] **Step 2: Run test to verify current state**

Run: `mix test test/cure/elab/proof_search_test.exs`
Expected: PASS at reachability level; no regression in Task 3/4 tests.

- [ ] **Step 3: Write minimal implementation**

Add `projection_candidates/3` and include it in the pool. **The `resolve/4` clause below REPLACES Task 4's `resolve/4` clause in place** (same reason as Task 4's note: appending a same-shaped clause leaves the old one shadowing the new one, since Elixir matches clauses top-to-bottom and Task 4's clause has no discriminating guard).

```elixir
  def resolve(goal, ctx, env, state) do
    candidates =
      local_candidates(goal, ctx, env) ++
        projection_candidates(goal, ctx, env) ++
        lemma_candidates(goal, ctx, env, state)

    decide(candidates, goal)
  end

  defp projection_candidates(goal, ctx, env) do
    goal_val = Cure.Core.Eval.eval(goal, Context.env(ctx))
    len = Context.length(ctx)

    for k <- 0..(len - 1)//1, len > 0 do
      case sigma_params(Context.lookup(ctx, k), ctx, env) do
        {:ok, a_value, predicate_value} ->
          term = sigma_second_of({:var, k}, a_value, predicate_value, ctx)

          case Kernel.check(ctx, term, goal_val) do
            :ok -> {term, {:projection, k}}
            _ -> {nil, {:projection, k}}
          end

        :error ->
          {nil, {:projection, k}}
      end
    end
    |> Enum.filter(fn {term, _} -> term != nil end)
  end

  # If a Value is a Sigma/dependent-pair type (or aliases to one, like
  # `PositiveNatural = {value: Nat | IsPositive(value)}`), return its two
  # family params `{:ok, a_value, predicate_value}`; else `:error`. Uses the
  # SAME canonical-family lookup the elaborator itself uses everywhere else it
  # needs "is this the Sigma family" (`Inductive.builtin(env, :sigma)` — see
  # `elaborator.ex:882,1242,1622,1827,8221`; confirmed via
  # `lib/cure/core/builtins.ex:344-353`'s `sigma_family/1`, the seed the
  # `@builtin(:sigma)` decl in `Std.Sigma` mirrors). Sigma has exactly two
  # params (`a: Type`, `b: (a) -> Type`) and zero indices, so `{:vdata, name,
  # params}`'s `params` is the 2-element list `[a_value, predicate_value]`
  # (`builtins.ex:346-353`). `Eval.eval({:data,...})` produces `{:vdata, name,
  # params}` (`eval.ex:62-63`); a type ALIAS's pushed Value may be an
  # un-delta-reduced neutral global application rather than already-expanded
  # Sigma, so whnf it first via `Normalise.whnf_value/2-3`
  # (`lib/cure/core/normalise.ex:56`) before comparing the family name — mirror
  # `telescope_arity_of/4`'s `Kernel.normalize`-then-match pattern
  # (`elaborator.ex:1239-1252`) if the plain Value-level whnf does not see
  # through `PositiveNatural`'s alias in practice.
  defp sigma_params(type_value, ctx, env) do
    case Cure.Core.Inductive.builtin(env, :sigma) do
      nil ->
        :error

      sigma_fam ->
        case Cure.Core.Normalise.whnf_value(type_value, Context.signature(ctx)) do
          {:vdata, ^sigma_fam, [a_value, predicate_value]} -> {:ok, a_value, predicate_value}
          _ -> :error
        end
    end
  end

  # `{:var,k}.2` — sigma_second applied with its implicit `{a}`/`{predicate}`
  # arguments reified DIRECTLY from the Sigma family's own params (NOT fresh
  # metavars: there is nothing to solve here — `sigma_params/3` already pinned
  # down `a_value`/`predicate_value` from the binder's own type, and
  # `Cure.Core.Term.t()` has no `{:meta, _}` variant for an unsolved one to
  # occupy — see the design note above for why a metavar-based construction
  # crashes `Kernel.check`/`Eval.eval` instead of being "solved implicitly").
  # NOT `{:hole,...}` either — holes would recurse into proof search — and NOT
  # a call into `elaborate_implicit_global_app`/`sigma_projection`, which
  # require a surface AST this layer does not have. `Quote.reify/3`'s
  # depth/sig convention (`Context.length(ctx)`, `Context.signature(ctx)`)
  # mirrors `telescope_arity_of/4`'s reify call (`elaborator.ex:1250`).
  defp sigma_second_of(var_term, a_value, predicate_value, ctx) do
    depth = Context.length(ctx)
    sig = Context.signature(ctx)
    a_term = Cure.Core.Quote.reify(a_value, depth, sig)
    predicate_term = Cure.Core.Quote.reify(predicate_value, depth, sig)
    build_app({:global, :sigma_second}, [a_term, predicate_term, var_term])
  end
```

**Critical:** `sigma_params/3` above is verified against the tree (`Inductive.builtin/2`, `Eval`'s `{:vdata,...}` shape, `Normalise.whnf_value/2-3`, and `Std.Sigma`'s exact 2-param family shape — see the comment above it), not a blind placeholder, but the ONE thing to double-check while implementing is whether a `PositiveNatural`-typed binder's pushed Value needs the `Kernel.normalize`-on-the-reified-term fallback (mirroring `telescope_arity_of/4`, `elaborator.ex:1239-1252`) instead of the plain Value-level `whnf_value` — i.e., whether `PositiveNatural`'s alias is already expanded to `{:vdata, sigma_fam, params}` by the time it reaches `Context.lookup`, or still sits behind a neutral global application. `sigma_second_of/4` above reifies the family's own already-known params (not metavars, not `{:hole,...}`, not a call into the surface-AST-only projection helpers) — see the design note above for why that revision was necessary. The Task 8 green test is the acceptance gate: if projection candidates are wrong (including if `sigma_params/3` under- or over-recognizes), Task 8 fails.

- [ ] **Step 4: Run tests**

Run: `mix test test/cure/elab/proof_search_test.exs`
Expected: PASS; no regression. (Behavioral proof deferred to Task 8.)

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/proof_search.ex test/cure/elab/proof_search_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): refinement/Sigma proof-projection candidates" -- lib/cure/elab/proof_search.ex test/cure/elab/proof_search_test.exs
```

---

### Task 6: Termination — depth bound and cycle stack

**Files:**
- Modify: `lib/cure/elab/proof_search.ex` — implement `deeper/2`, the `@depth_limit` guard, and the `trying` cycle stack; finalize `ensure_core/2`.
- Test: `test/cure/elab/proof_search_test.exs` (extend)

**Interfaces:**
- Consumes: `Cure.Core.Conv.conv?/5` (`lib/cure/core/conv.ex`) for up-to-conversion cycle detection, OR structural `==` on zonked Core goals if `Conv` is awkward from this layer.
- Produces:
  - `resolve(goal, ctx, env, %{depth: d, trying: ts})` returns `:none` when `d > @depth_limit` OR when `goal` is already in `ts` (up to conversion). `deeper(state, subgoal)` increments `depth` and pushes `subgoal` onto `trying`.

- [ ] **Step 1: Write the failing test** (extend `proof_search_test.exs`)

```elixir
  test "a self-referential lemma set does not loop — cyclic goal abandons the branch" do
    # A lemma whose only hypothesis is its own conclusion: Cyc(n) -> Cyc(n).
    # With no base case and no local hypothesis, resolve must return :none
    # (not loop) because the sub-goal equals a goal already on the stack.
    source = """
    mod CycLemma
      use Std.Proof.Math
      type Cyc indices (n: Nat)
        MkCyc : Cyc(n) -> Cyc(n)
      @lemma
      fn cyc_step({n: Nat}, prev: Cyc(n)) -> Cyc(n) = MkCyc(prev)
    end
    """
    {:ok, env} = Cure.Elab.Program.elaborate(source)

    # Drive resolve/4 DIRECTLY at goal Cyc(n) with an empty context (no Cyc
    # hypothesis in scope) — this is the only candidate source is `cyc_step`
    # itself, whose sole hypothesis is again `Cyc(n)`, so an unguarded resolver
    # recurses forever. This must genuinely be red before Task 6's guards land
    # (Program.elaborate alone does not invoke ProofSearch until Task 7 wires
    # the hole trigger, so this test calls resolve/4 itself rather than relying
    # on elaborate to reach it).
    cyc_family = Cure.Core.Env.resolve_key(env, env.families, :Cyc)
    zero = {:ctor, Cure.Core.Env.resolve_key(env, env.ctors, :Z), []}
    goal = {:data, cyc_family, [], [zero]}
    ctx = Cure.Core.Context.empty(env)

    assert :none = Cure.Elab.ProofSearch.resolve(goal, ctx, env, %{depth: 0, trying: []})
  end

  test "depth bound: a real, satisfiable candidate is suppressed once the depth limit is exceeded" do
    # env_with_p/0 gives a genuine candidate (`h : P` in scope for goal `P`) so
    # this test discriminates the guard: WITHOUT it, resolve finds {:var, 0}
    # regardless of `depth`; WITH it, `depth: 999` (> @depth_limit) must force
    # :none even though a real proof is sitting right there in context.
    env = env_with_p()
    goal = {:data, :P, [], []}
    goal_val = Eval.eval(goal, [])
    ctx = Context.empty(env) |> Context.extend(goal_val)

    assert {:ok, {:var, 0}} = Cure.Elab.ProofSearch.resolve(goal, ctx, env, %{depth: 0, trying: []})
    assert :none = Cure.Elab.ProofSearch.resolve(goal, ctx, env, %{depth: 999, trying: []})
  end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/proof_search_test.exs`
Expected: FAIL on both new tests before Step 3's guards exist — the cyclic test hangs/exhausts the stack (kill it if it does not terminate within the test timeout; that non-termination *is* the red signal) because `resolve/4` recurses into `cyc_step`'s hypothesis `Cyc(n)` forever with no cycle check; the depth-bound test's second assertion fails because `resolve/4` ignores `state.depth` entirely and still returns `{:ok, {:var, 0}}` when `depth: 999`.

- [ ] **Step 3: Write minimal implementation**

**These two clauses REPLACE Task 5's single `resolve/4` clause in place** (same reason as Tasks 4/5's notes) — Task 5's clause has no discriminating guard, so it must be deleted, not left in place alongside these.

```elixir
  def resolve(goal, ctx, env, %{depth: d} = _state) when d > @depth_limit, do: :none

  def resolve(goal, ctx, env, %{trying: ts} = state) do
    if Enum.any?(ts, &same_goal?(&1, goal, ctx, env)) do
      :none
    else
      candidates =
        local_candidates(goal, ctx, env) ++
          projection_candidates(goal, ctx, env) ++
          lemma_candidates(goal, ctx, env, state)

      decide(candidates, goal)
    end
  end

  defp deeper(%{depth: d, trying: ts}, subgoal), do: %{depth: d + 1, trying: [subgoal | ts]}

  defp ensure_core(term, _ctx), do: term # already a Core term from zonk/reify

  # Up-to-conversion equality of two goal Core terms, evaluated in ctx.
  defp same_goal?(a, b, ctx, env) do
    va = Cure.Core.Eval.eval(a, Context.env(ctx))
    vb = Cure.Core.Eval.eval(b, Context.env(ctx))
    Cure.Core.Conv.conv?(va, vb, Context.env(ctx), Context.length(ctx), env)
  end
```

Verified against the tree (`lib/cure/core/conv.ex:49`): `conv?/5`'s signature is `conv?(term1, term2, env, depth, sig \\ nil)`, matching the call above. If `Conv` from this layer proves awkward in practice, fall back to structural `==` on zonked goals — cycle detection need not be complete, only sound-enough to stop the demo's and the test's loops.

- [ ] **Step 4: Run tests**

Run: `mix test test/cure/elab/proof_search_test.exs`
Expected: PASS (all Task 3–6 tests). No test hangs.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/proof_search.ex test/cure/elab/proof_search_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): depth-bound and cycle-stack termination guards for ProofSearch" -- lib/cure/elab/proof_search.ex test/cure/elab/proof_search_test.exs
```

---

### Task 7: Wire the trigger + RED integration test

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` — add a `{:hole, meta, _}` clause to `elaborate_expr_checked` (place it immediately BEFORE the catch-all at `elaborator.ex:1760`).
- Test: `test/cure/elab/proof_hole_resolution_test.exs` (Create)

**Interfaces:**
- Consumes: `Cure.Elab.ProofSearch.resolve/3` (Tasks 3–6); the checked-mode expected type `expected_core` (the Core goal, meta-free at the demo's proof slot per spec §4.1); `ctx`, `env`.
- Produces: at a proof-position hole,
  - `resolve/3` → `{:ok, term}` ⇒ return `{:ok, term}` (elaboration continues as if authored);
  - `resolve/3` → `:none` ⇒ return `{:ok, {:hole, Keyword.get(meta, :name, "")}}` (graceful unsolved hole — mirrors `declarations.ex:1041`, so `hole_goals`/`check_codegen_ready` see it like a body-level hole);
  - `resolve/3` → `{:error, {:ambiguous_proof_search, _, _}} = err` ⇒ return `err` (surface the ambiguity as an elaboration error).

- [ ] **Step 1: Write the failing test**

```elixir
defmodule Cure.Elab.ProofHoleResolutionTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # A LOCAL, UNTAGGED lemma. No @lemma anywhere → the argument-position hole
  # must reach the resolver, which DECLINES, so the hole survives GRACEFULLY as
  # an unfilled hole — NOT the raw {:unsupported_expression,...} of today, and
  # NOT auto-discharged. This proves resolution is gated on the tag.
  @red """
  mod RedUntagged
    use Std.Proof.Math
    use Std.Refine

    fn untagged_fact({left: Nat}, {right: Nat},
          lp: IsPositive(left), rp: IsPositive(right)) -> IsPositive(multiply(left, right)) =
      multiplying_positive_numbers_is_positive(lp, rp)

    fn demo(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
      refine(multiply(refined_value(left), refined_value(right)), ?)
  end
  """

  test "an argument-position proof hole with no tagged lemma elaborates to a graceful unfilled hole" do
    assert {:ok, env} = Program.elaborate(@red)

    # The program TYPECHECKS (hole accepted at its goal type) but the codegen
    # gate reports the unfilled hole — NOT a hard {:unsupported_expression}.
    assert {:error, {:unfilled_hole, name}} = Program.check_codegen_ready(env)
    assert Atom.to_string(name) |> String.contains?("demo")
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/proof_hole_resolution_test.exs`
Expected: FAIL — today `Program.elaborate(@red)` returns `{:error, {:unsupported_expression, {:hole, ...}}}` (the argument-position hole has no clause), so the first `assert {:ok, env}` fails. This is the precise "wrong reason" the spec §8.2 warns about; the task makes it the graceful path.

- [ ] **Step 3: Write minimal implementation**

In `lib/cure/elab/elaborator.ex`, immediately before the catch-all clause `def elaborate_expr_checked(expr, expected_core, names, ctx, env)` at line 1760:

```elixir
  # A proof-position hole: attempt auto-resolution before falling through to a
  # graceful unsolved-hole term. `expected_core` is the Core goal at this slot.
  # Soundness: ProofSearch only builds a term; the kernel re-checks it. On
  # :none the hole survives as {:hole, name} exactly like a body-level hole
  # (declarations.ex:1041), so hole_goals / check_codegen_ready still gate it.
  def elaborate_expr_checked({:hole, meta, _}, expected_core, _names, ctx, env) do
    case Cure.Elab.ProofSearch.resolve(expected_core, ctx, env) do
      {:ok, term} -> {:ok, term}
      :none -> {:ok, {:hole, Keyword.get(meta, :name, "")}}
      {:error, _} = err -> err
    end
  end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/proof_hole_resolution_test.exs`
Expected: PASS. `elaborate` now succeeds (hole gracefully accepted), and `check_codegen_ready` reports `{:unfilled_hole, :"RedUntagged#demo"}` because the resolver declined (no `@lemma`).

- [ ] **Step 5: Run the ProofSearch unit tests + a broad elaborator test to check for regression**

Run: `mix test test/cure/elab/proof_search_test.exs test/cure/elab/hole_goal_test.exs test/cure/elab/hole_test.exs`
Expected: PASS. Body-level holes still behave as before; the new clause only matches `{:hole,...}` in checked-mode expression position.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/elaborator.ex test/cure/elab/proof_hole_resolution_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): resolve proof-position holes via ProofSearch, graceful on decline" -- lib/cure/elab/elaborator.ex test/cure/elab/proof_hole_resolution_test.exs
```

---

### Task 8: GREEN — tagged lemma discharges the hole + differential golden

**Files:**
- Test: `test/cure/elab/proof_hole_resolution_test.exs` (extend)

**Interfaces:**
- Consumes: everything above; `Program.elaborate/1`; `Program.check_codegen_ready/1`; the elaborated `env.defs` map (to pull a function's Core body for the differential).

- [ ] **Step 1: Write the failing test** (extend `proof_hole_resolution_test.exs`)

```elixir
  # Identical to @red but the local lemma is TAGGED @lemma. Now the hole must be
  # discharged automatically: sub-goals IsPositive(refined_value(left/right))
  # come from the refinement projections of the two PositiveNatural binders.
  #
  # CRITICAL: @green and @reference below use the SAME module name
  # (`TaggedDemo`). Global def names are module-qualified (`Cure.Elab.Name.qualify/2`,
  # `Owner#base` — `lib/cure/elab/name.ex:17-19`) via `Env.resolve_key`'s
  # `owned_name`-first lookup (`inductive.ex:116-152`), so the LOCAL lemma
  # `tagged_fact` would resolve to a DIFFERENT global atom in each program if
  # the two modules had different names (`TaggedDemo#tagged_fact` vs some other
  # owner) — making `demo_body(green_env) == demo_body(ref_env)` structurally
  # false no matter how correct ProofSearch is. `use`d stdlib calls
  # (`refine`/`refined_value`/`multiply`/…) are unaffected by this — they are
  # owned by `Std.Refine`/`Std.Proof.Math` regardless of the calling module's
  # name, resolved via `resolve_key`'s owner-alias fallback — only a LOCALLY
  # defined name like `tagged_fact` is owned by its enclosing module. Each
  # `Program.elaborate` call below builds an independent `Env` from scratch (no
  # shared registry keyed by module name across the two calls — confirmed: the
  # only cross-call cache in `lib/cure/elab/program.ex` is the `use`-dependency
  # loader keyed by `module_name -> {:loaded, interface}` for modules loaded
  # BY PATH from disk, which does not apply to an inline top-level source
  # string), so reusing the same module name for both is safe.
  @green """
  mod TaggedDemo
    use Std.Proof.Math
    use Std.Refine

    @lemma
    fn tagged_fact({left: Nat}, {right: Nat},
          lp: IsPositive(left), rp: IsPositive(right)) -> IsPositive(multiply(left, right)) =
      multiplying_positive_numbers_is_positive(lp, rp)

    fn demo(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
      refine(multiply(refined_value(left), refined_value(right)), ?)
  end
  """

  # Same program, same module name, but the proof is written BY HAND (no hole).
  # Its `demo` body is the reference the resolved term must equal.
  @reference """
  mod TaggedDemo
    use Std.Proof.Math
    use Std.Refine

    @lemma
    fn tagged_fact({left: Nat}, {right: Nat},
          lp: IsPositive(left), rp: IsPositive(right)) -> IsPositive(multiply(left, right)) =
      multiplying_positive_numbers_is_positive(lp, rp)

    fn demo(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
      refine(multiply(refined_value(left), refined_value(right)),
             tagged_fact(refinement_proof(left), refinement_proof(right)))
  end
  """

  defp demo_body(env) do
    {_name, %{body: body}} =
      Enum.find(env.defs, fn {name, _} -> Atom.to_string(name) |> String.ends_with?("demo") end)
    body
  end

  test "tagging the lemma discharges the hole and the program passes the codegen gate" do
    assert {:ok, env} = Program.elaborate(@green)
    assert :ok = Program.check_codegen_ready(env)
  end

  test "the found proof term equals the hand-written proof term (same-run differential)" do
    {:ok, green_env} = Program.elaborate(@green)
    {:ok, ref_env} = Program.elaborate(@reference)

    assert demo_body(green_env) == demo_body(ref_env)
  end
```

- [ ] **Step 2: Run test to verify it fails/passes**

Run: `mix test test/cure/elab/proof_hole_resolution_test.exs`
Expected: the two new tests initially FAIL if any of Tasks 4–6 (lemma application, projection, assembly) is incomplete — this is the real behavioral gate for those tasks. The differential test is the strongest signal: it fails until the assembled term exactly matches the hand-written `tagged_fact(refinement_proof(left), refinement_proof(right))`.

- [ ] **Step 3: Make it green**

No new production file in this task if Tasks 4–6 are correct. If the differential fails, the diff between `demo_body(green_env)` and `demo_body(ref_env)` pinpoints the discrepancy — typically:
- the projection candidate not producing the same `sigma_second`/`refinement_proof` shape (fix Task 5's `sigma_second_of/4` to reify the Sigma family's own params — see Task 5's design note — exactly), or
- implicit arguments zonked to a different-but-convertible form (normalize both via the same reify/zonk path in `ProofSearch`'s own construction before returning the term, so the *implementation* always produces a fully-zonked, structurally-canonical term).

The `==` assertion is per spec §8.3's explicit mandate and is NOT to be weakened to `Cure.Core.Conv.conv?` — a `conv?`-only pass would hide implicit arguments left as unzonked metavars or filled in a non-canonical (but convertible) shape, which is exactly the class of construction bug this test exists to catch. Fix `ProofSearch`'s construction (zonk before returning; match the canonical `sigma_second`/`{:global, name}` application shape) until the bodies are `==`. The test is immutable once green; if `==` is ever suspected to be the wrong bar, that requires first proving — by inspecting both bodies and showing they differ only in a benign, unzonked-metavar way that conversion also accepts — that the test itself demands more than spec §8.3 intends, and stating that explicitly before touching it.

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/elab/proof_hole_resolution_test.exs`
Expected: PASS (red test from Task 7 + both green tests).

- [ ] **Step 5: Commit**

```bash
git add -- test/cure/elab/proof_hole_resolution_test.exs lib/cure/elab/proof_search.ex
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(elab): @lemma discharges proof hole; found term equals hand-written proof" -- test/cure/elab/proof_hole_resolution_test.exs lib/cure/elab/proof_search.ex
```

(If Step 3 required no `proof_search.ex` change, drop it from the pathspec.)

---

### Task 9: Ship the stdlib demo + regression

**Files:**
- Modify: `lib/std/proof_math.cure` — add `@lemma` to `multiplying_positive_numbers_is_positive` (`proof_math.cure:111`).
- Modify: `lib/std/refine.cure` — rewrite `multiply_positive_natural_numbers` (`refine.cure:47-51`) to leave the proof hole.
- Test: `test/cure/stdlib/refine_test.exs` (existing — must stay green), `test/cure/meta_ast/conformance_tripwire_test.exs` (existing — must stay green).

**Interfaces:**
- Consumes: the whole feature (Tasks 1–8). After this task the shipped `Std.Refine` relies on the resolver to fill the hole at every elaboration. This is the first point in the plan where the lemma is registered in one module (`Std.Proof.Math`) and consumed via a hole in a *different* module (`Std.Refine`, `use Std.Proof.Math`) — exactly the cross-module path Task 1's `merge_env/2` fix and cross-module red test exist to cover. If Step 3 below fails with an empty/missing-lemma-style resolution failure, re-check that Task 1's `merge_env/2` change actually landed rather than debugging `ProofSearch` itself.

- [ ] **Step 1: Add `@lemma` to the stdlib multiply lemma**

In `lib/std/proof_math.cure`, immediately above `fn multiplying_positive_numbers_is_positive` (line 111), add the decorator:

```
  @lemma
  fn multiplying_positive_numbers_is_positive(
```

- [ ] **Step 2: Rewrite the stdlib multiply refinement to use the hole**

In `lib/std/refine.cure`, replace lines 47-51:

```
  ## Multiplying two positive natural numbers preserves positivity.
  fn multiply_positive_natural_numbers(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
    refine(
      multiply(refined_value(left), refined_value(right)),
      ?
    )
```

- [ ] **Step 3: Run the stdlib refine + proof_math tests**

Run: `mix test test/cure/stdlib/refine_test.exs test/cure/stdlib/proof_math_test.exs`
Expected: PASS. In particular `refine_test.exs`'s `multiply_positive_natural_numbers(two(), two())` (line 53) and the explicit `multiply_positive_values` (lines 19-23) must both still elaborate — the shipped hole is filled by the resolver, and the explicit form is unaffected.

- [ ] **Step 4: Run the MetaAST conformance tripwire**

Run: `mix test test/cure/meta_ast/conformance_tripwire_test.exs`
Expected: PASS. `@lemma` is an ordinary decorator (the `:decorator` node tag is already in the frozen vocabulary); the `?` hole is an existing node kind. If the tripwire reports a NEW meta node tag, stop — the `@lemma`/hole surface introduced an unexpected AST shape and must be classified before proceeding.

- [ ] **Step 5: Targeted regression sweep**

Run: `mix test test/cure/elab/ test/cure/stdlib/ test/cure/core/final_core_boundary_test.exs test/cure/elab/program_codegen_gate_test.exs`
Expected: PASS. (The full suite runs once at the Stage 6 gate, outside this plan — do not run it concurrently with any other suite.)

- [ ] **Step 6: Commit**

```bash
git add -- lib/std/proof_math.cure lib/std/refine.cure
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(std): multiply_positive_natural_numbers discharges its proof via auto-search" -- lib/std/proof_math.cure lib/std/refine.cure
```

---

## Self-Review

**Spec coverage** (design §-by-§):
- §3 soundness (kernel re-checks) → Task 3 `Kernel.check` validation + Task 7 graceful fallthrough; §3 runtime-cost note → no grading change made (Global Constraints).
- §4.1 trigger (hole clause on `elaborate_expr_checked`) → Task 7.
- §4.2 dispatcher/solver seam → Task 3 `resolve/4` candidate pool (ordered: local, projection, lemma).
- §4.3 registry + resolution → Task 1 (registry), Task 2 (registration), Task 4 (resolution).
- §5 refinement leaf projection → Task 5.
- §6 unique-or-defer → Task 3 `decide/2`; termination → Task 6.
- §8.1 capability unit tests → Tasks 1,3,4,5,6; §8.2 red → Task 7; §8.3 green + differential → Task 8; §8.4 regression + tripwire → Task 9.
- §9 files → `lib/cure/elab/program.ex` (Task 1's `merge_env/2` fix) is an addition beyond the design's indicative list; §9 is explicitly "indicative; finalized in the plan," and this addition is required for Task 9's cross-module lemma visibility (see Task 1's "Cross-module note") — all other created/modified files match.

**Known honest gaps (called out inline, not hidden):** Tasks 4 and 5's *isolated* unit assertions are reachability-level, because hand-constructing an indexed-family + metavar + Sigma context is as much code as the feature and would couple the test to internals. Their behavioral proof is the Task 8 differential golden, which is strong (found term must structurally equal the hand-written proof). This is a deliberate, disclosed testing trade-off, consistent with spec §8.3 designating the differential as the load-bearing check. Separately, cross-module lemma visibility (Task 1's `merge_env/2` fix) has its own dedicated red test in Task 1, precisely because Task 8's differential does not exercise that path (its lemma and hole share a module) and Task 9 is the first task that does.

**Placeholder scan:** `MetaCtx.new/0`, `MetaCtx.fresh/2`, `Subst.instantiate/2`'s list-argument shape, `Unify.unify/4`/`Unify.zonk/2`, and `Conv.conv?/5`'s argument order are all confirmed verbatim against the tree in this review (`lib/cure/elab/unify.ex:1-90,557`; `lib/cure/elab/subst.ex:82`; `lib/cure/core/conv.ex:49`) — the code as written already uses the real call shapes, not placeholders. `sigma_params/3` (Task 5) is likewise implemented against a confirmed real helper (`Inductive.builtin/2`, `Normalise.whnf_value/2-3`, `Std.Sigma`'s exact 2-param family shape) rather than left as a `false` stub, and its implicit arguments are reified directly from the family's own already-known params rather than left as unsolvable fresh metavars (an earlier draft's metavar construction was found to crash `Kernel.check`/`Eval.eval` — `Cure.Core.Term.t()` has no `{:meta, _}` variant — and was replaced; see Task 5's design note). Its one remaining open question (whether `PositiveNatural`'s alias needs the `Kernel.normalize`-on-reified-term fallback in addition to Value-level whnf) is called out explicitly at its definition site. Nothing in Tasks 3–6 is unverified scaffolding at this point.

**Type consistency:** `resolve/3` and `resolve/4`, `put_lemma/3`/`lemmas/2`, `conclusion_head/1`, entry shape `%{name, type, arity}`, provenance tuples `{:local,k}`/`{:projection,k}`/`{:lemma,name}`, and `{:error, {:ambiguous_proof_search, goal, provenance}}` are used identically across Tasks 1–8.

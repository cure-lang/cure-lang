# Builtin-Inductive Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Introduce a builtin-inductive registry so the kernel and erasure can resolve a canonical inductive by key, use it to retire the bespoke `bool_elim` primitive by making `Bool` a real inductive checked through the general `:case`, and give `Nat` a native machine-integer runtime representation.

**Architecture:** A schema-validated registry lives on the kernel's signature struct (`Cure.Core.Env`), seeded once from the prelude's `@builtin`-tagged `Bool`/`Nat` declarations (and mirrored by a programmatic `Cure.Core.Builtins.seed/1` for kernel-internal and conformance test contexts) — this seed is now unconditional (`Cure.Elab.Program.check_ast/1`'s `env0`, Task 4.5), not contingent on the compiled source explicitly importing the prelude, since no working import path exists in this codebase today. `infer_prim` and `eval`'s `fold/2` produce the inductive `Bool`'s `True`/`False` constructors instead of the primitive `{:vbool*}` forms; `if`/guards/literal-patterns desugar to `:case` on `Bool` instead of `bool_elim`; the `bool_elim`/`bool_type`/`bool_lit` term family is deleted across nine core modules, **plus** the `lib/cure/elab/declarations.ex` chokepoint that hardcodes `Bool` (uniquely among the language's types) to the primitive form in every type annotation, independent of the kernel entirely (Task 4.5). Erasure lowers `Bool`'s constructors to native `false`/`true` atoms and (Phase 2, below the kernel) `Nat`'s constructors to native integers.

**Tech Stack:** Elixir (compiler host), Cure surface language, BEAM/Erlang abstract forms (codegen target), ExUnit (tests), Antigen (metatheory/soundness antibodies), the differential oracle (`mix cure.oracle`) vs `idris2`.

## Global Constraints

- **Ghost-writer commits.** `git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only.** `git add -- <path>` and `git commit -- <path>`; NEVER `git add -A` / `git add .` (a concurrent agent may share the worktree).
- **One build at a time.** Never run two `mix` suites concurrently (a past concurrent full-suite run caused a kernel panic). Prefer scoped `mix test <file>`; run the full suite once, alone, at each phase gate.
- **Stay on branch `autopilot/lean-shape-matching`.** Do NOT create a new branch or worktree.
- **TCB HARD-STOP (Phase 1).** Phase 1 as a whole is TCB-gated (Tasks 5, 6, 8, 9 directly modify `lib/cure/core/*`; Tasks 1-4, 4.5, 7, 10, 11 modify the surrounding parser/elaborator/erasure layers that feed the kernel — not every individual task touches `lib/cure/core/*.ex` itself, but the phase's cumulative diff does and is reviewed as a unit). The Phase 1 gate (Task 12) requires: red-green per task, a new Antigen antibody, the full Antigen suite, the full test suite, AND an explicit human review before merge. Do NOT auto-merge Phase 1.
- **Z3 stays OUT of the dependent kernel TCB** — untrusted lint only (not touched by this plan; restated for scope).
- **Entry point is `start/0`**, not `main/0`; compile Cure for AtomVM with OTP 26–28 (host `mix test` may use newer).
- **Tests are behavioral and immutable once green.** The one sanctioned exception in this plan: assertions that pin the *old primitive Bool representation* (`{:vbool_type}`, `{:vbool, b}`, `bool_elim` terms, `(bool-type)` conformance lines) are being changed by an intentional representation migration — updating exactly those assertions to the new inductive representation is part of the cutover, not a test edit-to-pass. Every such change is called out in the task that makes it.

**Resolved design decisions** (the spec flagged two as open; both are decided here so implementation has no ambiguity):

1. **Bootstrap-seeded Env — and "the real compile" means literally every compile, unconditionally.** The real compile seeds `:bool`/`:nat` from the prelude's `@builtin` declarations, **regardless of whether the compiled source explicitly imports `Std.Bool`/`Std.Nat`** — verified that `import Std.X` syntax is exercised nowhere in this codebase today, and that `Bool` is currently a hardcoded hard-wired primitive in `lib/cure/elab/declarations.ex`'s `primitive_type/1`, fully independent of `env`/imports (see Task 4.5, added during hardening review — this is a required task, not optional polish). Kernel unit tests and the `core_conformance` harness operate on bare `Context.empty()` contexts that never load the prelude, yet `infer_prim`/`eval` now need `:bool` resolved. Decision: add `Cure.Core.Builtins.seed/1`, which declares the canonical `Bool` and `Nat` families and registers their builtin keys on an `Env`. The prelude path (via `Program.check_ast/1`'s unconditional `env0` seed, Task 4.5) and the test/conformance path (via `Builtins.seed(Env.empty())` directly) both obtain a seeded base env this way; a test (Task 4, Step 5) asserts the prelude-compiled `:bool` family is structurally identical to `Builtins.seed(Env.empty())`'s (full family equality, not just constructor-name equality), preventing drift. **Caveat surfaced by this same decision (Task 4.5):** because `Env.families` is keyed by bare name atom with no module-qualification, unconditionally pre-seeding `:Bool`/`:Nat` creates a name-collision surface for any module that separately declares its own `type Bool = …`/`type Nat = …` under the same bare name — flagged as an explicit open item for the Task 12 human gate, not silently resolved by this decision.

2. **Nat native-Int is scoped to non-generic / monomorphic call sites — confirmed, not merely "contingent."** `Nat`'s native-integer representation is applied only where `Nat` appears **concretely** in erased code. Verified against source (Task 15, hardening review): monomorphisation (`lib/cure/optimizer/monomorphise.ex`) does not run anywhere in the dependent-kernel pipeline (`lib/cure/compiler.ex`'s `dependent_codegen/1` goes straight from elaboration to erasure/emit) and targets the legacy type system's own polymorphism concept, unrelated to the dependent kernel's erased `{a: Type}` generics — so an unspecialised generic body over an abstract type parameter instantiated at `Nat` **always** keeps the generic `{:ctor, …}` tuple/atom representation; the "monomorphised copy gets the native rep" branch has no code path that reaches it today. This is a real, permanent scope limit for this plan (not a TODO to revisit inside Phase 2) — Task 15 states it as settled fact and guards the fallback accordingly.

---

## Phase 1 — Registry + Bool-as-inductive (TCB, GATED)

Tasks 1–4 are purely additive (the tree stays green with the primitive `Bool` still in place). **Task 4.5 is the first cutover step** (found during hardening review, not in the original task numbering) — it removes `declarations.ex`'s hardcoded `Bool → {:bool_type}` short-circuit and changes `Program.check_ast/1`'s default env, and must land before Task 7 (Task 7's own red test needs `Bool`-as-inductive to already type-check as a return-type annotation). Tasks 5–11 are the remaining cutover and deletion. Task 12 is the gate.

---

### Task 1: Builtin-bindings field + accessors on `Cure.Core.Env`

**Files:**
- Modify: `lib/cure/core/inductive.ex` (the `Cure.Core.Env` defstruct at lines 1-86, and `Cure.Core.Inductive` accessors)
- Test: `test/cure/core/builtins_registry_test.exs` (create)

**Interfaces:**
- Produces:
  - `Cure.Core.Env` gains field `builtins: %{}` (`%{atom() => atom()}`, key → family-id).
  - `Cure.Core.Inductive.register_builtin(env, key, family_id)` → `Env.t()`; raises `ArgumentError` if `key` already bound (single-registration invariant).
  - `Cure.Core.Inductive.builtin(env, key)` → `atom() | nil` (the family-id) — consumed by kernel `infer_prim` and erasure.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/builtins_registry_test.exs
defmodule Cure.Core.BuiltinsRegistryTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive}

  test "register_builtin binds a key resolvable by builtin/2" do
    env = Inductive.register_builtin(Env.empty(), :bool, :Bool)
    assert Inductive.builtin(env, :bool) == :Bool
  end

  test "builtin/2 returns nil for an unbound key" do
    assert Inductive.builtin(Env.empty(), :bool) == nil
  end

  test "a second registration of the same key is a hard error" do
    env = Inductive.register_builtin(Env.empty(), :bool, :Bool)
    assert_raise ArgumentError, ~r/already bound/, fn ->
      Inductive.register_builtin(env, :bool, :OtherBool)
    end
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/builtins_registry_test.exs`
Expected: FAIL — `builtins` key not in struct / `register_builtin`/`builtin` undefined.

- [ ] **Step 3: Add the field and functions**

In `lib/cure/core/inductive.ex`, extend the `Cure.Core.Env` defstruct and typespec:

```elixir
defstruct families: %{}, ctors: %{}, ctor_to_family: %{}, defs: %{}, certified: nil, builtins: %{}

@type t :: %__MODULE__{
        families: %{atom() => map()},
        ctors: %{atom() => map()},
        ctor_to_family: %{atom() => atom()},
        defs: %{atom() => map()},
        certified: MapSet.t() | nil,
        builtins: %{atom() => atom()}
      }
```

In `defmodule Cure.Core.Inductive`, add:

```elixir
@doc "Bind a builtin key to a family-id. Hard error on re-registration (single-registration invariant)."
@spec register_builtin(Env.t(), atom(), atom()) :: Env.t()
def register_builtin(%Env{builtins: b}, key, _family_id) when is_map_key(b, key) do
  raise ArgumentError, "builtin key #{inspect(key)} already bound to #{inspect(Map.fetch!(b, key))}"
end

def register_builtin(%Env{} = env, key, family_id) do
  %{env | builtins: Map.put(env.builtins, key, family_id)}
end

@doc "Resolve a builtin key to its family-id, or nil."
@spec builtin(Env.t(), atom()) :: atom() | nil
def builtin(%Env{builtins: b}, key), do: Map.get(b, key)
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/builtins_registry_test.exs`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/core/inductive.ex test/cure/core/builtins_registry_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(core): builtin-bindings registry on Env (register_builtin/builtin, single-registration)"
```

---

### Task 2: Schema validation (shape + constructor names)

**Files:**
- Create: `lib/cure/core/builtins.ex` (module `Cure.Core.Builtins`)
- Test: `test/cure/core/builtins_schema_test.exs` (create)

**Interfaces:**
- Consumes: `Env`, `Inductive.get_family/2`, `Inductive.ctors_of/2`, `Inductive.arg_telescope/2` (from `inductive.ex`).
- Produces:
  - `Cure.Core.Builtins.schema(key)` → the expected schema descriptor for `:bool`/`:nat` (raises for unknown key).
  - `Cure.Core.Builtins.validate!(env, key, family_id)` → `:ok` or raises `ArgumentError` with a specific reason (wrong arity, wrong/missing constructor names). Checks **names, not arity alone** (spec §1: a `Coin = Heads | Tails` tagged `@builtin(:bool)` must be rejected).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/builtins_schema_test.exs
defmodule Cure.Core.BuiltinsSchemaTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  defp declare_family(env, fname, ctors) do
    # `Inductive.family/4`'s real shape is `%{name:, params:, indices:, level:}`
    # (lib/cure/core/inductive.ex:108-120) — `level` is NOT optional: the kernel
    # pattern-matches `%{params:, indices:, level:}` when it builds a family's
    # type value (kernel.ex:171, :433, :682). A family map missing `:level`
    # crashes the first time the kernel inspects it (`FunctionClauseError`), not
    # at declare-time — so this helper (and Task 3's `bool_family/0`/`nat_family/0`,
    # built the same way) MUST set `level: 0` for both Bool and Nat (both are
    # Type-0 families here). Ctor maps are plain maps keyed by whatever
    # `Inductive.ctor/3..5` produces (`:name`, `:args`, `:result_indices`,
    # `:result_params`, `:quantities`) — there is no `:family` field on a ctor
    # map; family membership is derived by `declare/3` itself into `ctor_to_family`.
    family = %{name: fname, params: [], indices: [], level: 0}
    ctor_maps =
      Enum.map(ctors, fn {cname, arg_types} ->
        %{name: cname, args: arg_types, result_indices: [], result_params: [], quantities: List.duplicate(:present, length(arg_types))}
      end)
    Inductive.declare(env, family, ctor_maps)
  end

  test "a well-formed Bool passes validation" do
    env = declare_family(Env.empty(), :Bool, [{:False, []}, {:True, []}])
    assert :ok = Builtins.validate!(env, :bool, :Bool)
  end

  test "Bool with wrong constructor names is rejected" do
    env = declare_family(Env.empty(), :Coin, [{:Heads, []}, {:Tails, []}])
    assert_raise ArgumentError, ~r/expected constructors/, fn ->
      Builtins.validate!(env, :bool, :Coin)
    end
  end

  test "Bool with wrong arity is rejected" do
    env = declare_family(Env.empty(), :Bad, [{:False, []}, {:True, [{:n, {:data, :Bad, [], []}}]}])
    assert_raise ArgumentError, ~r/arity|nullary/, fn ->
      Builtins.validate!(env, :bool, :Bad)
    end
  end

  test "a well-formed Nat passes validation" do
    env = declare_family(Env.empty(), :Nat, [{:Z, []}, {:S, [{:n, {:data, :Nat, [], []}}]}])
    assert :ok = Builtins.validate!(env, :nat, :Nat)
  end
end
```

> **Implementer note (verified against source):** a constructor's argument telescope (`:args`, per `arg_telescope/2` and the `ctor()` type at `inductive.ex:108-113`) is `[{atom(), Cure.Core.Term.t()}]` — a list of `{binder_name, type_term}` pairs, exactly the same telescope shape `param_telescope`/`index_telescope` use. A self-referential field (`S`'s single `Nat` argument) is one telescope entry whose type term is `{:data, fname, [], []}` — the same term form `Cure.Elab.Declarations`'s `idx_to_core`/`resolve_index_name` (`declarations.ex:719-724, 798-812`) produces for any bare reference to a declared family, self-referential or not (there is no special "self" marker; the kernel's strict-positivity check, `Inductive.positive?/2`, is what enforces that the reference only appears in a strictly-positive position). The test bodies above use this real shape (`{:n, {:data, :Nat, [], []}}`) rather than the placeholder `{:family, :Nat}` tuple an earlier draft of this plan used — that placeholder was never valid telescope syntax and would have produced a nonsensical constructor shape if implemented literally.

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/builtins_schema_test.exs`
Expected: FAIL — `Cure.Core.Builtins.validate!/3` undefined.

- [ ] **Step 3: Implement the schema + validator**

```elixir
# lib/cure/core/builtins.ex
defmodule Cure.Core.Builtins do
  @moduledoc """
  Canonical builtin-inductive schemas and the programmatic seeder.
  Schema validation checks constructor NAMES and arities, not arity alone:
  the literal wiring (true/false -> True/False) and erasure atom mapping
  (False/True -> false/true; Z/S -> int) key off these exact names, so a
  shape-conformant but name-mismatched binding is a real miscompile risk.
  """
  alias Cure.Core.{Env, Inductive}

  # key => list of {ctor_name, arity}. Names are load-bearing.
  @schemas %{
    bool: [{:False, 0}, {:True, 0}],
    nat: [{:Z, 0}, {:S, 1}]
  }

  @spec schema(atom()) :: [{atom(), non_neg_integer()}]
  def schema(key), do: Map.fetch!(@schemas, key)

  @spec validate!(Env.t(), atom(), atom()) :: :ok
  def validate!(%Env{} = env, key, family_id) do
    expected = schema(key)
    ctors = Inductive.ctors_of(env, family_id) || []

    actual =
      ctors
      |> Enum.map(fn c -> {c.name, length(Map.get(c, :args, []))} end)
      |> Enum.sort()

    if actual == Enum.sort(expected) do
      :ok
    else
      raise ArgumentError,
            "@builtin(#{inspect(key)}) on #{inspect(family_id)}: expected constructors " <>
              "#{inspect(Enum.sort(expected))} (name and arity), got #{inspect(actual)}"
    end
  end
end
```

> **Implementer note (verified against source):** `Inductive.ctors_of/2` (`inductive.ex:246-247`) returns the family's constructor maps, each shaped `%{name:, args:, result_indices:, result_params:, quantities:}` (the `ctor()` type at `inductive.ex:108-113`) — `:args` is the correct field for the argument telescope (same field `arg_telescope/2` reads at `inductive.ex:195-201`), so `Map.get(c, :args, [])` is already right; no accessor mismatch to resolve here. Separately, `Inductive.family/4` (`inductive.ex:118-120`) requires a `:level` field on every family map — `declare/3` doesn't enforce this (it only pattern-matches `%{name: fname}`), but the kernel does the first time it inspects the family (`kernel.ex:171`, `:433`, `:682` all pattern-match `%{..., level: level}`), so any family map built by this module (including Task 3's `seed/1`) must include `level: 0` for Bool and Nat or the kernel crashes with `FunctionClauseError` on first use, not at declare-time.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/builtins_schema_test.exs`
Expected: PASS (4 tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/core/builtins.ex test/cure/core/builtins_schema_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(core): builtin schema validation (name+arity, not arity alone)"
```

---

### Task 3: `Builtins.seed/1` — canonical Bool + Nat families, validated

**Files:**
- Modify: `lib/cure/core/builtins.ex`
- Test: `test/cure/core/builtins_seed_test.exs` (create)

**Interfaces:**
- Consumes: `Inductive.declare/3`, `register_builtin/3`, `validate!/3`.
- Produces: `Cure.Core.Builtins.seed(env)` → `Env.t()` with the canonical `Bool` (`False | True`) and `Nat` (`Z | S(Nat)`) families declared, each validated, and `:bool`/`:nat` registered. This is the base env for kernel unit tests and the conformance harness (design decision 1).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/builtins_seed_test.exs
defmodule Cure.Core.BuiltinsSeedTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  test "seed/1 registers validated bool and nat" do
    env = Builtins.seed(Env.empty())
    assert Inductive.builtin(env, :bool) == :Bool
    assert Inductive.builtin(env, :nat) == :Nat
    assert Inductive.family?(env, :Bool)
    assert Inductive.family?(env, :Nat)
  end

  test "seeded bool family has exactly False and True" do
    env = Builtins.seed(Env.empty())
    names = env |> Inductive.ctors_of(:Bool) |> Enum.map(& &1.name) |> Enum.sort()
    assert names == [:False, :True]
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/builtins_seed_test.exs`
Expected: FAIL — `Builtins.seed/1` undefined.

- [ ] **Step 3: Implement `seed/1`**

Add to `lib/cure/core/builtins.ex` (adjust the family/ctor map literals to the exact shape `Inductive.declare/3` expects, confirmed while implementing Task 2):

```elixir
@spec seed(Env.t()) :: Env.t()
def seed(%Env{} = env) do
  env
  |> declare_and_register(:bool, bool_family(), bool_ctors())
  |> declare_and_register(:nat, nat_family(), nat_ctors())
end

defp declare_and_register(env, key, family, ctors) do
  fid = family.name
  env = Inductive.declare(env, family, ctors)
  :ok = validate!(env, key, fid)
  Inductive.register_builtin(env, key, fid)
end

# NOTE: bool_family/bool_ctors/nat_family/nat_ctors build the SAME family
# maps Inductive.declare/3 consumes elsewhere. Keep the ctor NAMES here in
# single-source-of-truth agreement with @schemas above and with eval.ex's
# hardcoded :True/:False (Task 6) — the Task 10 antibody enforces this.
```

> **Implementer note (verified against source):** fill `bool_family/0`, `bool_ctors/0`, `nat_family/0`, `nat_ctors/0` with the concrete maps matching `Inductive.family/4`/`Inductive.ctor/3..5`'s real shapes (`inductive.ex:108-113,118-149`) — **both families need `level: 0`** (see Task 2's implementer note; this is not optional, the kernel pattern-matches on it). `Nat`'s `S` constructor's single field must reference the `Nat` family exactly as the real declaration path encodes a recursive argument (mirror what the prelude compile produces for `type Nat = Z | S(Nat)` — Task 4 asserts they match, so build this to that target). Prefer calling `Inductive.family(:Bool, [], [], 0)` / `Inductive.ctor(:False, [], [])` / `Inductive.ctor(:True, [], [])` directly (the public constructor functions at `inductive.ex:118-149`) rather than hand-building the maps — that guarantees every required field (including `:level`, `:result_params`, `:quantities`) is present.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/builtins_seed_test.exs`
Expected: PASS (2 tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/core/builtins.ex test/cure/core/builtins_seed_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(core): Builtins.seed/1 seeds canonical Bool+Nat (validated)"
```

---

### Task 4: Parser — attach `@builtin(:key)` to a `type` declaration; wire prelude registration

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_at/1` at 4159-4210, `attach_decorator/3` at 4212-4253)
- Modify: `lib/std/nat.cure` (tag with `@builtin(:nat)`, ensure it is in the `:core` group and ordered first — see Task 11 for load-order)
- Create: `lib/std/bool.cure` (`@builtin(:bool) type Bool = False | True`)
- Modify: the prelude-elaboration path that honors decorators on type declarations — `lib/cure/elab/program.ex` register pass (lines 278-313) — to call `Builtins.validate!/3` + `Inductive.register_builtin/3` when it processes a `@builtin`-tagged type **only for designated prelude sources**.
- Test: `test/cure/compiler/builtin_decorator_parse_test.exs` (create); `test/cure/elab/builtin_prelude_seed_test.exs` (create)

**Interfaces:**
- Consumes: `Builtins.validate!/3`, `Inductive.register_builtin/3`, `Builtins.seed/1` (for the equivalence assertion).
- Produces: type-declaration AST nodes carry `[decorator: {:builtin, [<key-atom>]}]` in their meta; the prelude register pass turns that into a validated builtin registration.

- [ ] **Step 1: Write the failing parse test**

```elixir
# test/cure/compiler/builtin_decorator_parse_test.exs
defmodule Cure.Compiler.BuiltinDecoratorParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  test "@builtin(:bool) attaches to the following type declaration" do
    src = "mod M\n  @builtin(:bool)\n  type Bool = False | True\n"
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    type_node = find_type_decl(ast, "Bool")
    assert {:builtin, [:bool]} = Keyword.get(elem(type_node, 1), :decorator)
  end
end
```

> **Implementer note (verified against source):** `Parser.parse/2` (`parser.ex:71-90`) takes **tokens**, not a raw source string — `@spec parse([Token.t()], keyword()) :: {:ok, ast()} | {:error, [term()]}` — so it must be preceded by `Lexer.tokenize/2` exactly as `Cure.Elab.Program.elaborate/1` itself does (`program.ex:16-19`); calling `Parser.parse(src)` directly on a string, as an earlier draft of this test did, would not compile (wrong arity/type). `find_type_decl/2` still needs writing against the real AST shape — for `type Bool = False | True` (no params, no indices) this is the `{:container, meta, variants}` node with `Keyword.get(meta, :container_type) == :enum` and `Keyword.get(meta, :name) == "Bool"` (confirmed via `parser.ex:2605-2677`'s `parse_type_def_adt/4`); walk the top-level `{:container, [container_type: :module], body}` wrapper's `body` list looking for that shape. The assertion — a `type` node carries the `:builtin` decorator with the key — is the fixed contract; `Keyword.get(elem(type_node, 1), :decorator)` reads the meta list directly rather than inventing a `get_in_meta/2` helper.

- [ ] **Step 2: Run parse test to verify it fails**

Run: `mix test test/cure/compiler/builtin_decorator_parse_test.exs`
Expected: FAIL — decorator parses as a disconnected `{:decorator, …}` standalone node; the `type` node has no `:decorator` meta.

- [ ] **Step 3: Extend decorator attachment to `type`**

In `parse_at/1` (parser.ex ~line 4186), add a `:type` case alongside the `:fn`/`:local`/`:rec` cases:

```elixir
    %Token{type: :keyword, value: kw} when kw in [:fn, :local] ->
      {fn_ast, state} = parse_expr(state, 0)
      fn_ast = attach_decorator(fn_ast, dec_name, args)
      {fn_ast, state}

    %Token{type: :keyword, value: :type} ->
      {type_ast, state} = parse_type_def(state)
      type_ast = attach_decorator(type_ast, dec_name, args)
      {type_ast, state}

    %Token{type: :keyword, value: :rec} ->
      ...
```

**No new `attach_decorator/3` clause is needed for `Bool`/`Nat`.** Verified against source: `parse_type_def/1` (`parser.ex:2542`) does NOT return a `{:type_def, ...}` tag — that tag does not exist anywhere in the parser. For a non-indexed, non-parameterized ADT like `type Bool = False | True` or `type Nat = Z | S(Nat)`, it delegates to `parse_type_def_adt/4` (`parser.ex:2605`), which returns `{:container, [container_type: :enum, name: "Bool", line: _, col: _], variants}` (`parser.ex:2653-2660`, the "ADT: multiple variants separated by `|`" branch — `Bool = False | True` and `Nat = Z | S(Nat)` both have two variants, so both take this branch) — the exact same tag record containers already use. `attach_decorator/3` **already has** a matching clause for `{:container, meta, body}` (`parser.ex:4214-4229`, added for `@derive(...)` on structs) whose `_ ->` branch (`parser.ex:4227-4228`) generically threads *any* decorator name into `Keyword.put(meta, :decorator, {String.to_atom(dec_name), args})` — this already does exactly what `@builtin(:bool)` needs, with zero new code. (An indexed/GADT `type` declaration returns `{:indexed_type, meta, ctors}` instead, and a plain alias returns `{:type_annotation, meta, body}` — neither has an `attach_decorator` clause today, so a `@builtin` on *those* forms would still be silently dropped; out of scope here since Bool/Nat are both simple enums, but worth a one-line comment at the `attach_decorator` catch-all (`other -> other`, `parser.ex:4250-4251`) for the next person who tags an indexed family.)

The only real gap is `parse_at/1`'s dispatch (`parser.ex:4159-4207`): it has no case for a following `:type` keyword, so `@builtin(:bool)` before `type Bool = …` currently falls to the `_ ->` branch and parses as a disconnected `{:decorator, ...}`/`{:property, ...}` node. Add the dispatch case:

```elixir
      %Token{type: :keyword, value: :type} ->
        {type_ast, state} = parse_type_def(state)
        type_ast = attach_decorator(type_ast, dec_name, args)
        {type_ast, state}
```

> **Implementer note:** `args` for `@builtin(:bool)` is the parsed call-arg list; confirm the key arrives as an atom `:bool` (from the `%[...]`/atom literal path) and normalize to `{:builtin, [:bool]}` if the raw arg is wrapped (e.g. `{:literal, _, :bool}`).

- [ ] **Step 4: Run parse test to verify it passes**

Run: `mix test test/cure/compiler/builtin_decorator_parse_test.exs`
Expected: PASS.

- [ ] **Step 5: Add the prelude sources and the register-pass wiring, with a failing seed test**

Create `lib/std/bool.cure`:

```cure
mod Std.Bool
  fn __group__() -> Atom = :core
  @builtin(:bool)
  type Bool = False | True
```

Tag `lib/std/nat.cure`'s existing declaration:

```cure
mod Std.Nat
  fn __group__() -> Atom = :core
  @builtin(:nat)
  type Nat = Z | S(Nat)
```

Write the failing test that compiling the prelude source *itself* yields a registered, schema-identical `:bool`:

**Grounding note — why the test elaborates `Std.Bool`'s own source, not a program that "imports" it:** `Cure.Elab.Program.elaborate/1` (and `check_ast/1` beneath it) take only a source **string**, with no filename/path argument — `import_env(imports(ast), MapSet.new())` (`program.ex:212-220`) resolves ONLY declarations reachable via an explicit `import Std.X` AST node, and returns `Env.empty()` when there are none (`program.ex:212`). Empirically, `import Std.X` syntax is not used anywhere in this codebase today (`grep -rn "^\s*import Std\." lib/std/*.cure` → zero hits), so there is no working precedent to build the register-pass gate against a "compiling a program that imports Std.Bool" scenario — and a plain `fn id(b: Bool) -> Bool = b` with no import never touches `Std.Bool`'s source at all (confirmed by direct elaboration: it type-checks today via the hardcoded `primitive_type("Bool")` path in `lib/cure/elab/declarations.ex:816`, completely independent of `env`/imports — see Task 4.5 below). The test below instead elaborates `Std.Bool`'s own declared source directly, and the register pass identifies "this is a prelude source" by the **module name the source itself declares** (`Cure.Elab.Program.module_atom/1`, `program.ex:102`, which builds `:"Cure.Std.Bool"` from `mod Std.Bool` exactly like `Cure.Stdlib.Preload`'s own `String.to_atom("Cure." <> declared)` convention at `preload.ex:114`) matching a key in `Cure.Stdlib.Preload.module_groups/0` — not a file path, since none is available at this layer. Whether an *arbitrary, unrelated* user program also ends up with `:bool` registered (so `Bool` is usable without an explicit import, matching today's ergonomics) is Task 4.5's separate concern, not this task's.

```elixir
# test/cure/elab/builtin_prelude_seed_test.exs
defmodule Cure.Elab.BuiltinPreludeSeedTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  @bool_src "mod Std.Bool\n  fn __group__() -> Atom = :core\n  @builtin(:bool)\n  type Bool = False | True\n"

  test "compiling Std.Bool's own prelude source registers :bool" do
    {:ok, env} = Cure.Elab.Program.elaborate(@bool_src)
    assert Inductive.builtin(env, :bool) == :Bool
  end

  test "prelude-compiled Bool family is structurally identical to Builtins.seed's" do
    {:ok, env} = Cure.Elab.Program.elaborate(@bool_src)
    seeded = Builtins.seed(Env.empty())
    # Full structural equality (design decision 1's actual claim), not just
    # constructor-name equality — a `:level`/telescope/quantities mismatch
    # between the two construction paths must fail this test, not slip through.
    assert Inductive.get_family(env, :Bool) == Inductive.get_family(seeded, :Bool)
    from_prelude = env |> Inductive.ctors_of(:Bool) |> Enum.sort_by(& &1.name)
    from_seed = seeded |> Inductive.ctors_of(:Bool) |> Enum.sort_by(& &1.name)
    assert from_prelude == from_seed
  end

  test "a @builtin decorator on a non-prelude module is ignored for registration" do
    src = "mod M\n  @builtin(:bool)\n  type Coin = Heads | Tails\n"
    {:ok, env} = Cure.Elab.Program.elaborate(src)
    refute Inductive.builtin(env, :bool) == :Coin
    assert Inductive.builtin(env, :bool) == nil
  end
end
```

- [ ] **Step 6: Run seed test to verify it fails**

Run: `mix test test/cure/elab/builtin_prelude_seed_test.exs`
Expected: FAIL — register pass ignores the `:builtin` decorator; `:bool` unregistered (also `Bool` may still be resolving as the primitive — that is fine for this task; the assertion is on the registry entry).

- [ ] **Step 7: Wire the register pass**

In `lib/cure/elab/program.ex`'s `check_ast/1` (which has the whole top-level `ast`, hence `module_atom(ast)`, before `elaborate_declarations` walks its unwrapped body), thread whether this compile is a designated prelude source down into `register_pass/2` (`program.ex:282-300`). A source is "prelude" iff its own declared module name is a key of `Cure.Stdlib.Preload.module_groups/0`:

```elixir
defp prelude_source?(ast), do: Map.has_key?(Cure.Stdlib.Preload.module_groups(), module_atom(ast))
```

In `register_pass/2`'s non-function-def branch, when the declaration carries `[decorator: {:builtin, [key]}]` (a `{:container, meta, _}` node per Task 4 Step 3) AND `prelude_source?(ast)` is true, after `Declarations.elaborate/2` has declared the family into `acc2`, additionally call:

```elixir
family_id = decl |> elem(1) |> Keyword.fetch!(:name) |> String.to_atom()
:ok = Cure.Core.Builtins.validate!(acc2, key, family_id)
acc2 = Cure.Core.Inductive.register_builtin(acc2, key, family_id)
```

A `@builtin` decorator on a **non-prelude** module is ignored for registration (ordinary user code cannot register a builtin key — spec §1 single-registration invariant part (1); the third test above covers this). `register_builtin/3`'s own hard-error on a duplicate key (Task 1) is the second half of the invariant.

> **Implementer note:** `family_id` is the declared family's own name (already an atom in `meta[:name]` after `Declarations.elaborate`'s container path, or re-derive it from `Keyword.fetch!(meta, :name) |> String.to_atom()` if `meta[:name]` is still the surface string). Thread `prelude_source?(ast)` (or the boolean) through `register_pass/2`'s existing `Enum.reduce_while` as extra accumulator state rather than recomputing it per-declaration. Keep the change minimal and localized to `register_pass/2`; do not touch `Declarations.elaborate/2` itself.

- [ ] **Step 8: Run seed test to verify it passes**

Run: `mix test test/cure/elab/builtin_prelude_seed_test.exs`
Expected: PASS (3 tests).

- [ ] **Step 9: Commit**

```bash
git add -- lib/cure/compiler/parser.ex lib/std/bool.cure lib/std/nat.cure lib/cure/elab/program.ex test/cure/compiler/builtin_decorator_parse_test.exs test/cure/elab/builtin_prelude_seed_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser,elab): @builtin(:key) on type decls; prelude registers validated Bool/Nat"
```

---

### Task 4.5: `Bool` resolves as the inductive family everywhere `Bool` is used as a *type* — auto-seeding + the `declarations.ex` chokepoint

**Why this task exists (found during hardening review, not in the original Explore report):** two facts, each independently verified against source and by direct elaboration, combine into a gap none of Tasks 1–4 or 5–9 close on their own:

1. **`Bool` as a *type annotation* does not go through `env`/the registry at all today.** `fn id(b: Bool) -> Bool = b`'s parameter/return types are resolved by `Cure.Elab.Declarations`'s `elaborate_param_telescope/2` → `idx_to_core/4` → `resolve_index_name/2` (`declarations.ex:421-436, 719-724, 798-812`), whose `cond` checks `primitive_type(name) != nil` **first**, before `Inductive.family?(env, atom)`. `defp primitive_type("Bool"), do: {:bool_type}` (`declarations.ex:816`) short-circuits unconditionally — confirmed by direct elaboration: `Cure.Elab.Program.elaborate("mod M\n  fn id(b: Bool) -> Bool = b\n")` returns `id`'s type as `{:pi, {:bool_type}, {:bool_type}}` **regardless of whether `Std.Bool` is imported**. `Nat` has no such entry in `primitive_type/1` (only `"Bool"`, `"Int"`, `"Float"`), which is exactly why `Nat` already resolves via the ordinary family-lookup branch today — `Bool` is the odd one out, uniquely hardcoded. Tasks 5-9 never touch `declarations.ex`, and Task 9's guard test only scans `lib/cure/core/*.ex` (not `lib/cure/elab/*.ex`), so this reference to `{:bool_type}` is invisible to that safety net.
2. **No working mechanism seeds an arbitrary program's `env` with `Std.Bool`/`Std.Nat` today.** `Cure.Elab.Program.check_ast/1`'s `env0 = import_env(imports(ast), MapSet.new())` (`program.ex:16-19, 212-220`) returns `Env.empty()` when the source has no explicit `import Std.X` statement, and empirically `import Std.X` syntax is used **nowhere** in this codebase (`grep -rn "^\s*import Std\." lib/std/*.cure` and across `test/` → zero hits) — it is unexercised, unvalidated machinery. Every existing dependent-kernel test either uses `Bool`/`Int` (hardcoded primitives, independent of `env`) or declares its own local inductive inline. Once fact (1) is fixed and `Bool` becomes an ordinary family lookup, **every** dependent-kernel program using `Bool` as a type (which is most of them — comparisons, `if`, guards) needs `:Bool` present in its `env`, with no existing import path to put it there.

Combined: fixing (1) alone, without (2), breaks every existing dependent-kernel test the moment `Bool` stops being a hardcoded primitive (an `{:unknown_family, :Bool}` kernel error on every `Bool`-typed signature). Both must land together, and **before Task 7** — Task 7's own red test (`fn t() -> Bool = true`) needs the return-type annotation `Bool` to resolve to the inductive family the moment the body starts producing a `{:ctor, :True, []}` term, or `Kernel.check/3` rejects a constructor-typed body against the (still-primitive) `{:vbool_type}` expected type. This task must be done before Task 7 begins.

**Files:**
- Modify: `lib/cure/elab/declarations.ex` (`primitive_type/1` at 816-819, its use sites `resolve_index_name/2` at 798-812 and `type_to_core/1` at 892-899)
- Modify: `lib/cure/elab/program.ex` (`check_ast/1` at 16-19, `import_env/2` at 212-220 — or a call site immediately around them)
- Test: `test/cure/elab/bool_always_resolves_test.exs` (create)

**Interfaces:**
- Consumes: `Builtins.seed/1` (Task 3).
- Produces: (a) `primitive_type/1` no longer special-cases `"Bool"` (the `Nat` precedent — no entry — is the model: `Bool` falls through to `Inductive.family?(env, atom) -> {:data, atom, [], []}` once `:Bool` is a real family); (b) `check_ast/1`'s `env0` always includes the seeded `Bool`/`Nat` families, whether or not the source imports anything explicitly (merge `Builtins.seed(Env.empty())` under whatever `import_env(imports(ast), seen)` resolves — explicit imports win on conflict, since they may re-derive the same family from the real prelude source).

**New risk this task introduces — a name collision the design spec's "nominal, not structural" claim doesn't account for.** `Inductive.declare/3` (`inductive.ex:154-165`) keys `env.families` by the bare declared name **atom**, with no module-qualification — `Map.put(env.families, fname, family)`, unconditionally, no "already declared" check anywhere in `declare/3` or `declare_at_min_level/4` (`declarations.ex:943-958`). Before this task, a module locally declaring `type Nat = Z | S(Nat)` (the design spec's own cited example, `test/cure/compiler/dependent_vec_codegen_test.exs`) was the *only* `:Nat` entry in its own `env` — no collision possible, because nothing pre-populated `env.families[:Nat]`. After this task's unconditional seed, `env0` already carries the canonical `Std.Nat` family under the *same* key (`:Nat`) before the user's own declarations are processed — so the user's local `type Nat = Z | S(Nat)` **silently overwrites** the seeded entry (same `Map.put`), and its `Z`/`S` constructors land in `ctor_to_family` under the same `:Nat` key the seed used. Since `Inductive.builtin(env, :nat)` only stores the atom `:Nat` (not a reference to a specific declaration), and `nat_family?/2` (Task 13) checks `Inductive.builtin(env, :nat) == Inductive.ctor_family(env, name)`, the *local* redeclaration's constructors now satisfy that check too — meaning the local `Nat` gets Phase 2's native-Int erasure, not the unary encoding the design spec's §1 "Nominal, not structural" section explicitly claims it keeps. This is a genuine gap between the design's stated semantics and what the flat, unqualified `env.families` map actually does once a builtin name is unconditionally pre-seeded. Practical impact is likely benign (a structurally-identical local redeclaration silently *becoming* the canonical family behaves the same as if it *were* the canonical family), but it is a real behavior the design spec gets wrong, and it deserves an explicit test and a decision at the Phase 1 gate, not silent discovery later — Step 5 below (after this task's own red-green cycle) adds the diagnostic test and the escalation instruction.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/bool_always_resolves_test.exs
defmodule Cure.Elab.BoolAlwaysResolvesTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Inductive

  test "Bool as a type annotation resolves to the inductive family with no import" do
    src = "mod M\n  fn id(b: Bool) -> Bool = b\n"
    {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert Inductive.builtin(env, :bool) == :Bool
    assert %{type: {:pi, {:data, :Bool, [], []}, {:data, :Bool, [], []}}} = Cure.Core.Env.get_def(env, :id)
  end

  test "a program using only Nat still works unaffected" do
    src = "mod M\n  fn f(n: Nat) -> Nat = n\n"
    assert {:ok, _env} = Cure.Elab.Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/bool_always_resolves_test.exs`
Expected: FAIL — `id`'s registered type is `{:pi, {:bool_type}, {:bool_type}}`, and `Inductive.builtin(env, :bool)` is `nil` (no family ever declared for this source).

- [ ] **Step 3: Remove the `Bool` short-circuit; auto-seed `check_ast/1`**

In `declarations.ex`, delete the `"Bool"` clause of `primitive_type/1` (leave `"Int"`/`"Float"` — out of scope per the design's "Out of scope" section, both stay irreducibly primitive):

```elixir
  defp primitive_type("Int"), do: {:int_type}
  defp primitive_type("Float"), do: {:float_type}
  defp primitive_type(_), do: nil
```

In `program.ex`'s `check_ast/1`, seed `env0` unconditionally before folding in whatever the source explicitly imports:

```elixir
  def check_ast(ast) do
    with {:ok, imported} <- import_env(imports(ast), MapSet.new()),
         env0 = merge_env(Cure.Core.Builtins.seed(Env.empty()), imported),
         {:ok, env} <- elaborate_declarations(declarations(ast), env0) do
      TotalityClosure.certify_type_level(env)
    end
  end
```

> **Implementer note:** `merge_env/2` (`program.ex:263-270`) is a private function today (`Map.merge` per-field, imported-side winning on key collision since it's passed as the *right* argument in existing call sites) — check its exact precedence and keep the seeded families as the base, not an override, so an explicit `import Std.Bool` (if one is ever written) still supersedes the seed with the real prelude-compiled family. Also guard against seeding `Std.Bool`/`Std.Nat`'s *own* compile (Task 4's `builtin_prelude_seed_test.exs`) double-declaring `:Bool`/`:Nat` — `Inductive.declare/3` overwrites by key so a second `declare` of the identical family is harmless, but `register_builtin/3`'s hard-error on re-registration (Task 1) means seeding `:bool`/`:nat` here must NOT also re-run `register_builtin` for a source that is itself `Std.Bool`/`Std.Nat` (it already self-registers via Task 4's register-pass hook). `Builtins.seed/1` only calls `Inductive.declare` + `register_builtin` once, called once per `check_ast/1` invocation, so this is fine as long as `Std.Bool`'s own compile doesn't ALSO get auto-seeded-and-then-self-registered in the same run — if it does, `register_builtin` raises. Resolve by special-casing: skip the auto-seed merge when `prelude_source?(ast)` is true for `Std.Bool`/`Std.Nat` themselves (they declare their own canonical family and register it directly; auto-seeding a *second* copy under the same key is exactly the hijack Task 1 exists to prevent). **Alternative worth considering instead** (simpler, but touches Task 1's already-committed behavior): relax `register_builtin/3` so a re-registration with the *same* `family_id` for an already-bound key is a no-op rather than a hard error — the hijack risk Task 1 guards against is a *different* family silently overwriting the key, which this preserves (Task 1's own test registers `:bool → :OtherBool` after `:bool → :Bool`, a genuine mismatch, so it is unaffected). Pick one approach and apply it consistently; do not half-implement both. Confirm whichever is chosen with a dedicated test in Step 4.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/bool_always_resolves_test.exs`
Expected: PASS. Also re-run Task 4's `builtin_prelude_seed_test.exs` and the full `test/cure/elab/` and `test/cure/compiler/` directories once — this changes a load-bearing default (`env0`) that many other elaboration tests implicitly depend on; catch any regression here, not at the Task 12 full-suite gate.

- [ ] **Step 5: Pin the name-collision behavior with a real assertion — do not fix it inline**

Before writing this test, determine the actual behavior empirically (a scratch `iex -S mix` probe or a throwaway `IO.inspect`, run once, not committed): compile `"mod M\n  type Nat = Z | S(Nat)\n  fn id(n: Nat) -> Nat = n\n"` through `Cure.Elab.Program.elaborate/1` and inspect `Inductive.get_family(env, :Nat)` / `Inductive.ctor_family(env, :Z)`. Per the analysis above, the expected outcome is that the local declaration silently overwrites the seeded family (no error) and its `Z`/`S` constructors resolve to the same `:Nat` key the seed uses. Write the test asserting **whatever is actually observed** — this is a real, immutable, asserting test like every other in this plan, not a placeholder:

```elixir
test "a module-local Nat redeclaration collides with the seeded :nat family (documented, not fixed)" do
  src = "mod M\n  type Nat = Z | S(Nat)\n  fn id(n: Nat) -> Nat = n\n"
  {:ok, env} = Cure.Elab.Program.elaborate(src)
  # Assert the actually-observed outcome (fill in from the probe above — do not
  # guess). If the collision analysis is correct, the local declaration silently
  # became the resolved :Nat family and its constructors satisfy nat_family?/2's
  # check against the seeded :nat key, e.g.:
  #   assert Inductive.ctor_family(env, :Z) == Inductive.builtin(env, :nat)
  # If the actual behavior differs (an error, a distinct non-colliding family,
  # etc.), assert that instead — the point is a pinned, truthful record of what
  # the implementation does, not a specific predicted outcome.
end
```

Do NOT attempt to fix the collision behavior inline in this task — changing `Inductive.declare/3`'s re-declaration semantics is itself a K-layer (TCB) change with blast radius across every family, not just Bool/Nat, and is a scope/semantics decision (error vs. silent alias vs. something else), not a bug with one obvious fix. Escalate the observed behavior to the human reviewer at Task 12's gate instead — the test above is the evidence that gate needs, not a fix.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/declarations.ex lib/cure/elab/program.ex test/cure/elab/bool_always_resolves_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "fix(elab): Bool resolves as the inductive family everywhere; auto-seed env0"
```

---

### Task 5: `infer_prim` returns the inductive `Bool` type

**Files:**
- Modify: `lib/cure/core/kernel.ex` (`infer_prim` at 1041-1071; the `{:bool_lit}`/`{:bool_type}` clauses at 60-61 stay for now — deleted in Task 9; the `:and`/`:or`/`:not` operand checks at 1055-1071)
- Test: `test/cure/core/prim_bool_inductive_test.exs` (create); update `test/cure/core/bool_prim_test.exs` (sanctioned migration edit)

**Interfaces:**
- Consumes: `Inductive.builtin(sig, :bool)`, `Context.signature/1` (kernel already threads `ctx → sig`), the seeded env from `Builtins.seed/1`.
- Produces: comparison/connective `{:prim, op, args}` now infer to the **type value denoting the `Bool` inductive**. This shape is not an implementer-discovery item — it is fully and unambiguously derivable from the kernel source, and is pinned here as the single closed form every one of Tasks 5-8 must use:

**The pivot shape (grounded, not to be re-derived per task).** `infer(ctx, {:ctor, name, args})` (`kernel.ex:179-201`) computes a nullary constructor's family type as `{:vdata, family_name, param_values ++ index_values}` (`kernel.ex:199`); for `Bool` (no params, no indices) this is exactly `{:vdata, :Bool, []}`. `Eval.eval({:data, name, params, indices}, env)` (`eval.ex:39-40`) computes precisely `{:vdata, name, Enum.map(params ++ indices, &eval(&1, env))}` — so `{:vdata, fid, []}` is *also* what evaluating the term `{:data, fid, [], []}` produces, with no `Eval.eval` call actually required (there is nothing to evaluate: params and indices are both `[]`). **`bool_type_value(sig) = {:vdata, Inductive.builtin(sig, :bool), []}`** is the whole definition — a two-line function, not a lookup that needs re-deriving in Tasks 6/7/8. Task 8's parallel **term**-level need (the `:case` motive's domain) is `bool_type_term(sig) = {:data, Inductive.builtin(sig, :bool), [], []}` (same family, term form instead of value form — `eval.ex:39` confirms `eval(bool_type_term(sig), _) == bool_type_value(sig)`). Task 6's need (the **evaluated constructor value** for `True`/`False`) is `Eval.eval({:ctor, name, args}, env) = {:vctor, name, Enum.map(args, &eval(&1, env))}` (`eval.ex:42`), so `vbool(true) = {:vctor, :True, []}` and `vbool(false) = {:vctor, :False, []}` — also closed forms, confirmed against `value.ex:20-21,48-49`'s `{:vdata, name, [value]}` / `{:vctor, name, [value]}` value-shape documentation. All four of `infer_prim` (Task 5), `fold/2` (Task 6), the literal clause (Task 7), and `:case` retarget (Task 8) key off these same two formulas — there is only one place either is defined (`bool_type_value/1` in `kernel.ex`, `vbool/1` in `eval.ex`; `bool_type_term/1` in `elaborator.ex` per Task 8), so there is no drift surface between them once each module's private helper matches the formula above.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/prim_bool_inductive_test.exs
defmodule Cure.Core.PrimBoolInductiveTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Inductive, Kernel}

  setup do
    %{ctx: Context.empty(Builtins.seed(Env.empty()))}
  end

  test "a comparison infers to the Bool inductive, not {:vbool_type}", %{ctx: ctx} do
    {:ok, ty} = Kernel.infer(ctx, {:prim, :lt, [{:int_lit, 3}, {:int_lit, 5}]})
    assert ty == {:vdata, :Bool, []}
  end
end
```

> **Implementer note:** `Context.empty/1` (`context.ex:28-29`) is the real constructor that installs a signature on a fresh context (`Context.empty(%Env{} = signature)`) — there is no `Context.with_signature/2` anywhere in the codebase; `Context.signature/1` (`context.ex:33`) is only the getter. This is the exact pattern `declarations.ex`'s own `build_context/2` (`declarations.ex:453`) already uses (`Context.empty(env)`).

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/prim_bool_inductive_test.exs`
Expected: FAIL — `infer_prim` still returns `{:vbool_type}`.

- [ ] **Step 3: Rewire `infer_prim`**

Add a private helper (the closed form above — no lookup into `{:ctor}`'s inference needed, it IS that formula) and replace **all four** `{:ok, {:vbool_type}}` result sites in `infer_prim` — there are four separate clauses, not three: comparisons (`:lt/:le/:gt/:ge`), equality (`:eq/:ne`, a *separate* clause from comparisons), connectives (`:and/:or`), and `:not` — plus the connective/`:not` operand checks:

```elixir
defp bool_type_value(sig) do
  fid = Inductive.builtin(sig, :bool) || raise "builtin :bool not seeded (bootstrap/load-order bug)"
  {:vdata, fid, []}
end
```

- Comparisons (`op in [:lt,:le,:gt,:ge]`): `{:ok, bool_type_value(Context.signature(ctx))}`.
- Equality (`op in [:eq,:ne]`, "Equality: any shared type, boolean result"): `{:ok, bool_type_value(Context.signature(ctx))}`. **Note for Task 6:** this clause accepts operands of *any shared type*, including two `Bool`-typed operands (`a == b` where `a, b : Bool` type-checks here) — Task 6 must not lose the `eval.ex` fold clause that handles Bool-operand equality when it rewires the *result* representation.
- Connectives (`op in [:and,:or]`) and `:not`: replace `check(ctx, a, {:vbool_type})` with `check(ctx, a, bool_type_value(Context.signature(ctx)))`, and return `bool_type_value(...)`.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/prim_bool_inductive_test.exs`
Expected: PASS.

- [ ] **Step 5: Migrate the old primitive-Bool assertions**

Update `test/cure/core/bool_prim_test.exs`'s `{:vbool_type}` expectations to the inductive `Bool` type value (sanctioned migration edit — the represented behavior intentionally changed). Keep the eval-fold assertions for Task 6.

Run: `mix test test/cure/core/bool_prim_test.exs`
Expected: the *typing* assertions PASS against the new value; eval-fold assertions may still expect `{:vbool, _}` (fixed in Task 6) — if the test file mixes both, split the eval-fold assertions into a `@tag :phase1_task6` skip or move them, and note it in the commit. Do NOT weaken the eval assertion to pass; migrate it in Task 6.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/core/kernel.ex test/cure/core/prim_bool_inductive_test.exs test/cure/core/bool_prim_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(core): infer_prim yields inductive Bool type (via builtin registry)"
```

---

### Task 6: `eval` `fold/2` produces `True`/`False` constructor values

**Files:**
- Modify: `lib/cure/core/eval.ex` (`fold/2` at 127-161, `prim/2` at 120-125)
- Test: `test/cure/core/prim_bool_eval_test.exs` (create); finish migrating `test/cure/core/bool_prim_test.exs`

**Interfaces:**
- Consumes: nothing new (design decision: `fold/2` **hardcodes** `:True`/`:False` — it has no `sig` on its path; spec §2 plumbing decision).
- Produces: bool-producing `fold/2` clauses return the constructor **value** for `True`/`False` (the value form `{:ctor, :True, []}` produces after `eval`; confirm the exact value tag — likely `{:vctor, :True, []}` or reuse how `eval({:ctor, …}, env)` evaluates). Define one helper `vbool(bool)` returning the right constructor value.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/prim_bool_eval_test.exs
defmodule Cure.Core.PrimBoolEvalTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Eval

  test "eval folds a comparison to the True constructor value" do
    v = Eval.eval({:prim, :lt, [{:int_lit, 3}, {:int_lit, 5}]}, [])
    assert v == Eval.eval({:ctor, :True, []}, [])
    refute v == {:vbool, true}
  end

  test "eval folds a false comparison to the False constructor value" do
    v = Eval.eval({:prim, :lt, [{:int_lit, 5}, {:int_lit, 3}]}, [])
    assert v == Eval.eval({:ctor, :False, []}, [])
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/prim_bool_eval_test.exs`
Expected: FAIL — `fold/2` still returns `{:vbool, true/false}`.

- [ ] **Step 3: Rewire `fold/2`**

Add the helper and update every bool-producing `fold` clause. **This is more than "comparisons + connectives + not":** `eval.ex` today has a `fold(:eq, [{:vbool,a},{:vbool,b}])` and `fold(:ne, [{:vbool,a},{:vbool,b}])` clause (`eval.ex:142,145`) handling equality *between two Bool-typed operands* — legal per `infer_prim`'s "any shared type" equality rule (Task 5) — separate from the numeric `:eq`/`:ne` clauses on `{:vint,_}`/`{:vfloat,_}`. Losing this clause silently turns `true == true` stuck (a real regression, not merely a missing nice-to-have): after this task, a Bool operand arrives as `{:vctor, :True/:False, []}`, not `{:vbool, _}`, so the old clause's pattern never matches post-migration and must be replaced, not just left in place.

```elixir
# Single source of truth with Builtins @schemas and seed/1. If those ctor
# names ever change, the Task 10 antibody fails — do not desync. Per Task 5's
# pinned closed form, `eval({:ctor, name, []}, _) == {:vctor, name, []}`
# (eval.ex:42) — no recursive eval call is actually needed here, but keeping
# it self-referential documents the identity the antibody checks.
defp vbool(true), do: eval({:ctor, :True, []}, [])
defp vbool(false), do: eval({:ctor, :False, []}, [])

defp fold(:and, [a, b]), do: with {:ok, x} <- as_bool(a), {:ok, y} <- as_bool(b), do: {:ok, vbool(x and y)}
defp fold(:or,  [a, b]), do: with {:ok, x} <- as_bool(a), {:ok, y} <- as_bool(b), do: {:ok, vbool(x or y)}
defp fold(:not, [a]),    do: with {:ok, x} <- as_bool(a), do: {:ok, vbool(not x)}
defp fold(:eq, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a == b)}
defp fold(:lt, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a < b)}
# ...same for :ne,:le,:gt,:ge and the parallel {:vfloat,_} clauses that currently produce {:vbool, _}

# Bool-operand equality (eval.ex:142,145 today) — MUST be replaced, not dropped:
# the old {:vbool,a},{:vbool,b} pattern never matches a {:vctor,_,_} operand.
defp fold(:eq, [a, b]), do: with {:ok, x} <- as_bool(a), {:ok, y} <- as_bool(b), do: {:ok, vbool(x == y)}
defp fold(:ne, [a, b]), do: with {:ok, x} <- as_bool(a), {:ok, y} <- as_bool(b), do: {:ok, vbool(x != y)}
```

`as_bool/1` maps a `True`/`False` constructor value back to an Elixir boolean for the connectives and Bool-equality (the operands are now constructor values, not `{:vbool, _}`):

```elixir
defp as_bool(v) do
  cond do
    v == vbool(true) -> {:ok, true}
    v == vbool(false) -> {:ok, false}
    true -> :stuck
  end
end
```

> **Implementer note:** clause ordering matters, but only *among the `:eq` clauses themselves* (and separately, only among the `:ne` clauses) — `[a, b]` is an unconstrained pattern that matches any 2-element argument list, so `fold(:eq, [a, b])` must be defined *after* `fold(:eq, [{:vint,_},{:vint,_}])` and `fold(:eq, [{:vfloat,_},{:vfloat,_}])` or it shadows them and numeric equality never reaches its specific clause (Elixir dispatches top-to-bottom, first match wins). Its position relative to `:lt`/`:le`/`:gt`/`:ge`/`:and`/`:or`/`:not` clauses is irrelevant — those are different leading atoms, so there is no cross-op shadowing risk to manage. If any connective or equality operand is a neutral (non-`True`/`False`) value, `as_bool` returns `:stuck` and `prim/2`'s existing `:stuck → neutral` path must handle it — verify `fold` returning `:stuck` (not a bad `with`) flows to the neutral case.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/prim_bool_eval_test.exs`
Expected: PASS.

- [ ] **Step 5: Finish migrating `bool_prim_test.exs`**

Update the eval-fold assertions (`{:vbool, true}` → the `True` constructor value) and remove any temporary skip added in Task 5.

Run: `mix test test/cure/core/bool_prim_test.exs`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/core/eval.ex test/cure/core/prim_bool_eval_test.exs test/cure/core/bool_prim_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(core): eval fold produces True/False constructor values (hardcoded, single-source)"
```

---

### Task 7: Surface `true`/`false` literals elaborate to `True`/`False` constructors

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (bool-literal clause at 307-314)
- Test: `test/cure/elab/bool_literal_ctor_test.exs` (create)

**Interfaces:**
- Consumes: the elaborator's constructor-elaboration path; `Inductive.builtin(sig, :bool)`.
- Produces: `{:literal, [subtype: :boolean], true}` elaborates to `{:ctor, :True, []}` typed at the inductive `Bool`; `false` → `{:ctor, :False, []}`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/bool_literal_ctor_test.exs
defmodule Cure.Elab.BoolLiteralCtorTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "a true literal in a Bool-returning fn elaborates and runs as the True atom" do
    src = "mod M\n  fn t() -> Bool = true\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Cure.Elab.Emit.compile_and_load(env, module: :"Cure.BoolLit1", functions: [:t])
    assert apply(mod, :t, []) == true   # erases to lowercase atom (Task 10)
  end
end
```

**Precondition:** Task 4.5 must already be done — this task's own test uses `Bool` as a return-type annotation (`fn t() -> Bool = true`), which needs `declarations.ex`'s `primitive_type/1` to no longer intercept `"Bool"` (Task 4.5, Step 3) and `:bool`/`:Bool` to be seeded into `env` with no explicit import (Task 4.5, Step 3). Without Task 4.5, `Kernel.check/3` would reject this task's own `{:ctor, :True, []}`-typed body against the still-primitive `{:vbool_type}` expected return type before this task's own change is even exercised.

> **Implementer note:** until Task 10 lands the erasure rule, `apply(mod, :t, [])` may yield the atom `:True` rather than `true`. If so, split this into (a) an elaboration-shape assertion now (`elaborate` produces `{:ctor, :True, []}` for the body — assert on the core term via the elaborator's typed entry) and (b) the runtime-`true` assertion moved to Task 10. Prefer the core-term assertion here so this task is independently green.

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/bool_literal_ctor_test.exs`
Expected: FAIL — literal still elaborates to `{:bool_lit, true}`.

- [ ] **Step 3: Rewire the literal clause**

Replace the `:boolean` case in `elaborate_expr_typed({:literal, meta, value}, …)` (elaborator.ex:307-314). There is no `elaborate_ctor_reference/4` helper anywhere in the codebase (verified: `grep -rn "elaborate_ctor_reference" lib/` is empty) — `elaborate_expr_typed` clauses return a 3-tuple `{:ok, core_term, type_value}` (see the very same clause's other branches, e.g. `{:ok, {:int_lit, value}, {:vint_type}}`), so build the result directly from Task 5's pinned `bool_type_value/1` closed form:

```elixir
    :boolean when is_boolean(value) ->
      ctor = if value, do: :True, else: :False
      {:ok, {:ctor, ctor, []}, bool_type_value(Context.signature(ctx))}
```

> **Implementer note:** `bool_type_value/1` is Task 5's helper on `Cure.Core.Kernel` — either call `Cure.Core.Kernel.bool_type_value/1` if it's exported (or export it, since it now has two callers across modules), or duplicate the two-line closed form (`{:vdata, Inductive.builtin(sig, :bool), []}`) locally with a comment pointing at the single source of truth. Do NOT re-derive the shape via a fresh `Kernel.infer` round-trip — the closed form is exact and cheaper. The function head currently binds this clause's context/env params as `_ctx, _env` (unused, underscore-prefixed) — since they are now used, drop the leading underscore on both in the function head, not just at the call site, or the code won't compile.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/bool_literal_ctor_test.exs`
Expected: PASS (per the note, the elaboration-shape assertion).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/elaborator.ex test/cure/elab/bool_literal_ctor_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): true/false literals elaborate to True/False constructors"
```

---

### Task 8: Retarget `if` / guards / literal-patterns from `bool_elim` to `:case` on `Bool`

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` — conditional infer (316-327), conditional check (604-611), `guard_chain` (1890-1909), `try_literal_match` bool branch (1949-1974), `literal_chain` (2028-2037)
- Test: existing `test/cure/elab/conditional_test.exs`, `test/cure/elab/guard_test.exs`, and the literal-pattern test from commit `ebc6a88` should stay green after the retarget (they assert runtime behavior, not the `bool_elim` term); add `test/cure/elab/if_lowers_to_case_test.exs` asserting the new core term is `:case`.

**Interfaces:**
- Consumes: the kernel's `:case` elaboration (coverage/motive/branch conversion for a 2-constructor family — already supported), `Inductive.builtin(sig, :bool)`.
- Produces: each of the five sites emits `{:case, scrut, motive, [{:True, 0, tt}, {:False, 0, ff}]}` (confirm the `:case` branch tuple shape from `erase.ex`'s `{:case, s, m, branches}` handling and the kernel's `:case` inference) instead of `{:bool_elim, scrut, motive, tt, ff}`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/if_lowers_to_case_test.exs
defmodule Cure.Elab.IfLowersToCaseTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "if on a Bool lowers to a :case core term, not bool_elim" do
    src = "mod M\n  type N = Z | S(N)\n  fn f(b: Bool) -> N = if b then S(Z()) else Z()\n"
    {:ok, env} = Program.elaborate(src)
    body = core_body_of(env, :f)          # helper: fetch f's elaborated core term
    assert match?({:case, _, _, _}, strip_to_head(body))
    refute has_bool_elim?(body)
  end
end
```

> **Implementer note:** `core_body_of/2`, `strip_to_head/1`, `has_bool_elim?/1` walk the elaborated env's def for `:f`. Confirm how to fetch a function's core body from the elaborated `Env` (`Env.get_def/2` per Explore report) and its term shape.

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/if_lowers_to_case_test.exs`
Expected: FAIL — body is still `{:bool_elim, …}`.

**Precondition:** Task 4.5 must already be done (same reasoning as Task 7 — `bool` must already be seeded/resolvable, independent of imports, before a `Bool`-typed `if`/guard/pattern can type-check against the new `:case` term).

- [ ] **Step 3: Retarget all five sites**

For each site, replace the `{:bool_elim, scrut, motive, tt, ff}` construction with a `:case` on `Bool`. The motive is unchanged in intent but its binder type changes from `{:bool_type}` to the `Bool` inductive type term. Introduce ONE helper in the elaborator, using Task 5's pinned closed form (`bool_type_term(sig) = {:data, Inductive.builtin(sig, :bool), [], []}` — the term-level counterpart of `bool_type_value/1`, not a shape to rediscover):

```elixir
defp bool_type_term(sig) do
  fid = Inductive.builtin(sig, :bool) || raise "builtin :bool not seeded (bootstrap/load-order bug)"
  {:data, fid, [], []}
end

defp bool_case(scrut_term, motive_body_type, tt, ff, ctx) do
  bool_ty = bool_type_term(Context.signature(ctx))     # core Term for the Bool inductive
  motive = {:lam, bool_ty, Cure.Core.Term.shift(motive_body_type, 1, 0)}
  {:case, scrut_term, motive, [{:True, 0, tt}, {:False, 0, ff}]}
end
```

- Conditional infer (316-327): `motive` used `{:lam, {:bool_type}, shift(t_type_core,1,0)}` → `bool_case(c_core, t_type_core, t_core, e_core, ctx)`.
- Conditional check (604-611): `bool_case(c_core, expected_core, t_core, e_core, ctx)`.
- `guard_chain` (1890-1909): the `{:bool_elim, test, motive, tt, ff}` → `bool_case(test, expected, tt, ff, ctx)`.
- `try_literal_match` bool branch (1961): `{:bool_elim, scrut_term, motive, t_core, f_core}` → `bool_case(scrut_term, expected, t_core, f_core, ctx)`.
- `literal_chain` (2035): `{:bool_elim, test, motive, body_core, rest_core}` → `bool_case(test, expected, body_core, rest_core, ctx)` (the `test = {:prim, :eq, …}` line is unchanged — it now yields the inductive `Bool` which `:case` scrutinises).

> **Implementer note:** confirm `:case`'s branch ordering/exhaustiveness expectation (does the kernel require branches in family-declaration order? include both constructors?). The 2-constructor `Bool` `:case` must satisfy the kernel's existing coverage check — this is the same coverage path every other inductive's `:case` already exercises (see Task 9's certificate.ex note for why this is sound, not just assumed).

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/elab/if_lowers_to_case_test.exs test/cure/elab/conditional_test.exs test/cure/elab/guard_test.exs`
Expected: PASS — new term is `:case`; the pre-existing behavioral tests still pass (runtime results unchanged).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/elaborator.ex test/cure/elab/if_lowers_to_case_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): retarget if/guards/literal-patterns to :case on inductive Bool"
```

---

### Task 9: Retire `bool_elim` / `bool_type` / `bool_lit` across the nine core modules

**Files (delete the now-dead clauses):**
- Modify: `lib/cure/core/term.ex` (25, 34, 73, 87-88, 114-115, 136-137, 195-196, 224-225, 286-288, 315-316, 356-357, 374-375)
- Modify: `lib/cure/core/value.ex` (54-55, 72 — both `value?({:vbool_type})` **and** `value?({:vbool, b})`, not just the first)
- Modify: `lib/cure/core/eval.ex` (49-50, 84-96)
- Modify: `lib/cure/core/quote.ex` (55-56, 76-77)
- Modify: `lib/cure/core/conv.ex` (76-77, 160, 206-207)
- Modify: `lib/cure/core/normalise.ex` (186-187, 242, 245, 247-248)
- Modify: `lib/cure/core/kernel.ex` (60-61, 253-265, 632-653 `check_bool_motive_wf/2` — dead once the `bool_elim` infer clause at 253-265 is gone, but still references `{:vbool_type}` at 642 so must be deleted too, not left as unreachable code, 676 `infer_type_value_sort` `:vbool_type`, 914, 917 `rigid_index?({:bool_type})`/`rigid_index?({:bool_lit, _})`)
- Modify: `lib/cure/core/certificate.ex` (164, 166, 254, 256)
- Modify: `lib/cure/core/serialize.ex` (38, 41, 148, 151-152 — the `(bool-type)`/`(bool <atom>)` S-expr grammar)
- Test: grep-guard test `test/cure/core/no_bool_primitive_test.exs` (create)

**Interfaces:**
- Consumes: nothing — this is pure deletion of code no longer reachable after Tasks 5–8.
- Produces: the `{:bool_type}`/`{:bool_lit}`/`{:bool_elim}`/`{:vbool}`/`{:vbool_type}`/`{:nbool_elim}` term/value forms no longer exist anywhere in `lib/cure/core`.

- [ ] **Step 1: Write the failing guard test**

```elixir
# test/cure/core/no_bool_primitive_test.exs
defmodule Cure.Core.NoBoolPrimitiveTest do
  use ExUnit.Case, async: true

  @core_files Path.wildcard("lib/cure/core/*.ex")

  test "no core module references the retired primitive Bool forms" do
    offenders =
      for f <- @core_files,
          src = File.read!(f),
          tok <- ~w(:bool_elim :bool_type :bool_lit :vbool :vbool_type :nbool_elim),
          String.contains?(src, tok),
          do: {Path.basename(f), tok}
    assert offenders == [], "still present: #{inspect(offenders)}"
  end
end
```

- [ ] **Step 2: Run guard test to verify it fails**

Run: `mix test test/cure/core/no_bool_primitive_test.exs`
Expected: FAIL — the tokens are still present in the nine modules.

- [ ] **Step 3: Delete the clauses module by module**

Remove each `:bool_type`/`:bool_lit`/`:bool_elim`/`:vbool`/`:vbool_type`/`:nbool_elim` clause/branch at the lines listed above. After each module, run that module's own test file (`mix test test/cure/core/<module>_test.exs` if present) to catch a broken deletion early. The deletion is mechanical BUT: the compiler will now reject any remaining producer — if compilation fails with "no clause matching `{:bool_elim, …}`", a producer was missed in Tasks 5–8; fix the producer, do not re-add the clause.

> **Implementer note (`certificate.ex`, SOUNDNESS — verified, not just asserted):** the `bool_elim` totality/guardedness clauses at 164-168 (`guarded_node?(name, p, {:bool_elim, s, m, tt, ff}, root, smaller)`) and 254-256 (`calls?(name, {:bool_elim, s, m, tt, ff})`) are safe to delete because the general `:case` clauses genuinely subsume them, for a concrete, checkable reason — not merely "it must, since other inductives use it":
> - `guarded_node?`'s general `:case` clause (`certificate.ex:138-153`) computes, per branch, `root2 = root + ar` and `smaller2 = shift(smaller, ar)` where `ar` is that branch's constructor arity. The deleted `bool_elim` clause's comment says exactly "bool_elim binds nothing, so every sub-term stays at the same root/smaller" — i.e. its behavior is the `ar = 0` instance of the general rule. Since Task 2's schema (`@schemas bool: [{:False, 0}, {:True, 0}]`) fixes both of `Bool`'s constructors at arity 0 — enforced by `Builtins.validate!/3`, not just convention — a `:case` on `Bool` *always* has `ar = 0` in both branches, so `guarded_node?`'s `:case` clause computes the identical `root2 = root`, `smaller2 = smaller` the `bool_elim` clause hand-wrote. The subsumption isn't incidental; it's forced by the schema's own arity constraint.
> - `calls?`'s general `:case` clause (`certificate.ex:249-252`, immediately before the deleted `calls?(name, {:bool_elim,...})` at 254-256) already recurses into `s`, `m`, and every branch body — exactly the four positions (`s`, `m`, `tt`, `ff`) the `bool_elim`-specific clause checked, just addressed as `branches` instead of two named args.
> - This reasoning is Bool-specific (it leans on Bool's constructors being schema-enforced nullary) — do not generalize it to argue any future arity-bearing builtin's `:case` is automatically safe; re-derive per builtin if this pattern is reused for something with non-nullary constructors.
>
> This is still the single most soundness-sensitive deletion in the plan — the reasoning above is what the Task 10 antibody and Task 12 adversarial review should be handed directly (cite `certificate.ex:138-153` and the arity-0 schema constraint), not re-derived from scratch under gate pressure.

- [ ] **Step 4: Run guard test + core suite to verify green**

Run: `mix test test/cure/core/no_bool_primitive_test.exs && mix test test/cure/core/`
Expected: PASS — no tokens remain; all core tests green.

- [ ] **Step 5: Update the conformance fixture**

Rewrite the affected lines of `test/fixtures/core_conformance.txt` to the inductive grammar:
- Line 8 `accept | (bool true) | (bool-type)` → the `True` constructor S-expr typed at the `Bool` family (use serialize.ex's new constructor grammar).
- Line 10 `accept | (bool-type) | (type 0)` → the `Bool` family reference typed at `(type 0)`.
- Line 15 `accept | (prim lt (int 3) (int 5)) | (bool-type)` → `... | <Bool family type S-expr>`.
- Line 16 `accept | (prim not (bool true)) | (bool-type)` → operand becomes the `True` constructor; result the `Bool` family type.
- Lines 24-25 (`reject` cases) — keep rejecting; update operand grammar (`(bool true)` → constructor S-expr) so the reason is unchanged (bool-not-numeric; and-needs-bool-operands).

The conformance harness base env must be `Builtins.seed(Env.empty())` (design decision 1) so `Bool` resolves. Update the harness's context construction accordingly.

> **Implementer note (verified against source):** the harness is `test/cure/core/conformance_test.exs`; it builds `ctx = Context.empty()` once (line 27) and reuses it for every corpus entry inside the `for` loop. The one-line fix is `ctx = Context.empty(Cure.Core.Builtins.seed(Cure.Core.Env.empty()))` — no other structural change to the harness is needed (it's still one shared `ctx` across the whole corpus).

- [ ] **Step 6: Run the conformance test to verify green**

Run: `mix test test/cure/core/conformance_test.exs`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/core/term.ex lib/cure/core/value.ex lib/cure/core/eval.ex lib/cure/core/quote.ex lib/cure/core/conv.ex lib/cure/core/normalise.ex lib/cure/core/kernel.ex lib/cure/core/certificate.ex lib/cure/core/serialize.ex test/cure/core/no_bool_primitive_test.exs test/fixtures/core_conformance.txt test/cure/core/conformance_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "refactor(core): retire bool_elim/bool_type/bool_lit; Bool is inductive (9 modules + conformance)"
```

---

### Task 10: Erasure — `False`/`True` lower to native `false`/`true` atoms; the drift antibody

**Files:**
- Modify: `lib/cure/elab/emit.ex` (constructor lowering at 139-143) OR `lib/cure/elab/erase.ex` (constructor erase at 20-30) — whichever is the single lowering chokepoint; prefer `emit.ex` since it produces the BEAM atom.
- Test: `test/cure/elab/bool_erasure_test.exs` (create); complete Task 7's runtime assertion; `test/antigen/builtin_bool_drift_test.exs` (create — the single-source-of-truth antibody)

**Interfaces:**
- Consumes: `Inductive.builtin(env, :bool)` to identify that a `{:ctor, name, []}` belongs to the `Bool` family.
- Produces: `{:ctor, :True, []}` lowers to the BEAM atom `true`; `{:ctor, :False, []}` to `false`; a `:case` on `Bool` scrutinises those lowercase atoms — matching what `{:prim}` comparisons already return at runtime.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/bool_erasure_test.exs
defmodule Cure.Elab.BoolErasureTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "True/False constructors run as lowercase BEAM booleans" do
    src = "mod M\n  fn t() -> Bool = true\n  fn f() -> Bool = false\n  fn c(b: Bool) -> Bool = if b then false else true\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.BoolErase1", functions: [:t, :f, :c])
    assert apply(mod, :t, []) == true
    assert apply(mod, :f, []) == false
    assert apply(mod, :c, [true]) == false
    assert apply(mod, :c, [false]) == true
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/bool_erasure_test.exs`
Expected: FAIL — constructors lower to atoms `:True`/`:False`, so `apply(mod, :t, [])` is `:True`, not `true`.

- [ ] **Step 3: Add the Bool-family lowering rule**

In `emit.ex`'s `lower/3` constructor clause, special-case the `Bool` family's nullary constructors to lowercase atoms:

```elixir
defp lower(env, {:ctor, name, args}, ctx) do
  cond do
    args == [] and Inductive.builtin(env, :bool) == Inductive.ctor_family(env, name) ->
      {:atom, @line, bool_atom(name)}     # :True -> true, :False -> false
    true ->
      case Enum.map(args, &lower(env, &1, ctx)) do
        [] -> {:atom, @line, name}
        forms -> {:tuple, @line, [{:atom, @line, name} | forms]}
      end
  end
end

defp bool_atom(:True), do: true
defp bool_atom(:False), do: false
```

The `:case` on `Bool` already lowers its branches keyed by constructor name via `branch_clause/4` (`emit.ex:260-280`); ensure its patterns use the lowercase atoms too. The exact edit site (verified against source): `branch_clause/4`'s arity-0 pattern is built as `{:atom, @line, cname}` directly from the raw constructor name (`emit.ex:272-275`, the `case present do [] -> {:atom, @line, cname}` branch) — change `cname` to `bool_atom_or_self(env, cname)` at that one call site:

```elixir
defp bool_atom_or_self(env, name) do
  if Inductive.builtin(env, :bool) == Inductive.ctor_family(env, name), do: bool_atom(name), else: name
end
```

> **Implementer note:** `emit.ex` must have `env` in scope at `lower/3` — confirmed (`lower(env, {:ctor, name, args}, ctx)`, `emit.ex:139`) — and `branch_clause/4` already receives `env` as its first argument (`emit.ex:260`), so no signature change is needed, only the one-line substitution in its pattern-building `case`. Confirm `Inductive.ctor_family/2` returns the family-id for a ctor name (it does — `inductive.ex:182-183`). The `:case`-branch lowering site needs this same treatment — otherwise construction erases to `true`/`false` but the match still tests `:True`/`:False` and never fires. Test `c/1` above is the guard for that.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/bool_erasure_test.exs`
Expected: PASS. Also re-run Task 7's `test/cure/elab/bool_literal_ctor_test.exs` and complete its runtime `== true` assertion.

- [ ] **Step 5: Write the drift antibody**

```elixir
# test/antigen/builtin_bool_drift_test.exs
defmodule Antigen.BuiltinBoolDriftTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Env, Eval}

  test "fold's hardcoded True/False agree with the seeded :bool schema names" do
    # Task 6 hardcodes :True/:False in eval; Task 2/3 seed the schema. They must not drift.
    names = Builtins.schema(:bool) |> Enum.map(&elem(&1, 0)) |> Enum.sort()
    assert names == [:False, :True]
    # fold's true-value must be the True constructor value.
    assert Eval.eval({:prim, :lt, [{:int_lit, 1}, {:int_lit, 2}]}, []) == Eval.eval({:ctor, :True, []}, [])
  end
end
```

- [ ] **Step 6: Run the antibody to verify it passes**

Run: `mix test test/antigen/builtin_bool_drift_test.exs`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/elab/emit.ex test/cure/elab/bool_erasure_test.exs test/cure/elab/bool_literal_ctor_test.exs test/antigen/builtin_bool_drift_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(erase): Bool constructors lower to native false/true atoms; drift antibody"
```

---

### Task 11: Load-order regression guard — confirm Task 4.5 makes `:core` ordering moot for the dependent path

**Revised scope (hardening-review correction).** The original framing of this task assumed `lib/cure/stdlib/preload.ex`'s `__group__`-based ordering (lines 27-123) governs the order in which the *dependent-kernel elaboration* pipeline (`Cure.Elab.Program`) processes prelude modules, and that `Std.Eq`/`Std.Core`'s comparison `{:prim}` ops needed `Std.Bool` to have compiled first within that ordering. Verified against source: `Cure.Stdlib.Preload` is a **runtime BEAM-loading** module (`:code.load_binary/3` into a running VM, per its own moduledoc) — it has no relationship to `Cure.Elab.Program.check_ast/1`'s compile-time env-building, which resolves imports individually and recursively via `import_env/2`/`import_source_env/2` (`program.ex:212-236`), not via any `:core`-group batch. There is no code path today by which `preload.ex`'s grouping affects what `Inductive.builtin(env, :bool)` resolves to during elaboration. Separately, `Std.Eq` (`lib/std/eq.cure`) declares `proto Eq(T)` / `impl Eq for Int` — protocol/impl surface syntax not confirmed to route through the dependent Core-kernel path (`Cure.Elab.Program.dependent?/1`) at all; it may be handled entirely by the legacy `Cure.Types`-based pipeline, which this plan does not touch and which has no dependency on `lib/cure/core`'s `{:vbool_type}`/`{:bool_type}` forms.

With **Task 4.5** landed, the actual bootstrapping risk this task was trying to close is already closed by construction: `check_ast/1`'s `env0` always includes the seeded `Bool`/`Nat` families *before* `elaborate_declarations` processes a single declaration of the module being compiled (Task 4.5, Step 3) — there is no "first declaration in some group" race left to guard, because nothing in the compiled module's own declaration order runs before the seed. This task is downgraded from "implement an ordering fix" to a **regression test** confirming that property, plus an explicit note correcting the design spec's bootstrapping-risk framing for future readers.

**Files:**
- Test: `test/cure/elab/builtin_load_order_test.exs` (create) — no production-code change expected; if this test fails, Task 4.5 is incomplete, not this task.

- [ ] **Step 1: Write the regression test**

```elixir
# test/cure/elab/builtin_load_order_test.exs
defmodule Cure.Elab.BuiltinLoadOrderTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Inductive

  test ":bool is seeded even when a Bool-typed comparison is the module's very first declaration" do
    src = "mod M\n  fn use_eq(a: Int, b: Int) -> Bool = a == b\n"
    assert {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert Inductive.builtin(env, :bool) == :Bool
  end

  test ":nat is seeded even when Nat arithmetic is the module's very first declaration" do
    src = "mod M\n  fn first(n: Nat) -> Nat = n\n"
    assert {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert Inductive.builtin(env, :nat) == :Nat
  end
end
```

- [ ] **Step 2: Run test to verify it passes**

Run: `mix test test/cure/elab/builtin_load_order_test.exs`
Expected: PASS immediately, given Task 4.5 (no ordering fix needed — this is the point). If either test fails, do not implement an ordering fix here; go back and fix Task 4.5's `env0` seeding instead, since that is the actual mechanism this property depends on.

- [ ] **Step 3: Commit**

```bash
git add -- test/cure/elab/builtin_load_order_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(elab): regression guard — Bool/Nat seeded before any declaration, no ordering dependency"
```

---

### Task 12: PHASE 1 GATE — Antigen antibodies + full Antigen + full suite + oracle + adversarial review + HUMAN HARD-STOP

**Files:**
- Create: `test/antigen/builtin_bool_migration_test.exs` (the migration-soundness antibody)
- Verify only (no new production code): full suite, full Antigen, oracle replay.

**This task does not merge. It produces the evidence package for the human TCB review and STOPS.**

- [ ] **Step 1: Write the migration-soundness antibody**

An antibody asserting the `bool_elim → :case` migration preserves normal forms and termination certification, and that a malformed/duplicate `@builtin` binding is rejected:

```elixir
# test/antigen/builtin_bool_migration_test.exs
defmodule Antigen.BuiltinBoolMigrationTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Env, Inductive, Eval}

  test "case-on-Bool normal forms match the intended branch semantics" do
    # if-true reduces to the then-branch; if-false to the else-branch — via :case, not bool_elim.
    t = Eval.eval({:ctor, :True, []}, [])
    f = Eval.eval({:ctor, :False, []}, [])
    refute t == f
  end

  test "a name-mismatched @builtin(:bool) binding is rejected (Coin as Bool)" do
    # Family/ctor maps per Task 2's grounded shape: family needs `level:`
    # (inductive.ex:108); ctor maps have no `:family` field (membership is
    # derived by `declare/3` into `ctor_to_family`, not carried on the ctor).
    env =
      Inductive.declare(Env.empty(), %{name: :Coin, params: [], indices: [], level: 0},
        [%{name: :Heads, args: [], result_indices: [], result_params: [], quantities: []},
         %{name: :Tails, args: [], result_indices: [], result_params: [], quantities: []}])
    assert_raise ArgumentError, fn -> Builtins.validate!(env, :bool, :Coin) end
  end

  test "a second :bool registration is a hard error, not a silent rebind" do
    env = Builtins.seed(Env.empty())
    assert_raise ArgumentError, fn -> Inductive.register_builtin(env, :bool, :OtherBool) end
  end
end
```

Run: `mix test test/antigen/builtin_bool_migration_test.exs`
Expected: PASS.

- [ ] **Step 2: Run the full Antigen suite (alone)**

Run: `mix test test/antigen/`
Expected: PASS — no soundness antibody regressed.

- [ ] **Step 3: Run the oracle replay + relevant clusters (alone)**

Run: `mix test test/oracle_replay_test.exs`
Then re-run the behavior-preservation clusters and confirm accept/accept unchanged:
Run: `mix cure.oracle cond && mix cure.oracle guard && mix cure.oracle match`
Expected: verdicts unchanged (accept/accept `same`); no cluster regresses.

- [ ] **Step 4: Run the FULL suite ONCE, alone**

Run: `mix test`
Expected: PASS. **Do not hardcode an expected pass count in this plan** — record the actual `mix test` pass count on this branch immediately before Task 1 begins (a fresh baseline run, not a number pinned at plan-writing time, since this branch accumulates other commits between when this plan is written and when it executes) and diff against that: this run's total should be baseline + every new test file/case added across Tasks 1-12, minus none.

- [ ] **Step 5: Dispatch an independent adversarial review subagent**

Dispatch ONE subagent (general-purpose, Sonnet) to adversarially verify the Phase 1 diff (`git diff main...HEAD -- lib/cure/core lib/cure/elab lib/cure/compiler`), specifically probing: (a) can any term still reach a deleted `bool_elim` clause and crash or mis-check; (b) does `:case`-on-`Bool` totality/coverage in `certificate.ex` genuinely subsume what `bool_elim` accounted for (no non-total term now certified total) — point the reviewer at Task 9's grounded arity-0 subsumption argument and have them verify it, not re-derive it; (c) can a `{:prim}` be reached with `:bool` unseeded to produce a wrong type silently instead of the intended `raise`; (d) does `fold/2`'s hardcoded `:True`/`:False` ever disagree with the schema; (e) does `Bool` as a *type annotation* (not just a literal/comparison) resolve correctly everywhere post-migration — specifically confirm `lib/cure/elab/declarations.ex`'s `primitive_type/1` no longer short-circuits `"Bool"` (Task 4.5) and that `Cure.Elab.Program.check_ast/1`'s `env0` is unconditionally seeded (Task 4.5) rather than relying on an explicit import; (f) what actually happens when a module locally redeclares `type Nat = Z | S(Nat)` (or `type Bool = False | True`) under the seeded builtin's bare name — confirm empirically (compile such a module and inspect the resulting `env`) whether it silently aliases the canonical family (per Task 4.5's collision analysis) and report the actual behavior, since this contradicts the design spec's "nominal, not structural" claim and was not resolved during planning. Require exact file:line evidence for each.

- [ ] **Step 6: Assemble the evidence package and HARD-STOP for human review**

Write `docs/superpowers/plans/PHASE1-GATE-EVIDENCE.md` summarizing: the per-task commits, red→green evidence, the antibody results, full-Antigen + full-suite + oracle results, and the adversarial reviewer's findings + resolutions. Then **STOP** — do NOT merge, do NOT proceed to Phase 2. Notify the operator: Phase 1 (TCB) is ready for review with the evidence package.

---

## Phase 2 — Nat → Int runtime erasure (untrusted, ungated but full-suite verified)

Phase 2 begins ONLY after the human approves Phase 1. It touches no kernel code. The `:nat` schema + `@builtin(:nat)` binding already landed in Phase 1 (Task 3/4), so Phase 2 is purely erase/emit consumption of an already-validated binding (spec §Phasing ownership clarification).

---

### Task 13: Erase `Z`/`S` to native integers (construction)

**Files:**
- Modify: `lib/cure/elab/emit.ex` (constructor lowering — extend the Task 10 `cond` with a `:nat` family arm)
- Test: `test/cure/elab/nat_erasure_construction_test.exs` (create)

**Interfaces:**
- Consumes: `Inductive.builtin(env, :nat)`, `Inductive.ctor_family/2`.
- Produces: `{:ctor, :Z, []}` lowers to integer `0`; `{:ctor, :S, [n]}` lowers to `lower(n) + 1`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/nat_erasure_construction_test.exs
defmodule Cure.Elab.NatErasureConstructionTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "Nat literals erase to native integers, not nested tuples" do
    src = "mod M\n  fn three() -> Nat = S(S(S(Z())))\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NatC1", functions: [:three])
    assert apply(mod, :three, []) == 3
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/nat_erasure_construction_test.exs`
Expected: FAIL — `three/0` returns `{:S, {:S, {:S, :Z}}}`.

- [ ] **Step 3: Add the `:nat` construction lowering**

Extend `emit.ex`'s `lower/3` constructor `cond` (from Task 10):

```elixir
    args == [] and nat_family?(env, name) ->        # :Z
      {:integer, @line, 0}
    match?([_], args) and nat_family?(env, name) -> # :S(n)
      [inner] = args
      {:op, @line, :+, lower(env, inner, ctx), {:integer, @line, 1}}
```

with `defp nat_family?(env, name), do: Inductive.builtin(env, :nat) == Inductive.ctor_family(env, name)`.

> **Forward-looking note (post-foundation extensibility — do NOT expand scope in this plan).** A future stdlib addition (`Std.Bounded`, the renamed `Fin`) is confirmed to take this exact same native-integer erasure (`First ↦ 0`, `Next(b) ↦ b + 1`, `match ↦ integer test/decrement`) — it is a bounded `Nat`, structurally unary, and would otherwise erase to RAM-fatal nested tuples on ESP32. To let it slot in by registration alone rather than a second copy of this lowering, prefer a general predicate — `native_int_builtin?(env, name)` that returns true when `name`'s family is registered under **any** native-int builtin key (today just `:nat`; later `:bounded`) — over hardcoding `:nat`. Keep the *set of keys* minimal and explicit (a small module-attribute list in `emit.ex`, e.g. `@native_int_builtins [:nat]`), so adding `:bounded` later is a one-line change with no new lowering logic. This is a naming/shape choice for THIS task's helper, not new behavior: for the foundation's scope the set is exactly `[:nat]`. Recorded in the `stdlib-dependent-expansion` project memory.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/nat_erasure_construction_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/emit.ex test/cure/elab/nat_erasure_construction_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(erase): Nat Z/S construction lowers to native integers"
```

---

### Task 14: Erase `match` on `Nat` to integer test/decrement

**Files:**
- Modify: `lib/cure/elab/emit.ex` (the `:case` lowering — add a `:nat`-family branch form)
- Test: `test/cure/elab/nat_erasure_match_test.exs` (create)

**Interfaces:**
- Consumes: `Inductive.builtin(env, :nat)`; the `:case` lowering site.
- Produces: a `:case` scrutinising a `Nat` lowers to `case <n> of 0 -> <Z-branch>; _ -> (<S-var> = <n> - 1; <S-branch>)` — the `S(m)` branch binds `m` to `n - 1`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/nat_erasure_match_test.exs
defmodule Cure.Elab.NatErasureMatchTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "pattern-matching a Nat uses integer test/decrement and returns correctly" do
    src = "mod M\n  fn pred(n: Nat) -> Nat = match n\n    Z() -> Z()\n    S(m) -> m\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NatM1", functions: [:pred])
    assert apply(mod, :pred, [0]) == 0
    assert apply(mod, :pred, [5]) == 4
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/nat_erasure_match_test.exs`
Expected: FAIL — the `:case` lowering emits atom/tuple patterns (`:Z` / `{:S, m}`) that never match the integer inputs.

- [ ] **Step 3: Add the `:nat` `:case` lowering**

In the `:case` lowering, when the scrutinee's family is `:nat`, emit the integer-test form instead of atom/tuple constructor patterns: a `0 ->` clause for the `Z` branch, and a catch-all `Other ->` clause that binds the `S` branch's variable to `Other - 1` before the branch body. Preserve branch order/semantics.

> **Implementer note:** locate the `:case` lowering in `emit.ex` (the counterpart to `erase.ex`'s `{:case, s, m, branches}`), read how branches carry `{ctor, arity, body}` and the branch's bound variable, and construct the Erlang `case` abstract form with the two clauses. The `S(m)` branch's bound `m` must be an Erlang match `M = Scrut - 1` (or a fresh var bound in the clause). Guard: this arm fires only when `Inductive.builtin(env, :nat) == <scrutinee family>`; all other families keep the existing constructor-pattern lowering unchanged.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/nat_erasure_match_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/emit.ex test/cure/elab/nat_erasure_match_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(erase): Nat match lowers to integer test/decrement"
```

---

### Task 15: Generics/monomorphisation guard + `S`/`Z` as first-class values

**Files:**
- Modify: `lib/cure/elab/emit.ex` (ensure `S`/`Z` used as first-class values lower to the increment/zero closures)
- Test: `test/cure/elab/nat_generics_guard_test.exs` (create)

**Interfaces:**
- Consumes: `Inductive.builtin(env, :nat)`. (Monomorphisation is **confirmed absent** from the dependent pipeline, not merely "to be verified" — see Step 3's grounded finding; there is nothing to consume from that stage.)
- Produces: `S`/`Z` referenced as values (not immediately applied) lower to `fun(N) -> N + 1 end` / `0`. Design decision 2's "concrete `Nat` argument to a monomorphised generic function uses the native rep" branch is unreachable in the current codebase (no monomorphisation on this path); an abstract-parameter generic body over an un-instantiated type variable does NOT emit native-int decrement, unconditionally.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/nat_generics_guard_test.exs
defmodule Cure.Elab.NatGenericsGuardTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "S used as a first-class value is the increment closure" do
    src = "mod M\n  fn bump(f: (Nat) -> Nat, n: Nat) -> Nat = f(n)\n  fn go() -> Nat = bump(S, Z())\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NatG1", functions: [:go])
    assert apply(mod, :go, []) == 1
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/nat_generics_guard_test.exs`
Expected: FAIL — bare `S` lowers to the atom `:S` / an arity-mismatched constructor form.

- [ ] **Step 3: Lower first-class `S`/`Z`; the monomorphisation guard is confirmed unconditional, not contingent**

- Lower a bare `Z` value to `{:integer, @line, 0}` and a bare `S` value to a 1-arg increment closure `fun(N) -> N + 1 end` (Erlang abstract form).
- The native `:nat` lowering fires only on a concrete `Nat` family match (`nat_family?/2`'s `Inductive.builtin(env, :nat) == Inductive.ctor_family(env, name)` check), which an abstract type variable never satisfies — an unspecialised generic body over an abstract parameter never emits native-int decrement. Add a comment at the `nat_family?/2` guard site recording this.

**Grounded resolution (hardening-review correction — this is settled, not an open implementer-verification item):** monomorphisation does **not** run pre-erasure in the dependent pipeline, confirmed by direct trace, not inference: `lib/cure/compiler.ex`'s `dependent_codegen/1` (~lines 241-249) — the actual entry point for any module `Cure.Elab.Program.dependent?/1` routes to the Core-kernel path — calls `Cure.Elab.Program.check_ast_with_locals(ast)` then `Cure.Elab.Emit.compile_forms(env, ...)` directly, with no monomorphisation step anywhere in between. `grep -rn "monomorph" lib/cure/elab/*.ex lib/cure/core/*.ex` returns zero hits. `Cure.Optimizer.Monomorphise` (`lib/cure/optimizer/monomorphise.ex`) exists and runs via `maybe_optimize/3` (`compiler.ex:204-208`), but it specializes call sites by resolving types through `Cure.Types.Type.resolve/1` and `Cure.Types.Unify.unify_many/1` — the **legacy**, non-dependent type system's own notion of polymorphism (`{:type_var, _}` placeholders), a completely different representation from the dependent kernel's erased `{a: Type}` Π-binders that `test/cure/compiler/dependent_vec_codegen_test.exs`'s `append({a: Type}, …)` uses. There is no evidence, and strong structural evidence against, `Monomorphise` ever specializing a dependent-kernel-checked generic function.

**Consequence:** design decision 2's "gets the native rep in its monomorphised copy" branch cannot fire for any function reaching erasure via the dependent path — for the entire currently-buildable scope of this plan, the fallback ("unspecialised generic body over an abstract parameter never emits native-int decrement, keeps the generic `{:ctor,…}` representation") is not a defensive contingency for a rare case; it is the **unconditional, always-taken** behavior for every generic dependent function whose type parameter is instantiated at `Nat`. State this plainly in the implementation (a comment at `nat_family?/2` citing this task, not a runtime check that branches on "is monomorphised" — there is nothing to branch on) rather than leaving a "confirm... if not guaranteed, STOP" hedge for the implementer to re-discover under Phase-2 time pressure. This does not block Phase 2 — it only means `Nat`'s native-Int win is scoped to monomorphic call sites and concretely-`Nat`-typed non-generic code that resolves to the *actual seeded* `:Nat` family — but it should be called out explicitly in Phase 2's own commit message and the design spec should be corrected (it currently frames this as "Phase 2 must state which, before implementation" as if the resolution were a matter of choice; it is not — monomorphisation-first is not available today, so the "unspecialised, no native rep" branch is the only one that exists). Note this is a *separate* scope limit from the "locally-redeclared `Nat` stays unary" claim in the design's "Nominal, not structural" section — Task 4.5 found that claim itself may not hold once `:nat` is unconditionally seeded (a name collision in the unqualified `env.families` map); see Task 4.5's escalation item.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/nat_generics_guard_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/emit.ex test/cure/elab/nat_generics_guard_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(erase): first-class S/Z closures; monomorphisation guard for Nat rep"
```

---

### Task 16: Representation-agreement property + Nat oracle probe + Phase 2 full-suite gate

**Files:**
- Create: `test/property/nat_representation_agreement_test.exs`
- Create: `test/oracle/nat/nat01_arith.cure`, `test/oracle/nat/nat01_arith.idr`, `test/oracle/nat/verdicts.json`
- Verify only: full suite.

**Interfaces:**
- Consumes: the erased-Nat runtime (Tasks 13-15) and the inductive-Nat kernel evaluation.
- Produces: a property test that erased-Nat evaluation agrees with inductive-Nat evaluation on a generated corpus; an oracle probe confirming efficient `Nat` arithmetic compiles + runs to the right integer on the BEAM, accept/accept vs Idris.

- [ ] **Step 1: Write the representation-agreement property**

```elixir
# test/property/nat_representation_agreement_test.exs
defmodule Cure.Property.NatRepresentationAgreementTest do
  use ExUnit.Case, async: true
  # For each n in a generated corpus, the erased runtime value of a Nat-producing
  # program equals n, matching the inductive-Nat count. Use the project's existing
  # property/StreamData harness if present; otherwise a deterministic corpus 0..64.

  for n <- 0..64 do
    test "erased S^#{n}(Z) evaluates to #{n}" do
      src = "mod M\n  fn v() -> Nat = #{String.duplicate("S(", unquote(n))}Z()#{String.duplicate(")", unquote(n))}\n"
      {:ok, env} = Cure.Elab.Program.elaborate(src)
      {:ok, mod} = Cure.Elab.Emit.compile_and_load(env, module: :"Cure.NatP#{unquote(n)}", functions: [:v])
      assert apply(mod, :v, []) == unquote(n)
    end
  end
end
```

> **Implementer note:** if the repo has an Antigen/StreamData generator convention for corpora, use it instead of the `0..64` unrolled range to match house style; the agreement invariant (erased value == inductive count) is the fixed contract.

- [ ] **Step 2: Run the property to verify it passes** (Tasks 13-15 make it green)

Run: `mix test test/property/nat_representation_agreement_test.exs`
Expected: PASS.

- [ ] **Step 3: Add the oracle probe**

**Note on this probe's own `type Nat = Z | S(Nat)`:** this declares `Nat` locally in `mod M` rather than importing `Std.Nat` — exactly the name-collision scenario Task 4.5 flags as an open question (does a locally-declared `Nat` silently take over the seeded `:nat` binding, given `env.families` is keyed by bare name with no module-qualification?). If Task 4.5's escalation resolved that question before Phase 2 starts, follow whatever behavior was decided; if it's still open, this probe is exactly the fixture to resolve it with (does `four/0` return `4` as a native integer, confirming the local declaration WAS treated as the canonical `:nat` family, or does it return a nested-tuple encoding, confirming it wasn't) — record which, don't assume.

Create the paired probe (faithful transliteration, same signature both languages):

`test/oracle/nat/nat01_arith.cure`:
```cure
mod M
  type Nat = Z | S(Nat)
  fn plus(a: Nat, b: Nat) -> Nat = match a
    Z() -> b
    S(m) -> S(plus(m, b))
  fn four() -> Nat = plus(S(S(Z())), S(S(Z())))
```

`test/oracle/nat/nat01_arith.idr` (`%default total`, no module line):
```idris
%default total
data Nat' = Z | S Nat'
plus : Nat' -> Nat' -> Nat'
plus Z b = b
plus (S m) b = S (plus m b)
four : Nat'
four = plus (S (S Z)) (S (S Z))
```

- [ ] **Step 4: Run the oracle and freeze verdicts**

Run: `mix cure.oracle nat`
Expected: both accept; write `test/oracle/nat/verdicts.json` with relation `same` (never hand-write a verdict — let the oracle produce it).

- [ ] **Step 5: Replay green**

Run: `mix test test/oracle_replay_test.exs`
Expected: PASS.

- [ ] **Step 6: Run the FULL suite ONCE, alone (Phase 2 gate)**

Run: `mix test`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add -- test/property/nat_representation_agreement_test.exs test/oracle/nat/nat01_arith.cure test/oracle/nat/nat01_arith.idr test/oracle/nat/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(nat): representation-agreement property + Nat arithmetic oracle probe"
```

---

## Self-Review (against the spec)

*Updated during recursive-skeptical-review hardening — the bullets below reflect the plan's state after that pass, not the original Explore-report-derived draft. Where the hardening pass changed a task's scope or closed an open verification point, this section says so rather than restating the superseded original claim.*

**Spec coverage:**
- §1 registry mechanism → Tasks 1 (field/accessors), 3 (seed), 4 (parser + prelude wiring). ✅
- §1 schema checks **names not arity** → Task 2. ✅
- §1 single-registration invariant (both halves: prelude-only honoring + hard error on duplicate) → Task 1 (hard error) + Task 4 (prelude-only gate, now grounded in `module_atom/1` + `Preload.module_groups/0` rather than a file-path check that `Program.elaborate/1` has no access to). ✅
- §1 `@builtin`-on-`type` parser gap → Task 4 (corrected: only `parse_at/1`'s dispatch needed a new case; `attach_decorator/3` already handles the `{:container, ...}` shape `type Bool = False | True` actually parses to — no new clause needed there). ✅
- §1 `Env` builtins-field extension → Task 1. ✅
- §1 nominal-not-structural caveat → surfaced in Task 15's note + design decision 2, **but the claim itself is now suspect, not confirmed** (hardening-review finding, Task 4.5): once `:bool`/`:nat` are unconditionally seeded (Task 4.5), a module locally redeclaring `type Nat = Z | S(Nat)` under the *same bare name* collides with the seeded family in the unqualified `env.families` map (`Inductive.declare/3` has no "already declared" guard) — it may silently become an alias of the canonical `:nat` family rather than staying a distinct, unary-encoded family as the spec claims. Flagged as an explicit test + human-escalation item in Task 4.5, not silently resolved either way. ⚠️ (open item for the Phase 1 gate, not a clean ✅)
- §1/§2 **`Bool` as a type annotation, independent of `{:prim}`/literals** → **not originally covered by any task; closed by new Task 4.5** (hardening-review finding: `declarations.ex`'s `primitive_type/1` hardcodes `"Bool" → {:bool_type}` for every function/record/alias type annotation, completely independent of the registry, and `Program.check_ast/1` never seeds `:bool`/`:nat` for a source with no explicit import — confirmed nowhere used in this codebase). Without Task 4.5, Task 9's kernel deletions would break every `Bool`-typed signature in the codebase, undetected by Task 9's own guard test (which only scans `lib/cure/core`, not `lib/cure/elab`).
- §2 `infer_prim` → inductive Bool → Task 5, now with the exact closed-form value (`{:vdata, fid, []}`) pinned instead of left to per-task rediscovery. ✅
- §2 `fold/2` hardcodes `:True`/`:False` + single-source-of-truth + drift assertion → Task 6 + Task 10 antibody, now including the previously-missing Bool-operand `:eq`/`:ne` fold clauses (the "any shared type" equality rule Task 5 documents). ✅
- §2 literals → constructors → Task 7. ✅
- §2 if/guard/literal retarget to `:case` → Task 8. ✅
- §2 retire across **nine** modules incl. `serialize.ex` + conformance fixture → Task 9, with the certificate.ex subsumption now a proven arity-0 argument rather than an "it must" assertion, and the file-citation list completed (`value.ex:55`, `check_bool_motive_wf/2`, `rigid_index?` clauses — all still self-healing via Task 9's own grep guard, since they're within `lib/cure/core`). ✅
- §2 erasure to lowercase atoms → Task 10, with the exact `branch_clause/4` edit site pinned. ✅
- §3 Nat→Int construction/match/first-class/arith → Tasks 13, 14, 15. ✅
- §3 soundness placement (untrusted) + representation-agreement → Task 16. ✅
- §3 generics gap (open) → **resolved as a confirmed fact, not a design choice**: monomorphisation does not run in the dependent pipeline at all (grounded trace through `compiler.ex`'s `dependent_codegen/1`), so the "unspecialised body, no native rep" branch is the only reachable one. Task 15 states this plainly. ✅
- §Phasing sequential, Phase 1 first, `:nat` schema seeded in Phase 1 → Tasks 3/4 seed `:nat`; Phase 2 consumes only. ✅
- §Testing antibodies (malformed + name-mismatched + duplicate + migration + drift) → Tasks 2, 10, 12. ✅
- §Risks bootstrapping/load-order → **downgraded from an implementation task to a regression test (Task 11)** once Task 4.5's unconditional `env0` seeding closed the actual gap; the design spec's own bootstrapping narrative (prelude compiles in `__group__`-ordered batches) does not describe how `Cure.Elab.Program`'s compile-time env-building actually works (`preload.ex` is a runtime BEAM-loader, unrelated to `check_ast/1`) and should be corrected in the spec, not just the plan. Migration churn → Task 8's reuse of green tests; capitalization → Tasks 7/10. ✅

**Placeholder scan:** No "TBD"/"handle edge cases" remain that aren't closed by a grounded citation. The two spec-flagged open questions are resolved as explicit design decisions (bootstrap-seeded, unconditional `env0`; monomorphisation confirmed absent, so Nat's native rep is scoped to non-generic/monomorphic call sites as a permanent property, not a contingency).

**Type consistency:** `Inductive.builtin/2`, `register_builtin/3`, `Builtins.validate!/3`, `Builtins.seed/1`, `Builtins.schema/1`, `bool_type_value/1` (kernel), `bool_type_term/1`/`bool_case/5` (elab), `vbool/1`/`as_bool/1` (eval), `bool_atom/1`/`bool_atom_or_self/2`/`nat_family?/2` (emit) are used consistently across the tasks that define and consume them, and `bool_type_value/1`/`bool_type_term/1`/`vbool/1` are now pinned to closed-form definitions (Task 5) rather than three independently-discovered shapes.

**Remaining implementer-verification points:** two are narrow and non-soundness-critical — whether `merge_env/2`'s field-merge precedence (Task 4.5) needs adjustment for the `Std.Bool`/`Std.Nat` self-compile double-seed interaction called out in that task's implementer note; the exact meta-key path for `family_id` extraction in the register pass (Task 4, Step 7) if `Declarations.elaborate`'s container path doesn't already leave `meta[:name]` as an atom. One is **not** narrow and is explicitly flagged for human decision rather than silent resolution: Task 4.5's discovery that unconditionally seeding `:bool`/`:nat` creates a name-collision surface in the unqualified `env.families` map — a local `type Nat = Z | S(Nat)` may silently become an alias of the canonical family instead of staying distinct, contradicting the design spec's own "nominal, not structural" claim. This is called out with its own test-and-escalate step in Task 4.5 and should be resolved (or explicitly accepted) at the Task 12 human gate, not discovered later.

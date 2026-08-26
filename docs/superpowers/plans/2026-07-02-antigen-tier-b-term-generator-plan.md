# Antigen Tier B — Dependent Term Generator + Differential Assays Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a general well-typed dependent Core term generator `gen_term(Γ, T)` plus the three differential self-consistency assays it feeds (`infer_check_agreement`, `subject_reduction`, `normalization_stability`) and the health gate that makes a green run count as soundness evidence.

**Architecture:** A mode-directed generator inverts the kernel's bidirectional `infer`/`check` rules, discharging every semantic side-condition (index unification, conversion) through the kernel's own fuel-bounded conversion checker at choice time, with a canonical-inhabitant fallback that makes generation total. Terms are drawn against a fixed versioned signature menu (families + certified defs) and a dependent context Γ, packaged as a new `:typed_term` Challenge that plugs into Tier A's existing Runner/corpus/replay machinery unchanged. Three pure differential assays consume `:typed_term` and are wired into the Runner registry, `mix antigen`, and the static replayer.

**Tech Stack:** Elixir; the existing `Antigen.*` harness (`Gen`, `Challenge`, `Coverage`, `Corpus`, `Runner`, `Report`, `Backend.StreamData`); the Cure kernel (`Cure.Core.{Kernel, Normalise, Conv, Eval, Inductive, Env, Context, Serialize}`). ExUnit for tests. StreamData is the current backend, quarantined behind `Backend.StreamData`.

## Global Constraints

- **StreamData quarantine (locked decision #4):** no module under `Antigen.Generators.*` or `Antigen.Assays.*` may reference `StreamData`. Only `Antigen.Backend.StreamData` may. Enforced by `test/antigen/architecture_test.exs`.
- **Semantic conditions discharged by the kernel, never re-derived (locked decisions #3/#5):** all conversion/index checks in the generator go through `Conv.conv_within?/6` (fuel-bounded) or `Normalise.whnf/3`; all certification goes through `Kernel.validate_certificate/2` — never a raw `Env.certify/2` bypass.
- **Fixed committed fuel decides verdicts (locked decision #6):** `@gen_fuel 500` (generation-time conversion) lives in `Antigen.Generators.Term`; `@assay_fuel 500` lives in `Antigen.Assays.Term`; they are distinct constants. No wall-clock in any verdict path.
- **Two never-pruned generator-independent stores:** antibodies → `test/antigen/corpus.sexp`, coverage-deduped seeds → `test/antigen/seeds.sexp`; reach pins → `test/antigen/reach.sexp`. All via `Antigen.Corpus`.
- **Pure verdicts:** an assay returns `:ok` or `{:violation, detail}`; no open/xfail states. Every infection becomes an antibody, a reach pin, or a generator red-green fix (§7.4 triage).
- **`ctx` order (spec §4.1):** the `:typed_term` payload `ctx` list is in kernel order — index 0 is the innermost/most-recently-bound variable, matching `Cure.Core.Context`'s own `types` list. Rebuild a Context by folding `Enum.reverse(ctx)` (outermost first) through `Context.extend/2`.
- **Tier B generates only the positive direction:** every `:typed_term` challenge has `label: :well_typed`. Ill-typed mutation is deferred.
- **Signature menu is versioned:** v1 is fixed; corpus records name their `sig:` version. Growing the menu is a new version, never an edit to v1.
- **Commit discipline:** commit per task; author `Made In Heaven <madeinheaven@madeinheaven.com>`; never co-sign, no `Co-Authored-By`. Only one full build/test run at a time — never launch concurrent suites.
- **Tests are immutable once written (strict TDD, red→green→commit):** for every task, Step 1's test is written and confirmed red (Step 2) before any implementation code is written; Step 3 implements only enough to turn it green (Step 4); the test itself is never weakened, skipped, or deleted to reach green. The sole exception is a test later proven to encode the wrong behavior — that must be argued explicitly (what the correct behavior is and where the test diverges), not asserted as a shortcut to green. Tasks 7/8/10's specific "do NOT weaken the assay" / "NOT lowering the floor" instructions are instances of this general rule, not special cases of it.

---

## File Structure

**Create:**
- `lib/antigen/generators/sig_menu.ex` — `Antigen.Generators.SigMenu`: the v1 signature menu, `env_of/1`, goal-type list, `inhabitable?/2`, `canon/2`, `rebuild_context/2`.
- `lib/antigen/generators/context.ex` — `Antigen.Generators.Context`: the dependent-telescope Γ generator.
- `lib/antigen/generators/term.ex` — `Antigen.Generators.Term`: `gen_term/2` engine + `typed_term/1` challenge wrapper.
- `lib/antigen/assays/term.ex` — `Antigen.Assays.Term`: the three differential assays.
- Test files mirroring each (`test/antigen/generators/sig_menu_test.exs`, `.../context_test.exs`, `.../term_test.exs`, `test/antigen/assays/term_test.exs`, `test/antigen/typed_term_seed_test.exs`, `test/antigen/health_gate_test.exs`).

**Modify:**
- `lib/antigen/challenge.ex` — add `:typed_term` to `@type kind`, `to_pieces/1`, `from_pieces/7`, and `@known_atoms`.
- `lib/antigen/coverage.ex` — add a `terms_of/1` clause for `:typed_term`.
- `lib/antigen/runner.ex` — add three assay-registry entries; compute binder-usage / reduction-activity / fuel-exhausted metrics; add health floors as module attributes; stamp `:healthy`/`:vacuous`.
- `lib/mix/tasks/antigen.ex` — extend `default_gen/0` with the three new branches.
- `test/antigen/mix_task_test.exs` — add a red test proving Tier B is actually drawn by the wired-in `default_gen/0` (Task 10).
- `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md` — update rows #22 / A8 / A10.

**Verify, not modify:** `test/antigen/architecture_test.exs` already glob-enforces StreamData-freedom over `lib/antigen/{generators,assays}/**/*.ex` (confirmed against source — see Task 9), which by construction of the paths above already covers every module this plan creates; no edit to that file is needed.

---

## Reference: verified kernel & harness interfaces

These are the exact signatures the tasks below rely on (verified against the tree at authoring time). Do not guess variants.

**`Cure.Core.Env`** (defined in `lib/cure/core/inductive.ex`): `empty/0`, `add_def(env, name, type_term, body_term)`, `add_def/5`, `get_def(env, name)`, `certify(env, name)`, `certified?(env, name)`. **Not** on `Env`, despite living in the same source file: `get_family/2`, `get_ctor/2`, `ctor_family/2`, `arg_telescope/2`, `ctor_result_indices/2`, `index_telescope/2`, `ctors_of/2` — those are all `Cure.Core.Inductive` functions (see below). `inductive.ex` defines two separate modules; do not call `Env.get_family/2` etc. — it does not exist and will raise `UndefinedFunctionError`.

**`Cure.Core.Inductive`** (also defined in `lib/cure/core/inductive.ex`): `family(name, param_tele, index_tele, level)`, `ctor(name, arg_tele, result_indices)` / `ctor/4` / `ctor/5`, `declare(env, family, ctors)`, `get_family(env, name)`, `get_ctor(env, name)`, `ctor_family(env, cname)`, `arg_telescope(env, cname)`, `ctor_result_indices(env, cname)`, `index_telescope(env, fname)`, `ctors_of(env, fname)`. A telescope is a list of `{atom_name, type_term}`.

**`Cure.Core.Context`**: `empty/0`, `empty(env)`, `signature(ctx)`, `extend(ctx, type_value)`, `lookup(ctx, k)`, `length(ctx)`, `env(ctx)` (→ `[Value.t()]`, index 0 = highest de Bruijn level).

**`Cure.Core.Kernel`**: `infer(ctx, term) :: {:ok, Value.t()} | {:error, term()}`; `check(ctx, term, value) :: :ok | {:error, term()}`; `check_def(env, name) :: :ok | {:error, term()}`; `validate_certificate(env, name) :: {:ok, Env.t()} | {:error, term()}`; `normalize(ctx, term) :: Term.t() | :fuel_exhausted`.

**`Cure.Core.Normalise`**: `whnf(ctx, term, opts \\ []) :: Term.t() | :fuel_exhausted`; `nf(ctx, term, opts \\ []) :: Term.t() | :fuel_exhausted`; `quote(value, depth, opts \\ []) :: Term.t()`; `with_fuel(fuel, fun)`.

**`Cure.Core.Conv`**: `conv_within?(t1, t2, env, depth, sig, fuel) :: {:ok, boolean()} | :fuel_exhausted` (Term-level, fuel-bounded); `conv?/5`; `conv_values?(v1, v2, depth, sig)`.

**`Cure.Core.Eval`**: `eval(term, value_env) :: Value.t()`; `apply(vfun, varg)`; `apply_closure/2`.

**`Antigen.Gen`**: `return/1`, `member_of/1`, `one_of/1`, `frequency([{weight, gen}])`, `bind/2`, `sized/1`, `resize/2`, `tag/2`, `int(lo, hi)`, `support/1`.

**`Antigen.Challenge`**: struct `[:kind, :assay, :label, :payload, :seed, :note]`, `@enforce_keys [:kind, :assay, :label, :payload]`; `new(keyword)`, `to_pieces/1`, `from_pieces/7`, `__known_atoms__/0`.

**`Antigen.Coverage`**: `key/1`, `key_string/1`, `terms_of/1`.

**`Antigen.Corpus`**: `encode_record/1,2`, `decode_record/1`, `append(path, challenge, dedup_key)`, `stream(path)`, `dedup_key(challenge, :seed | :antibody)`.

**`Antigen.Runner`**: `explore/1`, `generate/1`, `replay/2`, `replay_one/1`; private `assay_module/1` registry and `summarize/2`.

**Backend draw idiom** (from `Runner.draw/2`): `Antigen.Backend.StreamData.interp(gen) |> Enum.take(count)` — use this in tests to sample a `Gen` program.

---

### Task 1: SigMenu — the v1 signature, env, inhabitability, canonical inhabitants

**Files:**
- Create: `lib/antigen/generators/sig_menu.ex`
- Test: `test/antigen/generators/sig_menu_test.exs`

**Interfaces:**
- Consumes: `Cure.Core.{Env, Inductive, Kernel, Context, Eval, Normalise}`.
- Produces:
  - `env_of(:v1) :: Env.t()` — families `Nat`, `Bd`, `Vec` declared; defs `plus`, `dbl` added and certified via `Kernel.validate_certificate/2`.
  - `nat() / bd() / vec(index_term) :: Term.t()` — the goal-type constructors (`{:data, :Nat, [], []}`, etc.).
  - `goal_types() :: [Term.t()]` — the fixed closed goal-type seeds (`Nat`, `Bd`, `Vec(Z)`, `Vec(S(Z))`).
  - `inhabitable?(ctx :: Context.t(), goal :: Term.t()) :: boolean()`.
  - `canon(ctx :: Context.t(), goal :: Term.t()) :: Term.t()` — a size-0 well-typed inhabitant (precondition: `inhabitable?`).
  - `rebuild_context(env :: Env.t(), ctx_types :: [Term.t()]) :: Context.t()`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/generators/sig_menu_test.exs
defmodule Antigen.Generators.SigMenuTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Env, Inductive, Context, Kernel}

  test "env_of(:v1) certifies plus and dbl through the real certifier" do
    env = SigMenu.env_of(:v1)
    assert Env.certified?(env, :plus)
    assert Env.certified?(env, :dbl)
    # families present (get_family/2 is on Inductive, not Env — see Reference)
    assert Inductive.get_family(env, :Nat)
    assert Inductive.get_family(env, :Bd)
    assert Inductive.get_family(env, :Vec)
  end

  test "canon builds a well-typed inhabitant for each closed goal type" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for goal <- SigMenu.goal_types() do
      assert SigMenu.inhabitable?(ctx, goal)
      term = SigMenu.canon(ctx, goal)
      {:ok, ty} = Kernel.infer(ctx, term)
      # inferred value must convert with the goal at top level
      assert Kernel.check(ctx, term, ty) == :ok
    end
  end

  test "canon handles a stuck-indexed Vec via a matching context variable" do
    env = SigMenu.env_of(:v1)
    # Γ = [ n : Nat, xs : Vec(n) ]  (kernel order: xs innermost = index 0)
    ctx = SigMenu.rebuild_context(env, [SigMenu.vec({:var, 0}), SigMenu.nat()])
    goal = SigMenu.vec({:var, 1})       # Vec(n), n = index 1 from the body
    assert SigMenu.inhabitable?(ctx, goal)
    term = SigMenu.canon(ctx, goal)
    assert {:ok, _} = Kernel.infer(ctx, term)
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/antigen/generators/sig_menu_test.exs`
Expected: FAIL — `Antigen.Generators.SigMenu` is undefined.

- [ ] **Step 3: Write the implementation**

```elixir
# lib/antigen/generators/sig_menu.ex
defmodule Antigen.Generators.SigMenu do
  @moduledoc """
  The fixed, versioned Tier-B signature menu (spec §5). Families + certified
  defs the term generator draws goals and heads from, plus the totality
  scaffolding (`inhabitable?/2` + `canon/2`) that makes `gen_term` total.

  Certification runs the REAL procedure (`Kernel.validate_certificate/2`) — never
  a raw `Env.certify/2` bypass (locked decision #3/#5).
  """
  alias Cure.Core.{Env, Inductive, Kernel, Context, Eval}

  # -- goal-type constructors -------------------------------------------------
  def nat, do: {:data, :Nat, [], []}
  def bd, do: {:data, :Bd, [], []}
  def vec(index_term), do: {:data, :Vec, [], [index_term]}
  defp z, do: {:ctor, :Z, []}
  defp s(n), do: {:ctor, :S, [n]}

  @doc "The fixed closed goal-type seeds (all inhabitable in the empty context)."
  def goal_types, do: [nat(), bd(), vec(z()), vec(s(z()))]

  # -- the v1 environment -----------------------------------------------------
  @doc "Declare families, add plus/dbl, and certify them through the kernel."
  @spec env_of(:v1) :: Env.t()
  def env_of(:v1) do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Nat, [], [], 0),
        [Inductive.ctor(:Z, [], []), Inductive.ctor(:S, [{:n, nat()}], [])])
      |> Inductive.declare(Inductive.family(:Bd, [], [], 0),
        [Inductive.ctor(:T, [], []), Inductive.ctor(:F, [], [])])
      |> Inductive.declare(Inductive.family(:Vec, [], [{:n, nat()}], 0),
        [
          Inductive.ctor(:vnil, [], [z()]),
          # vcons : (n:Nat) -> Nat -> Vec(n) -> Vec(S(n))
          #   arg telescope [n, x, xs]; in xs's type Vec(n), n is index 1;
          #   in the result index S(n), n is index 2.
          Inductive.ctor(:vcons, [{:n, nat()}, {:x, nat()}, {:xs, vec({:var, 1})}], [s({:var, 2})])
        ])

    # plus m n = case m of Z -> n | S(k) -> S(plus(k, n))   (structural on arg 1)
    plus_type = {:pi, nat(), {:pi, nat(), nat()}}
    plus_body =
      {:lam, nat(), {:lam, nat(),
        {:case, {:var, 1}, {:lam, nat(), nat()},
         [{:Z, 0, {:var, 0}},
          {:S, 1, s({:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 1}})}]}}}

    # dbl m = plus m m
    dbl_type = {:pi, nat(), nat()}
    dbl_body = {:lam, nat(), {:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 0}}}

    env = Env.add_def(env, :plus, plus_type, plus_body)
    {:ok, env} = Kernel.validate_certificate(env, :plus)
    env = Env.add_def(env, :dbl, dbl_type, dbl_body)
    {:ok, env} = Kernel.validate_certificate(env, :dbl)
    env
  end

  # -- context rebuild (spec §4.1) --------------------------------------------
  @doc "Rebuild a Context from a kernel-order ctx list (index 0 = innermost)."
  @spec rebuild_context(Env.t(), [Cure.Core.Term.t()]) :: Context.t()
  def rebuild_context(env, ctx_types) do
    Enum.reduce(Enum.reverse(ctx_types), Context.empty(env), fn ty_term, ctx ->
      Context.extend(ctx, Eval.eval(ty_term, Context.env(ctx)))
    end)
  end

  # -- inhabitability + canonical inhabitants (spec §6.4) ---------------------
  @spec inhabitable?(Context.t(), Cure.Core.Term.t()) :: boolean()
  def inhabitable?(ctx, goal) do
    case whnf(ctx, goal) do
      {:data, :Nat, _, _} -> true
      {:data, :Bd, _, _} -> true
      {:type, _} -> true
      {:pi, dom, cod} -> inhabitable?(Context.extend(ctx, Eval.eval(dom, Context.env(ctx))), cod)
      {:sigma, a, b} ->
        inhabitable?(ctx, a) and
          inhabitable?(Context.extend(ctx, Eval.eval(a, Context.env(ctx))), b)
      {:data, :Vec, _, [i]} ->
        closed_numeral?(whnf(ctx, i)) or has_var_of_type?(ctx, {:data, :Vec, [], [i]})
      _ -> false
    end
  end

  @spec canon(Context.t(), Cure.Core.Term.t()) :: Cure.Core.Term.t()
  def canon(ctx, goal) do
    case whnf(ctx, goal) do
      {:data, :Nat, _, _} -> z()
      {:data, :Bd, _, _} -> {:ctor, :T, []}
      {:type, _} -> nat()
      {:pi, dom, cod} ->
        {:lam, dom, canon(Context.extend(ctx, Eval.eval(dom, Context.env(ctx))), cod)}
      {:sigma, a, b} ->
        av = canon(ctx, a)
        {:pair, av, canon(ctx, subst0(b, av, ctx))}
      {:data, :Vec, _, [i]} = vgoal ->
        case whnf(ctx, i) do
          {:ctor, :Z, []} -> {:ctor, :vnil, []}
          {:ctor, :S, [j]} -> {:ctor, :vcons, [j, z(), canon(ctx, vec(j))]}
          _ -> var_of_type(ctx, vgoal)   # stuck index: a Γ-var by the invariant
        end
    end
  end

  # -- helpers ----------------------------------------------------------------
  # Deliberately unbounded (unlike Generators.Term's own `whnf/2`, which spec
  # §6.3 requires to run under @gen_fuel): this helper backs the totality
  # FALLBACK (`inhabitable?`/`canon`), not a generator choice being accepted
  # or rejected against a goal — it is not one of the "semantic conditions"
  # locked decision #3 scopes. `canon/2`'s job is to always terminate with an
  # answer given v1's finite, closed menu, and threading a fuel budget through
  # here would change `inhabitable?/2`/`canon/2`'s public 2-arity (used
  # throughout Tasks 1/3/4/6/7/8/9) for no v1 behavioral benefit.
  defp whnf(ctx, term) do
    case Cure.Core.Normalise.whnf(ctx, term) do
      :fuel_exhausted -> term
      w -> w
    end
  end

  defp closed_numeral?({:ctor, :Z, []}), do: true
  defp closed_numeral?({:ctor, :S, [n]}), do: closed_numeral?(n)
  defp closed_numeral?(_), do: false

  # Does Γ hold a variable whose type converts with `goal`?
  defp has_var_of_type?(ctx, goal), do: var_of_type(ctx, goal) != nil

  defp var_of_type(ctx, goal) do
    env = Context.env(ctx)
    depth = Context.length(ctx)
    sig = Context.signature(ctx)

    Enum.find_value(0..(depth - 1)//1, fn k ->
      ty_val = Context.lookup(ctx, k)
      ty_term = Cure.Core.Normalise.quote(ty_val, depth)

      case Cure.Core.Conv.conv_within?(ty_term, goal, env, depth, sig, 500) do
        {:ok, true} -> {:var, k}
        _ -> nil
      end
    end)
  end

  # β-substitute `arg`'s value for the Sigma's own bound variable (de Bruijn 0)
  # into `b`. `b` is written one binder deeper than `ctx` (the `:sigma` binding
  # convention: `{:sigma, a, b}` binds in `b`, matching `Kernel.infer`'s
  # `ctx2 = Context.extend(ctx, a_value)` before checking `b`) — but the
  # component actually placed in `{:pair, av, ...}` must be a term in the
  # UNEXTENDED `ctx` (`Kernel.check`'s `:pair` clause checks its second
  # component in the original `ctx`, against `cod_closure` applied to
  # `a_value` — never in an extended context). A raw `Term.subst/3` is not
  # enough: it replaces only index 0 and leaves every OTHER free index in `b`
  # unchanged, so a reference to an outer `ctx` variable would stay off-by-one.
  # Evaluating `b` under `[arg_value | env]` and quoting back (the same
  # technique `subst_cod` in Task 4 uses) performs the substitution and the
  # necessary renumbering in one step.
  @spec subst0(Cure.Core.Term.t(), Cure.Core.Term.t(), Context.t()) :: Cure.Core.Term.t()
  def subst0(b, arg, ctx) do
    env = Context.env(ctx)
    arg_value = Eval.eval(arg, env)
    Cure.Core.Normalise.quote(Eval.eval(b, [arg_value | env]), Context.length(ctx))
  end
end
```

Note on `subst0/3`: `{:sigma, ...}` never actually appears as a goal in v1 — `SigMenu.goal_types/0` has no Sigma entry, `Generators.Context.entry_type/2` (Task 2) never offers one as a context-entry type, and `Term.intro_rules`'s `Type 0` clause (Task 3) never offers a Sigma type-former — so `canon`'s and `intro_rules`'s Sigma clauses are unreachable under the v1 menu (no code path ever calls `gen_term`/`canon` with an actual `{:sigma, _, _}` goal). `subst0/3` is still implemented as a real eval/quote substitution rather than an identity no-op: an identity subst would be wrong even for a "non-dependent" `b` (one that doesn't mention the Sigma's own bound variable) whenever `b` references some OTHER outer `ctx` variable — only a fully closed `b` makes identity correct. This also matches the spec's own canonical-inhabitant formula `canon(B[canon(A)])` (§6.4), which is a genuine substitution, not a context-extension trick. Getting this right now, while unreachable, avoids banking a latent bug for the day a later signature-menu version adds a Sigma goal — the test matrix in Step 1 exercises only non-Sigma goals, matching what v1 actually reaches.

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/antigen/generators/sig_menu_test.exs`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/generators/sig_menu.ex test/antigen/generators/sig_menu_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): Tier-B v1 signature menu + inhabitability + canonical inhabitants"
```

---

### Task 2: Context generator — dependent telescopes Γ

**Files:**
- Create: `lib/antigen/generators/context.ex`
- Test: `test/antigen/generators/context_test.exs`

**Interfaces:**
- Consumes: `SigMenu.{env_of, nat, bd, vec, rebuild_context}`; `Antigen.Gen`; `Cure.Core.{Context, Kernel}`.
- Produces: `gen(env :: Env.t()) :: Gen.t()` — a `Gen` of `ctx_types :: [Term.t()]` in kernel order (index 0 innermost), each entry well-typed in the context of the entries after it (outer to it). Because a later (inner) entry may reference an earlier (outer) one, the list is a genuine dependent telescope.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/generators/context_test.exs
defmodule Antigen.Generators.ContextTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.SigMenu
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.Kernel

  test "every generated telescope is well-formed (each entry checks in its outer prefix)" do
    env = SigMenu.env_of(:v1)
    samples = B.interp(Antigen.Generators.Context.gen(env)) |> Enum.take(50)

    for ctx_types <- samples do
      # Walk outermost-first; each entry's type must be a valid Type in its prefix.
      Enum.reduce(Enum.reverse(ctx_types), Cure.Core.Context.empty(env), fn ty, prefix ->
        assert {:ok, _sort} = Kernel.infer(prefix, ty)
        Cure.Core.Context.extend(prefix, Cure.Core.Eval.eval(ty, Cure.Core.Context.env(prefix)))
      end)
    end
  end

  test "at least some samples exercise a dependent entry (Vec(n) after an n : Nat)" do
    env = SigMenu.env_of(:v1)
    samples = B.interp(Antigen.Generators.Context.gen(env)) |> Enum.take(200)
    assert Enum.any?(samples, fn ctx -> Enum.any?(ctx, &match?({:data, :Vec, _, _}, &1)) end)
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/antigen/generators/context_test.exs`
Expected: FAIL — `Antigen.Generators.Context` undefined.

- [ ] **Step 3: Write the implementation**

```elixir
# lib/antigen/generators/context.ex
defmodule Antigen.Generators.Context do
  @moduledoc """
  Generates Γ as a genuinely dependent telescope (spec §5.1): a size-bounded
  number of entries, each entry's TYPE generated in the context of the entries
  outer to it, so an inner entry may depend on an outer one (e.g. `Vec(n)` after
  `n : Nat`). Deliberately repeats type shapes at nearby positions so de Bruijn
  arithmetic is exercised. Returns a kernel-order list (index 0 = innermost).
  """
  alias Antigen.Gen
  alias Antigen.Generators.SigMenu

  @spec gen(Cure.Core.Env.t()) :: Gen.t()
  def gen(env) do
    Gen.sized(fn size ->
      count = min(size, 4)
      build(env, [], count)
    end)
  end

  # Accumulate entries innermost-LAST; we prepend each new inner entry so the
  # returned list is kernel-order (index 0 innermost). `outer` is the telescope
  # built so far in kernel order.
  defp build(_env, acc, 0), do: Gen.return(acc)

  defp build(env, acc, n) do
    Gen.bind(entry_type(env, acc), fn ty ->
      build(env, [ty | acc], n - 1)
    end)
  end

  # A type valid in the current prefix (= the acc telescope). Depends on what is
  # already in scope: `Vec(n)` is only offered when some `n : Nat` variable
  # exists in acc. `Nat`/`Bd` are always available (and repeated to force
  # shadowing / nearby de Bruijn reuse).
  defp entry_type(_env, acc) do
    nat_vars = nat_var_indices(acc)

    vec_choices =
      for k <- nat_vars, do: {2, Gen.return(SigMenu.vec({:var, k}))}

    Gen.frequency([
      {3, Gen.return(SigMenu.nat())},
      {2, Gen.return(SigMenu.bd())},
      {1, Gen.return(SigMenu.vec({:ctor, :Z, []}))}
      | vec_choices
    ])
  end

  # Indices (into the FUTURE context, i.e. counting from the body that will sit
  # under the whole telescope) of acc entries whose type is exactly Nat. `acc` is
  # kernel-order with the innermost bound entry at the head; an entry at position
  # `i` in `acc` (0 = head/innermost-so-far) sits at de Bruijn index `i` relative
  # to a new entry prepended in front of it.
  defp nat_var_indices(acc) do
    acc
    |> Enum.with_index()
    |> Enum.filter(fn {ty, _i} -> match?({:data, :Nat, [], []}, ty) end)
    |> Enum.map(fn {_ty, i} -> i end)
  end
end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/antigen/generators/context_test.exs`
Expected: PASS (2 tests). If the "dependent entry" test flakes at count 200, raise the sample count — the `vec_choices` weighting guarantees Vec entries appear once a Nat var exists.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/generators/context.ex test/antigen/generators/context_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): Tier-B dependent context (telescope) generator"
```

---

### Task 3: `gen_term/2` — skeleton (intros + canonical fallback)

**Files:**
- Create: `lib/antigen/generators/term.ex` (skeleton; eliminations added in Task 4)
- Test: `test/antigen/generators/term_test.exs`

**Interfaces:**
- Consumes: `SigMenu.{env_of, canon, inhabitable?, rebuild_context, nat, bd, vec}`; `Antigen.Gen`; `Cure.Core.{Context, Kernel, Normalise, Eval, Conv}`.
- Produces: `gen_term(ctx :: Context.t(), goal :: Term.t()) :: Gen.t()` returning a Core term `t` with claimed `ctx ⊢ t : goal`. `@gen_fuel 500`.

This task implements ONLY the check-mode introduction rules (`lam`, `pair`, constructor, `Type 0` former) plus the canonical fallback. Infer-mode eliminations (var/INDIR/app/case/fst/snd) land in Task 4. After this task the generator is already total and sound over the intro fragment.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/generators/term_test.exs
defmodule Antigen.Generators.TermTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Term, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel}

  @doc false
  def sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "every intro-fragment term checks at its goal (soundness over the fragment)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for goal <- SigMenu.goal_types() do
      for t <- sample(Term.gen_term(ctx, goal), 40) do
        {:ok, ty} = Kernel.infer(ctx, t)
        assert Kernel.check(ctx, t, ty) == :ok
      end
    end
  end

  test "a Pi goal yields a lambda" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    goal = {:pi, SigMenu.nat(), SigMenu.nat()}
    ts = sample(Term.gen_term(ctx, goal), 40)
    assert Enum.any?(ts, &match?({:lam, _, _}, &1))
    for t <- ts, do: assert {:ok, _} = Kernel.infer(ctx, t)
  end

  test "a Type 0 goal yields a menu type former (the {:type,_} intro row)" do
    # `{:type, 0}` is never drawn as a goal by `Term.typed_term/1`'s `goal_gen`
    # (Task 6) or by `Generators.Context` (Task 2) — see the goal-space note
    # after Task 6 — so this is the ONLY place the `{:type,_}` clause of
    # `intro_rules` (and its var/INDIR-only elimination companions) gets
    # exercised at all. Without this test the clause would ship with zero
    # coverage.
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    goal = {:type, 0}
    ts = sample(Term.gen_term(ctx, goal), 40)
    assert Enum.all?(ts, &(&1 in [SigMenu.nat(), SigMenu.bd(), SigMenu.vec({:ctor, :Z, []})]))
    for t <- ts, do: assert {:ok, _} = Kernel.infer(ctx, t)
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/antigen/generators/term_test.exs`
Expected: FAIL — `Antigen.Generators.Term` undefined.

- [ ] **Step 3: Write the implementation**

```elixir
# lib/antigen/generators/term.ex
defmodule Antigen.Generators.Term do
  @moduledoc """
  The dependent Core term generator (spec §6). Mode-directed inversion of the
  kernel's bidirectional rules; every semantic side-condition is discharged by
  the kernel's own fuel-bounded conversion (`@gen_fuel`). A canonical-inhabitant
  fallback (`SigMenu.canon/2`) makes generation total — at size 0 or an empty
  option set the generator emits the canonical term (spec §6.4).
  """
  alias Antigen.Gen
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Context, Eval, Normalise}

  @gen_fuel 500
  def gen_fuel, do: @gen_fuel

  @spec gen_term(Context.t(), Cure.Core.Term.t()) :: Gen.t()
  def gen_term(ctx, goal), do: Gen.sized(fn size -> gen(ctx, goal, size) end)

  # size 0 → canonical inhabitant (total, no search).
  defp gen(ctx, goal, 0), do: Gen.return(SigMenu.canon(ctx, goal))

  defp gen(ctx, goal, size) do
    wgoal = whnf(ctx, goal)
    rules = intro_rules(ctx, goal, wgoal, size)

    case rules do
      [] -> Gen.return(SigMenu.canon(ctx, goal))
      rs -> Gen.frequency([{1, Gen.return(SigMenu.canon(ctx, goal))} | rs])
    end
  end

  # -- check-mode introductions ----------------------------------------------
  defp intro_rules(ctx, _goal, {:pi, dom, cod}, size) do
    body_ctx = Context.extend(ctx, Eval.eval(dom, Context.env(ctx)))
    [{3, Gen.bind(gen(body_ctx, cod, size - 1), fn b -> Gen.return({:lam, dom, b}) end)}]
  end

  defp intro_rules(ctx, _goal, {:sigma, a, b}, size) do
    [{3,
      Gen.bind(gen(ctx, a, size - 1), fn av ->
        # `b` is written one binder deeper than `ctx` (sigma binds in `b`); the
        # component that ends up inside `{:pair, av, bv}` must be a term in the
        # UNEXTENDED `ctx` (`Kernel.check`'s `:pair` clause checks it there) —
        # so β-substitute `av` for `b`'s own bound variable via `SigMenu.subst0/3`
        # (same reasoning as `SigMenu.canon`'s Sigma clause, Task 1) before
        # recursing. Unreachable in v1 (see Task 1's note) but must stay correct.
        Gen.bind(gen(ctx, SigMenu.subst0(b, av, ctx), size - 1), fn bv ->
          Gen.return({:pair, av, bv})
        end)
      end)}]
  end

  defp intro_rules(ctx, _goal, {:data, :Vec, _, [i]}, size) do
    ctor_rules_for_vec(ctx, i, size)
  end

  defp intro_rules(_ctx, _goal, {:data, :Nat, _, _}, size) do
    [
      {2, Gen.return({:ctor, :Z, []})},
      {2, Gen.bind(gen_nat(size - 1), fn n -> Gen.return(n) end)}
    ]
  end

  defp intro_rules(_ctx, _goal, {:data, :Bd, _, _}, _size) do
    [{2, Gen.member_of([{:ctor, :T, []}, {:ctor, :F, []}])}]
  end

  defp intro_rules(_ctx, _goal, {:type, _}, _size) do
    [{2, Gen.member_of([SigMenu.nat(), SigMenu.bd(), SigMenu.vec({:ctor, :Z, []})])}]
  end

  defp intro_rules(_ctx, _goal, _other, _size), do: []

  # Constructor choice under indices (spec §6.3): vnil iff i≡Z, vcons iff i≡S(j).
  defp ctor_rules_for_vec(ctx, i, size) do
    case whnf(ctx, i) do
      {:ctor, :Z, []} ->
        [{2, Gen.return({:ctor, :vnil, []})}]

      {:ctor, :S, [j]} ->
        if SigMenu.inhabitable?(ctx, SigMenu.vec(j)) do
          [{2,
            Gen.bind(gen(ctx, SigMenu.nat(), size - 1), fn x ->
              Gen.bind(gen(ctx, SigMenu.vec(j), size - 1), fn tail ->
                Gen.return({:ctor, :vcons, [j, x, tail]})
              end)
            end)}]
        else
          []
        end

      _stuck ->
        []   # stuck index: only eliminations apply (Task 4); intros offer nothing
    end
  end

  # A small closed Nat generator (numerals), for variety at Nat goals.
  defp gen_nat(0), do: Gen.return({:ctor, :Z, []})
  defp gen_nat(size) do
    Gen.frequency([
      {2, Gen.return({:ctor, :Z, []})},
      {2, Gen.bind(gen_nat(size - 1), fn n -> Gen.return({:ctor, :S, [n]}) end)}
    ])
  end

  # whnf that degrades to the input term on fuel exhaustion (never crashes gen).
  # Bounded by @gen_fuel, not the default :infinity — spec §6.3: the shape/
  # index inspections this backs ("is the goal a Pi/data/Vec(S j)?") are
  # semantic conditions and must run under the same @gen_fuel-bounded kernel
  # calls as the acceptance rule, "not a separate unbounded check".
  defp whnf(ctx, term) do
    case Normalise.whnf(ctx, term, fuel: @gen_fuel) do
      :fuel_exhausted -> term
      w -> w
    end
  end
end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/antigen/generators/term_test.exs`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/generators/term.ex test/antigen/generators/term_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): gen_term intro fragment + canonical fallback (total, sound)"
```

---

### Task 4: `gen_term/2` — eliminations (var, INDIR, plain app, case, fst/snd)

**Files:**
- Modify: `lib/antigen/generators/term.ex`
- Test: `test/antigen/generators/term_test.exs` (add cases)

**Interfaces:**
- Consumes: everything from Task 3 plus `Cure.Core.{Kernel, Conv, Normalise}`, `Env.get_def/2`, and (if needed) `Inductive.arg_telescope/2` — note `arg_telescope/2` is on `Inductive`, not `Env`, despite both living in `inductive.ex` (see Reference).
- Produces: extends `gen/3` with an `elim_rules/4` branch merged into every goal's rule set. Adds `@gen_fuel`-bounded acceptance via `accept_infer?/4`. No signature change to `gen_term/2`.

- [ ] **Step 1: Write the failing test (add to term_test.exs)**

```elixir
  test "generated terms exercise eliminations and firing redexes" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    ts = for goal <- SigMenu.goal_types(),
             t <- sample(Term.gen_term(ctx, goal), 80), do: t

    # every term still checks (soundness across the full rule set)
    for t <- ts do
      {:ok, ty} = Kernel.infer(ctx, t)
      assert Kernel.check(ctx, t, ty) == :ok
    end

    # at least some terms contain an elimination and some fire a redex
    assert Enum.any?(ts, &contains_tag?(&1, :app))
    assert Enum.any?(ts, &contains_tag?(&1, :case))
    assert Enum.any?(ts, fn t -> Kernel.normalize(ctx, t) != t end)
  end

  test "a stuck-indexed Vec goal is satisfied from the context (elimination path)" do
    env = SigMenu.env_of(:v1)
    ctx = SigMenu.rebuild_context(env, [SigMenu.vec({:var, 0}), SigMenu.nat()])
    goal = SigMenu.vec({:var, 1})
    for t <- sample(Term.gen_term(ctx, goal), 40) do
      assert {:ok, _} = Kernel.infer(ctx, t)
    end
  end

  defp contains_tag?(t, tag) when is_tuple(t) do
    (elem(t, 0) == tag) or (t |> Tuple.to_list() |> tl() |> Enum.any?(&contains_tag?(&1, tag)))
  end
  defp contains_tag?(l, tag) when is_list(l), do: Enum.any?(l, &contains_tag?(&1, tag))
  defp contains_tag?(_, _), do: false
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/antigen/generators/term_test.exs`
Expected: FAIL — the new `:app`/`:case`/redex assertions fail (only intros exist so far), and the stuck-Vec goal falls back to `canon` only (still passes infer, but the elimination-coverage assertions in the first new test fail).

- [ ] **Step 3: Write the implementation (extend term.ex)**

Add `elim_rules/4` to the rule set and the acceptance helper. Replace the `gen/3` non-zero clause to merge eliminations:

```elixir
  defp gen(ctx, goal, size) do
    wgoal = whnf(ctx, goal)
    rules = intro_rules(ctx, goal, wgoal, size) ++ elim_rules(ctx, goal, size)

    case rules do
      [] -> Gen.return(SigMenu.canon(ctx, goal))
      rs -> Gen.frequency([{1, Gen.return(SigMenu.canon(ctx, goal))} | rs])
    end
  end
```

Add:

```elixir
  # -- infer-mode eliminations (available at every goal) ----------------------
  # Each elimination builds a term whose inferred type must convert with `goal`
  # under @gen_fuel; candidates that don't converge are simply not offered.
  defp elim_rules(ctx, goal, size) do
    var_rules(ctx, goal) ++
      indir_rules(ctx, goal, size) ++
      app_rule(ctx, goal, size) ++
      case_rule(ctx, goal, size) ++
      proj_rules(ctx, goal)
  end

  # Context variables whose type converts with the goal.
  defp var_rules(ctx, goal) do
    depth = Context.length(ctx)

    for k <- (if depth == 0, do: [], else: Enum.to_list(0..(depth - 1))),
        accept_infer?(ctx, {:var, k}, goal) do
      {3, Gen.return({:var, k})}
    end
  end

  # INDIR: saturate a certified-def head into the goal. v1 heads: plus/2, dbl/1.
  # We generate all arguments at their (dependent) domain types, then accept iff
  # the saturated application's inferred type converges with the goal.
  defp indir_rules(ctx, goal, size) do
    Enum.flat_map([:plus, :dbl], fn head ->
      saturate(ctx, {:global, head}, def_type(ctx, head), goal, size)
    end)
  end

  # Plain application (manufactures β-redexes INDIR cannot): apply a freshly
  # generated lambda. Only offered at Nat/Bd goals in v1 (non-dependent codomain).
  defp app_rule(ctx, goal, size) when size > 1 do
    case whnf(ctx, goal) do
      {:data, fam, _, _} when fam in [:Nat, :Bd] ->
        dom = SigMenu.nat()
        body_ctx = Context.extend(ctx, Eval.eval(dom, Context.env(ctx)))
        [{2,
          Gen.bind(gen(body_ctx, shift_goal(goal), size - 1), fn body ->
            Gen.bind(gen(ctx, dom, size - 1), fn arg ->
              Gen.return({:app, {:lam, dom, body}, arg})
            end)
          end)}]
      _ -> []
    end
  end
  defp app_rule(_ctx, _goal, _size), do: []

  # case on a menu family scrutinee (Nat or Bd), constant motive λ_. goal.
  # Gated on the goal's (whnf'd) shape, mirroring `app_rule`: spec §6.1's
  # `Type 0` row is deliberately narrower than the full elimination menu
  # (var/INDIR only) — WITHOUT this guard, `case` would still typecheck at a
  # `{:type, _}` goal (a case whose branches are themselves menu type-formers
  # is a perfectly well-typed universe-valued case expression: e.g.
  # `case n of Z -> Nat | S _ -> Bd : Type 0`), so leaving it ungated is sound
  # but silently broadens the generator past what the rule table documents —
  # and would make any test asserting the `{:type,_}` row's candidate set
  # (see Task 3's Type-0-goal test) unreliable.
  defp case_rule(ctx, goal, size) when size > 1 do
    case whnf(ctx, goal) do
      {:type, _} ->
        []

      _ ->
        Enum.flat_map([{:Nat, [:Z, :S]}, {:Bd, [:T, :F]}], fn {fam, _ctors} ->
          scrut_ty = {:data, fam, [], []}
          motive = {:lam, scrut_ty, shift_goal(goal)}
          [{2,
            Gen.bind(gen(ctx, scrut_ty, size - 1), fn scrut ->
              Gen.bind(branches(ctx, fam, goal, size - 1), fn brs ->
                Gen.return({:case, scrut, motive, brs})
              end)
            end)}]
        end)
    end
  end
  defp case_rule(_ctx, _goal, _size), do: []

  # fst/snd of a Γ-variable of Sigma type whose relevant component meets the goal.
  defp proj_rules(ctx, goal) do
    depth = Context.length(ctx)

    Enum.flat_map((if depth == 0, do: [], else: Enum.to_list(0..(depth - 1))), fn k ->
      case whnf(ctx, Normalise.quote(Context.lookup(ctx, k), depth)) do
        {:sigma, _a, _b} ->
          fst_r = if accept_infer?(ctx, {:fst, {:var, k}}, goal), do: [{2, Gen.return({:fst, {:var, k}})}], else: []
          snd_r = if accept_infer?(ctx, {:snd, {:var, k}}, goal), do: [{2, Gen.return({:snd, {:var, k}})}], else: []
          fst_r ++ snd_r
        _ -> []
      end
    end)
  end

  # Saturate `head : head_ty` (a Π-telescope) with generated args, accepting only
  # if the result's inferred type converges with `goal`. Args are generated at
  # each domain with earlier args substituted (via the closure env) into later
  # domains — the dependent-generation core (spec §6.2).
  defp saturate(ctx, head_term, head_ty, goal, size) do
    args_gen = gen_args(ctx, head_ty, size, [])

    [{2,
      Gen.bind(args_gen, fn args ->
        term = Enum.reduce(args, head_term, fn a, acc -> {:app, acc, a} end)
        if accept_infer?(ctx, term, goal), do: Gen.return(term), else: Gen.return(SigMenu.canon(ctx, goal))
      end)}]
  end

  # Walk a Π-telescope, generating each domain argument.
  defp gen_args(_ctx, {:pi, _dom, _cod} = _ty, _size, _acc) when false, do: nil
  defp gen_args(ctx, ty, size, acc) do
    case whnf(ctx, ty) do
      {:pi, dom, cod} ->
        Gen.bind(gen(ctx, dom, max(size - 1, 1)), fn a ->
          # substitute `a` into `cod` by evaluating cod's closure with a's value
          cod_ctx_ty = subst_cod(cod, a, ctx)
          gen_args(ctx, cod_ctx_ty, size, [a | acc])
        end)
      _ -> Gen.return(Enum.reverse(acc))
    end
  end

  # cod is a Term with de Bruijn 0 = the just-bound arg; substitute `a` for it.
  defp subst_cod(cod, a, ctx) do
    env = Context.env(ctx)
    Normalise.quote(Eval.eval(cod, [Eval.eval(a, env) | env]), Context.length(ctx))
  end

  # Branch bodies for a `case` on `fam` at (constant-motive) goal.
  defp branches(ctx, :Nat, goal, size) do
    Gen.bind(gen(ctx, goal, size), fn zbody ->
      kctx = Context.extend(ctx, Eval.eval(SigMenu.nat(), Context.env(ctx)))
      Gen.bind(gen(kctx, shift_goal(goal), size), fn sbody ->
        Gen.return([{:Z, 0, zbody}, {:S, 1, sbody}])
      end)
    end)
  end

  defp branches(ctx, :Bd, goal, size) do
    Gen.bind(gen(ctx, goal, size), fn tb ->
      Gen.bind(gen(ctx, goal, size), fn fb ->
        Gen.return([{:T, 0, tb}, {:F, 0, fb}])
      end)
    end)
  end

  # Accept an infer-mode candidate iff its inferred type converts with the goal
  # under @gen_fuel (spec §6.1). Fuel exhaustion or false ⇒ not offered.
  defp accept_infer?(ctx, term, goal) do
    case Cure.Core.Kernel.infer(ctx, term) do
      {:ok, inferred_val} ->
        depth = Context.length(ctx)
        inferred_term = Normalise.quote(inferred_val, depth)

        case Cure.Core.Conv.conv_within?(inferred_term, goal, Context.env(ctx), depth,
               Context.signature(ctx), @gen_fuel) do
          {:ok, true} -> true
          _ -> false
        end

      {:error, _} -> false
    end
  end

  defp def_type(ctx, name) do
    %{type: ty} = Cure.Core.Env.get_def(Context.signature(ctx), name)
    ty
  end

  # A goal moved under one extra binder (its free de Bruijn indices shift by 1).
  defp shift_goal(goal), do: Cure.Core.Term.shift(goal, 1, 0)
```

Notes for the implementer:
- `Cure.Core.Term.shift/3` is confirmed against `lib/cure/core/term.ex`: `shift(term, amount, cutoff \\ 0)`, lifting every free de Bruijn index ≥ `cutoff` by `amount`. `Cure.Core.Term.shift(goal, 1, 0)` is therefore exactly the right call for "shift every free index in `goal` by 1" (moving it under one new binder, cutoff 0) — no adjustment needed, no `shift/2` to prefer.
- `saturate/5` uses `SigMenu.canon/2` as the fallback when the saturated application does not converge with the goal — this keeps every offered branch well-typed rather than emitting an ill-typed application. The canonical fallback is already trusted from Task 1.
- The `accept_infer?` gate is what keeps the elimination rules sound: nothing is offered whose inferred type the kernel cannot reconcile with the goal within fuel.

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/antigen/generators/term_test.exs`
Expected: PASS (5 tests). The redex/elimination-coverage assertions now hold.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/generators/term.ex test/antigen/generators/term_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): gen_term eliminations — var/INDIR/app/case/proj, fuel-gated"
```

---

### Task 5: `:typed_term` Challenge kind — serialization + coverage

**Files:**
- Modify: `lib/antigen/challenge.ex`
- Modify: `lib/antigen/coverage.ex`
- Test: `test/antigen/typed_term_seed_test.exs`

**Interfaces:**
- Consumes: `Cure.Core.Term` pieces.
- Produces: `Challenge` with `kind: :typed_term`, `payload: %{sig: :v1, ctx: [Term], type: Term, term: Term}`, `label: :well_typed`. Round-trips through `Corpus.encode_record/decode_record`. `Coverage.terms_of/1` returns `[type, term | ctx]`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/typed_term_seed_test.exs
defmodule Antigen.TypedTermSeedTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus, Coverage}
  alias Antigen.Generators.SigMenu

  defp sample_challenge do
    Challenge.new(
      kind: :typed_term,
      assay: "term/infer_check",
      label: :well_typed,
      payload: %{sig: :v1, ctx: [SigMenu.nat()], type: SigMenu.nat(), term: {:var, 0}}
    )
  end

  test "to_pieces / from_pieces round-trip preserves the challenge" do
    c = sample_challenge()
    {scaffold, pieces} = Challenge.to_pieces(c)
    rebuilt = Challenge.from_pieces(:typed_term, c.assay, c.label, c.seed, c.note, scaffold, pieces)
    assert rebuilt.payload == c.payload
    assert rebuilt.kind == :typed_term
  end

  test "corpus encode → decode is identity" do
    c = sample_challenge()
    line = Corpus.encode_record(c)
    assert {:ok, decoded} = Corpus.decode_record(line)
    assert decoded.kind == :typed_term
    assert decoded.payload == c.payload
  end

  test "terms_of returns type, term, and ctx entries" do
    assert Coverage.terms_of(sample_challenge()) == [SigMenu.nat(), {:var, 0}, SigMenu.nat()]
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/antigen/typed_term_seed_test.exs`
Expected: FAIL — no `:typed_term` clause in `to_pieces`/`from_pieces`/`terms_of`.

- [ ] **Step 3: Write the implementation**

In `lib/antigen/challenge.ex`:

1. Extend the kind type (line 7):
```elixir
  @type kind :: :stub | :def_group | :family | :forcing_pair | :indexed_case | :rewrite_eq | :typed_term
```

2. Add to `@known_atoms` (after the universes line):
```elixir
    # tier-B typed-term vertical: kind, family/ctor/def names, sig version
    :typed_term, :v1, :Bd, :T, :F, :Vec, :vnil, :vcons, :plus, :dbl, :x, :xs
```
(`:well_typed`, `:Nat`, `:Z`, `:S`, `:n`, `:p` are already present.)

3. Add a `to_pieces/1` clause (after the `:indexed_case`/`:rewrite_eq` clause):
```elixir
  def to_pieces(%__MODULE__{kind: :typed_term, payload: p}) do
    %{sig: sig, ctx: ctx, type: type, term: term} = p
    ctx_pieces = ctx |> Enum.with_index() |> Enum.map(fn {t, i} -> {"ctx#{i}", t} end)
    scaffold = %{"sig" => Atom.to_string(sig), "ctx_len" => length(ctx)}
    {scaffold, ctx_pieces ++ [{"type", type}, {"term", term}]}
  end
```

4. Add a `from_pieces/7` clause (after the `:rewrite_eq` clause):
```elixir
  def from_pieces(:typed_term, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)
    len = scaffold["ctx_len"]
    ctx = for i <- (if len == 0, do: [], else: 0..(len - 1)), do: Map.fetch!(pmap, "ctx#{i}")
    payload = %{
      sig: String.to_existing_atom(scaffold["sig"]),
      ctx: ctx,
      type: Map.fetch!(pmap, "type"),
      term: Map.fetch!(pmap, "term")
    }
    new(kind: :typed_term, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end
```

In `lib/antigen/coverage.ex`, add a `terms_of/1` clause (after the `:stub` clause):
```elixir
  def terms_of(%Challenge{kind: :typed_term, payload: %{ctx: ctx, type: type, term: term}}),
    do: [type, term | ctx]
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/antigen/typed_term_seed_test.exs`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/challenge.ex lib/antigen/coverage.ex test/antigen/typed_term_seed_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): :typed_term challenge kind — serialization + coverage keying"
```

---

### Task 6: `typed_term/1` — assay-id-tagged challenge generator

**Files:**
- Modify: `lib/antigen/generators/term.ex` (add `typed_term/1` + `default_gen/0`)
- Test: `test/antigen/generators/term_test.exs` (add cases)

**Interfaces:**
- Consumes: `gen_term/2`, `Generators.Context.gen/1`, `SigMenu.{env_of, goal_types, rebuild_context}`.
- Produces:
  - `typed_term(assay_id :: String.t()) :: Gen.t()` — a `Gen` of `%Challenge{kind: :typed_term, assay: assay_id, label: :well_typed, payload: %{sig: :v1, ctx, type, term}}`.
  - `default_gen() :: Gen.t()` — `Gen.frequency` over the three assay ids (weight 1 each), used by the mix task.

- [ ] **Step 1: Write the failing test (add to term_test.exs)**

```elixir
  test "typed_term/1 emits a well-typed :typed_term challenge for its assay id" do
    alias Antigen.Challenge
    for id <- ["term/infer_check", "term/subject_reduction", "term/normalization"] do
      for c <- sample(Term.typed_term(id), 20) do
        assert %Challenge{kind: :typed_term, assay: ^id, label: :well_typed, payload: p} = c
        assert p.sig == :v1
        # the claimed term checks in its rebuilt context
        env = SigMenu.env_of(:v1)
        ctx = SigMenu.rebuild_context(env, p.ctx)
        assert {:ok, _} = Kernel.infer(ctx, p.term)
      end
    end
  end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/antigen/generators/term_test.exs`
Expected: FAIL — `Term.typed_term/1` undefined.

- [ ] **Step 3: Write the implementation (add to term.ex)**

```elixir
  alias Antigen.Challenge
  alias Antigen.Generators.Context, as: CtxGen

  @assay_ids ["term/infer_check", "term/subject_reduction", "term/normalization"]
  def assay_ids, do: @assay_ids

  @spec typed_term(String.t()) :: Gen.t()
  def typed_term(assay_id) when assay_id in @assay_ids do
    env = SigMenu.env_of(:v1)

    Gen.bind(CtxGen.gen(env), fn ctx_types ->
      ctx = SigMenu.rebuild_context(env, ctx_types)

      Gen.bind(goal_gen(ctx), fn goal ->
        Gen.bind(gen_term(ctx, goal), fn term ->
          Gen.return(
            Challenge.new(
              kind: :typed_term,
              assay: assay_id,
              label: :well_typed,
              payload: %{sig: :v1, ctx: ctx_types, type: goal, term: term}
            )
          )
        end)
      end)
    end)
  end

  # A goal over the current context: a closed menu goal, or Vec(var) when a
  # matching Nat var exists (drives stuck-index generation).
  defp goal_gen(ctx) do
    base = Enum.map(SigMenu.goal_types(), fn g -> {1, Gen.return(g)} end)

    depth = Context.length(ctx)
    vec_var_goals =
      for k <- (if depth == 0, do: [], else: 0..(depth - 1)),
          match?({:data, :Nat, [], []}, Normalise.quote(Context.lookup(ctx, k), depth)),
          do: {1, Gen.return(SigMenu.vec({:var, k}))}

    Gen.frequency(base ++ vec_var_goals)
  end

  @spec default_gen() :: Gen.t()
  def default_gen do
    Gen.frequency(Enum.map(@assay_ids, fn id -> {1, typed_term(id)} end))
  end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/antigen/generators/term_test.exs`
Expected: PASS (6 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/generators/term.ex test/antigen/generators/term_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): typed_term/1 + default_gen — assay-id-tagged challenges"
```

**Deviation note (goal-space narrowing vs. spec §5/§5.1):** two places in this
plan deliberately implement a narrower goal-type space than the spec's prose
describes, on top of the already-documented Sigma-unreachability (Task 1's
`subst0` note):

1. §5.1 describes the context generator as recursing into the engine itself
   — `gen_term(Γ_so_far, Type 0)` — to draw each entry's type. Task 2's
   `Generators.Context.entry_type/2` does not do this: it is a fixed,
   hand-written `Gen.frequency` over `SigMenu.nat/bd/vec`, with no dependency
   on `Generators.Term`. This is a genuine simplification, not a slip: Task 2
   is built before Task 3 (`gen_term` does not exist yet when Context is
   written), and introducing a Context → Term dependency would invert that
   ordering. The two are behaviorally aligned regardless — `entry_type/2`'s
   choices are drawn from exactly the same menu vocabulary `intro_rules`'s
   `{:type,_}` clause (Task 3/4) would itself offer — so nothing unsound is
   introduced, only untested: the `{:type,_}` row is never reached via
   Context, only via the dedicated unit test added in Task 3.
2. §5 lists the goal-type space as "`Nat`, `Bd`, `Vec(i)` ..., `Pi`/`Sigma`
   over these". Task 6's `goal_gen/1` (the generator that actually feeds
   `typed_term/1`, and therefore the health gate, the assays, and the banked
   corpus) only ever offers `SigMenu.goal_types()` (`Nat`, `Bd`, closed
   `Vec`) plus `Vec(var)` goals — **never** a `Pi` or `Sigma` goal. The `Pi`
   introduction rule (`intro_rules(ctx, _goal, {:pi, dom, cod}, size)`, Task
   3) is real, correctly implemented, and unit-tested in isolation (Task 3's
   "a Pi goal yields a lambda" test, Task 9's canonical-fallback totality
   matrix) — but it is never exercised through the actual `typed_term`/
   `default_gen`/health-gate/assay pipeline, so no banked seed or assay run
   ever claims a Pi-typed term. `Sigma` is separately unreachable end-to-end
   per Task 1's note. This is accepted as a v1 scope decision (menu richness
   grows by *version*, per the Global Constraints' "signature menu is
   versioned" rule) rather than fixed here, because widening `goal_gen` to
   include Pi goals changes the health-metric distribution (a canonical
   `Pi(A,B) → lam(canon(B))` inhabitant may leave its binder unused, which
   would need frequency-weight tuning against the live floors in Task 8/10 —
   a judgment call that belongs with whoever runs the acceptance pass with
   real numbers in hand, not a blind edit here). If a future version widens
   `goal_gen` to include Pi/Sigma, re-verify the binder-usage floor still
   clears (§11's "tuning is measurable inside acceptance run 1" applies).

---

### Task 7: The three differential assays

**Files:**
- Create: `lib/antigen/assays/term.ex`
- Test: `test/antigen/assays/term_test.exs`

**Interfaces:**
- Consumes: `Challenge`; `SigMenu.rebuild_context/2`; `Cure.Core.{Kernel, Normalise, Conv, Serialize, Context}`.
- Produces: `run(challenge) :: :ok | {:violation, detail}` dispatching on `c.assay`. `@assay_fuel 500`. Violation classes per spec §7.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/assays/term_test.exs
defmodule Antigen.Assays.TermTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Term, as: A
  alias Antigen.Challenge
  alias Antigen.Generators.{Term, SigMenu}
  alias Antigen.Backend.StreamData, as: B

  defp samples(id, n), do: B.interp(Term.typed_term(id)) |> Enum.take(n)

  test "infer_check assay is green on generated well-typed terms" do
    for c <- samples("term/infer_check", 60), do: assert A.run(c) == :ok
  end

  test "subject_reduction assay is green on generated well-typed terms" do
    for c <- samples("term/subject_reduction", 60), do: assert A.run(c) == :ok
  end

  test "normalization assay is green on generated well-typed terms" do
    for c <- samples("term/normalization", 60), do: assert A.run(c) == :ok
  end

  test "a deliberately ill-typed :typed_term is caught (mechanism check)" do
    # hand-break the claim: term {:var,0} but empty context → infer fails
    bad = Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
            payload: %{sig: :v1, ctx: [], type: SigMenu.nat(), term: {:var, 0}})
    assert {:violation, {:infer_failed, _}} = A.run(bad)
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/antigen/assays/term_test.exs`
Expected: FAIL — `Antigen.Assays.Term` undefined.

- [ ] **Step 3: Write the implementation**

```elixir
# lib/antigen/assays/term.ex
defmodule Antigen.Assays.Term do
  @moduledoc """
  The Tier-B differential self-consistency assays (spec §7). Each consumes a
  `:typed_term` challenge and probes the kernel against itself:

    * term/infer_check       — infer(t)=A ⟹ check(t,A)=:ok ∧ A ≡ claimed T
    * term/subject_reduction — nf(t) still checks at A
    * term/normalization     — nf(nf t)=nf t, nf t re-checks, C2 round-trips

  Fuel exhaustion at any stage is its own violation class `{:fuel_exhausted,
  stage}` — a suspected non-normalization, never conflated with a mismatch.
  """
  alias Antigen.Challenge
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Kernel, Normalise, Conv, Serialize, Context}

  @assay_fuel 500
  def assay_fuel, do: @assay_fuel

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :typed_term, assay: assay, payload: p}) do
    env = SigMenu.env_of(p.sig)
    ctx = SigMenu.rebuild_context(env, p.ctx)

    case Kernel.infer(ctx, p.term) do
      {:ok, inferred} -> dispatch(assay, ctx, p, inferred)
      {:error, e} -> {:violation, {:infer_failed, e}}
    end
  end

  # --- term/infer_check ------------------------------------------------------
  defp dispatch("term/infer_check", ctx, p, inferred) do
    depth = Context.length(ctx)
    inferred_term = Normalise.quote(inferred, depth)

    cond do
      Kernel.check(ctx, p.term, inferred) != :ok ->
        {:violation, {:check_disagrees, Kernel.check(ctx, p.term, inferred)}}

      not converges?(inferred_term, p.type, ctx) ->
        {:violation, {:inferred_type_mismatch, inferred_term, p.type}}

      true -> :ok
    end
  end

  # --- term/subject_reduction ------------------------------------------------
  # `fuel: @assay_fuel` is required, not cosmetic: `Normalise.nf/3`'s default
  # (2-arg call) is `fuel: :infinity`, which would make `:fuel_exhausted`
  # below permanently unreachable — silently defeating locked decision #6
  # ("fixed committed fuel decides verdicts") and this module's own moduledoc
  # claim that fuel exhaustion is its own violation class.
  defp dispatch("term/subject_reduction", ctx, p, inferred) do
    case Normalise.nf(ctx, p.term, fuel: @assay_fuel) do
      :fuel_exhausted -> {:violation, {:fuel_exhausted, :nf}}
      nf ->
        case Kernel.check(ctx, nf, inferred) do
          :ok -> :ok
          err -> {:violation, {:nf_ill_typed, err}}
        end
    end
  end

  # --- term/normalization ----------------------------------------------------
  defp dispatch("term/normalization", ctx, p, inferred) do
    with nf when nf != :fuel_exhausted <- Normalise.nf(ctx, p.term, fuel: @assay_fuel),
         nf2 when nf2 != :fuel_exhausted <- Normalise.nf(ctx, nf, fuel: @assay_fuel) do
      cond do
        nf2 != nf -> {:violation, {:not_idempotent, nf, nf2}}
        Kernel.check(ctx, nf, inferred) != :ok -> {:violation, {:nf_ill_typed, nf}}
        not round_trips?(nf) -> {:violation, {:c2_round_trip, nf}}
        true -> :ok
      end
    else
      :fuel_exhausted -> {:violation, {:fuel_exhausted, :nf}}
    end
  end

  defp converges?(t1, t2, ctx) do
    case Conv.conv_within?(t1, t2, Context.env(ctx), Context.length(ctx),
           Context.signature(ctx), @assay_fuel) do
      {:ok, true} -> true
      _ -> false
    end
  end

  defp round_trips?(term) do
    case Serialize.decode(Serialize.encode(term)) do
      {:ok, ^term} -> true
      _ -> false
    end
  end
end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/antigen/assays/term_test.exs`
Expected: PASS (4 tests). If a generated term legitimately trips a violation, apply the §7.4 triage rule: reproduce minimally, then either fix the generator (add a self-test) or pin the term in `test/antigen/reach.sexp` — do NOT weaken the assay.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/assays/term.ex test/antigen/assays/term_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): three Tier-B differential assays (infer_check/subject_red/normalization)"
```

---

### Task 8: Wire the Runner registry + health gate

**Files:**
- Modify: `lib/antigen/runner.ex`
- Test: `test/antigen/health_gate_test.exs`

**Interfaces:**
- Consumes: `Assays.Term.run/1`; `Coverage.terms_of/1`; `Normalise.nf/2`.
- Produces:
  - Runner `assay_module/1` clauses for the three ids → `Antigen.Assays.Term`.
  - Health metrics over `:typed_term` challenges: `binder_usage`, `reduction_activity`, `fuel_exhausted_count`; floors `@binder_usage_floor 0.60`, `@reduction_activity_floor 0.25`, `@discard_floor 0.10` as module attributes; `summarize/2` returns them and a `:healthy | :vacuous` stamp.
  - Public `health_metrics(challenges :: [Challenge.t()]) :: map()` so the static-replay meta-test can assert floors over a banked corpus without running a generation.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/health_gate_test.exs
defmodule Antigen.HealthGateTest do
  use ExUnit.Case, async: true
  alias Antigen.Runner
  alias Antigen.Generators.Term
  alias Antigen.Backend.StreamData, as: B

  test "health_metrics computes binder-usage and reduction-activity over :typed_term" do
    challenges = B.interp(Term.default_gen()) |> Enum.take(200)
    m = Runner.health_metrics(challenges)
    assert is_float(m.binder_usage)
    assert is_float(m.reduction_activity)
    assert is_integer(m.fuel_exhausted_count)
    # the v1 engine must clear its own floors
    assert m.binder_usage >= 0.60, "binder-usage #{m.binder_usage} below floor"
    assert m.reduction_activity >= 0.25, "reduction-activity #{m.reduction_activity} below floor"
  end

  test "the three term assay ids resolve to Assays.Term" do
    for id <- Term.assay_ids() do
      assert Runner.assay_module_for(id) == Antigen.Assays.Term
    end
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/antigen/health_gate_test.exs`
Expected: FAIL — `Runner.health_metrics/1` and `Runner.assay_module_for/1` undefined; no registry entry for the ids.

- [ ] **Step 3: Write the implementation (edit runner.ex)**

1. Add registry clauses (in the private `assay_module/1` group):
```elixir
  defp assay_module("term/infer_check"), do: Antigen.Assays.Term
  defp assay_module("term/subject_reduction"), do: Antigen.Assays.Term
  defp assay_module("term/normalization"), do: Antigen.Assays.Term
```

2. Expose it for tests (public wrapper near the other public funcs):
```elixir
  @doc "Public view of the assay registry (for tests)."
  def assay_module_for(assay_id), do: assay_module(assay_id)
```

3. Add the floors + metrics. Near the top of the module:
```elixir
  @binder_usage_floor 0.60
  @reduction_activity_floor 0.25
  @discard_floor 0.10
```

4. Add `health_metrics/1` and a stamp helper:
```elixir
  @doc """
  Health metrics over the :typed_term subset (spec §8): binder-usage and
  reduction-activity are scoped to :typed_term only; fuel-exhausted nf results
  are counted separately and excluded from reduction-activity.
  """
  def health_metrics(challenges) do
    tts = Enum.filter(challenges, &match?(%Antigen.Challenge{kind: :typed_term}, &1))
    terms = Enum.map(tts, fn c -> c.payload.term end)

    {used, total} =
      Enum.reduce(terms, {0, 0}, fn t, {u, tot} ->
        {tu, tt} = binder_stats(t)
        {u + tu, tot + tt}
      end)

    {fired, denom, fuel_out} =
      Enum.reduce(tts, {0, 0, 0}, fn c, {f, d, fx} ->
        env = Antigen.Generators.SigMenu.env_of(c.payload.sig)
        ctx = Antigen.Generators.SigMenu.rebuild_context(env, c.payload.ctx)

        # `fuel: ...` matters here for the same reason it does in Assays.Term:
        # the 2-arg call defaults to :infinity, which would make
        # `fuel_exhausted_count` permanently 0 regardless of the corpus.
        # Reuse Assays.Term's committed constant rather than inventing a
        # second one — Runner has no fuel budget of its own (§6.6/§8: the two
        # named constants are @gen_fuel and @assay_fuel, nothing else).
        case Cure.Core.Normalise.nf(ctx, c.payload.term, fuel: Antigen.Assays.Term.assay_fuel()) do
          :fuel_exhausted -> {f, d, fx + 1}
          nf -> {f + (if nf != c.payload.term, do: 1, else: 0), d + 1, fx}
        end
      end)

    %{
      binder_usage: safe_ratio(used, total),
      reduction_activity: safe_ratio(fired, denom),
      fuel_exhausted_count: fuel_out
    }
  end

  def health_stamp(metrics, discard_rate) do
    if metrics.binder_usage >= @binder_usage_floor and
         metrics.reduction_activity >= @reduction_activity_floor and
         discard_rate < @discard_floor,
       do: :healthy,
       else: :vacuous
  end

  # Count binders (lam / case-branch) and how many bind a variable that occurs.
  defp binder_stats(t), do: binder_stats(t, {0, 0})

  defp binder_stats({:lam, _dom, body}, {u, tot}) do
    used = if occurs?(body, 0), do: 1, else: 0
    binder_stats(body, {u + used, tot + 1})
  end

  defp binder_stats({:case, scrut, motive, branches}, acc) do
    acc = binder_stats(scrut, acc)
    acc = binder_stats(motive, acc)

    Enum.reduce(branches, acc, fn {_c, arity, body}, {u, tot} ->
      used = if arity > 0 and Enum.any?(0..(arity - 1), &occurs?(body, &1)), do: 1, else: 0
      tot2 = if arity > 0, do: tot + 1, else: tot
      binder_stats(body, {u + used, tot2})
    end)
  end

  defp binder_stats(t, acc) when is_tuple(t) do
    t |> Tuple.to_list() |> tl() |> Enum.reduce(acc, &binder_stats/2)
  end

  defp binder_stats(l, acc) when is_list(l), do: Enum.reduce(l, acc, &binder_stats/2)
  defp binder_stats(_leaf, acc), do: acc

  # Does de Bruijn index `k` occur free in `t`? (crosses binders by incrementing k)
  defp occurs?({:var, k}, k), do: true
  defp occurs?({:var, _}, _k), do: false
  defp occurs?({:lam, dom, body}, k), do: occurs?(dom, k) or occurs?(body, k + 1)
  defp occurs?({:pi, dom, cod}, k), do: occurs?(dom, k) or occurs?(cod, k + 1)
  defp occurs?({:sigma, a, b}, k), do: occurs?(a, k) or occurs?(b, k + 1)

  defp occurs?({:case, scrut, motive, branches}, k) do
    # `motive` is itself a `:lam`-headed term (spec §6.5's constant-motive
    # convention). It does NOT get a `k + 1` bump here: `Term.shift`/`Term.subst`'s
    # own `:case` clauses thread the SAME cutoff/index into `motive` (never `+1`),
    # because the extra binder lives inside motive's own `:lam` node and is
    # already handled by the generic `:lam` clause below. Bumping here too would
    # double-shift and cause `occurs?` to silently miss real occurrences.
    occurs?(scrut, k) or occurs?(motive, k) or
      Enum.any?(branches, fn {_c, arity, body} -> occurs?(body, k + arity) end)
  end

  defp occurs?(t, k) when is_tuple(t), do: t |> Tuple.to_list() |> tl() |> Enum.any?(&occurs?(&1, k))
  defp occurs?(l, k) when is_list(l), do: Enum.any?(l, &occurs?(&1, k))
  defp occurs?(_leaf, _k), do: false

  defp safe_ratio(_num, 0), do: 1.0
  defp safe_ratio(num, den), do: num / den
```

5. In `explore/1`, after the reduce, compute and print the health line. Replace the final `%{infections: ...}` return with one that folds in health:
```elixir
    metrics = health_metrics(challenges)
    discard_rate = final.discards / max(count, 1)
    stamp = health_stamp(metrics, discard_rate)

    IO.puts(
      "antigen health[typed_term]: binder_usage=#{Float.round(metrics.binder_usage, 2)} " <>
        "reduction_activity=#{Float.round(metrics.reduction_activity, 2)} " <>
        "fuel_exhausted=#{metrics.fuel_exhausted_count} discard=#{Float.round(discard_rate, 2)} → #{stamp}"
    )

    %{infections: final.infections, seeds_banked: final.seeds_banked,
      health: summarize(final, count), health_metrics: metrics, stamp: stamp}
```

Note: `occurs?/2`'s generic tuple/list fallbacks intentionally do NOT re-increment `k` for non-binder nodes — only the explicit `:lam`/`:pi`/`:sigma` clauses (body/cod at `k + 1`) and `:case`'s branches (body at `k + arity`) cross binders; `:case`'s `motive` argument stays at the SAME `k` (see the comment on that clause — motive's own `:lam` supplies the crossing). Confirm no other Core term form binds a variable (per `lib/cure/core/term.ex` there is none besides these); if one exists, add its clause.

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/antigen/health_gate_test.exs`
Expected: PASS (2 tests). If `binder_usage`/`reduction_activity` fall below floor, the fix is generator frequency tuning (raise `:lam`/`:case`/`:app` weights in `term.ex`), NOT lowering the floor (spec §11).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/runner.ex test/antigen/health_gate_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): Runner registry + health gate (binder-usage/reduction-activity)"
```

---

### Task 9: Static-replay meta-test + generator soundness meta-test + architecture test

**Files:**
- Create: `test/antigen/typed_term_meta_test.exs`
- Verify (no modification expected): `test/antigen/architecture_test.exs` — confirmed glob-based, see below.

**Interfaces:**
- Consumes: `Term.{typed_term, assay_ids}`, `Assays.Term.run/1`, `Runner.health_metrics/1`, `Corpus.stream/1`, `SigMenu`.
- Produces: durable `mix test`-time guards that (a) generated terms are sound, (b) the banked seed corpus meets health floors statically, (c) the new modules are StreamData-free.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/typed_term_meta_test.exs
defmodule Antigen.TypedTermMetaTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Term, SigMenu}
  alias Antigen.{Runner, Corpus, Challenge}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel}

  test "generator soundness: a fixed sample all checks at its claimed type" do
    for id <- Term.assay_ids() do
      for c <- B.interp(Term.typed_term(id)) |> Enum.take(50) do
        env = SigMenu.env_of(:v1)
        ctx = SigMenu.rebuild_context(env, c.payload.ctx)
        assert {:ok, _} = Kernel.infer(ctx, c.payload.term),
               "unsound generated term for #{id}: #{inspect(c.payload.term)}"
      end
    end
  end

  test "canonical-fallback totality over a fixed goal matrix" do
    env = SigMenu.env_of(:v1)
    empty = Context.empty(env)
    stuck_ctx = SigMenu.rebuild_context(env, [SigMenu.vec({:var, 0}), SigMenu.nat()])

    goals = [
      {empty, SigMenu.nat()}, {empty, SigMenu.bd()},
      {empty, SigMenu.vec({:ctor, :Z, []})},
      {empty, SigMenu.vec({:ctor, :S, [{:ctor, :Z, []}]})},
      {empty, {:pi, SigMenu.nat(), SigMenu.nat()}},
      {stuck_ctx, SigMenu.vec({:var, 1})}
    ]

    for {ctx, g} <- goals do
      assert SigMenu.inhabitable?(ctx, g)
      assert {:ok, _} = Kernel.infer(ctx, SigMenu.canon(ctx, g))
    end
  end

  @seeds_path "test/antigen/seeds.sexp"
  test "banked :typed_term seed corpus meets the health floors (static replay)" do
    if File.exists?(@seeds_path) do
      banked =
        Corpus.stream(@seeds_path)
        |> Enum.flat_map(fn
          {:ok, %Challenge{kind: :typed_term} = c} -> [c]
          _ -> []
        end)

      if banked != [] do
        m = Runner.health_metrics(banked)
        assert m.binder_usage >= 0.60, "banked binder-usage #{m.binder_usage} below floor"
        assert m.reduction_activity >= 0.25, "banked reduction-activity #{m.reduction_activity} below floor"
      end
    end
  end
end
```

`test/antigen/architecture_test.exs` is confirmed (read against the tree) to glob by directory, not enumerate modules — its entire body is:
```elixir
Path.wildcard("lib/antigen/{generators,assays}/**/*.ex")
|> Enum.filter(fn f -> File.read!(f) =~ ~r/\bStreamData\b/ end)
```
This pattern already covers `sig_menu.ex`, `context.ex`, `term.ex` (under `lib/antigen/generators/`) and `assays/term.ex` (under `lib/antigen/assays/`) — **no code change to this file is needed** for Task 9; it already enforces the StreamData-free constraint on every file this plan creates, by construction of the file paths in the File Structure section. (There is no module-enumeration branch to fall back to.)

- [ ] **Step 2: Run the test to verify it fails (then passes for the ones already satisfiable)**

Run: `mix test test/antigen/typed_term_meta_test.exs test/antigen/architecture_test.exs`
Expected: the soundness + totality tests PASS immediately (they exercise Tasks 1–6); the banked-corpus test is a no-op until Task 10 populates `seeds.sexp`. Architecture test PASS.

- [ ] **Step 3: (no new impl)** — confirmed glob-based (see above); no code change to `architecture_test.exs` is needed.

- [ ] **Step 4: Run the tests to verify they pass**

Run: `mix test test/antigen/typed_term_meta_test.exs test/antigen/architecture_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add test/antigen/typed_term_meta_test.exs test/antigen/architecture_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(antigen): Tier-B soundness + totality + static-health meta-tests; arch test"
```

---

### Task 10: Wire `mix antigen`, run the acceptance explore, update the ledger

**Files:**
- Modify: `lib/mix/tasks/antigen.ex`
- Modify: `test/antigen/mix_task_test.exs` (new red test for the wiring)
- Modify: `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md`
- Commits: banked `seeds.sexp` (and any `corpus.sexp`/`reach.sexp` produced by triage)

**Interfaces:**
- Consumes: `Antigen.Generators.Term.default_gen/0`.
- Produces: the six-branch `default_gen/0` in the mix task; a banked `:typed_term` seed corpus; updated ledger rows.

`default_gen/0` is private, so this task's red test has to observe the wiring
through the mix task's own public surface — the same way the existing
`test/antigen/mix_task_test.exs` tests already do (run the task, inspect its
side effects) — rather than calling `default_gen/0` directly. The existing
"`mix antigen --count` runs the explorer and prints a summary" test in that
file is NOT a substitute: it only asserts the output contains "antigen" and
either "infection" or "banked", which is already true today with just Tier
A's three branches, so it passes identically before and after this task's
change and proves nothing about Tier B actually being wired in.

- [ ] **Step 1: Write the failing test (add to `test/antigen/mix_task_test.exs`)**

```elixir
  test "the wired-in default_gen draws :typed_term challenges (Tier B is live)" do
    seeds_path = Path.join(@tmp, "seeds_tier_b.sexp")

    Mix.Tasks.Antigen.run([
      "generate",
      "--count",
      "300",
      "--seeds",
      seeds_path,
      "--report-dir",
      @tmp
    ])

    kinds =
      Antigen.Corpus.stream(seeds_path)
      |> Enum.flat_map(fn
        {:ok, c} -> [c.kind]
        _ -> []
      end)
      |> MapSet.new()

    assert :typed_term in kinds
  end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/antigen/mix_task_test.exs`
Expected: FAIL — `default_gen/0` only draws Tier-A's three known-label generators, so no `:typed_term` challenge is ever banked at any sample count; `:typed_term in kinds` is false.

- [ ] **Step 3: Extend the mix task's `default_gen/0`**

Edit `lib/mix/tasks/antigen.ex` — replace the private `default_gen/0`:
```elixir
  # Explorer default: Tier-A's three known-label generators + Tier-B's three
  # typed-term/assay-id branches, weight 1 each (six branches).
  defp default_gen do
    Antigen.Gen.frequency([
      {1, Antigen.Generators.Totality.gen()},
      {1, Antigen.Generators.Positivity.gen()},
      {1, Antigen.Generators.Forcing.gen()},
      {1, Antigen.Generators.Term.typed_term("term/infer_check")},
      {1, Antigen.Generators.Term.typed_term("term/subject_reduction")},
      {1, Antigen.Generators.Term.typed_term("term/normalization")}
    ])
  end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/antigen/mix_task_test.exs`
Expected: PASS (4 tests) — `:typed_term` now appears among the 300 harvested seeds' kinds.

- [ ] **Step 5: Run the acceptance explore (spec §10 criterion 1)**

Run: `mix antigen --count 500`
Expected: a run that prints `antigen: N infection(s), M seed(s) banked` and the `antigen health[typed_term]: …→ healthy` line. Roughly ~250 of 500 draws are `:typed_term` at equal weighting.

- If any infection is reported: read the `tmp/antigen/` report, apply §7.4 triage — reproduce the term by hand, then either (a) fix the generator and re-run this step, or (b) if genuinely a kernel incompleteness (wrongly rejected), pin it in `test/antigen/reach.sexp` via a dedicated commit. Do NOT proceed to Step 7 with an unexplained infection.
- If `→ vacuous`: raise `:lam`/`:case`/`:app` frequency weights in `term.ex` (spec §11) and re-run. Do not lower floors.

- [ ] **Step 6: Run the full suite once (spec §10 criterion 4)**

Run: `mix test`
Expected: green. (Only one suite at a time — never concurrent.) Note: `mix test` sets `Mix.env() == :test`, so the mix task's SIGTERM trap stays uninstalled, as designed.

- [ ] **Step 7: Bank the seed corpus and commit it**

The `mix antigen --count 500` run already appended to `test/antigen/seeds.sexp` (and possibly `corpus.sexp`). Verify the static-health meta-test now sees a populated corpus:

Run: `mix test test/antigen/typed_term_meta_test.exs`
Expected: the banked-corpus health test now asserts over real records and passes.

```bash
git add test/antigen/seeds.sexp test/antigen/corpus.sexp test/antigen/reach.sexp 2>/dev/null; \
git add lib/mix/tasks/antigen.ex test/antigen/mix_task_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(antigen): wire Tier-B into mix antigen; bank typed_term seed corpus"
```

- [ ] **Step 8: Update the parity ledger and commit**

Edit `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md`:
- Row **#22** (`Term-generator metatheory engine`): change Status from `⬜ (designed)` to `✅` (or `🟡` if any assay landed as a reach pin rather than green), and update the cell to note the three differential assays + health gate landed, referencing this plan.
- Expansion **A8**: `🔵 biggest leverage (designed)` → `✅ done` (term generator + differential trio) with the same caveat if applicable.
- Expansion **A10**: note partial — the typed-term stream feeds the three differential assays; feeding the *existing* known-label verticals from a generated stream remains open.
- Update the "honest headline" tally (§2) to reflect #22 moving to parity.

```bash
git add docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "docs(ledger): row 22 / A8 — Tier-B term generator + differential assays landed"
```

---

## Self-Review

**1. Spec coverage:**
- §1 in-scope generator → Tasks 1–6; context generator → Task 2; `:typed_term` kind → Task 5; three assays → Task 7; health gate → Task 8. ✓
- §2 locked decisions → Global Constraints + enforced in Tasks 1 (real certification), 3/4/7/8 (fuel-bounded whnf/conv/nf — every call site explicitly passes `fuel:`, confirmed during this review), 9 (architecture test). ✓
- §5 signature menu / §5.1 context → Tasks 1, 2. ✓
- §6 engine (rule table, INDIR, ctor choice, canonical fallback, redexes/case, size/determinism) → Tasks 3, 4. ✓
- §7 assays incl. triage → Task 7 (+ triage applied in Tasks 7/10). ✓
- §8 health gate (metric scoping, fuel-exhausted handling, floor locations, two-place enforcement) → Task 8 (runtime stamp) + Task 9 (static meta-test). ✓
- §9 testing the engine (architecture, soundness-meta, round-trip, support-set) → Tasks 5 (round-trip), 9 (soundness + architecture). Support-set: the spec §9 conclusion is that `gen_term`'s overall support is `:over_approx` and Tier B adds no fixed-point `Gen` node — so there is no finiteness claim to test at the engine level; the inspectable finite claim is about a single rule-choice `frequency` node. This is a documented non-test (asserting `:over_approx` would test the obvious); noted here rather than adding a vacuous test. ✓ (documented deviation)
- §10 acceptance → Task 10. ✓
- §11 risks → mitigations embedded (floor-not-lowered rule in Tasks 8/10). ✓
- §12 base → the worktree is already cut from the transliteration branch. ✓

**2. Placeholder scan:** No "TBD"/"handle edge cases"/"similar to Task N". The one soft spot — `SigMenu.subst0/2` identity and `Term.shift/3` arity — are explicitly flagged with a read-the-source instruction and a v1-scope justification, not left vague.

**3. Type consistency:** `typed_term/1` returns a `%Challenge{}` (Task 6) consumed by `Assays.Term.run/1` (Task 7) and `Runner.health_metrics/1` (Task 8) with matching payload keys `%{sig, ctx, type, term}`. `assay_ids/0` (Task 6) is used by Tasks 8/9. `env_of/1`, `rebuild_context/2`, `canon/2`, `inhabitable?/2` signatures (Task 1) are used identically downstream. `conv_within?/6` and `Normalise.nf/2`/`quote/2` arities match the verified reference block.

**Deviations recorded:** (a) support-set §9 is a documented non-test per above; (b) `subst0/3` (Task 1) is a real eval/quote substitution — unreachable in v1 (no Sigma goal ever arises) but implemented correctly rather than as an identity no-op, per the recursive-skeptical-review pass that found the identity version silently mis-scoped free variables; (c) `Term.shift/3`'s signature is confirmed against source (`shift(term, amount, cutoff \\ 0)`) and `Term.shift(goal, 1, 0)` in Task 4 is verified correct — no open question remains; (d) the goal-type space actually reachable through `typed_term`/`goal_gen` (Task 6) is narrower than spec §5/§5.1's prose (no `Pi`/`Sigma` goal, and `Generators.Context` does not recurse into `gen_term` for `Type 0`) — see the deviation note after Task 6 for the task-ordering and health-metric rationale; the `{:type,_}` and `Pi` rule-table rows still get direct (if isolated) unit coverage via the dedicated tests added in Task 3, and `case_rule` (Task 4) was corrected during this review to gate on the goal's whnf shape so it no longer fires at a `{:type,_}` goal, matching spec §6.1's Type-0 row and keeping Task 3's new Type-0 test deterministic; (e) every `Normalise.nf`/`Normalise.whnf` call in `Generators.Term` (Task 3/4's own `whnf/2`), `Assays.Term` (Task 7's `subject_reduction`/`normalization` dispatch), and `Runner.health_metrics/1` (Task 8) was corrected during this review to pass an explicit `fuel:` option (`@gen_fuel` / `@assay_fuel`) — the plan as first drafted called all of these with the 2-arg form, whose default is `fuel: :infinity` (confirmed against `Normalise.nf/3`'s `normalize_opts/1`), which would have made every `:fuel_exhausted` branch described in spec §6.3/§7.2/§7.3/§8 (and locked decision #6, "fixed committed fuel decides verdicts") permanently dead code. `Generators.SigMenu`'s own `whnf/2` (Task 1) is deliberately left unbounded — see the comment added there — since it backs the totality fallback, not a generator choice being accepted/rejected against a goal.

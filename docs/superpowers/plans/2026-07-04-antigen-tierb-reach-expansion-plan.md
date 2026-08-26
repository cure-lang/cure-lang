# Antigen Tier-B Reach Expansion — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Widen the dependent-term generator's reach (Π/Σ goal seeds + a parametric `List(A)` family), add a `term/erasure_preservation` assay, and add ill-typed mutation operators for the new type formers.

**Architecture:** Three sequential phases, each independently committed. Phase 1 enriches `SigMenu`'s menu (the stream Phases 2–3 consume). Phase 2 marks one arg `:erased` (so erasure isn't the identity) then adds an assay checking `nf(erase t) ≡ erase(nf t)`. Phase 3 adds mutation operators. All work is in `Antigen.*` + the menu; **no kernel/TCB edits**.

**Tech Stack:** Elixir/ExUnit, the reified `Antigen.Gen` DSL, `Cure.Core.{Inductive,Kernel,Normalise,Eval,Conv}`, `Cure.Elab.Erase` (read-only through op-maps).

## Global Constraints

- **`MIX_ENV=test`**, run from worktree root `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/antigen-tier-b`. **One build/test run at a time.**
- **No edits to `Cure.*`** — reached read-only through op-maps. No `:meck`, no new dependency.
- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NEVER a `Co-Authored-By` trailer.
- **StreamData quarantine:** nothing under `Antigen.Generators.*`/`Antigen.Assays.*` may contain the literal `StreamData` token. New generator code uses `Antigen.Gen`.
- **Assays return only `:ok | {:violation, term()}`** (fuel exhaustion is its own tagged violation, never conflated with a mismatch).
- **Full existing suite green each phase** (2732 baseline); every new assay/operator ships a negative control that demonstrably infects.
- **Menu changes are additive to `:v1`** (spec §8-5) — never remove/reshape an existing family/ctor/def, so banked `:v1` seeds replay unchanged.
- **Tests immutable once written** (strict TDD): pass by editing implementation, never by weakening a test.
- Stay on `autopilot/antigen-tier-b`.

## File structure

- `lib/antigen/generators/sig_menu.ex` — `List(A)` family, Π/Σ/List goal seeds, `canon`/`inhabitable?` clauses, `vcons` `:erased` mark.
- `lib/antigen/generators/term.ex` — `intro_rules` clause for `:List`, `@assay_ids` +1, `typed_term/1`'s check-mode-only top-level wrap (`top_level_term/3` + `check_mode_only?/2` — Task 2 Step 4c).
- `lib/antigen/assays/term.ex` — `term/erasure_preservation` dispatch clause + helpers.
- `lib/antigen/generators/mutation.ex` — `:pair_component`, `:app_result`, `:type_param_mismatch` operators.
- `lib/antigen/runner.ex` — `assay_module("term/erasure_preservation")` clause.
- `lib/antigen/challenge.ex` — `@known_atoms`: `:List`, `:Nil`, `:Cons`, `:A`, new mutation op atoms.
- Tests: `test/antigen/generators/sig_menu_test.exs` (or existing), `test/antigen/assays/erasure_preservation_test.exs`, `test/antigen/generators/mutation_test.exs`.

---

## PHASE 1 — Richer generator menu

### Task 1: `List(A)` parametric family + atoms

**Files:** `lib/antigen/generators/sig_menu.ex`, `lib/antigen/challenge.ex`, test.

- [ ] **Step 1: Verify the param-family declaration convention.** `List` is the FIRST
  param-bearing family in `SigMenu` (Vec uses an *index*, `params: []`). Before declaring it,
  read `lib/cure/core/inductive.ex` (`family/4`, `ctor/3,4`, `param_count/2`,
  `ctor_quantities/2`) and grep the codebase for any existing param-bearing family
  (`grep -rn "Inductive.family([^,]*, \[{" lib/ test/`) to confirm how a ctor's telescope
  references the family parameter in de Bruijn (the param is an outer binder in scope over
  the ctor telescope). Record the confirmed convention as a comment. Do NOT guess.

- [ ] **Step 2: Write the failing test** — `test/antigen/generators/sig_menu_test.exs` (create if absent):

```elixir
defmodule Antigen.Generators.SigMenuTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Context, Inductive}

  test "env_of(:v1) registers the List(A) family with Nil/Cons" do
    env = SigMenu.env_of(:v1)
    assert Inductive.param_count(env, :List) == 1
    assert Inductive.ctor_quantities(env, :Nil) != nil
    assert Inductive.ctor_quantities(env, :Cons) != nil
  end

  test "List(Nat) is inhabitable and canon gives Nil" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    list_nat = {:data, :List, [SigMenu.nat()], []}
    assert SigMenu.inhabitable?(ctx, list_nat)
    assert SigMenu.canon(ctx, list_nat) == {:ctor, :Nil, []}
  end

  # Kernel-soundness test for the param-bearing declaration (result_params
  # correctness — see Step 4's rationale). The two tests above never invoke the
  # kernel checker at all (structural/predicate assertions only), so neither
  # can catch a missing/wrong `result_params`; this is the one that can. List
  # is check-mode-only at the top level (no bare `:ctor` of a param-bearing
  # family ever infers — kernel.ex), so wrap in the same identity-application
  # trick Task 6/8 use for mutation.
  test "Cons/Nil check-mode-accept against List(Nat) (result_params correctness)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    list_nat = {:data, :List, [SigMenu.nat()], []}
    nil_wrapped = {:app, {:lam, list_nat, {:var, 0}}, {:ctor, :Nil, []}}
    cons_wrapped = {:app, {:lam, list_nat, {:var, 0}},
                     {:ctor, :Cons, [{:ctor, :Z, []}, {:ctor, :Nil, []}]}}
    assert {:ok, _} = Cure.Core.Kernel.infer(ctx, nil_wrapped)
    assert {:ok, _} = Cure.Core.Kernel.infer(ctx, cons_wrapped)
  end
end
```

- [ ] **Step 3: Run to verify RED.** `MIX_ENV=test mix test test/antigen/generators/sig_menu_test.exs` → FAIL (3 failures: `:List` unregistered; `inhabitable?`/`canon` have no `:List` clause; the third test's `Kernel.infer` calls fail with `{:error, {:unknown_family, :List}}` since `:List` isn't declared yet).

- [ ] **Step 4: Declare the family** in `env_of(:v1)` (append to the `|> Inductive.declare(...)` chain). **De Bruijn convention CONFIRMED (not a guess) by two independent sources**, so this is no longer Step-1-verify-and-correct — it is locked: (a) tracing `Kernel.check_ctor_app`/`check_ctor_app_rec` (kernel.ex) — the runtime CHECK-mode path every param-bearing ctor application actually goes through — shows the local eval env is seeded with the family's param values (most-recent-param-first) and then each ctor arg is prepended as it's checked, so a param referenced from the FIRST ctor arg's type sits at `{:var, 0}` (no args bound yet) and shifts by 1 per subsequent arg bound; (b) this is exactly corroborated by the existing single-param/single-arg family in `test/antigen/assays/elab_soundness_test.exs` (`F(a:Type)`, `Mk(x:a)` declared as `ctor(:Mk, [{:x, {:var, 0}}], [], [:present], [{:var, 1}])`) and `test/cure/core/param_index_split_test.exs` (`P(a:Type)`, `wrap(p:a)` with the SAME `{:var,0}`-in-first-arg / `{:var,1}`-in-result-params shape). **A second, independently-confirmed requirement those same two existing tests document and the original candidate below omitted: a param-bearing ctor MUST also supply explicit `result_params` (via `ctor/5`, not the `ctor/3` used below in the original draft) — `elab_soundness_test.exs` lines 80-88 spell out exactly why: with `result_params: []` (the `ctor/3` default), `Kernel.check`'s `{:ctor,...}` clause re-derives `actual = {:vdata, family, [] ++ indices}` (param dropped from the actual spine), which fails `Conv.conv_values?`'s spine-length check against the expected `{:vdata, family, [param_val] ++ indices}` even for an intentionally well-typed term.** Traced end-to-end against `check_uniform_params`'s formula `{:var, num_args + (num_params - 1 - p)}`: for `Nil` (0 args, 1 param) that's `{:var, 0}`; for `Cons` (2 args, 1 param) that's `{:var, 2}`.

```elixir
      |> Inductive.declare(Inductive.family(:List, [{:A, {:type, 0}}], [], 0),
        [
          # Nil : List(A). result_params = [{:var,0}]: with 0 args bound, A sits
          # at var 0 in the (params-only) checking frame — required so
          # Kernel.check's {:ctor,...} clause re-derives {:vdata,:List,[A]}
          # (not {:vdata,:List,[]}) and converts against the expected List(A).
          Inductive.ctor(:Nil, [], [], [], [{:var, 0}]),
          # Cons : (A) => A -> List(A) -> List(A). Arg telescope: hd's type
          # references A at {:var,0} (no ctor args bound yet, A is the sole
          # binder in scope); tl's type references A at {:var,1} (hd has since
          # been bound, shifting A down by one) — confirmed against
          # check_ctor_app_rec's local eval-env construction (params seeded
          # first, then each arg prepended as checked) and against
          # elab_soundness_test.exs's structurally-identical F(a)/Mk(x:a) case.
          # result_params = [{:var,2}]: with both args bound (hd, tl), ctx_full
          # = [A, hd, tl] by declaration order, so A sits at var 2.
          Inductive.ctor(:Cons, [{:hd, {:var, 0}}, {:tl, {:data, :List, [{:var, 1}], []}}], [],
            [:present, :present], [{:var, 2}])
        ])
```

- [ ] **Step 5: Add `canon`/`inhabitable?` clauses** for `:List` (mirror the Vec structure at sig_menu.ex:80-104):

```elixir
  # in inhabitable?/2, before the catch-all `_ -> false`:
      {:data, :List, [a], _} -> inhabitable?(ctx, a)
  # in canon/2:
      {:data, :List, [_a], _} -> {:ctor, :Nil, []}
```

- [ ] **Step 6: Intern atoms** in `lib/antigen/challenge.ex` `@known_atoms` (append):

```elixir
    # Tier-B reach expansion: List parametric family + param binder name
    :List, :Nil, :Cons, :A
```

- [ ] **Step 7: Run to verify GREEN.** `MIX_ENV=test mix test test/antigen/generators/sig_menu_test.exs` → PASS (3: all three tests from Step 2, including the kernel-soundness test — it must not be skipped even though Step 4's declaration already "looks" right, since it's the only test in Task 1 that actually exercises the kernel on a param-bearing checking-mode term and is what would have caught a missing `result_params`).

- [ ] **Step 8: Commit** — `feat(antigen): add List(A) parametric family to the Tier-B menu`

### Task 2: `List` introduction rule + goal seeds

**Files:** `lib/antigen/generators/term.ex`, `lib/antigen/generators/sig_menu.ex`, test.

- [ ] **Step 1: Write the failing test** (append to `sig_menu_test.exs`):

```elixir
  test "gen_term over List(Nat) produces a List constructor" do
    alias Antigen.Generators.Term
    alias Antigen.Backend.StreamData, as: SD
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    gen = Term.gen_term(ctx, {:data, :List, [SigMenu.nat()], []})
    terms = SD.sample(SD.interp(gen), 20)
    assert Enum.all?(terms, fn t -> match?({:ctor, :Nil, []}, t) or match?({:ctor, :Cons, _}, t) end)
    # at least one Cons (non-vacuous) across the sample at reasonable size
  end
```

> Note: this test lives in a `test/` file, so referencing `Antigen.Backend.StreamData` is
> allowed (the quarantine covers only `lib/antigen/{generators,assays}`). Confirm the sample
> helper signature against `backend/stream_data.ex` (`sample(native, count)`); adjust if the
> generator must be `interp`'d then sampled differently.

- [ ] **Step 2: Run to verify RED** — `gen_term` over `List(Nat)` currently hits `intro_rules`' `_other -> []` catch-all and falls back to `canon` (only `Nil`), never `Cons`; or the size-driven path errors. Confirm the failure.

- [ ] **Step 3: Add the `intro_rules` clause** in `term.ex` (before the `_other` catch-all at term.ex:147), mirroring `ctor_rules_for_vec`:

```elixir
  defp intro_rules(ctx, _goal, {:data, :List, [a], _}, size) do
    nil_rule = {2, Gen.return({:ctor, :Nil, []})}

    cons_rules =
      if SigMenu.inhabitable?(ctx, a) do
        [{2,
          Gen.bind(gen(ctx, a, size - 1), fn hd ->
            Gen.bind(gen(ctx, {:data, :List, [a], []}, size - 1), fn tl ->
              Gen.return({:ctor, :Cons, [hd, tl]})
            end)
          end)}]
      else
        []
      end

    [nil_rule | cons_rules]
  end
```

- [ ] **Step 4: Add List goal seeds** in `sig_menu.ex` `goal_types/0`:

```elixir
  def goal_types, do: [nat(), bd(), vec(z()), vec(s(z())),
                       {:data, :List, [nat()], []}, {:data, :List, [bd()], []}]
```

- [ ] **Step 4a: RED against an EXISTING test — this step is required, not optional.**
  `goal_types/0` feeds `Term.typed_term/1`, which is the challenge-construction entry point
  `Antigen.Runner`/`Mix.Tasks.Antigen.default_gen`/`test/antigen/typed_term_meta_test.exs` all
  consume. Once `List(Nat)`/`List(Bd)` are goal seeds, `Term.gen_term`'s `canon` fallback (weight
  1, always offered) and its new `intro_rules` clause (Step 3, weight 2) will, with high
  probability, produce a BARE top-level `{:ctor, :Nil, []}` / `{:ctor, :Cons, _}` as
  `c.payload.term`. `Antigen.Assays.Term.run/2` (assays/term.ex:29-37) unconditionally calls
  `k.infer.(ctx, p.term)` FIRST, before any dispatch — it has no expected-type-directed check
  path. `Kernel.infer(ctx, {:ctor, cname, args})` (kernel.ex) explicitly returns
  `{:error, {:ctor_requires_checking_mode, family_name}}` for EVERY bare ctor of a
  param-bearing family (`List` has 1 param, `Inductive.param_count(sig,:List) > 0`) —
  regardless of whether the term is actually well-typed. Run:
  `MIX_ENV=test mix test test/antigen/typed_term_meta_test.exs` → **FAILS**: its "generator
  soundness: a fixed sample all checks at its claimed type" test (line 8) does
  `for c <- B.interp(Term.typed_term(id)) |> Enum.take(50), do: assert {:ok,_} = Kernel.infer(ctx,
  c.payload.term)` across all 3 `term/*` assay ids — with List now ~2/9 of `goal_types`, this
  will assert-fail (not crash) on List-typed samples with `{:error, {:ctor_requires_checking_mode,
  :List}}`. Confirm this failure before proceeding — it is the RED for Step 4c, not a sign
  Step 3/4 did something wrong.

- [ ] **Step 4b: Write a second, targeted failing test** pinning the exact fix contract (append
  to `sig_menu_test.exs`):

```elixir
  test "typed_term challenges over List goals are infer-viable at the top level" do
    alias Antigen.Generators.Term
    alias Antigen.Backend.StreamData, as: SD
    for id <- Term.assay_ids() do
      samples = SD.interp(Term.typed_term(id)) |> Enum.take(80)
      list_samples = Enum.filter(samples, &match?({:data, :List, _, _}, &1.payload.type))
      assert list_samples != [], "no List sample drawn in 80 tries for #{id} (widen sample or check goal_types)"
      for c <- list_samples do
        env = SigMenu.env_of(:v1)
        ctx = SigMenu.rebuild_context(env, c.payload.ctx)
        assert {:ok, _} = Cure.Core.Kernel.infer(ctx, c.payload.term),
               "top-level List challenge term not infer-viable: #{inspect(c.payload.term)}"
      end
    end
  end
```

- [ ] **Step 4c: Implement the fix** — a top-level check-mode-only-term wrap in
  `lib/antigen/generators/term.ex`'s `typed_term/1`. `Assays.Term.run/2` always infers the
  OUTER challenge term with no expected type available to fall back to `check` — so any
  top-level shape with no infer path (a bare `:pair`, which has NO `Kernel.infer` clause at
  all — see Task 6/8's spec-§5 analysis of the identical crash risk for mutation — or a bare
  `:ctor` of a param-bearing family) must be routed through `check` mode via the SAME
  identity-application trick Phase 3's mutation operators use
  (`{:app, {:lam, sigma_type, {:var,0}}, bad_pair}`): `infer` on `{:app, {:lam, goal, {:var,0}},
  term}` infers the identity lambda's Pi type `goal -> goal`, then CHECKS `term` against the
  domain `goal` — exactly the check-mode path a param-bearing ctor or a bare pair requires, and
  the overall inferred type reduces back to `goal` (a closed constant closure), so
  `dispatch/5`'s downstream use of `inferred` is unaffected. Every OTHER v1 top-level shape
  (Nat/Bd/Vec ctor, `:lam`, `:var`, `:app`, `:case`, `:fst`, `:snd`) already has a working infer
  path and is left bare — additive-only, no existing banked-seed shape changes (spec §8-5), since
  List/Sigma challenges are new and have never been banked before this fix lands.

```elixir
  # In generators/term.ex — add Inductive to the existing Context/Eval/Normalise alias.
  alias Cure.Core.{Context, Eval, Inductive, Normalise}

  @doc "A `Gen` of a `:typed_term` challenge tagged for `assay_id`."
  @spec typed_term(String.t()) :: Gen.t()
  def typed_term(assay_id) when is_binary(assay_id) do
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
              payload: %{sig: :v1, ctx: ctx_types, type: goal, term: top_level_term(ctx, goal, term)}
            )
          )
        end)
      end)
    end)
  end

  # Route a check-mode-only top-level term through the identity-application wrap
  # (see Step 4c's rationale) so Assays.Term.run/2's unconditional k.infer.(ctx,
  # p.term) never hits a shape with no infer path.
  defp top_level_term(ctx, goal, term) do
    if check_mode_only?(ctx, term), do: {:app, {:lam, goal, {:var, 0}}, term}, else: term
  end

  # Sigma has no Kernel.infer clause at all (check-mode-only, like a param-bearing
  # ctor — see kernel.ex). A param-bearing family's bare ctor explicitly errors
  # {:ctor_requires_checking_mode, _} from infer. Both need the wrap.
  defp check_mode_only?(_ctx, {:pair, _, _}), do: true

  defp check_mode_only?(ctx, {:ctor, cname, _args}) do
    sig = Context.signature(ctx)

    case Inductive.ctor_family(sig, cname) do
      nil -> false
      fam -> Inductive.param_count(sig, fam) > 0
    end
  end

  defp check_mode_only?(_ctx, _other), do: false
```

  Note: `Term.gen_term/2` itself (called directly, not via `typed_term/1`) is UNCHANGED and
  still returns the bare shape — Step 1's test above (which calls `Term.gen_term` directly)
  keeps asserting `match?({:ctor,:Nil,[]},t) or match?({:ctor,:Cons,_},t)` unmodified. Only the
  `:typed_term` CHALLENGE-construction entry point wraps.

- [ ] **Step 4d: Run to verify GREEN** —
  `MIX_ENV=test mix test test/antigen/typed_term_meta_test.exs test/antigen/generators/sig_menu_test.exs`
  → PASS. The wrap also strictly improves (never regresses) Task 3 Step 5's health-gate floors:
  it adds a guaranteed-firing β-redex (the identity application) with a USED binder to every
  List-typed challenge, which can only raise `binder_usage`/`reduction_activity`, never lower them.

- [ ] **Step 5: Run to verify GREEN** — `MIX_ENV=test mix test test/antigen/generators/sig_menu_test.exs` → PASS (5: Task 1's 3 + this task's "gen_term over List(Nat)" (Step 1) + Step 4b's targeted infer-viability test).

- [ ] **Step 6: Commit** — `feat(antigen): generate List(A) terms + List goal seeds`

### Task 3: Π/Σ goal seeds

**Files:** `lib/antigen/generators/sig_menu.ex`, test.

- [ ] **Step 1: Write the failing test** (append to `sig_menu_test.exs`):

```elixir
  test "goal_types includes a Pi and a Sigma seed, each inhabitable, canon total" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    seeds = SigMenu.goal_types()
    assert Enum.any?(seeds, &match?({:pi, _, _}, &1))
    assert Enum.any?(seeds, &match?({:sigma, _, _}, &1))
    for g <- seeds do
      assert SigMenu.inhabitable?(ctx, g), "non-inhabitable seed: #{inspect(g)}"
      # canon must not raise
      assert SigMenu.canon(ctx, g)
    end
  end

  test "gen_term over a Pi goal produces a lambda" do
    alias Antigen.Generators.Term
    alias Antigen.Backend.StreamData, as: SD
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    gen = Term.gen_term(ctx, {:pi, SigMenu.nat(), SigMenu.nat()})
    terms = SD.sample(SD.interp(gen), 10)
    assert Enum.any?(terms, &match?({:lam, _, _}, &1))
  end
```

- [ ] **Step 2: Run to verify RED** — `goal_types` has no `:pi`/`:sigma` seed today.

- [ ] **Step 3: Add Π/Σ seeds** to `goal_types/0` (Σ of inhabitables; keep the index closed):

```elixir
  def goal_types, do: [nat(), bd(), vec(z()), vec(s(z())),
                       {:data, :List, [nat()], []}, {:data, :List, [bd()], []},
                       {:pi, nat(), nat()}, {:pi, nat(), bd()},
                       {:sigma, nat(), nat()}]
```

> `{:sigma, nat(), nat()}` (a non-dependent pair `Nat × Nat`) is the safe minimal Σ seed —
> its `b` doesn't reference the bound var, so `subst0` is trivial and inhabitability is
> `inhabitable?(nat()) ∧ inhabitable?(nat())` = true. A `{:sigma, nat(), vec({:var,0})}`
> (dependent) seed is a richer follow-up but risks a stuck Vec index at canon; keep it out
> unless Step 1's inhabitability check passes for it.

- [ ] **Step 4: Run to verify GREEN** — PASS (7: the 5 from Tasks 1–2 plus this task's 2 new tests). The `intro_rules` for `:pi`/`:sigma` already exist (term.ex:104-122), so no generator change is needed. **The top-level infer-viability wrap Task 2 Step 4c added already covers this Σ seed for free** — `check_mode_only?/2` matches bare `{:pair, _, _}` generically, not just List-specific shapes, since `:sigma`-goal top-level terms (from `canon`'s Sigma clause, always weight 1, and `intro_rules`'s Sigma clause, weight 3) are exactly as check-mode-only as List's bare ctors (Sigma has NO `Kernel.infer` clause at all in kernel.ex — a bare `{:pair,_,_}` would otherwise raise `FunctionClauseError`, not a clean `{:error,_}`, making this the more severe half of the same root issue Task 2 Step 4a-4d fixed). **Do not skip verifying this** — run
  `MIX_ENV=test mix test test/antigen/typed_term_meta_test.exs` immediately after adding the Σ
  seed above and confirm it's still green (no new code needed here if Task 2's wrap landed
  first; if it crashes, the wrap from Task 2 Step 4c is missing or `check_mode_only?/2`'s
  `{:pair,_,_}` clause was dropped — stop and fix before continuing).

- [ ] **Step 5: Health gate + differential trio** — `MIX_ENV=test mix test test/antigen/typed_term_meta_test.exs test/antigen/health_gate_test.exs` → PASS (the richer menu must not tank binder-usage/reduction-activity floors, and the three differential assays stay green over the deeper stream). If a floor regresses, investigate before proceeding (do NOT lower the floor).

- [ ] **Step 6: Commit** — `feat(antigen): add Pi/Sigma goal seeds to the Tier-B menu`

---

## PHASE 2 — `erasure_preservation` assay

### Task 4: Mark `vcons`'s `n` argument `:erased` (precondition)

**Files:** `lib/antigen/generators/sig_menu.ex`, test.

- [ ] **Step 1: Write the failing test** (append to `sig_menu_test.exs`):

```elixir
  test "vcons declares its length witness n as :erased (so erase is not the identity)" do
    env = SigMenu.env_of(:v1)
    assert Inductive.ctor_quantities(env, :vcons) == [:erased, :present, :present]
  end
```

- [ ] **Step 2: Run to verify RED** — `vcons` currently declares no quantities (defaults all-`:present`).

- [ ] **Step 3: Add the quantity vector** to the `vcons` declaration in `env_of(:v1)` (sig_menu.ex:38):

```elixir
          Inductive.ctor(:vcons, [{:n, nat()}, {:x, nat()}, {:xs, vec({:var, 1})}], [s({:var, 2})],
            [:erased, :present, :present])
```

- [ ] **Step 4: Run to verify GREEN** — PASS. Then **run the FULL suite** (`MIX_ENV=test mix test`) — marking `n` erased changes `Erase.erase` behavior but NOT `vcons`'s arity/types (spec §4/§8-5), so `Kernel.infer`/`check`/`Term.term?` and banked-seed replay must be unaffected. Expect 0 failures. If the differential trio or a banked seed breaks, STOP — the additive-only assumption was wrong; investigate.

- [ ] **Step 5: Commit** — `feat(antigen): mark vcons length witness :erased (enables non-vacuous erasure testing)`

### Task 5: `term/erasure_preservation` assay + negative control

**Files:** `lib/antigen/assays/term.ex` (or new `erasure_preservation.ex`), `lib/antigen/generators/term.ex` (`@assay_ids`), `lib/antigen/runner.ex`, test.

- [ ] **Step 1: Confirm the erase/nf/quote API** — read `assays/term.ex`'s existing
  `term/normalization` clause to see exactly how it calls `Normalise` (does it `nf` a Core
  term directly, or `eval` then `quote`?), the fuel constant (`@assay_fuel`), and how it
  detects `:fuel_exhausted`. `erasure_preservation` must use the SAME nf/quote entry point on
  both `erase(t)` and `t` so the comparison is apples-to-apples. Also confirm
  `Cure.Elab.Erase.erase/2`'s arity (`(env, term)`) and that `p.ctx`/`p.type` give the env.

- [ ] **Step 2: Write the failing tests** — `test/antigen/assays/erasure_preservation_test.exs`.
  **Two corrections to the original draft, both verified by hand-tracing `nf`/`erase` against
  `kernel.ex`/`normalise.ex`/`erase.ex` before writing any implementation — do not substitute
  the original simpler versions, they are confirmed broken:**

  1. **Payload shape bug:** `Assays.Term.run/2` does `ctx = SigMenu.rebuild_context(env, p.ctx)`
     (assays/term.ex:31), which expects `p.ctx` to be a **list of Core-term ctx types**
     (`Enum.reverse`d and folded — see `Term.typed_term/1`'s own `ctx: ctx_types` and
     `to_pieces`'s `:typed_term` clause, which always stores a list). Passing a built
     `Context.t()` struct directly as `p.ctx` (the original draft's `ctx: ctx` where
     `ctx = Context.empty(env)`) makes `rebuild_context` call `Enum.reverse/1` on a struct with
     no `Enumerable` implementation — a `Protocol.UndefinedError` crash, not a clean test
     failure. Use `ctx: []` (the list form for an empty context) instead.
  2. **Vacuous witness term / vacuous negative control:** the original draft's `t =
     {:ctor,:vcons,[Z,Z,vnil]}` has **no reducible redex anywhere** — `nf(t) == t` trivially.
     Traced through `Normalise.nf`'s per-argument-independent congruence and `Erase.erase`'s
     per-argument structural filter: **for a redex-free `t`, `nf(erase(t)) ≡ erase(nf(t))`
     reduces to the tautology `erase(t) ≡ erase(t)` and holds for LITERALLY ANY erase
     function**, correct or broken — including the original draft's own negative-control stub
     (verified by hand: `bad_erase` dropping "the first kept arg" on `{:ctor,:vcons,[Z,Z,vnil]}`
     coincidentally drops the SAME position (0) as the real erase, since `n` (the erased slot)
     already sits at position 0 — so the stub produces the byte-identical output on both sides
     and the assay reports `:ok`, not a violation; the "negative control" silently fails to
     infect). More generally: **any fixed-position-drop stub trivially commutes with `nf` for
     ANY position**, because `nf` treats each constructor argument independently (a
     congruence) and a positional filter is also a congruence, and congruences compose —
     this holds whether or not the dropped position matches the REAL erased slot, and whether
     or not `t` contains a redex. The property (formulation (a)) is only sensitive to a
     *reduction-state-dependent* erasure bug (one whose decision differs before vs. after
     normalization), not to "drops the structurally wrong but still fixed slot." The fix below
     uses (i) a witness term with a genuine redex on the erased (`n`) argument specifically, so
     `nf` does real work, and (ii) a shape-inspecting (not position-fixed) `bad_erase` stub
     whose decision of what to drop differs depending on whether it observes the redex
     pre- or post-reduction — verified end-to-end by hand-trace to make the REAL erase still
     pass and the stub genuinely infect:

```elixir
defmodule Antigen.Assays.ErasurePreservationTest do
  use ExUnit.Case, async: false
  alias Antigen.Assays.Term, as: TermAssay   # or Antigen.Assays.ErasurePreservation
  alias Antigen.Challenge

  defp ch(term, type) do
    Challenge.new(kind: :typed_term, assay: "term/erasure_preservation",
      label: :positive, payload: %{term: term, type: type, ctx: [], sig: :v1}, seed: 1)
  end

  # n is a CLOSED beta-redex ((λy:Nat.y) Z), not a bare Z literal — Eval.eval
  # (used by Kernel.check_ctor_app_rec to compute xs's expected index type)
  # fully reduces it via NbE, so the term is well-typed (xs=vnil : Vec(Z)
  # matches Vec(n_redex_value) = Vec(Z)) even though `n` is syntactically
  # unreduced. This is essential: it's what makes the witness term exercise
  # `nf`'s actual reduction machinery instead of being a no-op no-redex value.
  defp n_redex, do: {:app, {:lam, {:data, :Nat, [], []}, {:var, 0}}, {:ctor, :Z, []}}
  defp t, do: {:ctor, :vcons, [n_redex(), {:ctor, :S, [{:ctor, :Z, []}]}, {:ctor, :vnil, []}]}
  defp ty, do: {:data, :Vec, [], [{:ctor, :S, [{:ctor, :Z, []}]}]}

  test "real erase preserves nf on a vcons term with a genuine redex on the erased n slot" do
    assert TermAssay.run(ch(t(), ty())) == :ok
  end

  test "negative control: a shape-sniffing (not position-fixed) erase stub infects" do
    # Drops the FIRST argument that is ALREADY a literal Z-shaped ctor, rather
    # than consulting the ctor's static quantity vector. Pre-normalization, `n`
    # is an unreduced :app (not Z-shaped) so this stub drops NOTHING; post-
    # normalization `n` has reduced to a literal Z and IS dropped — the two
    # branches diverge (verified: nf(erase(t)) keeps 3 args, erase(nf(t)) keeps
    # 2 — different arities, so no reduction-independence coincidence is possible).
    bad_erase = fn
      _env, {:ctor, c, args} ->
        case Enum.find_index(args, &match?({:ctor, :Z, []}, &1)) do
          nil -> {:ctor, c, args}
          i -> {:ctor, c, List.delete_at(args, i)}
        end

      _env, other -> other
    end

    k = %{TermAssay.__real_erase_ops__() | erase: bad_erase}
    assert {:violation, {:erasure_not_preserved, _}} = TermAssay.run(ch(t(), ty()), k)
  end
end
```

> The exact op-map accessor name (`__real_erase_ops__` vs extending the existing
> `@real_kernel`) is pinned in Step 3 — match whatever `assays/term.ex` already exposes;
> if it exposes `@real_kernel` via a `__real__/0`, extend that map with `erase`.

- [ ] **Step 3: Run to verify RED** — no `term/erasure_preservation` dispatch clause; `run` raises/FunctionClause.

- [ ] **Step 4: Implement the assay** — add to `assays/term.ex`. Extend the op-map with `erase: &Cure.Elab.Erase.erase/2`; add the dispatch clause (formulation (a), spec §8-2):

```elixir
  defp dispatch("term/erasure_preservation", ctx, p, _inferred, k) do
    env = Context.env(ctx)
    erased = k.erase.(env, p.term)
    with {:ok, nf_erased} <- nf_or_fuel(erased, ctx),
         {:ok, nf_t} <- nf_or_fuel(p.term, ctx),
         erased_nf_t = k.erase.(env, nf_t) do
      cond do
        Serialize.encode(nf_erased) == Serialize.encode(erased_nf_t) -> :ok
        true -> {:violation, {:erasure_not_preserved, %{lhs: nf_erased, rhs: erased_nf_t}}}
      end
    else
      {:fuel, stage} -> {:violation, {:fuel_exhausted, stage}}
    end
  end
```

> `nf_or_fuel/2` wraps the normalize call, returning `{:ok, term}` or `{:fuel, stage}` —
> model it on how `term/normalization` already distinguishes fuel exhaustion (Step 1). The
> LHS is `nf(erase t)`, the RHS is `erase(nf t)` (commutation). Compare via `Serialize.encode`
> (canonical) rather than raw `==` to match the existing assays' comparison discipline.

- [ ] **Step 5: Wire** — add `"term/erasure_preservation"` to `Term.@assay_ids` (term.ex) and a `assay_module("term/erasure_preservation")` clause in `runner.ex`.

- [ ] **Step 6: Run to verify GREEN** — PASS (2). The baseline passes (real erase commutes with nf on the redex-bearing, erased-n vcons term); the shape-sniffing negative-control stub infects (diverges to a 3-arg vs 2-arg result, per Step 2's hand-verified trace).

- [ ] **Step 7: Full suite** — `MIX_ENV=test mix test` → 0 failures.

- [ ] **Step 8: Commit** — `feat(antigen): term/erasure_preservation assay (nf∘erase ≡ erase∘nf, finds erase corruption)`

---

## PHASE 3 — Ill-typed mutation for the new type formers

### Task 6: `pair_component` operator (self-wrapped)

**Files:** `lib/antigen/generators/mutation.ex`, `lib/antigen/challenge.ex`, test.

- [ ] **Step 1: Read** `mutation.ex`'s existing `build/2` clauses + the `wrap`/`@wrappers`/`deepen` machinery (esp. the `:pair` wrapper `wrap(inner, :pair, filler) = {:app, {:lam, sig(), z()}, {:pair, inner, filler}}`) and `operators/0`. Confirm `sig()`/`nat_t()` helpers.

- [ ] **Step 2: Write the failing test** — `test/antigen/generators/mutation_test.exs` (append or create):

```elixir
  test "pair_component builds a check-embedded ill-typed pair the kernel rejects" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    mutant = Mutation.build(ctx, :pair_component)
    # never a bare :pair (would crash Kernel.infer) — must be app-wrapped
    refute match?({:pair, _, _}, mutant)
    assert {:error, _} = Kernel.infer(ctx, mutant)
  end
```

- [ ] **Step 3: Run to verify RED** — `build(ctx, :pair_component)` undefined (FunctionClause).

- [ ] **Step 4: Implement** — add to `mutation.ex` (and `:pair_component` to `operators/0`):

```elixir
  def build(ctx, :pair_component) do
    # Σ Nat. Nat expects both components Nat; put a Bd in the first slot, embedded
    # in an identity application against the sigma type so Kernel.infer type-CHECKS
    # the pair (a bare :pair has NO infer clause — it would crash, spec §5).
    sigma_t = {:sigma, nat_t(), nat_t()}
    bad_pair = {:pair, {:ctor, :T, []}, {:ctor, :Z, []}}   # T : Bd, not Nat
    {:app, {:lam, sigma_t, {:var, 0}}, bad_pair}
  end
```

> Confirm `nat_t()`/`sig()` helper names against Step 1; use the existing ones.

- [ ] **Step 5: Run to verify GREEN** — PASS. The mutant is app-wrapped and `Kernel.infer` rejects it (checks `bad_pair` against `Σ Nat.Nat`, `T : Bd ≠ Nat`).

- [ ] **Step 6: Load-bearing analog check** — add a test that the WELL-TYPED analog (same wrapper, a valid `{:pair, Z, Z}`) is ACCEPTED, proving the operator genuinely ill-types:

```elixir
  test "pair_component's well-typed analog is accepted (operator genuinely ill-types)" do
    env = SigMenu.env_of(:v1); ctx = Context.empty(env)
    good = {:app, {:lam, {:sigma, {:data,:Nat,[],[]}, {:data,:Nat,[],[]}},
                   {:var, 0}}, {:pair, {:ctor,:Z,[]}, {:ctor,:Z,[]}}}
    assert {:ok, _} = Kernel.infer(ctx, good)
  end
```

- [ ] **Step 7: Intern atoms** — `:pair_component` in `challenge.ex` `@known_atoms` (mutants bank via `explore/1`).

- [ ] **Step 8: Commit** — `feat(antigen): pair_component mutation operator (Sigma component type mismatch)`

### Task 7: `app_result` operator (codomain break)

**Files:** `lib/antigen/generators/mutation.ex`, `lib/antigen/challenge.ex`, test.

- [ ] **Step 1: Write the failing test** (append to `mutation_test.exs`):

```elixir
  test "app_result builds a function whose result violates its declared codomain, rejected" do
    env = SigMenu.env_of(:v1); ctx = Context.empty(env)
    mutant = Mutation.build(ctx, :app_result)
    assert {:error, _} = Kernel.infer(ctx, mutant)
  end
```

- [ ] **Step 2: Run to verify RED.**

- [ ] **Step 3: Implement** — a λ claiming codomain `Nat` but returning `Bd`, forced by ascription/application so `infer` sees the mismatch (distinct from `app_domain`, which breaks the *domain*):

```elixir
  def build(_ctx, :app_result) do
    # (λ x:Nat. T) : Nat -> Nat  applied to Z  — body T : Bd violates codomain Nat.
    # Wrap the lambda so its declared Pi type is checked against the Bd-typed body.
    bad_fun = {:lam, nat_t(), {:ctor, :T, []}}           # body T : Bd, not Nat
    pi_t = {:pi, nat_t(), nat_t()}
    {:app, {:lam, pi_t, {:app, {:var, 0}, {:ctor, :Z, []}}}, bad_fun}
  end
```

> **CONFIRMED by hand-trace through `Kernel.infer`/`check` (kernel.ex) — this construction is
> correct as written; the fallback below is not needed.** `check(ctx,{:lam,dom,body},{:vpi,
> exp_dom,cod_closure})` is a DEDICATED bidirectional clause — it never falls back to
> `infer(lam)` plus a subtype check, so the "if infer instead accepts" concern cannot arise:
> tracing the outer `{:app, {:lam, pi_t, {:app,{:var,0},Z}}, bad_fun}` step by step —
> `infer(ctx,f)` synthesizes `f : (Nat->Nat) -> Nat` (the identity-shaped `f` applies its
> argument to `Z`); `ensure_pi` gives `dom = (Nat->Nat)`; `check(ctx, bad_fun, dom)` enters the
> `:lam`-vs-`:vpi` clause: `bad_fun`'s own declared domain (`nat_t()`) matches `dom`'s expected
> domain (`Nat`) — so the OUTER domain check passes cleanly, and rejection happens exactly
> where intended, one level in: `check`'s codomain step checks `bad_fun`'s BODY (`T`) against
> the expected codomain (`Nat`), which hits `check`'s `{:ctor,cname,args},{:vdata,family,_}`
> clause and fails with `{:error,{:foreign_ctor,:T}}` (`Inductive.ctor_family(sig,:T) = :Bd ≠
> :Nat`) — a clean rejection, specifically at the body-vs-codomain step, never at the
> domain-conversion step `app_domain` already covers. `Kernel.infer(ctx, mutant) =
> {:error, {:foreign_ctor, :T}}`. Confirmed distinct fault class from `app_domain` (which fails
> at the OUTER argument-vs-domain check, never reaching a lambda body at all).

- [ ] **Step 4: GREEN** + analog-accepted test — well-typed `(λx:Nat.Z)` version accepted:

```elixir
  test "app_result's well-typed analog is accepted (operator genuinely ill-types)" do
    env = SigMenu.env_of(:v1); ctx = Context.empty(env)
    good_fun = {:lam, nat_t(), {:ctor, :Z, []}}
    pi_t = {:pi, nat_t(), nat_t()}
    good = {:app, {:lam, pi_t, {:app, {:var, 0}, {:ctor, :Z, []}}}, good_fun}
    assert {:ok, _} = Kernel.infer(ctx, good)
  end
```

  (Traced: `check(ctx, good_fun, Nat->Nat)` — outer domain matches (Nat==Nat), then checks
  `good_fun`'s body `Z` against codomain `Nat` — `check(ctx,{:ctor,:Z,[]},{:vdata,:Nat,[]})`
  succeeds (`ctor_family(:Z)=:Nat=family`, 0-param family so no `result_params` concern here,
  unlike List — see Task 1's finding). `:ok`, confirming the operator's fault is genuinely
  introduced by `T`, not an artifact of the wrapper.)

- [ ] **Step 5: Intern** `:app_result` in `@known_atoms`; add to `operators/0`. (`lam_body_type`
  is dropped — Step 3's confirmed trace shows a single `app_result` operator already cleanly
  produces the codomain fault class; no fallback decision needed.)

- [ ] **Step 6: Commit** — `feat(antigen): app_result mutation operator (Pi codomain mismatch)`

### Task 8: `type_param_mismatch` operator (List parameter)

**Files:** `lib/antigen/generators/mutation.ex`, `lib/antigen/challenge.ex`, test.

- [ ] **Step 1: Write the failing test** (append):

```elixir
  test "type_param_mismatch: Cons of a wrong-param element into List(Nat), rejected" do
    env = SigMenu.env_of(:v1); ctx = Context.empty(env)
    mutant = Mutation.build(ctx, :type_param_mismatch)
    refute match?({:ctor, :Cons, _}, mutant)   # never bare (param-ctor → :ctor_requires_checking_mode)
    assert {:error, _} = Kernel.infer(ctx, mutant)
  end
```

- [ ] **Step 2: Run to verify RED.**

- [ ] **Step 3: Implement** — embed a `Cons (T:Bd) Nil : List(Nat)` where the kernel CHECKS it against `List(Nat)` (a bare param-ctor would hit `:ctor_requires_checking_mode` for the good analog too — spec §5). Decide deepen-compat per §5 (submit pre-wrapped, no deepen — record):

```elixir
  def build(_ctx, :type_param_mismatch) do
    list_nat = {:data, :List, [nat_t()], []}
    # Cons (T:Bd) Nil — element T : Bd violates the List(Nat) parameter
    bad_cons = {:ctor, :Cons, [{:ctor, :T, []}, {:ctor, :Nil, []}]}
    {:app, {:lam, list_nat, {:var, 0}}, bad_cons}   # forces CHECK of bad_cons : List(Nat)
  end
```

- [ ] **Step 4: GREEN** + analog-accepted test: the well-typed `Cons Z Nil : List(Nat)` (same wrapper) is accepted — proving both that the operator ill-types AND that Task 1's `List` family type-checks a correct `Cons` in check mode.

- [ ] **Step 5: Intern** `:type_param_mismatch` in `@known_atoms`; add to `operators/0`.

- [ ] **Step 6: Commit** — `feat(antigen): type_param_mismatch mutation operator (List parameter mismatch)`

---

## Task 9: Full-suite verification (Stage 5 gate)

- [ ] **Step 1: Quarantine** — `MIX_ENV=test mix test test/antigen/architecture_test.exs` → PASS (no `StreamData` token in the new assay/generator code).
- [ ] **Step 2: Full suite (single run)** — `MIX_ENV=test mix test` → 0 failures (2732 baseline + new tests). If any pre-existing test fails, STOP — a menu/atom edit regressed something.
- [ ] **Step 3: Restore side effects** — `git checkout -- test/antigen/seeds.sexp 2>/dev/null; git status --short` (the generator may have banked new `:typed_term`/`:mutant_term` seeds during the run — per the standing corpus-expansion instruction those are intentional expansions; if `seeds.sexp` grew with valid new seeds, that is expected, KEEP them and commit separately; only revert if the diff is spurious). Confirm the tree state is intentional.
- [ ] **Step 4:** (Report is Stage 5 of autopilot — written separately.)

## Self-review (against spec)

- **Spec §3 richer menu** → Tasks 1–3 (List family, List gen+seeds, Π/Σ seeds). ✓
- **Spec §4 erasure_preservation + the `:erased` precondition** → Task 4 (vcons `:erased` FIRST) then Task 5 (assay, formulation (a), fuel class, negative control). ✓
- **Spec §5 three mutation constructions with the self-wrap/no-bare requirements** → Tasks 6 (pair_component app-wrapped), 7 (app_result codomain), 8 (type_param_mismatch check-embedded). Each has the load-bearing analog-accepted test (spec §9). ✓
- **Spec §8-1 (List intro-only, no eliminator)** → Task 2 adds intro rule only; no case-eliminator. ✓
- **Spec §8-5 (additive `:v1`)** → Tasks 1/4 are additive; Task 4 Step 4 explicitly re-runs the full suite to confirm banked replay unaffected. ✓
- **Spec §6 invariants** → no `Cure.*` edits; quarantine (Task 9); `:ok|{:violation}` only (fuel its own class); atoms interned (Tasks 1/6/7/8); health gate (Task 3 Step 5). ✓
- **First-param-family risk** → Task 1 Step 1/Step 4 confirms the `Inductive` param convention (de Bruijn indices AND the previously-missing `result_params`) against `kernel.ex` plus two existing param-bearing-family tests — no guess, and no longer just "verified first" but load-bearing-tested (Step 2's third test, run red-then-green across Steps 3/7). ✓
- **No placeholders:** every code step shows code; the param de Bruijn convention and the exact nf/fuel entry point are resolved by direct source trace, not hand-waves.
- **recursive-skeptical-review hardening (2026-07-04, converged after 7 passes, last 2 clean):**
  four load-bearing defects confirmed and fixed in place, plus incidental consistency fixes
  surfaced while integrating them:
  1. Task 1's `Nil`/`Cons` needed explicit `result_params` (`ctor/5`, not the `ctor/3` the
     original draft used), without which EVERY check-mode use of List against an expected
     `List(...)` type — including Task 8's own load-bearing well-typed-analog test — would
     falsely fail on a spine-length `Conv` mismatch. Confirmed by tracing `Kernel.check`'s
     `{:ctor,...}` clause and corroborated by two existing param-bearing-family tests
     (`elab_soundness_test.exs`, `param_index_split_test.exs`) that document exactly this
     requirement. A dedicated kernel-soundness test (Task 1 Step 2's third test) now guards it.
  2. Adding `List`/`Sigma` as TOP-LEVEL `goal_types/0` seeds (Tasks 2/3) crashes or
     false-violates the EXISTING differential-assay pipeline: `Assays.Term.run/2`
     unconditionally calls `Kernel.infer` on the bare top-level challenge term first, which has
     no infer path for a bare Sigma pair (raw `FunctionClauseError` — Sigma has no
     `Kernel.infer` clause at all) or a bare param-bearing ctor (`:ctor_requires_checking_mode`).
     Fixed via a `top_level_term/3` + `check_mode_only?/2` identity-application wrap in
     `Term.typed_term/1` (Task 2 Steps 4a-4d), reused generically by Task 3's Sigma seed with
     its own regression check (Task 3 Step 4).
  3. Task 5's original witness term/negative-control stub was VACUOUS: a redex-free `t` makes
     `nf(erase(t)) ≡ erase(nf(t))` hold for ANY erase function, and more generally ANY
     fixed-position-drop stub trivially commutes with `nf` regardless of which position it
     drops (`nf`'s per-argument congruence composes with any positional filter, so the property
     can't distinguish "drops the right slot" from "drops a wrong but still fixed slot"). Fixed
     with a redex-bearing witness term (a closed β-redex on the erased `n` slot) and a
     reduction-state-dependent (shape-sniffing) stub, verified end-to-end by hand-trace to let
     the real erase pass and make the stub genuinely infect. Also fixed a payload-shape bug in
     the same test (`ctx` must be the ctx-types list `Term.typed_term/1` produces, not a built
     `Context.t()` — the original draft's `ctx: Context.empty(env)` would crash
     `SigMenu.rebuild_context`'s `Enum.reverse/1` call with `Protocol.UndefinedError`).
  4. Task 7's `app_result` construction, flagged uncertain in the original draft ("if infer
     instead accepts... adjust... if elusive, drop `lam_body_type`"), is CONFIRMED correct by
     full kernel trace (rejects at the body-vs-codomain check specifically, a fault class
     `app_domain` cannot produce) — the uncertainty hedge and the `lam_body_type` fallback
     operator are removed as unnecessary; a dedicated well-typed-analog test was added.

  Task 1's de Bruijn convention itself and Task 6/8's self-wrap/anti-crash constructions were
  independently verified correct as originally drafted (no change needed). Incidental fixes
  found while re-verifying the above: cumulative test-count claims (`PASS (N)`) drifted out of
  sync with the actual `sig_menu_test.exs` file across Tasks 1-3 as tests were added/relocated —
  corrected to 3/5/7; Task 1's new kernel-soundness test was originally sequenced AFTER its own
  fix (would never actually go red) — relocated into Step 2's initial test batch, ahead of
  Step 4's fix, restoring genuine red-before-green; a dead `SigMenu` alias left over from the
  Task 5 test rewrite was removed.

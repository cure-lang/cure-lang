# Inductive `Int` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace Cure's primitive `Int` with a canonical two-constructor inductive `Int` (`FromNat(Nat) | NegativeSuccessor(Nat)`) that still compiles to a native BEAM integer, giving the typechecker `match` and structural induction on integers while every existing program stays byte-identical.

**Architecture:** Mirror the in-tree `Nat` machinery exactly. `Int` becomes a `@builtin(:int)` inductive family (via `seed_builtin`, not `seed_primitives`); the existing compact `{:int_lit, n}` Core node becomes its canonical value form (as `{:nat_lit}` is for `Nat`); a new audited `int_to_ctor` fold bridges literal↔constructor at every ι/conversion site; and new name-keyed codegen lowers the two 1-ary constructors. The single TCB addition is the fold, Lean-aligned (`Int.ofNat`/`negSucc` are `@[extern]`-backed) and sound only because BEAM integers are arbitrary-precision.

**Naming note (spec cross-reference):** the spec (§3.2, §4) labels this fold `reduce_int`. This plan names it `int_to_ctor`/`int_to_ctor_if` instead — a deliberate choice, not a drift — because it mirrors the *actual* in-tree precedent function names exactly (`Eval.nat_to_ctor/1` / `nat_to_ctor_if/1`, `lib/cure/core/eval.ex:244-252`), which the spec's own §3.2 prose cites when explaining the precedent. Wherever the spec's TCB analysis (§4) says "the `reduce_int` fold," read it as this plan's `int_to_ctor`/`int_to_ctor_if`.

**Tech Stack:** Elixir (the Cure compiler under `lib/cure/`), Cure stdlib (`lib/std/`), the differential oracle (``mix otp.oracle` in `cure-otp`` against Idris2 at `~/Develop/Idris2/build/exec/idris2`), ExUnit kernel/soundness suite.

## Global Constraints

- **Byte-identical back-compat gate.** Every existing `Int` program (all stdlib, all examples, phase demos) MUST typecheck and compile byte-identically. Any regression that is not a *provably-equivalent* re-spelling is a **Halt condition**, not a fixup. This is the primary correctness gate for Phase 1.
- **One build/test run at a time.** Never launch concurrent full suites (a past concurrent run caused a kernel panic).
- **Author in `lib/std/`, never `priv/std`** (`priv/std/*.cure` is a generated bundle).
- **Ghost commits only:** author as the user (`--author="Made In Heaven <madeinheaven@madeinheaven.com>"`), no `Co-Authored-By` trailer, explicit-pathspec staging (never `git add -A`).
- **Descriptive naming directive:** spell names out (`FromNat`/`NegativeSuccessor`, `negate`, `IsLessThanOrEqual`) — never terse abbreviations.
- **TCB blanket approval applies** (change is Lean-aligned), but every kernel touch still runs the full gate.
- **Elaborator hard-stop principle:** if anything seems to need a new kernel *rule* beyond the `int_to_ctor` fold, STOP and Halt — do not invent a rule.
- **Steer:** work in `lib/cure/core/*` and `lib/cure/elab/*`. IGNORE `lib/cure/compiler/*` and `lib/cure/types/*` (non-dependent decoys).
- **The `{:int_lit, n}` node is retained and load-bearing** — it is the compact canonical form. Do NOT remove it. Only `{:int_type}`/`{:vint_type}` (the primitive *type* nodes) are candidates for retirement/repoint (Task 4).
- **Tests are immutable once written — for every task, not just Task 5.** This covers the ExUnit red tests (`int_family_test.exs`, `int_fold_test.exs`, `int_codegen_test.exs`, `int_surface_test.exs`), the differential oracle probes (Tasks 5–8), and the proof-compile checks (Tasks 5–8) alike. Reach green by changing implementation or proof code ONLY — never by deleting, skipping, loosening an assertion, or rewriting a test/probe to match whatever the code currently does. The sole exception is a test that is itself provably wrong (asserts the wrong expected behavior); that requires stating why the test is wrong, in the plan-execution log, before touching it. (Task 5 restates this for the `negate_involutive` proof specifically — that is a reminder, not the only place it applies.)

---

## Source of truth

Read `docs/superpowers/plans/../specs/kernel/2026-07-18-inductive-int-design.md` (the hardened spec) before starting. This plan implements it. Where they disagree, the spec's §5 back-compat gate and §4 TCB analysis win.

## The `Nat` precedent (the template every task mirrors)

`Nat` is already exactly what `Int` is becoming. Hold these five sites in mind — each `Int` task is "do what `Nat` does here":

| Concern | `Nat` implementation | File:line |
| --- | --- | --- |
| Family seed + schema | `nat: [{:Z,0},{:S,1}]`; `nat_family`/`nat_ctors`; `seed_builtin(env,:nat,…)`; wired into `seed/2` | `lib/cure/core/builtins.ex:20,254,313,132` |
| Literal typing | `infer({:nat_lit,n})` → `nat_type_value(sig)` | `lib/cure/core/kernel.ex:69` |
| Compact value + fold | `{:vnat,n}`; `nat_to_ctor/1`, `nat_to_ctor_if/1` (peel one layer) | `lib/cure/core/eval.ex:71,244-252` |
| ι-sites the fold wires into | `eval`'s `:case` (line 119), `Normalise`'s two `ncase` arms, `Conv` | `eval.ex:119`, `normalise.ex`, `conv.ex` |
| Conversion bridge (lit↔ctor) | `unify_one({:nat_lit},{:ctor})` via `nat_lit_ctor/1` | `kernel.ex:1349-1356,1539` |
| Codegen — ctor lowering | `nat_ctor?`; `Z`→0, `S(n)`→`n+1` | `lib/cure/elab/emit.ex:476,1079` |
| Codegen — case lowering | `nat_branch_clause`; `Z`→literal 0, `S`→guarded `N>0`, bind `k=N-1` | `emit.ex:958,906` |

**Key divergence from `Nat`:** `Int` has **two 1-ary constructors**, so arity cannot disambiguate them at codegen (unlike `Nat`'s 0-ary `Z` / 1-ary `S`). Every codegen hook must be **name-keyed**, not arity-keyed (spec §3.4). And the fold is **single-step** (no recursive peel — `Int` has only the two outermost constructors, whose fields are already compact `Nat`).

The literal↔constructor correspondence (the TCB contract):

```
FromNat({:nat_lit, k})            ⇓  {:int_lit, k}          # k ≥ 0
NegativeSuccessor({:nat_lit, k})  ⇓  {:int_lit, -(k+1)}     # -1, -2, …
# eliminator on {:int_lit, n}:
#   n ≥ 0  →  FromNat            arm, field bound to {:nat_lit, n}
#   n < 0  →  NegativeSuccessor  arm, field bound to {:nat_lit, -n-1}
```

## File structure

- **`lib/cure/core/builtins.ex`** — add the `:int` schema, `int_family`/`int_ctors`, `seed_builtin(:int)` clause, wire into `seed/2` after `:nat`; later (Task 4) remove `Int` from `seed_primitives` and repoint `seed_ops`'s int domain to the data type.
- **`lib/cure/core/eval.ex`** — add `int_to_ctor/1` + `int_to_ctor_if/1`; route the `:case` scrutinee through it.
- **`lib/cure/core/normalise.ex`** — route both `ncase` ι-arms through `int_to_ctor_if`.
- **`lib/cure/core/conv.ex`** — literal-vs-constructor conversion-checking (the soundness-critical defeq site).
- **`lib/cure/core/kernel.ex`** — `unify_one` `{:int_lit}`↔`{:ctor}` bridge (`int_lit_ctor/1`); (Task 4) repoint `infer({:int_lit})` typing and `rigid_index?`.
- **`lib/cure/elab/emit.ex`** — new name-keyed `int_ctor?` + ctor lowering + `int_branch_clause`.
- **`lib/std/int.cure`** — flip `@builtin(:int) primitive Int` → `type Int = FromNat(Nat) | NegativeSuccessor(Nat)`.
- **Repoint cohort (Task 4, `{:int_type}`/`{:vint_type}` special-cases):** `kernel.ex`, `eval.ex`, `conv.ex`, `meta_check.ex`, `printer.ex`, `quote.ex`, `serialize.ex`, `term.ex`, `value.ex`, `declarations.ex`, `implementation.ex`, `resolve.ex`, `unify.ex`, `union.ex`, `subst.ex`, `guard_lint.ex`, `elaborator.ex` (confirmed live hits via `grep -rn "int_type\|vint_type" lib/cure/core lib/cure/elab | grep -v int_lit`: 18 files total in `lib/cure/core`+`lib/cure/elab`, including `builtins.ex` handled separately above via its own dedicated repoint-contract items — `validator.ex`, `certificate.ex`, and `totality_closure.ex` currently have ZERO hits, so they are dropped from this list; re-grep at Task-4 time regardless, since the tree will have moved). **Note:** `eval.ex:70` (`eval({:int_type},_env) -> {:vint_type}`) and `conv.ex:90,255` (`conv_struct?({:vint_type},{:vint_type},...)`, `same_value_no_delta?({:vint_type},{:vint_type},...)`) are genuine repoint targets distinct from Task 2's work in those same files — Task 2 only adds the `int_to_ctor` peel/defeq machinery, it does not retire these `{:int_type}`/`{:vint_type}` type-node clauses. Do not assume Task 2 already covered them.
- **`lib/std/proof_int_math.cure`, `lib/std/nat.cure`** — doc-comment refresh only (Task 5, §6).
- **Tests:** `test/cure/core/int_family_test.exs`, `test/cure/core/int_fold_test.exs`, `test/cure/elab/int_codegen_test.exs`, `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_inductive.{cure,idr}`, plus Phase-2 probes.

---

# PHASE 1 — Substrate

**Phase-1 deliverable:** `match`/induction on `Int` works, and the full existing suite is byte-identically green. Tasks 1–3 are **purely additive** (the new family/fold/codegen fire only on `FromNat`/`NegativeSuccessor`, which no existing program produces), so each ends with the suite green *without touching the primitive path*. Task 4 is the single atomic surface flip. Task 5 proves the substrate and refreshes stale docs.

### Task 1: Register the `Int` inductive family (dormant, alongside the primitive)

**Files:**
- Modify: `lib/cure/core/builtins.ex` (`@schemas`, add `int_family`/`int_ctors`, `seed_builtin(:int)` clause, wire into `seed/2`)
- Test: `test/cure/core/int_family_test.exs`

**Interfaces:**
- Produces: `Cure.Core.Inductive.builtin(env, :int)` returns the `Std.Int#Int` family id after `Builtins.seed/2`; its constructors are `FromNat(Nat)` and `NegativeSuccessor(Nat)`, validated by `Builtins.validate!(env, :int, fid)`.
- Consumes: the existing `Nat` family must be seeded first (Int's ctor fields reference `Nat`).

**Design note:** This task is additive — `Int` stays in `seed_primitives` too for now (surface `Int` still resolves to `{:int_type}`). The family is registered but unused by the surface, so the suite stays green. The primitive→inductive flip is Task 4.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/int_family_test.exs
defmodule Cure.Core.IntFamilyTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Env, Inductive}

  test "seed registers the Int inductive family with FromNat/NegativeSuccessor" do
    env = Builtins.seed(Env.new())
    fid = Inductive.builtin(env, :int)
    assert fid != nil
    assert :ok == Builtins.validate!(env, :int, fid)

    names =
      env
      |> Inductive.ctors_of(fid)
      |> Enum.map(fn c -> Cure.Elab.Name.base(c.name) end)
      |> Enum.sort()

    assert names == ["FromNat", "NegativeSuccessor"]
  end
end
```

- [ ] **Step 2: Run it to verify it fails**

Run: `mix test test/cure/core/int_family_test.exs`
Expected: FAIL — `Inductive.builtin(env, :int)` returns `nil` (no `:int` schema/seed yet).

- [ ] **Step 3: Add the schema**

In `lib/cure/core/builtins.ex`, add to the `@schemas` map (after the `bounded:` entry), keeping the "names are load-bearing" contract:

```elixir
    # Int : Type0 = FromNat(Nat) | NegativeSuccessor(Nat). Both constructors are
    # 1-ary (each field is a Nat), so — unlike Nat's Z/S — arity cannot
    # disambiguate them; every literal/erasure hook that keys off Int is
    # NAME-keyed, not arity-keyed. FromNat(n) = n; NegativeSuccessor(n) = -(n+1).
    int: [{:FromNat, 1}, {:NegativeSuccessor, 1}]
```

- [ ] **Step 4: Add the family/ctor descriptors**

In `lib/cure/core/builtins.ex`, after `nat_ctors/1` (around line 319), add — mirroring `nat_family`/`nat_ctors`, with both fields referencing the `Nat` family:

```elixir
  # Int : Type0 = FromNat(Nat) | NegativeSuccessor(Nat). Both fields reference the
  # Nat family (like S's field references Nat). Source of truth is the
  # @builtin(:int) decl in Std.Int (lib/std/int.cure); this seed is its
  # byte-for-byte mirror, pinned by the conformance drift harness.
  defp int_family(env), do: Inductive.family(Env.owned_name(env, :Int), [], [], 0)

  defp int_ctors(env),
    do: [
      Inductive.ctor(Env.owned_name(env, :FromNat), [{:n, {:data, Env.owned_name(env, :Nat), [], []}}], []),
      Inductive.ctor(
        Env.owned_name(env, :NegativeSuccessor),
        [{:n, {:data, Env.owned_name(env, :Nat), [], []}}],
        []
      )
    ]
```

- [ ] **Step 5: Add the `seed_builtin(:int)` clause and wire it into `seed/2`**

In `lib/cure/core/builtins.ex`, add a clause next to the other `seed_builtin(env, key, exclude)` clauses (after the `:list` clause, before the generic `seed_builtin(env, key, family, ctors, exclude)` fallthrough):

```elixir
  defp seed_builtin(env, :int, exclude),
    do:
      seed_builtin(
        env,
        :int,
        int_family(Env.with_owner(env, "Std.Int")),
        int_ctors(Env.with_owner(env, "Std.Int")),
        exclude
      )
```

Then in `seed/2` (line 128), add `|> seed_builtin(:int, exclude)` **after** `seed_builtin(:nat, exclude)` and before `seed_ops()` (Int's ctors reference `Nat`, and `seed_ops` will later read the Int family):

```elixir
    env
    |> seed_builtin(:bool, exclude)
    |> seed_builtin(:nat, exclude)
    |> seed_builtin(:int, exclude)
    |> seed_builtin(:eq, exclude)
    |> seed_builtin(:sigma, exclude)
    |> seed_builtin(:list, exclude)
    |> seed_ops()
    |> seed_primitives()
```

- [ ] **Step 6: Run the new test to verify it passes**

Run: `mix test test/cure/core/int_family_test.exs`
Expected: PASS.

- [ ] **Step 7: Run the full suite (back-compat gate)**

Run: `mix test`
Expected: PASS, byte-identical to baseline. The family is registered but unused by the surface (Int still primitive-seeded), so nothing changes. If any conformance/drift test now expects the `@builtin(:int)` decl in `lib/std/int.cure` and fails because that file is still `primitive Int`, that pin is asserting the Task-4 end state — note it and defer the drift-pin fix to Task 4 (do NOT flip int.cure yet). If any *non-drift* test regresses, that is a Halt (the additive seed changed a judgement it shouldn't have).

- [ ] **Step 8: Commit**

```bash
git add lib/cure/core/builtins.ex test/cure/core/int_family_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(core): register dormant Int inductive family (FromNat/NegativeSuccessor)"
```

---

### Task 2: `int_to_ctor` fold + conversion bridge (dormant)

**Files:**
- Modify: `lib/cure/core/eval.ex` (add `int_to_ctor/1`, `int_to_ctor_if/1`; route `:case`)
- Modify: `lib/cure/core/normalise.ex` (route both `ncase` ι-arms)
- Modify: `lib/cure/core/conv.ex` (literal-vs-ctor conversion)
- Modify: `lib/cure/core/kernel.ex` (`unify_one` `{:int_lit}`↔`{:ctor}` bridge via `int_lit_ctor/1`)
- Test: `test/cure/core/int_fold_test.exs`

**Interfaces:**
- Consumes: the `Int` family from Task 1; the existing `{:vint, n}` compact value (`eval.ex:71`) and `{:int_lit, n}` term.
- Produces: `Cure.Core.Eval.int_to_ctor_if({:vint, n})` peels to `{:vctor, :FromNat, [{:vnat, n}]}` for `n ≥ 0` and `{:vctor, :NegativeSuccessor, [{:vnat, -n-1}]}` for `n < 0`; `{:int_lit, n}` is definitionally equal to the corresponding explicit constructor term at every conversion/ι site.

**Design note:** Still additive. The fold fires only when a `{:vint}`/`{:int_lit}` meets a `FromNat`/`NegativeSuccessor` constructor or a `:case` with those arms — which no existing program produces. Existing arithmetic (`{:vint}` op `{:vint}`) is untouched.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/int_fold_test.exs
defmodule Cure.Core.IntFoldTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Eval

  test "int_to_ctor_if peels a nonneg compact Int to FromNat" do
    assert Eval.int_to_ctor_if({:vint, 3}) == {:vctor, :FromNat, [{:vnat, 3}]}
    assert Eval.int_to_ctor_if({:vint, 0}) == {:vctor, :FromNat, [{:vnat, 0}]}
  end

  test "int_to_ctor_if peels a negative compact Int to NegativeSuccessor" do
    assert Eval.int_to_ctor_if({:vint, -1}) == {:vctor, :NegativeSuccessor, [{:vnat, 0}]}
    assert Eval.int_to_ctor_if({:vint, -4}) == {:vctor, :NegativeSuccessor, [{:vnat, 3}]}
  end

  test "int_to_ctor_if passes non-Int values through unchanged" do
    assert Eval.int_to_ctor_if({:vnat, 2}) == {:vnat, 2}
    assert Eval.int_to_ctor_if({:vneutral, {:nvar, 0}}) == {:vneutral, {:nvar, 0}}
  end

  test "case on a compact Int selects the matching constructor arm" do
    # case {:vint, 5} of FromNat(n) -> n | NegativeSuccessor(n) -> n
    # (body {:var,0} returns the bound field)
    branches = [{:FromNat, 1, {:var, 0}}, {:NegativeSuccessor, 1, {:var, 0}}]
    scrut = {:int_lit, 5}
    assert Eval.eval({:case, scrut, {:var, 0}, branches}, []) == {:vnat, 5}

    scrut_neg = {:int_lit, -2}
    assert Eval.eval({:case, scrut_neg, {:var, 0}, branches}, []) == {:vnat, 1}
  end
end
```

- [ ] **Step 2: Run it to verify it fails**

Run: `mix test test/cure/core/int_fold_test.exs`
Expected: FAIL — `Eval.int_to_ctor_if/1` is undefined.

- [ ] **Step 3: Add `int_to_ctor`/`int_to_ctor_if` to `eval.ex`**

In `lib/cure/core/eval.ex`, after `nat_to_ctor_if/1` (line 252), add the single-step Int peel (no recursive peel — `Int`'s fields are already compact `Nat`):

```elixir
  # -- compact Int peeling ----------------------------------------------------

  # Map a compact Int literal to its FromNat/NegativeSuccessor constructor value.
  # Unlike nat_to_ctor (which peels ONE S layer, leaving a compact predecessor),
  # this is SINGLE-STEP: Int has exactly two outermost constructors, each with a
  # single compact-Nat field. This is the one audited literal→constructor mapping
  # for Int (Lean's Int.ofNat/negSucc, @[extern]-backed). SOUND only because BEAM
  # integers are arbitrary-precision (see Std.Int module doc): the inductive ℤ is
  # unbounded and native bignums never wrap.
  #   FromNat(n)           = n            (n ≥ 0)
  #   NegativeSuccessor(n) = -(n + 1)     (-1, -2, …)
  @doc false
  def int_to_ctor({:vint, n}) when is_integer(n) and n >= 0, do: {:vctor, :FromNat, [{:vnat, n}]}
  def int_to_ctor({:vint, n}) when is_integer(n) and n < 0, do: {:vctor, :NegativeSuccessor, [{:vnat, -n - 1}]}

  @doc false
  def int_to_ctor_if({:vint, _} = int), do: int_to_ctor(int)
  def int_to_ctor_if(value), do: value
```

- [ ] **Step 4: Route the `:case` scrutinee through the Int peel**

In `lib/cure/core/eval.ex`, the `:case` handler (line 119) currently does `case nat_to_ctor_if(eval(scrut, env)) do`. A `{:vint}` scrutinee is not a `{:vnat}`, so `nat_to_ctor_if` passes it through and it falls to the `other ->` raise. Compose the Int peel with the Nat peel so a `{:vint}` scrutinee reaches the shared `{:vctor, …}` ι-logic. Change the scrutinee normalisation to:

```elixir
    case int_to_ctor_if(nat_to_ctor_if(eval(scrut, env))) do
```

(`int_to_ctor_if` is a no-op on the `{:vnat}`/`{:vbounded}`/neutral forms the other arms handle, and `nat_to_ctor_if` is a no-op on `{:vint}`, so the two compose without interfering. The peeled `{:vctor, :FromNat/:NegativeSuccessor, [{:vnat,_}]}` then flows into the existing `{:vctor, cname, args}` arm, which finds the branch and calls `reduce_branch_body`.)

- [ ] **Step 5: Route `Normalise`'s two `ncase` ι-arms**

In `lib/cure/core/normalise.ex`, find the two sites (`normalise.ex:279` and `normalise.ex:321`) that peel a compact scrutinee to constructor form. **Both currently read `Eval.bounded_to_ctor_if(Eval.nat_to_ctor_if(whnf_value({:vneutral, scrut}, sig, opts)))` — a TWO-fold compose (Nat then Bounded), not just `nat_to_ctor_if` alone.** Wrap that existing expression with the Int peel on the OUTSIDE, preserving both existing folds — the correct three-way compose is:

```elixir
case Eval.int_to_ctor_if(Eval.bounded_to_ctor_if(Eval.nat_to_ctor_if(whnf_value({:vneutral, scrut}, sig, opts)))) do
```

**Do NOT drop `Eval.bounded_to_ctor_if` from this expression** — `int_to_ctor_if`/`bounded_to_ctor_if`/`nat_to_ctor_if` are no-ops outside their own value shape (`{:vint}`/`{:vbounded}`/`{:vnat}` respectively), so composing all three is safe and order-independent, but omitting `bounded_to_ctor_if` would silently stop peeling `{:vbounded}` scrutinees in both `ncase` arms — a real regression (breaks `case`-on-`Bounded`/`Char` reduction through `Normalise`, e.g. a stuck global unfold with a Bounded/Char scrutinee), not an additive change. Do NOT add a new `case` arm — reuse the existing `{:vctor, …}` handling downstream.

- [ ] **Step 6: Route `Conv` (the soundness-critical defeq site)**

In `lib/cure/core/conv.ex`, find where `nat_to_ctor_if` (or the equivalent literal-vs-explicit-ctor conversion) is applied (spec cites `conv.ex:107,110`). Apply `Eval.int_to_ctor_if` at the same points so `{:vint, n}` and the explicit `FromNat`/`NegativeSuccessor` constructor value are judged defeq. This is what makes constructor, eliminator, and literal mutually defeq for `Int`. Mirror the `Nat` spelling precisely.

- [ ] **Step 7: Add the `unify_one` literal↔ctor bridge in `kernel.ex`**

In `lib/cure/core/kernel.ex`, next to the `{:nat_lit}` bridge (lines 1349-1356) and `nat_lit_ctor/1` (line 1539), add the Int analog so an `{:int_lit, n}` *index* unifies with an explicit constructor term during index unification:

```elixir
  defp unify_one({:int_lit, a}, {:int_lit, b}, _arity, subst),
    do: if(a == b, do: {:ok, subst}, else: :nomatch)

  defp unify_one({:int_lit, n}, {:ctor, _, _} = s, arity, subst),
    do: unify_one(int_lit_ctor(n), s, arity, subst)

  defp unify_one({:ctor, _, _} = r, {:int_lit, n}, arity, subst),
    do: unify_one(r, int_lit_ctor(n), arity, subst)
```

and the term-level expansion helper next to `nat_lit_ctor/1`:

```elixir
  defp int_lit_ctor(n) when is_integer(n) and n >= 0, do: {:ctor, :FromNat, [{:nat_lit, n}]}
  defp int_lit_ctor(n) when is_integer(n) and n < 0, do: {:ctor, :NegativeSuccessor, [{:nat_lit, -n - 1}]}
```

Place these clauses so they do not shadow the existing catch-all `unify_one` clauses (same relative position as the `{:nat_lit}` clauses — before the generic fallthrough).

- [ ] **Step 8: Run the new test to verify it passes**

Run: `mix test test/cure/core/int_fold_test.exs`
Expected: PASS.

- [ ] **Step 9: Run the full suite (back-compat gate)**

Run: `mix test`
Expected: PASS, byte-identical. The fold/bridge fire only on `FromNat`/`NegativeSuccessor`/`{:int_lit}`-vs-`{:ctor}`, none of which existing programs produce. Any regression on an existing program is a Halt.

- [ ] **Step 10: Commit**

```bash
git add lib/cure/core/eval.ex lib/cure/core/normalise.ex lib/cure/core/conv.ex \
        lib/cure/core/kernel.ex test/cure/core/int_fold_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(core): audited int_to_ctor fold + literal↔ctor conversion bridge"
```

---

### Task 3: Codegen — name-keyed `int_ctor?` + `int_branch_clause` (dormant)

**Files:**
- Modify: `lib/cure/elab/emit.ex` (add `int_ctor?`, ctor-lowering branch, `int_branch_clause`; wire into `lower({:ctor})` and `branch_clause`)
- Test: `test/cure/elab/int_codegen_test.exs`

**Interfaces:**
- Consumes: the `Int` family (Task 1); `Inductive.builtin(env, :int)`, `Inductive.ctor_family(env, name)` (same registry lookups `nat_ctor?` uses).
- Produces: an **open** `FromNat(n)` lowers to `lower(n)` (identity, no `+1`); `NegativeSuccessor(n)` lowers to `-(lower(n)+1)`; a `case`-on-`Int` lowers to two guarded Erlang clauses (`FromNat`: `N >= 0`, bind field `= N`; `NegativeSuccessor`: `N < 0`, bind field `= -N-1`).

**Design note:** Both constructors are 1-ary, so dispatch is by **constructor name**, not arity (spec §3.4). A **closed** application already folds to `{:int_lit,_}` before emit (Task 2), so this path is only exercised by open constructor terms — which nothing produces until Task 5's smoke-test. Still additive.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/int_codegen_test.exs
defmodule Cure.Elab.IntCodegenTest do
  use ExUnit.Case, async: true

  # End-to-end: compile a tiny module that uses the Int constructors on an OPEN
  # argument (cannot fold at compile time), run it, assert native-integer parity.
  # Uses the project's standard compile+run harness (mirror the one nat codegen
  # tests use — grep test/elab for the existing Nat erasure test and copy its
  # `compile_and_run/2` helper spelling).
  test "open FromNat(n) lowers to the identity native integer" do
    src = """
    @group(:core)
    mod IntCodegenProbe
      use Std.Nat
      use Std.Int
      fn to_int(n: Nat) -> Int = FromNat(n)
      fn neg1(n: Nat) -> Int = NegativeSuccessor(n)
      fn start() -> Int = to_int(S(S(Z())))   # FromNat(2) => 2
    end
    """

    assert run_start(src) == 2
  end

  test "case-on-Int dispatches by sign at runtime" do
    src = """
    @group(:core)
    mod IntCaseProbe
      use Std.Nat
      use Std.Int
      fn magnitude(i: Int) -> Nat =
        match i
          FromNat(n) -> n
          NegativeSuccessor(n) -> S(n)
      fn start() -> Nat = magnitude(NegativeSuccessor(S(S(Z()))))  # -(3) => magnitude 3
    end
    """

    assert run_start(src) == 3
  end

  # Replace `run_start/1` with the repo's canonical compile-a-source-string-and-
  # invoke-start helper. If none exists in test/elab, add a thin wrapper over the
  # same pipeline `phase35/run-on-unix.sh` drives, or over the elaborator+emit+
  # :erlang evaluation the existing emit tests use. Do NOT weaken the assertions.
end
```

- [ ] **Step 2: Run it to verify it fails**

Run: `mix test test/cure/elab/int_codegen_test.exs`
Expected: FAIL — open `FromNat(n)` hits the generic tagged-tuple `true ->` arm of `lower({:ctor})` (emit.ex:511) and emits `{FromNat, N}` instead of a native integer; `magnitude` fails to match.

- [ ] **Step 3: Add the name-keyed `int_ctor?` predicate**

In `lib/cure/elab/emit.ex`, after `nat_ctor?/2` (line 1082), add:

```elixir
  # The canonical Std.Int family (registry-keyed, nominal): its values are native
  # BEAM machine integers (spec 2026-07-18-inductive-int). Both constructors are
  # 1-ary, so — unlike Nat's Z/S — the erasure MUST key off the constructor NAME:
  #   FromNat(n)           -> n            (identity, no +1)
  #   NegativeSuccessor(n) -> -(n + 1)
  # A locally-redeclared structural twin has a different family-id and keeps tuples.
  defp int_ctor?(env, name) do
    fam = Inductive.builtin(env, :int)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end
```

- [ ] **Step 4: Add the ctor-lowering branch (name-keyed)**

In `lib/cure/elab/emit.ex`, in the `lower(env, {:ctor, name, args}, ctx)` `cond` (line 471), add a branch **before** the `true ->` fallthrough, dispatching on `base_name(name)`:

```elixir
      int_ctor?(env, name) ->
        [n] = args
        case base_name(name) do
          :FromNat -> lower(env, n, ctx)
          :NegativeSuccessor ->
            {:op, @line, :-, {:op, @line, :-, {:integer, @line, 0}, lower(env, n, ctx)}, {:integer, @line, 1}}
        end
```

(`NegativeSuccessor(n)` = `-(n+1)` = `0 - n - 1`; expressed as nested `:-` BEAM ops. Equivalently emit `{:op, :-, {:op, :-, {integer,0}, N}, {integer,1}}`. Keep the arithmetic explicit and native.)

- [ ] **Step 5: Add `int_branch_clause` (guarded, sign-dispatched)**

In `lib/cure/elab/emit.ex`, after `nat_branch_clause/3` (line 970), add — mirroring `nat_branch_clause` but with a **sign guard per constructor name** (both arms match a bare variable `N`; the guards `N >= 0` / `N < 0` are mutually exclusive and exhaustive over ℤ):

```elixir
  # case-on-Int: the runtime scrutinee is a native BEAM integer. FromNat(n) matches
  # any N with guard `N >= 0`, binding the field n = N (identity — no `-1`, unlike
  # Nat's S). NegativeSuccessor(n) matches any N with guard `N < 0`, binding the
  # field n = -N - 1 (since NegativeSuccessor(n) = -(n+1)). Erlang patterns/guards
  # cannot compute-and-bind, so the field binding opens the body as its first form.
  # The body's de Bruijn frame counts the single field (index 0), exactly as the
  # tuple form would have bound it. Guards are mutually exclusive, so clause order
  # follows source-arm order.
  defp int_branch_clause(env, {name, 1, body}, ctx) do
    n_var = fresh_var("N")
    field = fresh_var("V")
    body_form = lower(env, body, [field | ctx])
    field_pat = underscore_if_unused({:var, @line, field}, body_form)

    {guard_cmp, field_expr} =
      case base_name(name) do
        :FromNat ->
          {:>=, {:var, @line, n_var}}

        :NegativeSuccessor ->
          # field = -N - 1
          {:<, {:op, @line, :-, {:op, @line, :-, {:integer, @line, 0}, {:var, @line, n_var}}, {:integer, @line, 1}}}
      end

    guard = [[{:op, @line, guard_cmp, {:var, @line, n_var}, {:integer, @line, 0}}]]
    bind = {:match, @line, field_pat, field_expr}
    {:clause, @line, [{:var, @line, n_var}], guard, [bind, body_form]}
  end
```

Then wire it into `branch_clause/3` (line 904), before the `true ->` generic arm:

```elixir
      int_ctor?(env, cname) -> int_branch_clause(env, {cname, arity, body}, ctx)
```

- [ ] **Step 6: Run the new test to verify it passes**

Run: `mix test test/cure/elab/int_codegen_test.exs`
Expected: PASS — `to_int(2)` yields `2`; `magnitude(-3)` yields `3`.

- [ ] **Step 7: Run the full suite (back-compat gate)**

Run: `mix test`
Expected: PASS, byte-identical. New codegen fires only on `FromNat`/`NegativeSuccessor`, unused by existing programs. Regression on existing programs = Halt.

- [ ] **Step 8: Commit**

```bash
git add lib/cure/elab/emit.ex test/cure/elab/int_codegen_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(emit): name-keyed Int ctor lowering + sign-guarded case-on-Int"
```

---

### Task 4: The surface flip — `Int` becomes inductive (atomic green-to-green)

**Files:**
- Modify: `lib/std/int.cure` (flip `primitive` → inductive family)
- Modify: `lib/cure/core/builtins.ex` (remove `Int` from `seed_primitives`; repoint `seed_ops` int domain to the Int data type)
- Modify: `lib/cure/core/kernel.ex` (`infer({:int_lit})` typing → Int data type; `infer({:int_type})`, `rigid_index?` — see repoint contract)
- Modify the **repoint cohort** (re-grep first — do not trust this static list): `eval.ex` (line 70: `eval({:int_type},_env) -> {:vint_type}`), `conv.ex` (lines 90, 255: `conv_struct?`/`same_value_no_delta?` on `{:vint_type}` — a distinct site from Task 2's `int_to_ctor` defeq additions in this same file), `meta_check.ex`, `printer.ex`, `quote.ex`, `serialize.ex`, `term.ex`, `value.ex`, `declarations.ex`, `implementation.ex`, `resolve.ex`, `unify.ex`, `union.ex`, `subst.ex`, `guard_lint.ex`, `elaborator.ex` (confirmed live hits as of plan-hardening time; `validator.ex`, `certificate.ex`, `totality_closure.ex` had zero `int_type`/`vint_type` hits and were dropped — re-grep may still turn up new hits if those files changed since)
- Test: reuses the full suite as the gate; add `test/cure/core/int_surface_test.exs`

**Interfaces:**
- Consumes: everything from Tasks 1–3 (family, fold, codegen all in place).
- Produces: surface `Int` in any signature elaborates to `{:data, int_family_id, [], []}` (as `Nat` does); `{:int_lit, n} : Int` via `infer` returning the Int data-type value; `match i` on `i : Int` is coverage-checked against `FromNat`/`NegativeSuccessor`.

**This is the one risky task.** Tasks 1–3 built and tested the substrate dormant; this task redirects the surface onto it. The back-compat gate (byte-identical suite) is the arbiter of every repoint decision.

**Repoint contract (apply to every `{:int_type}`/`{:vint_type}` site):** `Nat` has **no** `{:nat_type}` node — its type is just `{:data, nat_fid, [], []}`. Mirror that. For each site currently special-casing `{:int_type}`/`{:vint_type}`:
1. **Literal typing** (`kernel.ex:63`, `infer({:int_lit,n})` → `{:vint_type}`): change to return the Int data-type value, via a new `int_type_value(sig)` helper mirroring `nat_type_value/1` (`kernel.ex:1691`). Add `int_type_value/1` right beside `nat_type_value/1`.
2. **Type-of-`Int`** (`kernel.ex:62`, `infer({:int_type})` → `{:vtype,0}`; `infer_type_value_sort({:vint_type})` → `0`): once the surface no longer produces `{:int_type}`, these become dead. **Preferred (faithful, spec §3a(i)):** retire `{:int_type}`/`{:vint_type}` nodes — remove their `term?`/`shift`/`subst`/`to_external`/`from_external` clauses (`term.ex:81,131,177,260,350,400`), `value.ex:63,86`, `eval.ex:70`, `conv.ex:90,255` (`conv_struct?`/`same_value_no_delta?`), and every special-case in the cohort, so `Int`'s only spelling is the data family. **Fallback (facade, spec §3a(ii)):** if retiring a given node's clause breaks a serialization/printer round-trip the back-compat gate flags, KEEP that node as an internal alias defeq to `{:data, int_fid, [], []}` at that seam and **record the fallback in a `# NOTE(int-facade):` comment + AUTOPILOT-STATE.md**. Per-site decision; a mixed outcome is acceptable if recorded.
3. **`rigid_index?`** (`kernel.ex:1522,1527`): `{:int_type}` and `{:int_lit,_}` are rigid. Keep `{:int_lit,_}` rigid (still a canonical literal). If `{:int_type}` is retired, drop its clause; the data type is already rigid via the existing `{:data,…}` handling.
4. **`seed_ops` int domain** (`builtins.ex:165`): the `@int_binops`/`@int_unops` domain is `{:int_type}`. Change it to the Int data-type value computed from the registry, mirroring how `bool_ty`/`bool_family_id/1` (line 188) snapshots the Bool family. Add an `int_ty`/`int_family_id/1` helper and pass `int_ty` as the `dom` to `seed_binops(@int_binops, int_ty, bool_ty)` and `seed_unops(@int_unops, int_ty)`. **Ordering:** `seed_ops` runs after `seed_builtin(:int)` in `seed/2`, so the family is registered when `int_family_id` snapshots it — verify. Guard the same `nil`-under-`exclude` scenario `bool_family_id/1` guards (a module declaring its own `Int`): fall back to the owned family name.
5. **Remove from `seed_primitives`** (`builtins.ex:146`): delete the `|> Env.put_primitive("Int", {:int_type})` line. `Float`/`Binary`/`Atom` stay.
6. **The cohort's `canonical_head?`/`head_atom`/`head_type_core`/`member_key`/`class_of_core`/`escapes?`/`primitive_tag_node`/printer/quote/serialize clauses:** each either (a) is repointed to recognize `{:data, int_fid, …}` where it recognized `{:int_type}` — usually already handled by the site's existing generic `{:data,…}` clause, so the `{:int_type}` clause becomes dead and is removed — or (b) keeps an alias per the fallback in (2). Re-grep `int_type|vint_type` in each cohort file and resolve every hit.

- [ ] **Step 1: Re-grep the live cohort (do not trust a stale list)**

Run: `grep -rn "int_type\|vint_type" lib/cure/core lib/cure/elab | grep -v "int_lit"`
Record every hit. This is the exhaustive worklist for the repoint. (`{:int_lit}` sites are excluded — the literal node stays.)

- [ ] **Step 2: Write the failing surface test**

```elixir
# test/cure/core/int_surface_test.exs
defmodule Cure.Core.IntSurfaceTest do
  use ExUnit.Case, async: true

  test "surface Int resolves to the inductive data family, and match on Int type-checks" do
    src = """
    @group(:core)
    mod IntSurfaceProbe
      use Std.Nat
      use Std.Int
      fn sign(i: Int) -> Nat =
        match i
          FromNat(n) -> S(Z())
          NegativeSuccessor(n) -> Z()
      fn start() -> Nat = sign(FromNat(Z()))
    end
    """
    # Elaborates cleanly (coverage-checked over FromNat/NegativeSuccessor) and runs.
    assert run_start(src) == 1  # sign(0) = 1
  end

  test "existing Int arithmetic still type-checks and folds byte-identically" do
    src = """
    @group(:core)
    mod IntArithProbe
      use Std.Int
      fn start() -> Int = 2 + 3 * 4    # stays {:int_lit, 14}
    end
    """
    assert run_start(src) == 14
  end
end
```

- [ ] **Step 3: Run it to verify it fails**

Run: `mix test test/cure/core/int_surface_test.exs`
Expected: the `match`-on-`Int` case FAILS — `Int` still resolves to the primitive `{:int_type}`, which has no constructors, so `match i` is rejected (non-inductive / no coverage). The arithmetic case may already pass.

- [ ] **Step 4: Flip `lib/std/int.cure`**

```cure
@group(:core)
@prelude
mod Std.Int
  ## Canonical inductive integer, native at runtime.
  ##
  ## `Int` is an inductive built on `Nat`: `FromNat(n) = n` and
  ## `NegativeSuccessor(n) = -(n + 1)`. It is CANONICAL (every integer has exactly
  ## one representation; zero is only `FromNat(Z())`), so structural equality is
  ## decidable. The compact literal `5`/`-3` is definitionally equal to the
  ## corresponding constructor spine via the audited `int_to_ctor` fold, and every
  ## value compiles to a native BEAM machine integer — arithmetic and bitwise ops
  ## remain builtin operators folding to native results.
  ##
  ## SOUNDNESS CAVEAT (load-bearing): the native↔inductive correspondence holds
  ## ONLY because BEAM integers are arbitrary-precision. The inductive ℤ is
  ## unbounded and BEAM bignums never wrap, so the native ops and the inductive
  ## semantics coincide on every value. On a FIXED-WIDTH target this fold would be
  ## UNSOUND (wraparound ≠ unbounded ℤ).
  use Std.Nat

  @prelude
  @builtin(:int)
  type Int = FromNat(Nat) | NegativeSuccessor(Nat)
```

- [ ] **Step 5: Apply the repoint contract**

Work the Step-1 worklist top to bottom. Do items in the order: (a) `builtins.ex` — remove from `seed_primitives`, add `int_type_value` usage and `int_ty` domain in `seed_ops`; (b) `kernel.ex` — `infer({:int_lit})` → `int_type_value(sig)`, add `int_type_value/1`, resolve `{:int_type}`/`rigid_index?`; (c) the remaining cohort files per the repoint contract §6. Compile frequently (`mix compile`) to catch dead-clause/unused-warning fallout early. Any node you keep as a facade alias gets a `# NOTE(int-facade):` comment.

- [ ] **Step 6: Run the surface test to verify it passes**

Run: `mix test test/cure/core/int_surface_test.exs`
Expected: PASS — both cases.

- [ ] **Step 7: Run the FULL suite — the byte-identical back-compat gate**

Run: `mix test`
Expected: PASS. This is the hard gate. Inspect every failure:
- A **drift/conformance** test that pins the `@builtin(:int)` decl equal to the programmatic seed should now pass (both are the inductive family) — if it *fails*, the `int_family`/`int_ctors` seed does not byte-match `lib/std/int.cure`; fix the seed to match the source (source is truth).
- An **oracle replay** or **existing-program** failure with output churn attributable to `Int` re-representation is a **Halt** (§5): the fold or family registration is wrong. Do not paper over.
- A **printer/serialize round-trip** failure points at a cohort site that needs the facade-alias fallback (repoint contract §2) — apply it, record it.

- [ ] **Step 8: Run the oracle replay explicitly**

Run: ``mix otp.oracle` in `cure-otp` && mix cure.oracle.replay` (use the repo's canonical replay task name — grep `mix.exs`/`lib/mix/tasks` if unsure). Expected: `rel=same` for every existing probe. Any `rel` change on an existing probe is a Halt.

- [ ] **Step 9: Commit**

```bash
git add lib/std/int.cure lib/cure/core/builtins.ex lib/cure/core/kernel.ex \
        lib/cure/core/term.ex lib/cure/core/value.ex lib/cure/core/eval.ex \
        lib/cure/core/conv.ex \
        lib/cure/core/meta_check.ex lib/cure/core/printer.ex lib/cure/core/quote.ex \
        lib/cure/core/serialize.ex \
        lib/cure/elab/declarations.ex lib/cure/elab/implementation.ex lib/cure/elab/resolve.ex \
        lib/cure/elab/unify.ex lib/cure/elab/union.ex lib/cure/elab/subst.ex \
        lib/cure/elab/guard_lint.ex lib/cure/elab/elaborator.ex \
        test/cure/core/int_surface_test.exs
# Stage only the cohort files you actually touched; drop any that had no int_type hit.
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(core): Int is now an inductive @builtin(:int) family (surface flip)"
```

---

### Task 5: Induction smoke-test, oracle probe, and doc-comment refresh

**Files:**
- Create: `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_inductive.cure`, `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_inductive.idr`
- Modify: `lib/std/int.cure` (add `negate` + the smoke-test lemma)
- Modify: `lib/std/proof_int_math.cure` (module-doc refresh — §6)
- Modify: `lib/std/nat.cure` (`of_int` doc refresh — §6)

**Interfaces:**
- Consumes: the inductive `Int` (Task 4).
- Produces: `Std.Int.negate/1` (`FromNat(Z)`→`FromNat(Z)`, `FromNat(S(k))`→`NegativeSuccessor(k)`, `NegativeSuccessor(k)`→`FromNat(S(k))`) and `negate_involutive` proved **by structural `match` on `Int`**, exercising the two constructors + defeq-to-literal end to end.

**Design note:** `negate` is defined so its involution proof is pure case analysis with clean ι-reduction in each arm (the spec's suggested `negate(negate(i)) = i`). This is the minimal genuine proof that the substrate enables induction/`match` + literal defeq. No arithmetic theory beyond it (that is Phase 2).

- [ ] **Step 1: Write the failing lemma in `lib/std/int.cure`**

Append to `lib/std/int.cure` (needs `use Std.Equivalent` for the identity type — mirror how `proof_math.cure`/other stdlib modules import it; grep for the exact `use` line):

```cure
  use Std.Equivalent

  ## Integer negation on the canonical representation.
  ##   negate(0)        = 0
  ##   negate(k+1)      = -(k+1)
  ##   negate(-(k+1))   = k+1
  fn negate(i: Int) -> Int =
    match i
      FromNat(n) ->
        match n
          Z() -> FromNat(Z())
          S(k) -> NegativeSuccessor(k)
      NegativeSuccessor(k) -> FromNat(S(k))

  ## Negation is an involution — proved by structural case analysis on `Int`
  ## (and, in the FromNat arm, on the inner `Nat`). Each arm reduces both sides to
  ## the same canonical form, discharged by reflexivity. This is the Phase-1
  ## smoke-test that `match`/induction and literal-defeq genuinely work on `Int`.
  fn negate_involutive(i: Int) -> Equivalent(Int, negate(negate(i)), i) =
    match i
      FromNat(n) ->
        match n
          Z() -> reflexive(FromNat(Z()))
          S(k) -> reflexive(FromNat(S(k)))
      NegativeSuccessor(k) -> reflexive(NegativeSuccessor(k))
```

- [ ] **Step 2: Compile to verify red→green on the lemma**

Run: `phase35/run-on-unix.sh Cure.Std.Int lib/std/int.cure` (or the repo's canonical stdlib-compile check — grep for how the suite compiles `lib/std`). Expected before the code exists: type error / unfilled obligation at `negate_involutive`. After: compiles clean (each arm's `reflexive` type-checks iff `negate(negate(arm)) ≡ arm` holds definitionally — which requires the `int_to_ctor` ι-rules from Task 2).

If any arm's `reflexive` does NOT type-check, the defeq is not firing — this is a substrate defect (Task 2), not a proof-weakening opportunity. Fix the fold, never the statement.

- [ ] **Step 3: Write the differential oracle probe**

```
# https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_inductive.cure  — mirror the .idr exactly (rel=same)
@group(:core)
mod IntInductive
  use Std.Nat
  use Std.Int
  fn magnitude(i: Int) -> Nat =
    match i
      FromNat(n) -> n
      NegativeSuccessor(n) -> S(n)
  fn start() -> Nat = magnitude(negate(FromNat(S(S(Z())))))   # negate(2) = -2, magnitude 2
```

```idris
-- https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_inductive.idr  — the Idris oracle (rel=same)
module IntInductive

data Nat' = Z | S Nat'
data Int' = FromNat Nat' | NegativeSuccessor Nat'

negate' : Int' -> Int'
negate' (FromNat Z)     = FromNat Z
negate' (FromNat (S k)) = NegativeSuccessor k
negate' (NegativeSuccessor k) = FromNat (S k)

magnitude : Int' -> Nat'
magnitude (FromNat n) = n
magnitude (NegativeSuccessor n) = S n

start : Nat'
start = magnitude (negate' (FromNat (S (S Z))))
```

(Match the repo's actual oracle-probe conventions — module naming, entry point, and how `.cure`/`.idr` outputs are compared. Grep `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/` for an existing paired probe and copy its shape exactly. The Cure side may use the real `Std.Int.negate`; the Idris side reproduces the same algorithm on a local mirror — that is the standard `rel=same` setup.)

- [ ] **Step 4: Run the oracle to verify the probe replays `rel=same`**

Run: ``mix otp.oracle` in `cure-otp`` then the replay task. Expected: `int_inductive` present with `rel=same`.

- [ ] **Step 5: Refresh the two stale doc-comments (§6, doc-only, no semantic change)**

In `lib/std/proof_int_math.cure`, the module doc (lines 3-10) asserts "`Int` is a primitive, not an inductive, so it admits no structural induction." Rewrite it to reflect reality: `IsTrue` remains the generic decidable-`Bool` reflector (Idris `So`) and the refinement-surface encoding — it does NOT depend on `Int` being primitive; with inductive `Int`, open arithmetic `IsTrue`-claims can additionally be discharged by induction (Phase 2). Do **not** change the `IsTrue`/`Confirmed`/`decide_is_true` definitions — semantics are untouched.

In `lib/std/nat.cure`, the `of_int` doc (lines 19-24) says "A primitive machine `Int` is not structurally well-founded, so this is an asserted FFI boundary." Rewrite: `of_int` remains the trusted clamp-to-`Z` FFI boundary — the inductive `Int` still has no upper bound and `of_int` still clamps negatives to `Z` — only the *reason* prose ("primitive machine `Int`") is stale. The `@extern` and behavior are unchanged.

- [ ] **Step 6: Full suite + oracle replay (Phase-1 definition of done)**

Run: `mix test` then ``mix otp.oracle` in `cure-otp`` + replay.
Expected: entire suite byte-identically green; `int_inductive` `rel=same`; every pre-existing probe still `rel=same`.

- [ ] **Step 7: Commit**

```bash
git add lib/std/int.cure lib/std/proof_int_math.cure lib/std/nat.cure \
        https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_inductive.cure https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_inductive.idr
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(std): negate + negate_involutive smoke-test; refresh stale Int-is-primitive docs"
```

**Phase 1 is now complete: `Int` is inductive, `match`/induction works, the smoke-test proves it, and the full suite is byte-identically green.**

---

# PHASE 2 — Ordered-ring lemma kit

**Phase-2 deliverable:** the reusable order/ring theory on `Int` — the shared dependency of the parked LIA checker and agent #4 — each an ordinary dependent proof, Idris-mirrored `rel=same`, suite green. This is genuine long-pole proof work; a proof wall the index-generalization inversion technique cannot route around is an **elaborator hard-stop → Halt** naming the exact stuck lemma (Phase 1 remains valid and useful regardless).

**Strategy (lowest-risk path):** express `Int` order by **reduction to the existing `Nat` order** in `Std.Proof.Math` (`IsLessThanOrEqual`/`IsLessThan` on `Nat`, with `adding_the_same_number_preserves_less_than_or_equal`, `less_than_or_equal_is_transitive`, `less_than_or_equal_is_reflexive` already proved, `proof_math.cure:120-148`). Define the `Int` order family + a total decision, and derive each `Int` lemma from its `Nat` counterpart. Reuse, don't re-derive.

**Naming (directive):** `IsLessThanOrEqual`, `IsLessThan`, `is_less_than_or_equal_is_reflexive`, `adding_preserves_order`, etc. — fully spelled out, mirroring `proof_math.cure`.

### Task 6: `Int` order family + reflexivity + decision

**Files:**
- Create: `lib/std/proof_int_order.cure` (module `Std.Proof.IntOrder`)
- Create: `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_order_refl.{cure,idr}`

**Interfaces:**
- Produces: `type IsLessThanOrEqual indices (left: Int, right: Int)`; `type IsLessThan indices (left: Int, right: Int)`; `fn is_less_than_or_equal_is_reflexive(value: Int) -> IsLessThanOrEqual(value, value)`; `fn decide_is_less_than_or_equal(left: Int, right: Int) -> Decision(IsLessThanOrEqual(left, right))`.
- Consumes: `Std.Int` (Task 5), `Std.Nat`, `Std.Proof.Math` (Nat order), `Std.Decision`.

**Design note on the family shape:** the robust encoding routes `Int` comparison through `Nat`. Concretely, define the family by cases on the two constructors so evidence for `FromNat`/`NegativeSuccessor` pairs reduces to `Nat`-order evidence (nonneg ≤ nonneg → `Nat` `IsLessThanOrEqual`; any negative ≤ any nonneg → immediate; negative ≤ negative → reversed `Nat` order on the successors; nonneg ≤ negative → uninhabited). Give each constructor of `IsLessThanOrEqual` a signature matching one of those four cases. If a direct inductive family proves intractable under the elaborator, fall back to the **reflected form** `IsTrue(le_int(a,b))` with a total `le_int : Int -> Int -> Bool` (spec §7 explicitly allows either) — record the choice.

- [ ] **Step 1: Write the failing reflexivity lemma**

```cure
@group(:core)
mod Std.Proof.IntOrder
  use Std.Nat
  use Std.Int
  use Std.Decision
  use Std.Proof.Math

  ## Evidence that one integer is ≤ another (four constructors, one per
  ## constructor-pair case; the negative/negative case reverses the Nat order on
  ## the successors, matching -(a+1) ≤ -(b+1) ⇔ b ≤ a).
  type IsLessThanOrEqual indices (left: Int, right: Int)
    NonNegAtMostNonNeg :
      IsLessThanOrEqual(FromNat(m), FromNat(n))   # requires evidence m ≤ n (Nat)
        -- refine to carry: (proof: Std.Proof.Math.IsLessThanOrEqual(m, n))
    NegBelowNonNeg :
      IsLessThanOrEqual(NegativeSuccessor(k), FromNat(n))
    NegAtMostNeg :
      IsLessThanOrEqual(NegativeSuccessor(a), NegativeSuccessor(b))
        -- requires evidence b ≤ a (Nat), reversed

  ## Reflexivity: every integer is ≤ itself.
  fn is_less_than_or_equal_is_reflexive(value: Int) -> IsLessThanOrEqual(value, value) =
    match value
      FromNat(n) -> NonNegAtMostNonNeg(less_than_or_equal_is_reflexive(n))
      NegativeSuccessor(k) -> NegAtMostNeg(less_than_or_equal_is_reflexive(k))
```

**Note to implementer:** the exact constructor argument syntax (carrying the `Nat`-order sub-proof as a field) must follow how `proof_math.cure` writes indexed-family constructors that carry sub-evidence (`SuccessorsAreLessThanOrEqual : IsLessThanOrEqual(left, right) -> IsLessThanOrEqual(S(left), S(right))`, `proof_math.cure:20`). Adjust the pseudo-syntax above to the real constructor-with-field form. This is design work to be finalized in-task; the signatures above are the target semantics.

- [ ] **Step 2: Compile to verify it fails, then implement to green**

Run the stdlib-compile check. Red = unfilled/ill-typed constructor or reflexivity arm. Green = compiles. Iterate on the family shape until reflexivity checks. If reflexivity cannot be made to check with a direct family after applying index-generalization inversion (memory: `index-generalization-inversion-technique`), switch to the reflected `IsTrue(le_int(...))` form and re-derive.

- [ ] **Step 3: Oracle probe + full suite**

Add `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_order_refl.{cure,idr}` (reflexivity applied to closed instances, e.g. `2 ≤ 2`, `-3 ≤ -3`), `rel=same`. Run `mix test` + oracle replay.

- [ ] **Step 4: Commit**

```bash
git add lib/std/proof_int_order.cure https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_order_refl.cure https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_order_refl.idr
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(std): Int order family + reflexivity + decision procedure"
```

### Task 7: Transitivity + add-monotonicity

**Files:**
- Modify: `lib/std/proof_int_order.cure`
- Create: `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_order_mono.{cure,idr}`

**Interfaces:**
- Produces: `fn is_less_than_or_equal_is_transitive({left},{middle},{right}, IsLessThanOrEqual(left,middle), IsLessThanOrEqual(middle,right)) -> IsLessThanOrEqual(left,right)`; `fn adding_the_same_number_preserves_less_than_or_equal(addend: Int, {left}, {right}, IsLessThanOrEqual(left,right)) -> IsLessThanOrEqual(add_int(addend,left), add_int(addend,right))`.
- Consumes: Task 6's family; `Std.Proof.Math` Nat transitivity/monotonicity (`proof_math.cure:126,141`); a total `add_int : Int -> Int -> Int` (define it here or reuse the builtin `+` if the elaborator lets a proof reason about `+` on `Int` — prefer a structurally-defined `add_int` the proof can compute with, mirroring `Std.Nat.plus`).

- [ ] **Step 1:** Write the failing transitivity lemma (mirror `less_than_or_equal_is_transitive`, `proof_math.cure:126`), case-splitting on both evidence values and delegating each case to the Nat lemma.
- [ ] **Step 2:** Compile red → implement → green.
- [ ] **Step 3:** Write the failing add-monotonicity lemma (mirror `adding_the_same_number_preserves_less_than_or_equal`, `proof_math.cure:141`). Define `add_int` structurally if needed.
- [ ] **Step 4:** Compile red → implement → green.
- [ ] **Step 5:** Oracle probe `int_order_mono.{cure,idr}` (transitivity + monotonicity on closed instances), `rel=same`; full suite.
- [ ] **Step 6:** Commit (`feat(std): Int order transitivity + add-monotonicity`).

### Task 8: Sign lemmas + nonneg-scaling monotonicity + `0 ≤ -1` contradiction extractor

**Files:**
- Modify: `lib/std/proof_int_order.cure`
- Create: `https://github.com/cure-lang/cure-otp/tree/main/metatheory/oracle/otp/int_order_sign.{cure,idr}`

**Interfaces:**
- Produces: `fn nonneg_of_from_nat(n: Nat) -> IsLessThanOrEqual(FromNat(Z()), FromNat(n))`; a nonneg-scaling monotonicity lemma (`0 ≤ a → b ≤ c → a*b ≤ a*c`, reducing to `Std.Proof.Math.multiply` facts); and `fn zero_is_not_at_most_negative_one(proof: IsLessThanOrEqual(FromNat(Z()), NegativeSuccessor(Z()))) -> Empty` (the `0 ≤ -1` refutation — LIA's contradiction extractor, discharged by empty `match` since no constructor targets that index pair).
- Consumes: Tasks 6-7; `Std.Proof.Math.multiply` + `multiplying_positive_numbers_is_positive` (`proof_math.cure:112`).

- [ ] **Step 1:** Write the failing `zero_is_not_at_most_negative_one` (empty-match refutation — mirror `zero_is_not_positive`, `proof_math.cure:33`). This is the keystone LIA needs.
- [ ] **Step 2:** Compile red → implement (empty `match proof`) → green.
- [ ] **Step 3:** Write the failing nonneg-scaling monotonicity lemma; reduce to `multiply` + Nat positivity.
- [ ] **Step 4:** Compile red → implement → green.
- [ ] **Step 5:** Oracle probe `int_order_sign.{cure,idr}`, `rel=same`; full suite.
- [ ] **Step 6:** Commit (`feat(std): Int sign lemmas, nonneg-scaling monotonicity, 0≤-1 refutation`).

- [ ] **Step 7: Document the public kit (Phase-2 definition of done)**

Add a header block to `lib/std/proof_int_order.cure` listing every public lemma name + signature, so LIA and agent #4 can consume them without reading the proofs. Commit (`docs(std): document Int ordered-ring lemma kit public surface`).

**Phase 2 is complete when the kit compiles, every lemma is Idris-mirrored `rel=same`, and the full suite is green.**

---

## Out of scope (follow-on, not this plan)

- Rebuilding the parked LIA checker (`autopilot/verified-lia-reflection`) on the new `Int` — it rebases onto this branch afterward, its local `Zed`/`Integer` substrate deleted.
- Migrating the refinement-surface desugaring.
- Any change to `IsTrue`/`Confirmed` semantics or agent #4's bridge (only the doc-comment in Task 5 is touched).

## Definition of done (whole plan)

- **Phase 1:** `Std.Int` is an inductive `@builtin(:int)` family; `match`/structural induction on `Int` works; `negate_involutive` proves + replays `rel=same`; the entire existing suite is byte-identically green with no `Int`-re-representation churn; the `int_to_ctor` fold is documented as the sole TCB addition with its bignum-soundness caveat.
- **Phase 2:** the ordered-ring kit is proven in Cure, each lemma Idris-mirrored `rel=same`, suite green; the kit's public lemma names/signatures are documented for LIA and #4.

## Halt conditions (§12)

- Back-compat regression not a provably-equivalent re-spelling → Halt (family/fold is wrong).
- §3a approach (i) blast radius unmanageable at a site → facade fallback (ii), recorded (not silent).
- `int_to_ctor` needs a kernel rule beyond the fold → elaborator hard-stop, Halt.
- Phase 2 proof wall index-generalization cannot route around → Halt naming the exact stuck lemma; Phase 1 stays valid, committed, useful.

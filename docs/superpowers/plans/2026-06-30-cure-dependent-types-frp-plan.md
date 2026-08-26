# Cure Dependent Types (Slice 1) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a sound, trusted `Cure.Core` dependent-type kernel + untrusted `Cure.Elab` elaborator that type-checks and runs one step of the Slice-1 FRP fragment (`Dec`/`and`/`SVDesc`/`SF`/`compose`/`step`/`Σ`/holes) end-to-end, replacing the six faked dependent-type modules.

**Architecture:** Surface Cure elaborates (untrusted) into explicit `Cure.Core` terms, which a small trusted kernel re-checks via NbE conversion against a small fixed cumulative universe hierarchy; checked terms are erased to the existing BEAM codegen. The kernel re-runs the totality/coverage decision procedure when validating the certificates that gate δ-reduction.

**Tech Stack:** Elixir (the Cure compiler), ExUnit, `mix test`. de Bruijn-indexed core terms; normalization-by-evaluation; Miller-pattern unification.

**Spec:** `docs/superpowers/specs/types/2026-06-30-cure-dependent-types-frp-design.md` (hardened, commit `aa55ee2`). Read §4 (Core calculus) before any kernel task.

## Global Constraints

- **Reference-first (standing rule, applies to EVERY implementation step):** before writing or fixing any kernel/elaborator code, open the mapped reference file(s) named in the task (from `/Users/ch/Develop/esp32-beam/reference/MANIFEST.md` → `reference/{idris2,lean4,agda}/…`) and follow their approach. On ANY failing step you cannot fix in one attempt, re-read the mapped reference before trying again. Idris2 = architecture/totality/erasure/patterns; Lean4 = kernel term/defeq/universes; Agda = dependent pattern matching/index unification.
- **One build at a time.** Never run more than one `mix test`/`mix compile` concurrently (a past concurrent full-suite run caused a kernel panic). Serialize all suite runs.
- **Strict TDD.** Red (write failing test) → confirm it fails for the stated reason → minimal implementation → confirm green → commit. Tests are behavioral and immutable; do not weaken a test to pass.
- **Commits:** never co-sign/co-author; author as the user only. Conventional-commit messages.
- **OTP 26–28** (per repo `CLAUDE.md`); `start/0` entry convention is irrelevant here (compiler-internal work).
- **Trusted vs untrusted boundary:** code under `lib/cure/core/` is the trusted kernel — keep it small, pure, deterministic, no side effects beyond returning results/errors. Cleverness (inference, unification, pattern compilation, the totality *closure walk*) lives in `lib/cure/elab/` and is re-checked by the kernel.
- **Soundness invariant:** the kernel never trusts an elaborator-asserted certificate — it re-runs the termination+coverage check on the Core definition itself (Task M7.2), over a def whose body it already type-checked (Task M7.1).
- **Core terms are serializable** (commitment C2): every `Cure.Core.Term` node must round-trip through `Core.Term.to_external/1` / `from_external/1` (plain tagged tuples/maps, no PIDs/refs/closures) so an independent checker can re-validate. Add a round-trip test whenever a new node is introduced.

**Milestone order (each self-contained, independently committable; halt cleanly on a boundary):**
M0 Core term repr → M1 universes + NbE eval/conv (Π/λ) → M2 kernel check/infer (Π/λ/Type) → M3 indexed families + positivity → M4 dependent `case` + ι → M5 Σ types → M6 `Eq`/`refl`/`rewrite` → M7 global defs + kernel-revalidated totality certificates + type-level closure → M8 elaborator (declarations, implicits, pattern compilation, holes) → M9 erasure → codegen → M10 Slice-1 acceptance (incl. negatives) → M11 conformance-corpus seed + serialization.

---

## Milestone M0 — Core term representation

**Reference:** `reference/lean4/src/kernel/expr.{h,cpp}` (node taxonomy, de Bruijn vars), `reference/idris2/src/Core/TT/Term.idr`, `reference/idris2/src/Core/TT/Var.idr`. Substitution: `reference/lean4/src/kernel/instantiate.{h,cpp}`, `reference/agda/src/full/Agda/TypeChecking/Substitute.hs`.

### Task M0.1: Core term datatype + constructors

**Files:**
- Create: `lib/cure/core/term.ex`
- Test: `test/cure/core/term_test.exs`

**Interfaces:**
- Produces: a Core term representation. Nodes (tagged tuples, de Bruijn): `{:type, level}` (level 0..2); `{:var, k}` (de Bruijn index, k≥0); `{:pi, dom_term, cod_term}`; `{:lam, dom_term, body_term}`; `{:app, f, a}`; `{:sigma, a, b}`; `{:pair, a, b}`; `{:fst, p}`; `{:snd, p}`; `{:data, name, params, indices}`; `{:ctor, name, args}`; `{:case, scrut, motive, branches}` where `branches :: [{ctor_name, arity, body}]`; `{:global, name}`; `{:eq, ty, a, b}`; `{:refl, a}`; `{:rewrite, proof, motive, body}`. Helper guards `Core.Term.term?/1`.

- [ ] **Step 1: Write the failing test**

```elixir
defmodule Cure.Core.TermTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Term

  test "constructs and recognises core nodes" do
    assert Term.term?({:type, 0})
    assert Term.term?({:var, 0})
    assert Term.term?({:pi, {:type, 0}, {:var, 0}})
    assert Term.term?({:app, {:lam, {:type, 0}, {:var, 0}}, {:type, 0}})
    refute Term.term?({:type, 3})        # level ceiling is 2
    refute Term.term?({:var, -1})
    refute Term.term?(:not_a_term)
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/term_test.exs`
Expected: FAIL — module `Cure.Core.Term` not defined.

- [ ] **Step 3: Write minimal implementation**

Implement `Cure.Core.Term` with a `term?/1` guard-style recogniser validating each node shape and the `0..2` level bound / non-negative de Bruijn indices. Mirror Lean's `expr` node set (read the reference first); keep it pure data.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/term_test.exs`  — Expected: PASS

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/term.ex test/cure/core/term_test.exs
git commit -m "feat(core): add Core term representation"
```

### Task M0.2: de Bruijn substitution + shifting

**Files:**
- Modify: `lib/cure/core/term.ex`
- Test: `test/cure/core/term_test.exs`

**Interfaces:**
- Produces: `Core.Term.shift(term, amount, cutoff \\ 0)` and `Core.Term.subst(term, j, replacement)` (substitute de Bruijn index `j`), correct under binders (`:pi`/`:lam`/`:sigma` introduce one binder in their codomain/body; `:case`/`:rewrite` branches introduce binders per their telescope/motive).

- [ ] **Step 1: Write the failing test**

```elixir
test "shift lifts free vars at/above the cutoff, leaves bound vars" do
  alias Cure.Core.Term
  # closed term (the body var #0 is bound by the λ) is unchanged by shifting
  assert {:lam, {:type, 0}, {:var, 0}} == Term.shift({:lam, {:type, 0}, {:var, 0}}, 1, 0)
  # a free var at/above the cutoff is lifted by the amount
  assert {:var, 2} == Term.shift({:var, 0}, 2, 0)
end

test "subst replaces the target index under binders, leaves others" do
  alias Cure.Core.Term
  # `λ. #1`: the body var #1 refers to the OUTER binder (index 0 outside the λ).
  # Substituting index 0 with a CLOSED replacement (shift is identity on it) must
  # descend under the one binder (target becomes index 1 there) and replace #1.
  assert {:lam, {:type, 0}, {:type, 1}} == Term.subst({:lam, {:type, 0}, {:var, 1}}, 0, {:type, 1})
  # `λ. #0`: the body var #0 is bound by the λ itself, so substituting outer index 0
  # must NOT touch it (capture-avoidance via the binder-depth shift).
  assert {:lam, {:type, 0}, {:var, 0}} == Term.subst({:lam, {:type, 0}, {:var, 0}}, 0, {:type, 1})
  # no-op when the target index does not occur.
  assert {:type, 0} == Term.subst({:type, 0}, 0, {:type, 1})
end
```

*(These assertions are convention-stable: the replacement is closed, so the under-binder behaviour is pinned by binder depth alone, not by the shift-of-replacement off-by-one. They are the immutable behavioral contract — capture-avoidance under a binder, an untouched bound var, and a no-op when absent.)*

- [ ] **Step 2: Run** `mix test test/cure/core/term_test.exs` — Expected: FAIL.
- [ ] **Step 3: Implement** `shift/3` and `subst/3` per `reference/lean4/src/kernel/instantiate.cpp` (`instantiate`/`lift` semantics). Increment cutoff at each binder.
- [ ] **Step 4: Run** — Expected: PASS.
- [ ] **Step 5: Commit** `feat(core): de Bruijn shift + substitution`

### Task M0.3: external serialization round-trip (C2)

**Files:** Modify `lib/cure/core/term.ex`; Test `test/cure/core/term_test.exs`.
**Interfaces:** Produces `Core.Term.to_external/1` / `from_external/1` (plain JSON-able maps; no PIDs/closures).

- [ ] **Step 1:** Failing test: `assert t == t |> Term.to_external() |> Term.from_external()` for one term of each node kind.
- [ ] **Step 2:** Run — FAIL.
- [ ] **Step 3:** Implement structural to/from external (tagged maps).
- [ ] **Step 4:** Run — PASS.
- [ ] **Step 5:** Commit `feat(core): serializable Core terms (C2)`

---

## Milestone M1 — Universes + NbE evaluator + conversion (Π/λ fragment)

**Reference:** `reference/lean4/src/kernel/level.{h,cpp}` (universes, `max`, cumulativity); `reference/idris2/src/Core/Value.idr` + `reference/idris2/src/Core/Normalise/Eval.idr` + `Normalise/Quote.idr` + `Normalise/Convert.idr` (NbE values/neutrals, eval, read-back, conversion); `reference/agda/src/full/Agda/TypeChecking/Reduce.hs`.

### Task M1.1: universe levels + cumulativity

**Files:** Create `lib/cure/core/universe.ex`; Test `test/cure/core/universe_test.exs`.
**Interfaces:** Produces `Universe.max(l1, l2)`, `Universe.le?(l1, l2)` (cumulativity `≤`), `Universe.ceiling()` = 2. Errors if a computed level exceeds 2 (`{:error, :universe_ceiling}`).

- [ ] **Step 1:** Failing tests: `max(0,1)==1`; `le?(0,1)` true, `le?(1,0)` false; `max(2,1)==2`; computing above 2 returns `{:error, :universe_ceiling}`.
- [ ] **Step 2:** Run `mix test test/cure/core/universe_test.exs` — FAIL.
- [ ] **Step 3:** Implement over the fixed set `{0,1,2}` per Lean `level.cpp` (`max`, `is_geq`).
- [ ] **Step 4:** Run — PASS.
- [ ] **Step 5:** Commit `feat(core): fixed cumulative universe hierarchy`

### Task M1.2: NbE value domain

**Files:** Create `lib/cure/core/value.ex`; Test `test/cure/core/value_test.exs`.
**Interfaces:** Produces semantic values with closures + neutrals: `{:vtype, level}`, `{:vpi, dom_value, closure}`, `{:vlam, closure}`, `{:vsigma, dom_value, closure}`, `{:vpair, v, v}`, `{:vneutral, neutral}`, `{:vdata, name, [value]}`, `{:vctor, name, [value]}`; neutrals `{:nvar, lvl}` (de Bruijn *level*), `{:nglobal, name}` (an opaque/uncertified global head — stuck until δ is permitted in M7.2), `{:napp, neutral, value}`, `{:nfst, neutral}`, `{:nsnd, neutral}`, `{:ncase, neutral, motive_closure, branch_closures}`. A `closure` is `{:closure, env, term}`. Recogniser `Value.value?/1`.

- [ ] **Step 1:** Failing test: construct one of each value/neutral shape and assert `Value.value?/1`; assert a closure carries `{env, term}`.
- [ ] **Step 2:** Run — FAIL.
- [ ] **Step 3:** Implement the value taxonomy per `reference/idris2/src/Core/Value.idr` (NF/Glued; we use eval-to-value + read-back). Use de Bruijn *levels* for neutrals (read-back converts to indices).
- [ ] **Step 4:** Run — PASS.
- [ ] **Step 5:** Commit `feat(core): NbE value domain`

### Task M1.3: evaluator `eval(term, env) -> value` (β + projections)

**Files:** Create `lib/cure/core/eval.ex`; Test `test/cure/core/eval_test.exs`.
**Interfaces:** Consumes `Term`, `Value`. Produces `Eval.eval(term, env)` and `Eval.apply(vfun, varg)`; `env :: [value]` (de Bruijn). δ-unfolding of `:global` is gated (Task M7); until then globals eval to a neutral.

- [ ] **Step 1:** Failing test — β: `eval((λ.#0) Type0, []) == {:vtype,0}`; projections: `eval(fst (pair Type0 Type1)) == {:vtype,0}`; a free var evaluates to `{:vneutral,{:nvar,_}}`; an (uncertified) `{:global, name}` evaluates to `{:vneutral,{:nglobal, name}}` (opaque until M7.2).
- [ ] **Step 2:** Run `mix test test/cure/core/eval_test.exs` — FAIL.
- [ ] **Step 3:** Implement environment-based eval per `reference/idris2/src/Core/Normalise/Eval.idr`: `:lam`→`:vlam` closure; `:app`→`apply` (β if `:vlam`, else extend neutral); `:pair`/`:fst`/`:snd` with ι on `:vpair`; `:pi`/`:sigma`→closures.
- [ ] **Step 4:** Run — PASS.
- [ ] **Step 5:** Commit `feat(core): NbE evaluator (beta + projections)`

### Task M1.4: read-back (quote) `reify(value, depth) -> term`

**Files:** Create `lib/cure/core/quote.ex` (or add to `eval.ex`); Test in `eval_test.exs`.
**Interfaces:** Produces `Quote.reify(value, depth)` converting values (incl. neutrals via level→index) back to a **β-normal** `Term`. η is **not** handled in read-back: η-expanding a neutral needs the neutral's type, which a `Value` does not carry, so reify stays untyped and β-normal. η is decided in `Conv.conv?` per the §4.5 rule (the λ-vs-neutral application trick), not by producing η-long normal forms here.

- [ ] **Step 1:** Failing test — round-trip: `reify(eval(t, []), 0)` is β-normal; identity `λ.#0` reifies to `{:lam, _, {:var,0}}`; a neutral applied under binders — `λ.λ. (#1 #0)` — round-trips to itself (level→index conversion correct).
- [ ] **Step 2:** Run — FAIL.
- [ ] **Step 3:** Implement per `reference/idris2/src/Core/Normalise/Quote.idr` (level→index conversion = `depth - lvl - 1`); produce β-normal forms (no η in read-back — see Interfaces).
- [ ] **Step 4:** Run — PASS.
- [ ] **Step 5:** Commit `feat(core): NbE read-back (beta-normal)`

### Task M1.5: conversion `conv?(t1, t2, env, depth)` (definitional equality)

**Files:** Create `lib/cure/core/conv.ex`; Test `test/cure/core/conv_test.exs`.
**Interfaces:** Produces `Conv.conv?(term1, term2, env, depth)` — true iff definitionally equal (β/ι/η; δ added in M7). η is handled **here**, type-free: when one side whnf's to a `:vlam` and the other does not, apply the non-λ side to a fresh neutral and compare bodies (the §4.5 η rule). **This `conv?/4` is the single canonical conversion signature — every caller (incl. M6 `refl`) uses it; there is no type-indexed variant.** Used by the kernel.

- [ ] **Step 1:** Failing tests — `(λ.#0) Type0 ≡ Type0`; `λ.#0 ≡ λ.#0`; η: `f ≡ λ.(f #0)` at Π; **negative:** `Type0 ≢ Type1`; `Dcoupled-ish ctor a ≢ ctor b`.
- [ ] **Step 2:** Run `mix test test/cure/core/conv_test.exs` — FAIL.
- [ ] **Step 3:** Implement conversion by eval-both-then-compare-normal-forms (NbE) per `reference/idris2/src/Core/Normalise/Convert.idr` and `reference/lean4/src/kernel/type_checker.cpp` (`is_def_eq`). Compare neutrals structurally; η at Π via the λ-vs-neutral application trick (Σ-η optional per §4.7).
- [ ] **Step 4:** Run — PASS.
- [ ] **Step 5:** Commit `feat(core): NbE definitional equality`

---

## Milestone M2 — Kernel check/infer (Π/λ/Type/var/app)

**Reference:** `reference/lean4/src/kernel/type_checker.{h,cpp}` (`check`/`infer`/`ensure_pi`/`ensure_sort`); `reference/idris2/src/TTImp/Elab/Check.idr` (bidirectional shape).

### Task M2.1: typing context

**Files:** Create `lib/cure/core/context.ex`; Test `test/cure/core/context_test.exs`.
**Interfaces:** Produces `Context.empty/0`, `Context.extend(ctx, type_value)`, `Context.lookup(ctx, debruijn_index) -> type_value`, `Context.length/1`, `Context.env(ctx)` (the value env for NbE, with fresh neutrals for each binder).

- [ ] **Step 1:** Failing test — extend twice, lookup index 0 returns the most-recent type; `env` yields `[{:vneutral,{:nvar,1}},{:vneutral,{:nvar,0}}]`-shaped fresh neutrals.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement.  → **Step 4:** PASS.  → **Step 5:** Commit `feat(core): typing context`.

### Task M2.2: `infer` for Type/var/Π

**Files:** Create `lib/cure/core/kernel.ex`; Test `test/cure/core/kernel_test.exs`.
**Interfaces:** Produces `Kernel.infer(ctx, term) -> {:ok, type_value} | {:error, reason}` and `Kernel.check(ctx, term, type_value) -> :ok | {:error, reason}`.

- [ ] **Step 1:** Failing tests — `infer(Type0) == Type1`; `infer(var)` returns its context type; `infer(Π(Type0).#0) == Type1` (max-level rule §4.3); cumulativity: `check(Type0, {:type, 2})` ok (`Type0 : Type1 ≤ Type2` — this exercises the cumulative rule; `check(Type0, Type1)` would hold by the direct typing rule and would not test cumulativity).
- [ ] **Step 2:** Run `mix test test/cure/core/kernel_test.exs` — FAIL.
- [ ] **Step 3:** Implement bidirectional `infer`/`check` for `{:type,_}`, `{:var,_}`, `{:pi,_,_}`; `check` falls back to `infer`+`conv?` with cumulative `le?` on sorts. Reference Lean `type_checker.cpp`.
- [ ] **Step 4:** Run — PASS.  → **Step 5:** Commit `feat(core): kernel infer for Type/var/Pi`.

### Task M2.3: `infer`/`check` for λ and application

**Files:** Modify `lib/cure/core/kernel.ex`; Test `kernel_test.exs`.
**Interfaces:** extends `infer`/`check` to `{:lam,_,_}` (checked against a `:vpi`) and `{:app,_,_}` (infer fun, `ensure_pi`, check arg, substitute arg value into codomain closure).

- [ ] **Step 1:** Failing tests — `check(λ(Type0).#0, Π(Type0).Type0)` ok; `infer((λ(Type0).#0) applied to Type0…)` — well-typed app yields the substituted codomain; **negative:** applying a non-function → `{:error, :not_a_function}`; arg type mismatch → `{:error, :type_mismatch}`.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement (`ensure_pi` evaluates the inferred type to a `:vpi`; codomain via closure application). → **Step 4:** PASS. → **Step 5:** Commit `feat(core): kernel for lambda + application`.

---

## Milestone M3 — Indexed families + strict positivity

**Reference:** `reference/lean4/src/kernel/inductive.{h,cpp}`; `reference/idris2/src/TTImp/ProcessData.idr` + `reference/idris2/src/Core/Context/Data.idr`; positivity `reference/agda/src/full/Agda/TypeChecking/Positivity.hs` + `reference/idris2/src/Core/Termination/Positivity.idr`; telescopes `reference/agda/src/full/Agda/TypeChecking/Telescope.hs`.

### Task M3.1: family + constructor declaration representation

**Files:** Create `lib/cure/core/inductive.ex`; Test `test/cure/core/inductive_test.exs`.
**Interfaces:** Produces `Inductive.family(name, param_tele, index_tele, level)`, `Inductive.ctor(name, arg_tele, result_indices)`, and the accessor `Inductive.ctor_result_indices(env, ctor_name) -> [index_term]`, where a telescope is `[{var_name, type_term}]` and `result_indices` are index *terms* over params+args (§4.4). Stored in the global signature map **`Cure.Core.Env`** — the module/struct defined here in `inductive.ex` that holds family/constructor signatures and (from M7.1) global function definitions; all later tasks refer to it as `Core.Env`.

- [ ] **Step 1:** Failing test — declare `Dec` (no params/indices, level 0) with ctors `Dcoupled`/`Causal`; declare `SF` (params none, indices `[as:SVDesc, bs:SVDesc, d:Dec]`, level 0) with `seq` whose result index `d` is `and(d1,d2)`. Assert the env stores them and `Inductive.ctor_result_indices(env, :seq)` returns the `and(...)` term.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement the signature env. → **Step 4:** PASS. → **Step 5:** Commit `feat(core): indexed family + constructor signatures`.

### Task M3.2: kernel checks a family/constructor declaration well-formed

**Files:** Modify `lib/cure/core/kernel.ex`; Test `kernel_test.exs`.
**Interfaces:** `Kernel.check_family(env, family)` and `Kernel.check_ctor(env, family, ctor)` — telescopes well-typed; each `result_index` checks against the family's index telescope type (evaluating computed indices via NbE); the family's declared universe `level` is verified to be **≥ the level of every type stored in its constructors** (so a constructor field of type `Type₀` forces the family to level ≥ 1, per the §2/§3 two-universe requirement).

- [ ] **Step 1:** Failing tests — well-formed `SF`/`seq` accepted; the `Sig = C(Type) | E(Type)` data type (a constructor stores `Type₀`) is well-formed **only at level ≥ 1** (`Sig : Type₁` — the §2 "two universe levels" case); declaring `Sig` at level 0 → `{:error, :universe_level}`; **negative:** a ctor whose `result_indices` arity ≠ family index arity → `{:error, :index_arity}`; a result index of wrong type (`Nat` where `Dec` expected) → `{:error, :type_mismatch}`.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement per Lean `inductive.cpp` (check_inductive_decl). → **Step 4:** PASS. → **Step 5:** Commit `feat(core): well-formedness of indexed families`.

### Task M3.3: strict positivity check

**Files:** Modify `lib/cure/core/inductive.ex`; Test `inductive_test.exs`.
**Interfaces:** `Inductive.positive?(env, family) -> :ok | {:error, {:non_strictly_positive, ctor}}`.

- [ ] **Step 1:** Failing tests — `Dec`/`SF` are strictly positive (ok); a synthetic ctor with the family in a negative position (`(D -> X) -> D`) → `{:error, :non_strictly_positive}`.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement per `reference/agda/.../Positivity.hs` / `reference/idris2/.../Positivity.idr` (occurrence polarity walk). → **Step 4:** PASS. → **Step 5:** Commit `feat(core): strict positivity check`.

### Task M3.4: kernel infers constructor application type with computed indices

**Files:** Modify `lib/cure/core/kernel.ex`; Test `kernel_test.exs`.
**Interfaces:** `infer({:ctor, name, args})` → checks args against the ctor telescope and returns the inferred **type value** `{:vdata, family_name, evaluated_params ++ evaluated_result_indices}` (the `:vdata` value shape from M1.2 — a single flat arg list; the source `{:data, name, params, indices}` term node from M0.1 keeps params and indices as separate lists and they flatten here). Indices computed by NbE, e.g. `and(Causal,Causal) ⇝ Causal`.

- [ ] **Step 1:** Failing tests — `infer(seq(l, r))` where `l : SF(as,bs,Causal)`, `r : SF(bs,cs,Causal)` yields `SF(as,cs,Causal)` (because `and(Causal,Causal) ⇝ Causal`); **negative (the headline):** `seq(l, r')` with `r' : SF(bs',cs,_)` and `bs' ≠ bs` → `{:error, :index_mismatch}`. (This is the **kernel-level** conversion check on already-explicit indices — a backstop. The user-facing §6(a) negative is produced earlier, in the elaborator's pattern/unification path, as `:index_unification` (M8.4 / M10.2a); `:index_mismatch` here is the kernel's internal reason for the same disagreement and is not one of the §10 user-facing codes.)
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement: unify the shared index var `bs` between args (conversion check), then evaluate the result indices. → **Step 4:** PASS. → **Step 5:** Commit `feat(core): constructor typing with computed indices`.

---

## Milestone M4 — Dependent `case` eliminator + ι-reduction

**Reference:** spec §4.4 (dependent-case rule); `reference/lean4/src/kernel/inductive.cpp` (recursor rules); `reference/idris2/src/Core/Case/CaseTree.idr`.

### Task M4.1: kernel checks the dependent `case` against a motive

**Files:** Modify `lib/cure/core/kernel.ex`; Test `kernel_test.exs`.
**Interfaces:** `check({:case, scrut, motive, branches}, expected)` implementing the §4.4 rule: infer `scrut : D p̄ ī`; check `motive` is a type family over indices+scrutinee; per branch, check `uⱼ` under the ctor telescope with index vars instantiated to that ctor's computed `s̄ⱼ`; result type `M[ī/ȷ̄, scrut/x]`.

- [ ] **Step 1:** Failing tests — a `case` on a `Dec` value with both branches returning the motive type checks; a `case` on `SF` with `prim`/`seq` branches checks under refined indices; **negative:** a branch body of the wrong type → `{:error, :branch_type}`; missing constructor → `{:error, :coverage}` (full coverage in M8, but kernel rejects a non-exhaustive `case` here).
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement the §4.4 rule (substitute computed indices into the motive per branch). → **Step 4:** PASS. → **Step 5:** Commit `feat(core): dependent case eliminator typing`.

### Task M4.2: ι-reduction for `case` in eval + conv

**Files:** Modify `lib/cure/core/eval.ex`, `lib/cure/core/conv.ex`; Test `eval_test.exs`, `conv_test.exs`.
**Interfaces:** `eval({:case, scrut, …})` reduces when `scrut` evals to `{:vctor, cⱼ, args}` → eval branch `uⱼ` with `args` bound; else neutral `{:ncase,…}`.

- [ ] **Step 1:** Failing tests — `case Causal of {Dcoupled→A; Causal→B}` evals to `B`; a `case` on a neutral scrutinee stays neutral and is conv-comparable to itself.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement ι per Lean recursor reduction. → **Step 4:** PASS. → **Step 5:** Commit `feat(core): iota reduction for case`.

---

## Milestone M5 — Σ types

**Reference:** spec §4.7; Σ is the dual of Π already built — mirror M1/M2 Π/λ work. Lean has Σ as an inductive; we treat it primitively per §4.7.

### Task M5.1: kernel typing for Σ / pair / fst / snd

**Files:** Modify `lib/cure/core/kernel.ex`; Test `kernel_test.exs`.
**Interfaces:** `infer`/`check` for `{:sigma,a,b}` (formation, `max` level), `{:pair,a,b}` (checked against a `:vsigma`; second component against `B[a/x]`), `{:fst,p}` (→ `A`), `{:snd,p}` (→ `B[fst p / x]`).

- [ ] **Step 1:** Failing tests — `Σ(Dec).SF(as,bs,#0)` is a type at level 0; `check((Causal, sf), Σ(Dec).SF(as,bs,#0))` ok when `sf : SF(as,bs,Causal)`; `infer(snd p)` substitutes `fst p`; **negative:** pair whose 2nd component's type ≠ `B[a/x]` → `{:error, :sigma_mismatch}`.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement (dual of Π; `fst`/`snd` substitution as in §4.7). → **Step 4:** PASS. → **Step 5:** Commit `feat(core): Sigma types, pairs, projections`.

*(ι for `fst`/`snd` already added in M1.3; add conv tests here confirming **both** §11 projection rules — `fst (a,b) ≡ a` and `snd (a,b) ≡ b` — at Σ.)*

---

## Milestone M6 — Minimal propositional equality (`Eq`/`refl`/`rewrite`)

**Reference:** spec §4.5–4.6; `reference/idris2/src/TTImp/Elab/Rewrite.idr`.

### Task M6.1: `Eq` formation + sound `refl`

**Files:** Modify `lib/cure/core/kernel.ex`; Test `kernel_test.exs`.
**Interfaces:** `infer({:eq, ty, a, b})` (homogeneous, level of `ty`); `check({:refl, a}, {:eq, ty, a', b'})` ok **iff** `conv?(a', b', env, depth)` AND `conv?(a, a', env, depth)` (the canonical `conv?/4` from M1.5, with `env`/`depth` taken from `ctx`; the type `ty` is already known well-formed and is *not* an argument to conv). This is the §4.6 soundness gate — the audit's bug was accepting any atom.

- [ ] **Step 1:** Failing tests — `refl Causal : Eq Dec Causal Causal` ok; `refl Causal : Eq Dec (and Causal Causal) Causal` ok (since `and Causal Causal ⇝ Causal`); **negative (the audit bug):** `refl Causal : Eq Dec Causal Dcoupled` → `{:error, :not_definitionally_equal}`.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement the conv-gated rule. → **Step 4:** PASS. → **Step 5:** Commit `feat(core): sound Eq formation and refl`.

### Task M6.2: `rewrite e at (x.M) in t` transport

**Files:** Modify `lib/cure/core/kernel.ex`, `lib/cure/core/eval.ex`; Test `kernel_test.exs`.
**Interfaces:** `check({:rewrite, e, motive, t}, expected)` per §4.6: `e : Eq A a b`, `motive = (x.M)`, `t : M[a/x]`, result `M[b/x]`; erased at runtime (eval drops the proof, `rewrite e _ t ⇝ t`).

- [ ] **Step 1:** Failing tests — a `rewrite` along a `refl` is the identity transport and typechecks at `M[b/x]`; eval of `rewrite` returns `eval(t)`; **negative:** `t` not of type `M[a/x]` → `{:error, :rewrite_premise}`.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement transport (substitute into the explicit motive) + erasure-eval. → **Step 4:** PASS. → **Step 5:** Commit `feat(core): rewrite/subst transport`.

---

## Milestone M7 — Totality certificates (kernel-revalidated)

**Reference:** `reference/idris2/src/Core/Termination.idr` + `Termination/SizeChange.idr` + `Termination/CallGraph.idr`; existing `lib/cure/types/totality.ex` + `lib/cure/types/pattern_checker.ex`. Spec §7 (trust boundary).

### Task M7.1: global function definitions — representation, kernel type-check, registration

**Files:** Modify `lib/cure/core/inductive.ex` (the global signature env that already holds families, M3.1) and `lib/cure/core/kernel.ex`; Test `test/cure/core/kernel_test.exs`.
**Interfaces:** `Core.Env.add_def(env, name, type_term, body_term)` stores a global function definition (declared type + Core body) in the same global signature env as families; `Kernel.check_def(env, def) -> :ok | {:error, reason}` type-checks `body` against `type` (reusing M2/M3 `check`) **before** the def may be registered or referenced as a `:global`. No δ yet — δ is gated on certification in M7.2; an unchecked/uncertified global stays opaque (neutral) per M1.3. (Families are checked by M3.2; this is the analogous step for function defs, and the prerequisite that makes a `:global` like `and` exist for M7.2/M10.)

- [ ] **Step 1:** Failing tests — registering `and : Π(Dec).Π(Dec).Dec` with its Core body (`λλ. case …`) and `Kernel.check_def` returns `:ok` (the body checks against the declared Π type); **negative #1:** a def whose body's type ≠ its declared type (e.g. body `λ.Type0` declared `Dec→Dec`) → `{:error, :type_mismatch}`; **negative #2:** a `:global` reference to an unregistered name → `{:error, :unknown_global}`.
- [ ] **Step 2:** Run `mix test test/cure/core/kernel_test.exs` — FAIL.
- [ ] **Step 3:** Implement def storage in `Core.Env` + `check_def` per Lean `type_checker.cpp` (definition checking) and `reference/idris2/src/Core/Context.idr` (global def storage). The kernel checks the body itself — it never trusts an elaborator-supplied type.
- [ ] **Step 4:** Run — PASS.  → **Step 5:** Commit `feat(core): global definition checking + registration`.

### Task M7.2: kernel re-runs termination+coverage when validating a certificate

**Files:** Create `lib/cure/core/certificate.ex`; Modify `lib/cure/core/kernel.ex`, `lib/cure/core/eval.ex`; Test `test/cure/core/certificate_test.exs`.
**Interfaces:** `Kernel.validate_certificate(env, global_def) -> {:ok, :certified} | {:error, :not_total}` — operates on a def already type-checked + registered by M7.1; invokes `Cure.Types.Totality` (termination) + `Cure.Types.PatternChecker` (coverage) on the Core def itself; only on `:ok` does `Eval` permit δ-unfolding of that `:global`. (The internal `:not_total` reason is surfaced to the user as the §10 `:totality_required` diagnostic by the elaborator's closure walk, M7.3.)

- [ ] **Step 1:** Failing tests — `and` (structurally total, exhaustive) certifies; δ-unfolds in conv (`and Causal Causal ≡ Causal` now reduces via δ); **negative:** a non-terminating global (`loop = loop`) → `{:error, :not_total}` and stays opaque (δ refuses to unfold; `loop ≢ loop`-body).
- [ ] **Step 2:** Run `mix test test/cure/core/certificate_test.exs` — FAIL.
- [ ] **Step 3:** Implement: wire `totality.ex`/`pattern_checker.ex` decision procedures to run on Core defs; gate `Eval` δ on a certified set held in `Core.Env`. The kernel re-runs the check (does not trust an external flag).
- [ ] **Step 4:** Run — PASS.  → **Step 5:** Commit `feat(core): kernel-revalidated totality certificates gating delta`.

### Task M7.3: elaborator type-level totality closure + `:totality_required` (untrusted driver)

**Reference:** Spec §7 (trust boundary — the elaborator decides *which* fns to submit; the kernel re-checks each); `reference/idris2/src/Core/Termination.idr` (what "total" means). This is the untrusted closure walk that §5/§7 assign to the elaborator — the half of §7 the kernel does *not* do.

**Files:** Create `lib/cure/elab/totality_closure.ex`; Test `test/cure/elab/totality_closure_test.exs`.
**Interfaces:** `TotalityClosure.type_level_fns(core_env) -> MapSet` — operates over the **Core defs/families registered in `Core.Env`** (M7.1/M3.1), *not* the surface AST, so it has no dependency on the M8 surface elaborator and is unit-testable with hand-built Core defs (as in the M7.1/M7.2 tests). It computes the transitive closure of every function reachable from a type (an index expression in a constructor signature, an argument/return type) plus any `@total`-flagged def. The elaborator submits each closure member to `Kernel.validate_certificate` (M7.2); a member that fails certification surfaces as the §10 `:totality_required` diagnostic **naming the offending function**. Runtime-only partial functions are NOT required to be total — their classification is merely reported. The walk is untrusted: a function it misses simply stays uncertified (opaque to δ), never a soundness hole (§7). (Surface `@total` annotations and the full program are wired into this walk at integration time, M9.2.)

- [ ] **Step 1:** Failing tests — build a `Core.Env` with `SF`'s `seq` constructor (whose result index is `and(d1,d2)`) and the `and` def; `and` is in `type_level_fns(env)` (reached via `seq`'s index expression) and, being structurally total, certifies via M7.2; **negative:** a non-total function used in a type → `{:error, {:totality_required, name}}` (the §10 code, naming the fn); a partial **runtime-only** def (referenced in no type, not `@total`) is allowed — no error, reported as partial.
- [ ] **Step 2:** Run `mix test test/cure/elab/totality_closure_test.exs` — FAIL.
- [ ] **Step 3:** Implement the closure walk per spec §7 (mark type-level fns transitively); submit each to `Kernel.validate_certificate`; map a failure to `:totality_required`. Reach `lib/cure/types/totality.ex` only *through* the kernel (M7.2), never trusting its verdict directly here.
- [ ] **Step 4:** Run — PASS.  → **Step 5:** Commit `feat(elab): type-level totality closure emitting totality-required`.

---

## Milestone M8 — Elaborator (surface → Core): implicits, pattern compilation, holes

**Reference:** `reference/idris2/src/TTImp/Elab/{Check,App,ImplicitBind,Binders,Term}.idr`, `reference/idris2/src/Core/Unify.idr`; pattern matching `reference/agda/src/full/Agda/TypeChecking/Rules/LHS.hs` + `Rules/LHS/Unify.hs` + `Coverage.hs`, `reference/idris2/src/Core/Case/CaseBuilder.idr`; holes `reference/idris2/src/TTImp/Elab/Hole.idr`.

### Task M8.0: surface declarations (`type` / `indexed type`) → Core families + constructors

**Files:** Create `lib/cure/elab/declarations.ex`; Test `test/cure/elab/declarations_test.exs`. (Depends only on the M3 family API + M2 kernel, so it runs first in M8; no dependency on the expression elaborator M8.1.)
**Interfaces:** `Declarations.elaborate(decl_ast, env) -> {:ok, env'} | {:error, diag}` — turns a surface `type X = …` ADT and an `indexed type D(…) where cⱼ : …` GADT into `Inductive.family/4` + `Inductive.ctor/3` (M3.1) registered in `Core.Env`, computing each constructor's `result_indices` term and the family's universe level, then running `Kernel.check_family`/`check_ctor` (M3.2) + `Inductive.positive?` (M3.3) so only well-formed families are registered. Consumes the existing parser AST for declarations (read `lib/cure/compiler/parser.ex`).

- [ ] **Step 1:** Failing tests — elaborating surface `type Dec = Dcoupled | Causal` registers a Core family at level 0 with two nullary ctors (`Kernel.check_family` accepts it); elaborating `indexed type SF(as,bs,d) where prim : … ; seq : SF(as,bs,d1) -> SF(bs,cs,d2) -> SF(as,cs,and(d1,d2))` registers a family whose `seq` ctor has `result_indices` `[as, cs, and(d1,d2)]` (matching the hand-built family of M3.1) and passes `check_family`/positivity; **negative:** a declaration with a non-strictly-positive ctor → `{:error, :non_strictly_positive}` (surfaced from M3.3).
- [ ] **Step 2:** Run `mix test test/cure/elab/declarations_test.exs` — FAIL.
- [ ] **Step 3:** Implement declaration elaboration per `reference/idris2/src/TTImp/ProcessData.idr` (data declaration processing); build the Core family/ctors and submit them to the kernel checks.
- [ ] **Step 4:** Run — PASS.  → **Step 5:** Commit `feat(elab): elaborate type/indexed-type declarations to Core families`.

### Task M8.1: surface AST → Core for the non-dependent core (Type/fn/app/var)

**Files:** Create `lib/cure/elab/elaborator.ex`; Test `test/cure/elab/elaborator_test.exs`.
**Interfaces:** `Elab.elaborate(surface_ast, ctx) -> {:ok, core_term, type_value} | {:error, diag}`. Consumes the existing parser AST (read `lib/cure/compiler/parser.ex` for node shapes).

- [ ] **Step 1:** Failing test — elaborating `fn id(x: Type) -> Type = x`-shaped surface yields a Core `λ` that `Kernel.check`s against `Π(Type0).Type0`.
- [ ] **Step 2:** Run `mix test test/cure/elab/elaborator_test.exs` — FAIL.
- [ ] **Step 3:** Implement bidirectional elaboration for the basic fragment, emitting Core terms the kernel accepts. Reference Idris `Elab/Check.idr`.
- [ ] **Step 4:** Run — PASS.  → **Step 5:** Commit `feat(elab): elaborate basic fragment to Core`.

### Task M8.2: metavariables + Miller-pattern unification (implicit inference)

**Files:** Create `lib/cure/elab/unify.ex`, `lib/cure/elab/implicits.ex`; Test `test/cure/elab/unify_test.exs`.
**Interfaces:** `Unify.fresh_meta/1`, `Unify.unify(v1, v2, depth) -> {:ok, subst}|{:error,_}` (Miller patterns only); `Implicits.insert(elab_result, expected)` inserts/solves implicit args; unsolved → `{:error, {:uninferable_implicit, ctx}}`.

- [ ] **Step 1:** Failing tests — `compose(l, r)` with all `{as,bs,cs,d1,d2}` implicit: unification solves them from `l`/`r`'s types; **negative:** a genuinely ambiguous (non-Miller) constraint → `{:error, :uninferable_implicit}`.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement per `reference/idris2/src/Core/Unify.idr` (pattern-fragment occurs-check + solve). → **Step 4:** PASS. → **Step 5:** Commit `feat(elab): metavariables + Miller-pattern unification`.

### Task M8.3: erasure marking ({0,ω}) + check

**Files:** Modify `lib/cure/elab/implicits.ex`; Test `test/cure/elab/unify_test.exs`.
**Interfaces:** `Implicits.mark_erasure(core_term) -> {:ok, annotated}|{:error, {:erased_used_relevantly, var}}` — implicits/type-level/`Eq`-proofs marked `0`; verifies a `0` binder is never scrutinised at runtime.

- [ ] **Step 1:** Failing tests — `compose`'s implicits mark `0` and pass; **negative:** a fn that runtime-pattern-matches on a `0`-marked arg → `{:error, :erased_used_relevantly}`.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement the `{0,ω}` usage check (read `reference/idris2/src/Core/LinearCheck.idr`, taking only the 0/ω slice). → **Step 4:** PASS. → **Step 5:** Commit `feat(elab): checked {0,ω} erasure marking`.

### Task M8.4: dependent pattern compilation + index unification + coverage

**Files:** Create `lib/cure/elab/patterns.ex`; Test `test/cure/elab/patterns_test.exs`.
**Interfaces:** `Patterns.compile(clauses, scrut_type, ctx) -> {:ok, core_case}|{:error, {:coverage,_}|{:index_unification,_}}` — compiles surface `match` clauses into a Core `:case`, running index unification per branch (refining indices) and a coverage check; emits impossible-branch elimination.

- [ ] **Step 1:** Failing tests — `step`'s `match sf { prim → … ; seq → … }` compiles to a Core `:case` the kernel accepts with per-branch index refinement; **Σ pair-pattern:** a `match p { (d, sf) → … }` over a `Σ(Dec).SF(as,bs,#0)` compiles to a Core `:case`/projection the kernel accepts, binding *both* components with the body's dependency on the first (this is the only place Σ pattern compilation is exercised, so it gets its own red test); **negative #1:** a non-exhaustive match → `{:error, :coverage}`; **negative #2:** a clause forcing an impossible index unification → flagged impossible/rejected.
- [ ] **Step 2:** Run `mix test test/cure/elab/patterns_test.exs` — FAIL.
- [ ] **Step 3:** Implement per `reference/agda/.../Rules/LHS/Unify.hs` + `Coverage.hs` and `reference/idris2/src/Core/Case/CaseBuilder.idr`. Start with the two-ctor `SF` (spec §12 risk note). Σ pair-patterns too (split a `:pair`).
- [ ] **Step 4:** Run — PASS.  → **Step 5:** Commit `feat(elab): dependent pattern compilation + coverage`.

### Task M8.5: holes — recognition + `:hole_goal` reporting

**Files:** Create `lib/cure/elab/holes.ex`; Modify the parser to accept `?name`/`??` (read `lib/cure/compiler/parser.ex`); Test `test/cure/elab/holes_test.exs`.
**Interfaces:** `Holes.recognise(surface) -> hole_nodes`; on elaboration each hole emits a `:hole_goal` pipeline event `{goal_type, local_context}` and the program is marked non-codegen.

- [ ] **Step 1:** Failing tests — `?body` parses to a hole node; elaborating `sketch … = ?body` emits a `:hole_goal` carrying the expected type `SF(as,cs,and(d1,d2))` and the in-scope vars with types; the module is flagged "has unfilled holes → no BEAM".
- [ ] **Step 2:** Run `mix test test/cure/elab/holes_test.exs` — FAIL.
- [ ] **Step 3:** Implement parser support + hole reporting per `reference/idris2/src/TTImp/Elab/Hole.idr`. (Replaces retired `types/holes.ex`.)
- [ ] **Step 4:** Run — PASS.  → **Step 5:** Commit `feat(elab): holes with goal-type reporting`.

---

## Milestone M9 — Erasure → existing codegen

**Reference:** spec §8; existing `lib/cure/compiler/codegen.ex`.

### Task M9.1: erase checked Core → runtime AST

**Files:** Create `lib/cure/core/erase.ex`; Test `test/cure/core/erase_test.exs`.
**Interfaces:** `Erase.erase(annotated_core_term) -> runtime_ast` — consumes the `{0,ω}`-**annotated** Core produced by `Implicits.mark_erasure/1` (M8.3), **not** bare kernel-checked Core (which is fully relevant and mark-free per §4.1). The annotated term is what flows Elab(mark, M8.3) → Kernel(checks the relevant projection, ignores the marks) → Erase. Drops `0`-marked binders, type-level data, universe levels, `Eq` proofs; family ctors → tagged tuples; `:case` → runtime case. `SF`'s value structure (tags + embedded transition fns) survives; its index args erase (§8).

- [ ] **Step 1:** Failing tests — erasing `compose` drops the 5 implicits; erasing `forget_dec` yields a 2-tuple; erasing `SF` ctors yields tagged tuples carrying the transition function, with index args gone; `Eq`/`refl`/`rewrite` erase to their payload/identity.
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement erasure to the shape `codegen.ex` consumes. → **Step 4:** PASS. → **Step 5:** Commit `feat(core): erase Core to runtime AST`.

### Task M9.2: pipeline wiring — route the dependent fragment through Elab+Kernel+Erase

**Files:** Modify `lib/cure/compiler.ex` (the `maybe_check` seam, read it first); Test `test/cure/core/pipeline_test.exs`.
**Interfaces:** Compilation routes `indexed type`/dependent fns through Elab→Kernel→Erase→codegen; non-dependent surface + refinements stay on the existing `checker.ex` path (spec §12 seam).

- [ ] **Step 1:** Failing test — a module with an `indexed type` + `compose` compiles to BEAM (`{:ok, _beam}`); a plain refinement-typed module still compiles via the old path (regression guard).
- [ ] **Step 2:** Run — FAIL.  → **Step 3:** Implement the seam (detect dependent constructs, dispatch). The routed Elab pass runs, in order: declaration elaboration (M8.0), function-def elaboration (M8.1/M8.4) + `Core.Env` registration/`check_def` (M7.1), the type-level totality closure (M7.3, with surface `@total` flags supplied here), then kernel check + erase. → **Step 4:** PASS. → **Step 5:** Commit `feat(compiler): route dependent fragment through Core pipeline`.

---

## Milestone M10 — Slice-1 acceptance (the §6 program + negatives)

### Task M10.1: positive acceptance — construct + run one step

**Files:** Create `test/cure/core/slice1_acceptance_test.exs`; fixture `test/fixtures/slice1.cure` (the §6 program).
**Interfaces:** end-to-end through the real compiler + run on generic-unix.

- [ ] **Step 1:** Failing test — compile `slice1.cure`; assert it type-checks; assert `compose(prim_a, prim_b)` has inferred type `SF(as,cs,Causal)`; **run one `step`** and assert the output value (a concrete sequential-composition step) matches the hand-computed expected. **Fixture note:** keep `slice1.cure` self-contained — declare `SVDesc` as its own minimal inductive (e.g. `type SVDesc = SVNil | SVCons(Sig, SVDesc)`) rather than `List(Sig)`, since Slice 1 needs only the descriptor *type* (no `++`/`map`, deferred per §2) and M8.0 elaborates such sum-type declarations directly — this avoids an unstated dependency on a stdlib `List` family or type-alias machinery that the Core pipeline does not yet handle.
- [ ] **Step 2:** Run `mix test test/cure/core/slice1_acceptance_test.exs` — FAIL.
- [ ] **Step 3:** Resolve whatever the references indicate for any gap (this task does no new impl beyond wiring fixtures; if it fails, the defect is in M1–M9 — fix there with a new red test, never by weakening this one).
- [ ] **Step 4:** Run — PASS.  → **Step 5:** Commit `test(core): Slice 1 positive acceptance`.

### Task M10.2: negative acceptance — the five §6 rejections

**Files:** Modify `test/cure/core/slice1_acceptance_test.exs`; fixtures per case.

- [ ] **Step 1:** Failing tests, one per §6 negative — (a) middle-index mismatch → `:index_unification`; (b) declared index contradicts `and` → `:conversion` (assert both normal forms in the message); (c) non-total `and` used in a type → `:totality_required` (emitted by the elaborator closure walk, M7.3); (d) Σ pair 2nd-component mismatch → `:sigma_mismatch`; (e) unfilled hole → `:hole_goal` emitted AND no BEAM produced.
- [ ] **Step 2:** Run — FAIL (cases not yet all wired to the right codes).
- [ ] **Step 3:** Ensure each diagnostic code (spec §10) is emitted; fix at the source module with its own red test if missing.
- [ ] **Step 4:** Run — PASS.  → **Step 5:** Commit `test(core): Slice 1 negative acceptance`.

---

## Milestone M11 — Conformance corpus seed + serialization (C2/C3)

### Task M11.1: conformance corpus of Core terms

**Files:** Create `test/cure/core/corpus/` (serialized Core terms via `Term.to_external`) + `test/cure/core/conformance_test.exs`.
**Interfaces:** `Conformance.run(corpus) -> results` — each entry is `{external_term, expected: :checks | {:rejects, code}}`; the test runs the kernel over the corpus.

- [ ] **Step 1:** Failing test — load N positive + M negative external terms (seeded from M1–M6 kernel tests), run the kernel, assert each matches its expected verdict.
- [ ] **Step 2:** Run `mix test test/cure/core/conformance_test.exs` — FAIL.
- [ ] **Step 3:** Implement the corpus loader/runner; seed it from existing kernel tests (reuse, don't duplicate). This is the **C3** artifact the Phase-2 self-host will differentially test against.
- [ ] **Step 4:** Run — PASS.  → **Step 5:** Commit `test(core): conformance corpus seed (C3)`.

### Task M11.2: retire the faked modules

**Files:** Delete `lib/cure/types/{sigma,pi,equality,dependent,holes,reduce}.ex` and their now-obsolete tests; Modify any references in `lib/cure/types/type.ex`/`checker.ex` that dispatched to them (read first; the audit lists the dispatch sites).

- [ ] **Step 1:** Failing test — a regression test asserting the dependent fragment still compiles (M9.2) and the faked-module functions are gone (`Code.ensure_loaded?` returns false for `Cure.Types.Sigma` etc.).
- [ ] **Step 2:** Run — FAIL (modules still present).
- [ ] **Step 3:** Delete the six modules; remove/redirect dispatch sites in `type.ex`/`checker.ex` (the `:sigma`/`:eq` subtype/resolve/display clauses) to the Core path or drop them; run the full suite once to catch fallout.
- [ ] **Step 4:** Run `mix test` (ONCE, whole suite) — Expected: PASS (no references to deleted modules).
- [ ] **Step 5:** Commit `refactor: retire faked dependent-type modules (replaced by Core/Elab)`.

---

## Self-Review

**Spec coverage:** §4.1 nodes → M0/M1/M4/M5/M6; §4.3 universes → M1.1/M2.2; §4.4 families+case → M3/M4; §4.5 conversion → M1.5/M7.2; §4.6 Eq/rewrite → M6; §4.7 Σ → M5; §5 architecture (kernel/elab split) → M2/M8; §5.1 module layout → all; §7 totality (global def check → M7.1; kernel re-validation → M7.2; elaborator type-level closure → M7.3); §8 erasure → M9; §6 Slice-1 program + negatives → M10; §10 diagnostics → M10.2 (`:totality_required` via M7.3, `:index_unification` via M8.4, `:conversion`/`:universe_ceiling`/`:sigma_mismatch`/`:hole_goal` at their source tasks); §11 testing layers → M1–M7 (kernel unit + totality), M7.3/M8 (elab), M10 (acceptance); commitments C2/C3 → M0.3/M11.1; retire faked modules (§1/§5.1) → M11.2. (The plan creates `inductive`/`quote`/`certificate`/`erase`/`declarations`/`totality_closure` beyond §5.1's module sketch — finer granularity on the same trusted/untrusted boundary, not a deviation.) No uncovered spec section.

**Placeholder scan:** Implementation steps for novel kernel internals cite the exact reference file + algorithm + interface signatures rather than pre-written speculative code — this is intentional per the Global "reference-first" rule and the research-grade domain, not a placeholder; every *test* step is concrete and immutable. M0.2 Step 1 now uses concrete, convention-stable assertions (closed replacements pin the under-binder behaviour without depending on the shift-of-replacement off-by-one), so there is no remaining contrived/placeholder test.

**Type consistency:** `Conv.conv?/4` (the sole conversion signature — η is handled in conv, type-free; no type-indexed variant), `Eval.eval/2`, `Quote.reify/2` (β-normal, untyped — η lives in conv, not read-back), `Kernel.{infer/2,check/3,check_def/2,validate_certificate/2}`, `Core.Env.add_def/4`, `TotalityClosure.type_level_fns/1`, `Unify.unify/3`, `Patterns.compile/3`, `Erase.erase/1` (consumes the M8.3-annotated Core), `Term.{shift/3,subst/3,to_external/1,from_external/1}` are used consistently across milestones. `infer` of a constructor application returns the `:vdata` type value (M1.2 shape). Value/neutral and term node tags match §4.1.

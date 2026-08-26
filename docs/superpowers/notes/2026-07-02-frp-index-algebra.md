# FRP index algebra — `loop` decoupledness, and the `switch`/`Init` scope gate

_Task 6.1 (= B4 scope-expansion gate). Re-derives the index algebra for the
FRP capstone the same way the design spec §2 did for `≫`/`∗∗`, and records
explicitly where the derivation is bounded by source availability._

## What is already grounded (spec §2 + the live oracle probes)

The core family is fully specified in `2026-06-30-cure-dependent-types-frp-design.md`
§2 and realised in `test/oracle/frp/frp01`,`frp02` (both `same`):

```
Dec  = DDec | DCau                      -- decoupledness flag
dmeet : Dec → Dec → Dec                 -- the paper's ∧: DDec iff BOTH DDec
SList = SNil | SCons Sig SList          -- SVDesc (signal-vector descriptor)
app   : SList → SList → SList           -- the paper's _++_

SF : SList → SList → Dec → Type
  prim : SF av bv DCau                                        -- a causal primitive
  seq  : SF av bv d1 → SF bv cv d2 → SF av cv (dmeet d1 d2)   -- ≫
  par  : SF av bv d1 → SF cv dv d2 → SF (app av cv)(app bv dv)(dmeet d1 d2)  -- ∗∗
```

`seq`/`par` refine the `Dec` index by `dmeet` and the `SList` indices by `app`.
The nested-`app` conversion this forces is exactly what Phase 4a's kernel fix
(09a80f3) made decidable, so `parAssoc` (frp01) checks.

## The `loop` index algebra (this note's derivation)

`loop` closes a feedback path: outputs `cs` are fed back as inputs `cs`. The
paper's **safety invariant** is that a feedback signal must not depend
*instantaneously* on itself — the sub-behaviour producing the fed-back signals
must be **decoupled**. In the single-`Dec`-per-SF model realised above, the
faithful (sound, slightly conservative) encoding of that invariant is:

```
  loop : SF (app av cv) (app bv cv) DDec → SF av bv DCau
```

i.e. `loop` accepts a body only when the WHOLE body is decoupled (`DDec`), which
implies the feedback sub-path is decoupled; the looped result is causal (`DCau`),
since its output can depend instantaneously on the external input `av` through
the forward path. Consequences, both demonstrable through the differential
oracle (Cure ↔ Idris, identical definitions):

- **Well-formed** (frp03): a decoupled body (`DDec`, e.g. `seq` of two decoupled
  stages) loops → `accept/accept`. The instantaneous cycle is broken.
- **Instantaneous / ill-formed** (frp04): a causal body (`DCau`, e.g. `prim`)
  cannot be looped — `DCau ≠ DDec` at `loop`'s argument index → `reject/reject`.
  This is the paper's headline result: *ill-formed feedback loops are rejected
  statically*, and it needs NO new mechanism beyond `dmeet`/`app` refinement +
  the 4a conversion fix.

**Conservativeness note (honest).** The ICFP'09 system tracks decoupledness at
a finer grain than one flag per SF (it can require only the *feedback projection*
to be decoupled while the forward path stays causal). The whole-body-`DDec`
constraint above is a sound over-approximation: it rejects every genuinely
instantaneous loop (no false accepts — the safety direction is preserved) and
may reject some loops the finer system would admit (false rejects — a
completeness, not soundness, gap). The capstone demonstrates the SAFETY property;
recovering the paper's exact per-signal decoupledness is a finer-index refinement
that does not change the mechanism set (still `Dec`-lattice refinement).

## Scope gate — `switch` / `Init` need source not in the tree

Task 6.1 Step 2 asks whether Phases 1–5's mechanisms generalise to the full
4-index family (`Init` + `switch`/`rswitch`/`dswitch`). **They cannot be derived
rigorously here:** the Sculthorpe–Nilsson Agda source is NOT vendored
(`reference/` holds only the Idris2/Lean4/Agda *kernel* reference impls, per its
MANIFEST), and the design spec explicitly **defers** `Init`/uninitialised-signal
descriptors and the `switch`/`dswitch` constructors "to later slices" (§ Deferred).
Deriving their computed-index/constructor shape from memory would violate the
cure-porting rule "verify against source, not memory," and a wrong index algebra
would silently mis-specify the capstone.

## Two elaborator gaps surfaced by the `loop` capstone (Task 6.2 findings)

Building the `loop` probes exposed two E-layer gaps — both about **computed
indices in constructor ARGUMENT positions**, neither a TCB matter:

1. **Implicit inference (FIXED, this run).** An index variable occurring only
   inside a computed index in a constructor argument (the fed-back `cv` in
   `loop : SF(app(av,cv), app(bv,cv), DDec) → …`) was never harvested as an
   implicit — `collect_implicit_vars` only read bare vars sitting directly in a
   family application — so the kernel saw a dangling reference and rejected the
   whole family with `:unknown_global`. Fixed in `declarations.ex`: harvest
   bare-variable arguments of a non-family global call too, typed by that
   function's domain telescope. Red-green in
   `test/cure/elab/computed_index_arg_test.exs`. This unblocks frp03/frp04.

2. **Composed-loop `loop(seq(a,b))` — CLOSED (2026-07-03), entirely in the
   elaborator, NO kernel change.** The original diagnosis below called the second
   layer a TCB/kernel gap; that was WRONG. Re-derived against real normal forms:
   `conv_values?(dmeet(DDec,DDec), DDec, sig)` is already `true` (the kernel's
   δ-capable conversion reduces the computed index fine — `seq(a,b)` checks
   against a `DDec` return type unaided). The reach was TWO **elaborator** bugs:
   (a) `Unify` was purely syntactic, so `DDec` vs the redex `dmeet(DDec,DDec)`
   gave `:cannot_unify` — fixed by a δ-convertibility fallback through the trusted
   `Conv` on closed meta-free terms (`Unify.unify/4`); and (b) `finish_ctor_app`
   evaluated a ctor's computed result type under `[]`, mis-levelling caller-frame
   index variables, which corrupted meta-solving when that type fed the outer
   `loop` application — fixed by evaluating under the caller's env. Oracle
   `frp05_computed_index_arg` + `frp06_composed_loop` both `same`. The TCB was NOT
   expanded: per the "prove no untrusted term works first" rule, the untrusted
   elaborator fix was found, so the kernel stays untouched. Original (now
   superseded) diagnosis retained below for the record:

   **[SUPERSEDED] Composed-loop `loop(seq(a,b))` — was believed a TWO-LAYER reach
   with a TCB second layer.**
   The probe: a loop whose body is a composition, so `seq`'s result Dec index is
   `dmeet(DDec, DDec)` fed to `loop`'s `DDec` slot. Idris reduces it and accepts;
   Cure rejects (a genuine `cure=reject / idris=accept` reach — verified live,
   then the probe was removed to keep the committed oracle green). Diagnosed to
   TWO independent layers, both of which must be fixed for parity:

   - **(a) E-layer — the elaborator's argument index-unification is syntactic.**
     `solve_arg` (`elaborator.ex`) calls the first-order `Unify` on the ctor
     argument's inferred type; `Unify` compares `DDec` vs `dmeet(DDec,DDec)`
     syntactically → `{:cannot_unify, …}`. A prototyped fix (retry-on-failure,
     reducing only the **ground/closed** index arguments — `dmeet(DDec,DDec)→DDec`
     — while leaving open neutral spines like `app(av,cv)` intact so they still
     unify against the ctor's index metavariables; a full `normalize` wrongly
     δ-unfolds the stuck `app` into a `case`-tree) resolves THIS layer. Sound
     (retry only on failure; ground reduction cannot capture). Not committed
     because it does not flip the probe green on its own — layer (b) still bites.

   - **(b) TCB-layer — the KERNEL's index unification does not normalise the
     computed index either.** With (a) applied, the assembled `loop(seq(a,b))`
     term reaches `Kernel.check` and is rejected with a bare `:index_mismatch`
     (`kernel.ex:558 remap_index_error` on the `{:vdata, SF, …}`). `loop(body)`
     with a *concrete* `DDec` body (frp03) checks fine, so the kernel's `{:vdata}`
     index unification specifically fails to reduce `dmeet(DDec,DDec) ≡ DDec` in
     this position. That is a **kernel completeness gap → HARD-STOP-and-review**:
     it needs a reviewed TCB change (index unification reducing a computed index
     before comparing) with the full gate (red-green + antibody + independent
     adversarial verification), not an E-layer patch. **Deferred.**

   Orthogonal to the safety demonstration (frp03/frp04 use directly-typed bodies).
   No soundness exposure at either layer — a false REJECT, never a false accept.

**Decision (explicit, not improvised):** the capstone (Task 6.2) demonstrates the
safety property on the *specified* core — `≫`/`∗∗`/`loop` + `Dec` decoupledness —
covering acceptance of well-formed nets and rejection of instantaneous cycles.
The `switch`/`Init` "uninitialised-signal escape" probe (6.2c) is **scoped out and
blocked on obtaining the ICFP'09 Agda source** (or an operator-supplied faithful
`Init`/`switch` signature). Mechanism prediction, to be confirmed when the source
arrives: `Init` is another computed index over a small lattice
(uninitialised/initialised), refined exactly like `Dec` by a `∨`/`∧`-style
operator, so no new kernel mechanism is expected — but this is a prediction, not
a grounded derivation, and Task 6.2c stays open until verified against source.

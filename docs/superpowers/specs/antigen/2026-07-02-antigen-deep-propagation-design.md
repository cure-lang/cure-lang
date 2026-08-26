# Antigen deep-propagation mutation — design (sub-project A of "deep injection")

**Parity ledger:** mutation-corpus follow-on. Closes the v1 limitation recorded in
the mutation-corpus report §"Accepted v1 limitation": v1 faults sit at their
scaffold root, so the corpus never tested whether the kernel correctly
**propagates a rejection up through many nested checked positions**
(error-swallowing / mis-threading at depth).

**Decomposition.** "Deep injection" is two sub-projects, sequenced; each its own
spec → plan → execute cycle. This spec is **A only**.
- **A — deep-propagation (this spec):** bury an *intrinsically*-ill-typed fault
  under D nested well-typed **checked** contexts. Tests error propagation up the
  checked-position stack. Cheap; no `Cure.Core.Term` changes.
- **B — conversion-at-depth (separate, next):** a *well-typed-but-wrong-type*
  subterm at a deep hole whose expected type must be **computed** by reducing its
  surroundings. Tests NbE/conversion at depth. Needs a `Term` seam. **Not in this
  spec** — its faults fail through a different kernel path (conversion, not
  intrinsic-infer-failure), so A does not subsume it and vice versa.

**One-liner:** wrap each v1 fault term in `D` nested well-typed checked contexts
(drawn from a 6-kind wrapper set), so `Kernel.infer` must thread the fault's
rejection up through `D` distinct error-propagation sites; a survivor is a real
error-swallowing bug.

---

## 1. Scope

Extends `Antigen.Generators.Mutation` (the 7 v1 operators) with a `deepen` layer.
Reuses the `:mutant_term` challenge kind and `Antigen.Assays.Mutation` **unchanged**
(the assay is still "`infer` must reject"). Depth 0 = today's shallow mutant, so
this is a strict generalization — existing behavior and banked seeds are
unaffected.

**Non-goals (deferred):** sub-project B (conversion-at-depth); context-dependent
faults (a fault that references carrier-bound variables — would need de Bruijn
re-indexing, explicitly avoided here per §4); a Sigma/pair *goal* in the menu
(the pair wrapper synthesizes its own Σ locally).

---

## 2. The bug class and why v1 misses it

v1 faults are *intrinsically* ill-typed: `infer(fault)` fails on the fault term
itself. When such a fault is the whole mutant (or one level down), the kernel
rejects it in one or two steps. What is never exercised: a fault buried `D` levels
deep, where the kernel must **carry the `{:error, _}` back up** through `D`
nested `with {:ok, _} <- …` chains — `check_ctor_app_rec`, `check_case_branches`,
the app-argument `check`, the Σ-component `check`. An error-swallowing or
mis-threading bug in any one of those paths would make a *deep* fault wrongly
**accepted** while its shallow twin is rejected. That gap is exactly what A fills.

---

## 3. Mechanism — recursive checked-wrapper stack

`deepen(ctx, term, fault, depth)` wraps `term` in `depth` nested checked contexts.
Each layer draws a wrapper kind uniformly from the set below and places `term`
(the running inner term) at that layer's **hole** — a checked argument position
that `infer` must descend into. The layer's other positions are well-typed filler
drawn from `Term.gen_term`/`SigMenu.canon`. Because the innermost term is
intrinsically infer-failing and every layer forces `infer` into its child, the
failure threads up all `D` layers (verified to depth 20).

**Wrapper set (6 — one per distinct kernel error-propagation path).** Verified:
each rejects a broken hole via the named reason; each is well-typed when the hole
is well-typed (a genuine checked context, control-tested).

| `wrap` kind | shape (hole = running inner term) | propagation path / reason |
|---|---|---|
| `:app_arg` | `{:app, {:app, {:global,:plus}, hole}, filler_nat}` | app-argument `check` → `:not_a_sigma`/`:foreign_ctor` |
| `:ctor_nat` | `{:ctor, :S, [hole]}` | Nat ctor-arg → `:index_mismatch` |
| `:ctor_vec` | `{:ctor, :vcons, [z, hole, filler_vec0]}` (`n=Z`, `filler_vec0 : Vec Z`) | Vec ctor-arg (`check_ctor_app_rec`) → `:index_mismatch` |
| `:case_scrut` | `{:case, hole, const_motive, arity0_branches}` | scrutinee `infer` → propagated |
| `:case_branch` | `{:case, filler_scrut, const_motive, [{:Z,0,hole}, {:S,1,filler}]}` | branch-body `check` → `:branch_type` |
| `:pair` | `{:app, {:lam, {:sigma,nat,nat}, filler_nat}, {:pair, hole, filler_nat}}` | Σ-component `check` (`check(pair, vsigma)`) → `:sigma_mismatch` |

Notes:
- **`:pair` reaches the Σ-component path without a Σ goal in the menu** by
  applying a locally-built `λ p:Σ Nat Nat. filler` to `pair(hole, filler)`, so the
  pair is *checked* against Σ. A **bare** pair (or `fst`/`snd` of a bare pair) must
  never be generated: `infer` has no pair clause and **crashes** (not a graceful
  `{:error}`) on one — see §5. The pair wrapper's pair is always a checked
  argument, never bare.
- **Depth counts wrapper *applications*, not structural levels** — the `:pair`
  wrapper nests two term constructors but contributes **one** propagation level.
  `wrap_path` (length = depth) records the kind sequence.

---

## 4. Correctness invariant (carried from v1, extended)

Every deep mutant must still satisfy the v1 invariant (construction-guaranteed
ill-typed; §3 of the mutation-corpus spec), plus two A-specific clauses:

> **(c) Every wrapper layer is a checked position** — `infer` provably descends
> into the hole (each of the 6 verified above), so the innermost fault's
> `{:error, _}` is reachable and must propagate to the top-level `infer`.
>
> **(d) No binder over the hole** — hole placement never introduces a binder that
> scopes the hole: `:case_branch` uses an **arity-0** branch (`Z`/`T`), and
> `:pair` places the hole in the app **argument**, not under the `λ`. Therefore the
> inner term keeps its original de Bruijn indexing and needs **no `Term.shift`**.
> (Faults that reference carrier-bound variables are a sub-project-B concern.)

Clause (c) is what makes "a survivor is a real bug" sound: if `infer` accepts a
deep mutant, the kernel *failed to propagate* a rejection it makes shallowly —
a genuine error-threading defect.

---

## 5. `infer` totality (no crashes)

The assay contract is `:ok | {:violation, …}`; a *crash* during `infer` breaks it.
The probe found `infer` **crashes** (`FunctionClauseError`) on a bare pair (no
infer clause). Constraint: the generator must keep every mutant **infer-total**
(graceful `{:error, _}`). The 6 wrappers all do (verified). The construction
guarantee test (§7.1) asserts `{:error, _}` and would surface any crash loudly as
a test error, so this is enforced, not merely intended. (A kernel *crash* on an
ill-typed term is a robustness issue, not a soundness violation, and is out of
scope for the rejection assay.)

---

## 6. Challenge model + health gate

**Challenge model.** Reuse `:mutant_term`. Extend the `fault` record:
```
fault = %{
  kind, witness, expected_head, injected_head, scope,   # v1 fields, unchanged
  depth: non_neg_integer,                               # NEW: wrapper applications (0 = shallow)
  wrap_path: [atom]                                     # NEW: wrapper-kind sequence, length == depth
}
```
`depth: 0` / `wrap_path: []` for a shallow (v1) mutant. New atoms to intern in
`Challenge.@known_atoms`: the 6 wrapper kinds
(`:app_arg, :ctor_nat, :ctor_vec, :case_scrut, :case_branch, :pair`) and the two
new field keys (`:depth, :wrap_path`). These ride in the `fault` map through the
scaffold `binary_to_term [:safe]` path, so — as the v1 key-atom fix showed — both
keys and values must be interned.

**Legacy banked records.** The 7 `:mutant_term` seeds already banked in
`test/antigen/seeds.sexp` (from the v1 mutation-corpus spec) predate these two
fields entirely — their decoded `fault` maps carry only the five v1 keys, with no
`:depth`/`:wrap_path` present at all (not even defaulted). Any code that reads
`fault.depth` / `fault.wrap_path` — the `mutation_metrics/1` extension (below in
this section, and §8) and its static-replay meta-test over the banked corpus
(§7.6) — MUST read
them defensively (`Map.get(fault, :depth, 0)` / `Map.get(fault, :wrap_path, [])`),
never by strict field/dot access, else replaying the pre-existing shallow seeds
crashes the meta-test with a `KeyError`. This is the same class of hazard the v1
key-atom fix guarded against, one level up: there the risk was an uninterned
atom; here it is an absent key from a record shape written before the key
existed.

**Generation.** `mutant/0` draws a base kind (existing 7 → shallow fault via
`build/2`), then draws `depth D` **uniformly** from `0..@max_depth` (matching the
per-layer wrapper-kind draw's uniformity above) and applies `deepen`. `@max_depth`
is a small constant (≈8) bounded by per-term `infer` cost, not construction cost.
Uniformity, not a shallow-skewed distribution, is what makes the `depth ≥
@depth_floor` test (§7.2) reliably non-flaky at ordinary batch sizes.

**Health gate (A-specific vacuity guards).** The v1 gate only checks `fault.kind`
diversity. Add two metrics over the `:mutant_term` subset (a corpus of all
depth-0, or all-one-wrapper, mutants is vacuous *for A*):
- **`max_depth`** — the deepest mutant generated; floor `≥ @depth_floor` (e.g. 4).
- **`wrap_diversity`** — count of distinct wrapper kinds exercised across the
  subset; floor `≥ @wrap_floor` (e.g. 4 of 6).

Unlike `reason_diversity` (scoped to *correctly-rejected* mutants only — §6.2 of
the mutation-corpus spec), both new metrics are **generation-quality** signals and
are computed over **every** `:mutant_term` challenge in the subset, regardless of
its assay verdict: whether the generator produced deep, diverse mutants is a
construction-time property, independent of whether the kernel happened to reject
each one correctly. Scoping them to rejected-only (mirroring `reason_diversity`'s
implementation shape by accident) would silently exclude any survivor's own
depth/wrap_path from the count — exactly the corpus slice the gate most needs to
see.

Both fold into the existing health line and stamp:
`antigen health[mutant_term]: reason_diversity=… max_depth=… wrap_diversity=… survivors=… → healthy|vacuous`.
The stamp remains **vacuity-only** (diversity + depth + wrap floors); `survivors`
stay a separately-surfaced infection, never folded into the stamp (v1 §6.2 rule).

---

## 7. Testing (TDD; artifact is executable code)

Red-green per plan step, matching the mutation-corpus spec's discipline: each
behavior below gets a failing test written first, then only the implementation
needed to turn it green.

1. **Deep construction guarantee** — for each wrapper kind and a range of depths
   (0, 1, mid, `@max_depth`), sampled mutants `infer`-reject (`{:error, _}`). This
   also enforces §5 (a crash fails the test). The load-bearing test.
2. **Depth reached** — a sampled batch contains a mutant with `depth ≥ @depth_floor`
   (and `fault.depth` matches the term's actual wrapper nesting).
3. **Wrapper-path diversity** — a sampled batch exercises `≥ @wrap_floor` distinct
   wrapper kinds; `wrap_path` length equals `depth` for every mutant.
4. **`fault.kind` diversity retained** — the v1 diversity floor still holds over
   the now-deep corpus.
5. **Serialization round-trip** — a deep `:mutant_term` (with `depth`/`wrap_path`)
   survives `to_pieces |> encode_scaffold |> decode_scaffold |> from_pieces`
   unchanged (extends the v1 round-trip; guards the new atoms).
6. **Health metrics** — `Runner.mutation_metrics/1` reports `max_depth` /
   `wrap_diversity`; the stamp is `:healthy` when all floors met, `:vacuous`
   otherwise; a static-replay meta-test enforces the floors on the banked corpus.
7. **Backward compatibility** — depth-0 mutants are byte-identical to v1's shallow
   output; the existing mutation tests and banked shallow seeds stay green.

---

## 8. Architecture & integration

- **Modify** `lib/antigen/generators/mutation.ex` — add `deepen/4`, the 6 wrapper
  builders, `@max_depth`, and the depth draw in `mutant/0`; extend each `build/2`
  fault record with `depth: 0, wrap_path: []` (shallow default). Stays
  backend-free (no `StreamData` literal — the grep quarantine bit us twice).
- **Modify** `lib/antigen/challenge.ex` — `@known_atoms` += 6 wrapper kinds +
  `:depth, :wrap_path`. (`to_pieces`/`from_pieces` need no change — `fault` is
  already carried whole in the scaffold.)
- **Modify** `lib/antigen/runner.ex` — `mutation_metrics/1` computes `max_depth` +
  `wrap_diversity`; `mutation_stamp/1` and the health line include them.
- **Modify** `test/antigen/seeds.sexp` — bank deep `:mutant_term` seeds (covering
  the wrapper kinds and a depth ≥ floor), coverage-deduped.
- **Extend tests** (all three already exist from v1) — `test/antigen/generators/mutation_test.exs`
  (deep construction/depth/wrap-path), `mutation_health_gate_test.exs` (new
  metrics), `mutation_meta_test.exs` (static depth/wrap floors).

Constraints (verbatim): construction-guaranteed ill-typedness; StreamData
quarantine; ghost-authored commits (`Made In Heaven`, no `Co-Authored-By`); one
full build/test run at a time; fueled `nf` if ever added (the gate uses `infer`).

---

## 9. Relationship to sub-project B

B (conversion-at-depth) is the sequenced follow-on. It reuses this spec's depth
machinery and challenge fields but swaps the *fault*: instead of an
intrinsically-broken inner term, B places a **well-typed** subterm of the wrong
type at a hole whose expected type the kernel must **compute** (e.g. `Vec (plus n
m)`), exercising conversion/NbE at depth — a path A structurally cannot reach
(A's fault dies at its own `infer` before any expected type is consulted). Neither
subsumes the other; both together maximize coverage. B gets its own spec after A
lands.

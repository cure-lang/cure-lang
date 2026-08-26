# `cure port` — Interactive BEAM-to-dependent porting — Design

**Status:** approved design, pre-plan.
**Date:** 2026-07-13.
**Topic:** an interactive mode that lifts compiled BEAM (from Elixir, Erlang, or
Gleam), brute-force fits the shapes of its computation onto Cure's dependent
surface, auto-discharges what it can from a transliterated proof library, and
interactively elicits the proofs it cannot find.

---

## 1. Goal & core insight

Take a compiled BEAM module — regardless of whether it started as Elixir, Erlang,
or Gleam — reconstruct it as a Cure module on the dependent surface, and drive the
user through exactly the proof obligations that remain.

The load-bearing insight: **lift the BEAM, not the source.** All three languages
lower to **Core Erlang**, whose grammar is a small, finite set of ~20 node types.
Macros, guards, and pattern-match compilation are already expanded there, so we see
*exactly* what the computation is — never fooled by surface syntax disagreeing with
what the compiler actually produced. That finiteness lets us build a **near-total
shape catalog** with a hard `unsupported_shape` surface (no silent fallthrough),
in the fail-closed spirit of the rest of this codebase (Antigen's cover manifest,
the fail-closed Core walkers).

## 2. Background — existing leverage

- **`:beam_lib` abstract-code reading** already lives in `lib/antigen/cover.ex`
  (`:beam_lib.chunks(beam, [:abstract_code])`), the entry point for lifting BEAM.
- **Core Erlang** is reachable per language: Erlang via `compile:file(F, [to_core])`;
  Elixir via `abstract_code` from `debug_info` → the `:compile` core pass; Gleam
  emits Erlang source → the same `to_core` path.
- **`Std.Proof`** already proves inductive equalities over `Nat` using the identity
  type `Equivalent(T, a, b)`, `reflexive`, and `rewrite … in …`. It is the *form*
  every banked lemma takes.
- **The Lean oracle** (real Lean, kept as an untrusted checker) validates candidate
  proofs; the **transliteration differential-oracle harness** (`test/oracle/*`,
  currently Cure↔Idris) is the pattern for validating transliterated lemmas.
- **The trust ledger** (`cure audit trust`) already accounts for every unproved
  assumption; postulated obligations flow into it.
- **`cure migrate`/`cure rewrite`** are intra-Cure rewriters — precedent for a
  new source-transforming verb, but this is cross-language and new.

## 3. Scope & phasing

`cure port` is genuinely four sub-projects. This spec defines the whole
architecture and the phase boundaries; each phase is implemented under its own
plan, Phase 0 first.

- **Phase 0 — pipeline end-to-end.** BEAM Reader + Shape Catalog + Fitter to Cure's
  **value surface** (no dependent refinement yet). Obligations limited to Cure's
  mandatory totality / coverage / termination. Non-interactive: auto-discharge the
  trivial ones, postulate the rest, emit Cure source + a porting report. Proves the
  lift works on real BEAM.
- **Phase 1 — the Proof Hammer.** Index the port proof library (§7), search it, and
  check candidates with the Lean oracle / kernel.
- **Phase 2 — the Interactive Prover REPL.** Walk residual obligations; user
  supplies proofs, cites lemmas, postulates, or marks a function partial.
- **Phase 3 — dependent-refinement pass.** Propose length/`Fin`/refinement
  invariants (turning list ports into `Vector`/`Bounded` ports), plus an optional
  **source-type enrichment** hook (Gleam types, Erlang `-spec`, Elixir `@spec`) that
  sharpens reconstructed types and thereby *shrinks* the obligation set.

**Out of scope:** porting BEAM concurrency semantics (`receive`/process linking)
to typed channels beyond a faithful `Std.Otp.Raw` wrapper; re-deriving Gleam's full
type system; binary/bitstring dependent refinement (Phase-3+ stretch).

## 4. Architecture & components

- **`Cure.Port.Reader`** — per-language adapters obtain Core Erlang for each unit
  and normalize to one stream. Input: a `.beam` (or a source file it compiles
  first). Output: `[core_form]`.
- **`Cure.Port.Shapes`** — classify every Core Erlang node into a catalogued shape.
  The catalog is the ~20 Core Erlang node types, each with a fitting rule. Any node
  that does not classify → `{:unsupported_shape, node, location}` (surfaced, never
  dropped). Coverage of the grammar is measured like Antigen's cover manifest.
- **`Cure.Port.Fitter`** — map each shape to a Cure surface construct and
  reconstruct types: infer ADTs from constructor/atom/tuple usage, function
  signatures from call and return usage. Emits `{cure_ast, [obligation]}`.
- **`Cure.Port.Obligation`** — the obligation datatype (§6): a Cure proposition or a
  totality/coverage/termination certificate request, each tagged with its source
  location and the shape that raised it.
- **`Cure.Port.Hammer`** — auto-discharge: index the proof library by conclusion
  head-shape, apply cheap tactics (normalize-then-`reflexive`, structural-induction
  schemas, `rewrite` chaining), and check candidates with the Lean oracle / kernel.
- **`Cure.Port.Prover`** — the interactive REPL (§9).
- **`Cure.Port.Emitter`** — write the Cure module + a porting report; route every
  accepted postulate into the trust ledger.

## 5. Data flow

```
.beam (Elixir | Erlang | Gleam)
  → Reader        → [Core Erlang forms]
  → Shapes        → shape tree (+ unsupported_shape reports)
  → Fitter        → { Cure AST, [obligation] }
  → Hammer        → { discharged, residual obligations }
  → Prover        → { proofs | postulates | partiality marks }
  → Emitter       → Cure source + porting report + trust-ledger entries
```

## 6. Obligation taxonomy — where proofs come from

Even a *faithful* port generates proof work, because Cure demands what the BEAM
does not. Every obligation has one of these origins:

1. **Totality** — the function is defined on all inputs. BEAM clauses are frequently
   partial (a `case` with no catch-all, a head that only matches some shapes).
2. **Coverage** — `c_case` exhaustiveness, and the "impossible" branches that a
   refined index makes unreachable.
3. **Termination** — each `c_letrec` recursion is well-founded (Cure's size-change).
4. **Refinement invariants** (Phase 3) — any dependent index the Fitter proposes:
   length relationships, `Fin`/`Bounded` in-range facts, sortedness, etc.
5. **Partiality reshaping** — `throw`/`error`/`exit` and partial matches become
   either an `Option`/`Result` reshaping (which then needs the monad laws to
   compose) or a recorded postulate.

## 7. The port proof library — *exactly* which proofs to bank

This is the crux. The Hammer can only discharge obligations whose supporting lemmas
are present, so we **pre-bank a library of proven lemmas**, transliterated from the
standard libraries of Lean (Mathlib / std4), Agda (agda-stdlib), Coq (stdlib +
MathComp), and Isabelle/HOL (+ AFP). Each lemma is banked as a Cure `Std.Proof`-style
proven function returning an `Equivalent(T, …)` (or a `Dec`/`So`/`Acc` witness), and
validated on the way in via the transliteration differential oracle against its
source system. Modules live under `Std.Port.*`. The Hammer indexes them by the head
symbols of their conclusion for retrieval.

Banked by family, in rough priority order (lists/nat/ordering/termination dominate
real BEAM ports):

**7.1 `Std.Port.Nat` — natural-number & integer arithmetic.**
`plus`/`mult` associativity, commutativity, left/right identity, `plus_succ`,
distributivity, `zero`-annihilation; truncated subtraction (monus) laws; `min`/`max`
laws; ordering `<`/`≤` reflexivity, transitivity, antisymmetry, totality/trichotomy,
`≤`-succ, `lt_irrefl`; **`<` is well-founded on `Nat`** (feeds §7.7).
*Sources:* Agda `Data.Nat.Properties`; Lean `Mathlib.Data.Nat.Basic`,
`Init.Data.Nat`; Coq `Coq.Arith.PeanoNat`; Isabelle `HOL.Nat`, `HOL.Arith`.

**7.2 `Std.Port.List` — list algebra (the workhorse).**
`++` associativity, left/right `[]` identity; `length (xs ++ ys) = length xs +
length ys`; `map` fusion (`map_map`), `map_append`, `length (map f xs) = length xs`;
`reverse_append`, `reverse_reverse`, `length (reverse xs) = length xs`; `foldr`/
`foldl` laws and `foldl = foldr` for associative-with-unit ops; `filter` length
bound and membership; `take`/`drop` (`take_drop_append`, `length_take`, `length_drop`);
membership (`mem_append`, `mem_map`); **non-emptiness lemmas** (`head`/`tail` require
`xs ≠ []`) and **indexing bounds** (`nth`/`lookup` well-defined when `i < length` —
the bridge to `Bounded`/`Fin`).
*Sources:* Agda `Data.List.Properties`; Lean `Mathlib.Data.List.Basic`; Coq
`Coq.Lists.List`; Isabelle `HOL.List`.

**7.3 `Std.Port.Vec` — length-indexed vectors & `Fin`.**
`Vector`/`Fin` analogues that let a list port *gain* a length index: `lookup`/`update`
correctness, `append` length additivity, `map` preserves length by construction,
`Fin` bound arithmetic and coercions, `Fin 0` is empty, `Vector _ Z` is uniquely
`empty`. These discharge refinement (§6.4) and coverage-by-impossibility (§7.8).
*Sources:* Agda `Data.Vec.Properties`, `Data.Fin.Properties`; Lean
`Mathlib.Data.Vector`, `Mathlib.Data.Fin.Basic`; Coq `Coq.Vectors.Vector`,
`Coq.Vectors.Fin`.

**7.4 `Std.Port.Order` — ordering, comparison, sorting.**
Total-order laws (reflexive/antisymmetric/transitive/total) for `Int`/`Nat`/`Char`/
`String`; `compare` trichotomy ↔ `Ordering`; and, for ports of sort routines,
**permutation** and **sortedness** lemmas (insertion preserves sorted, `sort` output
is a sorted permutation of input).
*Sources:* Agda `Data.List.Relation.Unary.Sorted`,
`Data.List.Relation.Binary.Permutation.Propositional`; Lean `Mathlib.Order.Basic`,
`Mathlib.Data.List.Sort`, `Mathlib.Data.List.Perm`; Coq `Coq.Sorting.Sorted`,
`Coq.Sorting.Permutation`; Isabelle `HOL.List` (sorted/mset) + AFP sorting.

**7.5 `Std.Port.Bool` — boolean algebra & guard reflection.**
`&&`/`||`/`not` de Morgan, idempotence, absorption, identity; `if`/guard
case-analysis; **reflection** between `Bool` and its `So`/decidable proposition —
BEAM guards are boolean expressions, so these justify refining a `case` by a guard.
*Sources:* Agda `Data.Bool.Properties`, `Relation.Nullary.Reflects`; Lean
`Mathlib.Logic.Basic`, `Init.SimpLemmas`; Coq `Coq.Bool.Bool`.

**7.6 `Std.Port.Eq` — equality & identity-type infrastructure.**
`sym`/`trans`/`cong`/`subst` over `Equivalent`; per-constructor congruence;
**constructor injectivity** (`S m = S n → m = n`) and **disjointness** (`Z ≠ S n`,
`[] ≠ x :: xs`); equality on products/sums; **decidable equality** (`DecEq`) for base
types and structurally-derived types. (Intensional stance + UIP are Cure's, noted so
extensionality is never assumed.)
*Sources:* Agda `Relation.Binary.PropositionalEquality`,
`Relation.Nullary.Decidable`; Lean `Init.Core`, `Mathlib.Logic.Basic`; Coq
`Coq.Init.Logic`, `Coq.Logic.Eqdep_dec`.

**7.7 `Std.Port.Wf` — well-foundedness & termination certificates.**
Well-founded recursion on `<` (Nat) and on **list length**; structural-subterm
ordering; `Acc`-based recursion; **lexicographic** combinations for nested/mutual
recursion; size-change witnesses. These discharge every §6.3 termination obligation
that isn't obviously structural.
*Sources:* Agda `Induction.WellFounded`, `Data.Nat.Induction`; Lean
`Mathlib.Order.WellFounded`, `Init.WFTactics`; Coq `Coq.Init.Wf`, `Coq.Arith.Wf_nat`,
`Recdef`; Isabelle `HOL.Wellfounded`.

**7.8 `Std.Port.Absurd` — impossibility / ⊥-elimination.**
`absurd`/`⊥`-elim to close unreachable branches created by refined indices
(`Fin 0`-elim, `Vector _ (S n)` has no `empty`, a discriminated tag can't recur).
Turns coverage obligations (§6.2) that are impossible-by-typing into one-line proofs.
*Sources:* Agda `Data.Empty`; Lean `absurd`, `False.elim`; Coq `False_rect`.

**7.9 `Std.Port.Map` — finite-map (BEAM map) laws.**
`get(put(k, v, m), k) = v`; `get(put(k, v, m), k') = get(m, k')` for `k ≠ k'`;
`keys`/`size` after `put`/`remove`; map extensionality.
*Sources:* Coq `Coq.FSets.FMapFacts`; Isabelle `HOL.Map`; Lean `Mathlib.Data.Finmap`;
Agda `Data.Tree.AVL.Map`.

**7.10 `Std.Port.Monad` — `Option`/`Result` laws for partiality reshaping.**
Functor and monad laws (`map` identity/composition; `bind` left-identity,
right-identity, associativity) for `Option` and `Result`, so partial functions
reshaped into `Option`/`Result` (§6.5) compose provably.
*Sources:* Agda `Data.Maybe`, `Effect.Monad`; Lean `Mathlib` monad laws; Coq option
in `Coq.Init.Datatypes`.

**7.11 `Std.Port.Bits` — binary/bitstring laws (Phase-3+ stretch).**
Length/concatenation of binaries and segment bounds — deferred, listed for
completeness because binaries are a BEAM primitive.
*Sources:* Coq `bbv` / `Coq.Bits`; Isabelle `HOL-Library.Word`; Lean
`Mathlib.Data.BitVec`.

**Banking workflow.** Each lemma is (1) transliterated from a named source module,
(2) checked against that system through the differential oracle (so we know the Cure
statement matches the trusted original), (3) proven in Cure (`reflexive`/`rewrite`/
induction), and (4) registered in the Hammer's index by conclusion head-shape.
Priority order for banking follows real BEAM frequency: 7.2 List, 7.1 Nat, 7.7 Wf,
7.6 Eq, 7.4 Order, 7.8 Absurd, 7.5 Bool, then 7.3 Vec, 7.10 Monad, 7.9 Map, 7.11 Bits.

## 8. Give-up behavior — three tiers into the trust ledger

For every obligation: **auto** (Hammer, §7) → **interactive** (§9) → **postulate**.
A postulate is an explicit `@extern`-free axiom recorded in the trust ledger, so an
incomplete port never blocks — its unproven facts are visible axioms, and
`cure audit trust` on the ported module diffs exactly what trust the port cost.

## 9. Interactive prover UX

`cure port <beam> [--interactive]` walks the residual obligations one at a time,
each pretty-printed via `Core.Printer` (goal + local context). At each, the user may:
supply a proof term; run a named tactic (e.g. `induction n`, `rewrite <lemma>`);
cite a library lemma; **postulate** it (recorded, §8); or **mark the source function
partial** (drop the totality claim, reshaping the return type to `Option`/`Result`).
State is journaled to a `.port/` sidecar so a session is resumable.

## 10. Testing & acceptance

- **Differential BEAM↔port equivalence** — the transliteration oracle idea, retargeted:
  run the *original* BEAM module and the *compiled Cure port* on the same generated
  inputs and compare results. A port is "faithful" when behavior matches across the
  corpus. This is the primary acceptance test.
- **Shape-catalog coverage** — a manifest (à la Antigen's cover manifest) enumerating
  which Core Erlang node types are handled; `unsupported_shape` occurrences are
  reported, so grammar coverage is a measured number, not a claim.
- **Proof-library conformance** — each banked lemma has a differential-oracle test
  against its source system and is kernel-checked.
- **Unit tests** per component (Reader adapters, Shapes classification, Fitter type
  reconstruction, Hammer discharge, Prover state machine).

## 11. Open questions & risks

- **Type reconstruction ambiguity** — Core Erlang is untyped; inferring precise ADTs
  from usage may be under-determined. Mitigation: Phase-3 source-type enrichment;
  otherwise fall back to a widened type + obligation.
- **Concurrency shapes** — `receive`/`spawn`/links have no clean total form; Phase-0
  wraps them faithfully via `Std.Otp.Raw` and postulates their properties.
- **Hammer search cost** — head-shape indexing + a depth bound; no full automation is
  promised, that is what the interactive tier is for.
- **Oracle availability** — the Lean oracle must be present for proof-library banking;
  headless/cron runs without it can still port (auto+postulate), just prove less.

## 12. Acceptance criteria

1. `Cure.Port.Reader` produces uniform Core Erlang for a `.beam` from each of the
   three source languages.
2. `Cure.Port.Shapes` classifies the Core Erlang grammar with measured coverage and
   surfaces every `unsupported_shape`.
3. `Cure.Port.Fitter` emits compilable Cure value-surface source plus a typed
   obligation list for a real ported module (Phase 0).
4. The `Std.Port.*` library banks the §7 families, each differential-oracle-checked
   against its source system and kernel-proven.
5. `Cure.Port.Hammer` discharges an obligation by finding and applying a banked lemma
   checked by the oracle/kernel.
6. `cure port --interactive` elicits a remaining proof and records a postulate into
   the trust ledger when declined.
7. A ported module passes differential BEAM↔port equivalence on its corpus.

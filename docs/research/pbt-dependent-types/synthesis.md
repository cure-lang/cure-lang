# Antigen research synthesis — PBT of a dependent type-theory kernel

**Purpose.** This document synthesises eleven papers read while designing
**Antigen**, the property-based metatheory-testing engine for Cure's trusted
kernel (`Cure.Core.*`). It is the durable record of that reading: what each
paper contributes, the cross-cutting conclusions, and the concrete design
implications for Antigen. It feeds the Antigen design spec
(`docs/superpowers/specs/antigen/2026-07-01-antigen-design.md`) — this is the *research*
layer; that is the *design* layer.

**Kernel under test (context).** Intensional Martin-Löf Type Theory:
**bidirectional** typing (`infer`/`check`), **Normalization-by-Evaluation**
conversion, **indexed inductive families**, a **strict-positivity** checker, and
a **totality/termination certifier** that gates δ-reduction (only certified-total
globals unfold). Confirmed soundness hole: the termination checker certifies
**mutual recursion** as total (`calls?/2` detects only a function's own name).

**Provenance.** Read 2026-06-30/07-01. All page-level digests are in the session
transcript. Two files were originally mislabelled and have been corrected (see
the corpus table). DOIs for the two re-sourced papers: Pałka AST'11 =
`10.1145/1982595.1982615`; Foundational PBT ITP'15 = `10.1007/978-3-319-22102-1_22`.

---

## 1. The corpus (11 papers)

| # | File | Paper | Role |
|---|------|-------|------|
| 1 | `palka-ast11-random-lambda-terms.pdf` | Pałka, Claessen, Russo, Hughes — *Testing an Optimising Compiler by Generating Random Lambda Terms* (AST'11) | Ancestor of typing-rules-as-generation; the **INDIR** trick; type-preserving shrinking |
| 2 | `making-random-judgments-esop15.pdf` | Fetscher, Claessen, Pałka, Hughes, Findler — *Making Random Judgments* (ESOP'15) | Generic goal-directed CLP-over-rules; closest blueprint; **no conversion, no shrinking** |
| 3 | `claessen-duregard-palka-flops14-constrained-uniform-data.pdf` | Claessen, Duregård, Pałka — *Generating Constrained Random Data with Uniform Distribution* (FLOPS'14) | Alternative lineage: FEAT enumeration + predicate inversion + bounded-backtracking uniformity |
| 4 | `generating-good-generators-inductive-relations-popl18.pdf` | Lampropoulos, Paraskevopoulou, Pierce — *Generating Good Generators for Inductive Relations* (POPL'18) | QuickChick derivation: inductive relation → **certified** generator (narrowing) |
| 5 | `quickchick-foundational-pbt-itp15.pdf` | Paraskevopoulou, Hriţcu, Dénès, Lampropoulos, Pierce — *Foundational Property-Based Testing* (ITP'15) | The **trust layer**: set-of-outcomes semantics; sound+complete generators |
| 6 | `well-typed-not-useless-popl24.pdf` | Frank, Quiring, Lampropoulos — *Generating Well-Typed Terms That Are Not "Useless"* (POPL'24) | Generate terms that **use their binders**; the false-confidence quality metric |
| 7 | `hiking-trip-generators-stlc.pdf` | Tarau — *A Hiking Trip Through the Orders of Magnitude* (LOPSTR'16) | Efficiency: **interleave generation with checking**; direct normal-form generation |
| 8 | `generic-bidirectional-typing-dtt.pdf` | Felicissimo — *Generic Bidirectional Typing for Dependent Type Theories* (2024) | The bidirectional **rule taxonomy to invert**; the guessing points |
| 9 | `certify-conversion-checker.pdf` | Lennon-Bertrand — *What does it take to certify a conversion checker?* (FSCD'25) | Conversion correctness obligations; **directly on our mutual-recursion hole** |
| 10 | `type-level-pbt.pdf` | Hansen, Brady — *Type-level Property-Based Testing* (TyDe'24) | Architecture: index-first generation; capability interface; keep oracle independent |
| 11 | `quickchick-inria-project-proposal.pdf` | INRIA project proposal (motivation only, no algorithms) | Context; mechanics live in #4 and #5 |

**Correctness of the corpus.** #1 and #5 were re-sourced by the user (their
DOIs above) after readers found the original files mislabelled: the file named
`palka-ast11` actually contained #3 (FLOPS'14), and `quickchick.pdf` was #11 (a
grant proposal). Both original files are retained under corrected names. The
load-bearing blueprints (#2, #4, #6, #8, #9) were correctly named throughout.

---

## 2. Per-paper contributions (load-bearing findings)

### 1. Pałka AST'11 — the ancestor, and two things its descendants dropped
- **Method.** Read each STLC typing rule *backwards* as a goal-directed
  generation rule: given a target type + environment, pick a rule whose
  *conclusion* yields that type, recurse on its *premises*, backtrack on dead
  ends. Hand-written (rule set hardcoded), depth-first, random-shuffle rule list,
  per-rule weights, size limit.
- **INDIR (the signature invention, §3.2).** Plain application `M N : τ` forces
  *inventing* the argument type `σ` — combinatorially catastrophic ("only a very
  specific choice of types will allow the search to progress"). INDIR instead
  **picks a function symbol `f` from the environment whose result type matches the
  goal, then reads the argument goals off `f`'s own type — guessing nothing.**
  Head-first saturated elimination.
- **Keep plain application too.** INDIR's head is always a symbol, never a λ, so
  it cannot produce redexes `(λx.M) N`. They retain APP to preserve redex
  generation — which a reduction-testing harness needs.
- **Type-preserving shrinking (§6.5).** Three moves — replace by same-type
  subterm; replace by same-type constant; **β-reduce** — all preserving types and
  bindings, terminating by strong normalization. Shrinks stay well-typed.
- **Master framing (§8).** "Type correctness is a *global* property achieved by a
  sequence of *local* choices. It is easy for a random generator to paint itself
  into a corner where generation can only be completed by trivial programs (in
  which variables are defined but almost never used)." This is the
  Well-Typed-Not-Useless thesis, 13 years early; INDIR + a seeded environment is
  the mitigation.
- **Oracle.** Differential testing of GHC across `-O0`/`-O1` on `List Int → List
  Int` functions probed with partially-defined ("bottom") inputs (strictness
  analyser). Found a real bug in ~20,000 terms / ~15 min.
- **Inherited blind spot.** Never biased toward shadowed variables ⇒ shadowed
  configs effectively unreachable ⇒ missed a substitution *capture* bug (noted by
  #2 and #4). Warning: deliberately generate shadowing contexts.

### 2. Making Random Judgments ESOP'15 — the generic goal-directed engine
- **Method.** Generalises #1 to *any* inductive relation: rules become a
  **constraint logic program**; state = goal stack + constraint store;
  `[reduce]` picks a matching rule, freshens, unifies conclusion with goal,
  pushes premises; terminal empty stack ⇒ read off the term; unconstrained vars
  filled randomly.
- **Novel machinery.** A **disequational constraint solver with
  universally-quantified disequations** (`param-elim`/`elim-x`), needed to compile
  *ordered* metafunction clauses into *unordered* judgment rules. This is the
  reusable jewel for ordered/overlapping side-conditions (positivity, freshness,
  exhaustiveness).
- **Search heuristics (Fig. 8).** Limits on backtracking, depth, derivation
  size; below the depth bound, randomized rule permutation; above it, sort by
  fewest premises to close derivations; two permutation strategies (uniform vs.
  premise-count-weighted via a depth-shifted binomial), one chosen per term.
  Uniform-over-rules biases toward trivial terms (STLC: "1 in 4 ⇒ a bare number").
- **Critical gaps for us.** Equality is **purely syntactic — no conversion**.
  **No shrinking** (dropped from #1). Oracle is always an **independent second
  artifact**; the paper never faces "the checker under test is its own oracle."
- **Empirical.** Redex Benchmark: 38/40 bugs (vs 31/40 ad-hoc), order-of-magnitude
  faster. Polymorphism is the dominant failure mode (parallel choices matched up
  late ⇒ backtracking storms; non-poly model improved counterexample rate from
  1-in-4,000K to 1-in-320) — a direct warning that indexed families will be worse.

### 3. Claessen/Duregård/Pałka FLOPS'14 — the enumerate-and-prune alternative
- **Method.** Represent the datatype as a size-indexed `Space` (FEAT), compute
  per-size cardinalities, draw a uniform index, decode. Add a predicate by
  **lazy predicate-guided pruning**: evaluate the predicate on partial values;
  `False` on a partial value removes the whole completion subspace.
- **Distribution knobs.** Bounded backtracking gives predictable "almost uniform"
  (probabilities differ by ≤ `b+1`); `b=0` uniform, `b=∞` unbounded.
- **Why it doesn't port cleanly to MLTT.** The "store the annotation in the term"
  trick collapses (types are terms ⇒ density ≈ 0). Lazy pruning is defeated
  because **NbE conversion forces subterms** (partial values yield `⊥`, not early
  `False`). Generate-and-filter dies below ~1% pass rate; dependent well-typed
  density is far below that. Useful only for the *enumeration substrate* and the
  distribution knobs, not the well-typed-term core.

### 4. Generating Good Generators POPL'18 — derive a *certified* generator
- **Method.** Compile an inductive relation `R` (with a chosen **mode** = which
  arguments are inputs vs outputs) into a generator via **narrowing** (lazy
  instantiation while traversing the definition), realised as
  **unification-in-a-state-monad**. `fixed` (input) ranges may only be
  matched/equality-checked, **never assigned** — this is what makes modes sound.
- **Trust (the key steal).** Each derived generator ships a **machine-checked
  certificate** `isSome ∩ ⟦g⟧ = Some[P]` — soundness (only valid outputs) AND
  completeness (every witness reachable) — via *translation validation* (per-
  generator proof, not a once-and-for-all compiler proof). Completeness is what
  makes an assay's **negative** result trustworthy.
- **Restrictions (the wall).** Data must be simply-typed (only the *relation* is
  dependent); premises must be **constructor expressions** (no arbitrary function
  applications). So typing premises that invoke **conversion/substitution in
  indices** are *not* narrowable — they can only be discharged as decidable `Dec`
  **checks** (degrading to generate-and-check on exactly the hard premises).
  Proofs require **monotonicity** side-conditions (inherited by #5).
- **Sweet spot for us.** Structural/syntactic relations — **positivity and
  totality** — are the proven-good class. Conversion-dependent typing is hybrid at
  best.

### 5. Foundational PBT ITP'15 — the trust/semantics layer
- **Set-of-outcomes (possibilistic) semantics.** A generator's meaning is its
  **support set** — values emittable with non-zero probability, probabilities
  discarded. `semGen g := {a | ∃ s r, run g s r = a}`.
- **Correct generator = `semGen g ≡ {x | P x}`** = soundness (`⊆`) + completeness
  (`⊇`). Completeness is the formal guard against the vacuous-truth trap ("Gave
  up! 88% discarded").
- **Compositional support law.** `support(bind g f) = ⋃_{a∈support g} support(f
  a)` — a composite's support computes by structural recursion from its parts'.
  This is what makes "what can this assay generator produce?" *answerable*.
- **Size hygiene.** The intuitive `bind` law is **unsound** unless parts are
  `Unsized` (size-independent support) or `SizeMonotonic` (bigger size ⇒
  superset), because `bind` threads the *same* size to both sides. These
  type-class side-conditions are the load-bearing hypothesis #4 inherits.
- **TCB / limits.** No distribution/quality guarantees (probabilities discarded).
  An **infinite-seed surjectivity axiom** (false of any real finite PRNG) sits in
  the TCB. Completeness for infinite-domain function generation needs
  prefix-freeness and is only partially formalized.
- **Case-study lesson.** Attempting the completeness proofs **surfaced real bugs**
  in thoroughly-tested generators — the *act* of characterising support was the
  payoff.

### 6. Well-Typed-Not-Useless POPL'24 — quality / anti-false-confidence
- **"Useless" = a function whose parameters are never used** (dead argument code):
  wastes generation + compile time and, worse, exercises fewer interesting
  behaviours. Root cause: top-down type-directed generation picks argument *types*
  before any *use* for the argument exists.
- **Fix.** Small-step generation over terms with **typed holes** + **arguments
  holes** (`▸^α`): **defer a binder's type until a use for it is generated**
  (rule GenParam▸ — the variable is created *because* it is used). Acyclicity
  side-condition `▸^α ∉ τ`. Backwards-compatible (bias, don't restrict).
- **Metric.** *Parameter usage rate*: real programs ≈ **94.9%**, naive top-down ≈
  **30%**; tunable via rule weights. The measurable face of false confidence.
- **Direct warning for us.** Uniform/trivial generators "almost always start with
  an abstraction" ⇒ "**completely ineffective for properties that involve
  reduction, such as preservation**." Names subject_reduction as the assay most at
  risk of passing vacuously. Also flags erasure_preservation (vacuous if the
  erased arg was never used).

### 7. Hiking Trip STLC — efficiency
- **#1 technique: interleave generation with type inference in one procedure** so
  ill-typed prefixes die early. At size 10: ~11× fewer inferences, ~10×
  wall-clock. Constrained enumeration is *faster than unconstrained* because
  typed terms are exponentially scarce — the constraint prunes an exponential
  subtree.
- **Generate normal forms directly** via a redex-excluding grammar (no
  `a(l(_,_),_)` production) ⇒ by-construction `nf(t)=t` fixtures; the smaller,
  redex-free search space.
- **Witness-dropping** for decision/count assays (skip building the term when only
  a yes/no is needed).
- **Dependency caveat.** The whole speedup rests on "inference is linear,
  inhabitation is PSPACE." Under MLTT, checking invokes NbE conversion — that
  asymmetry **narrows or inverts**. Benchmark by wall-clock/conversion-work, not
  kernel-call counts (conversion cost is hidden). Memoization of subterm judgments
  is impossible (subterms are open) — *worse* under dependency.

### 8. Generic Bidirectional Typing for DTT — the rules to invert
- **Constructor/destructor split drives everything.** Constructors are introduction
  forms typed in **check** mode (omitted args recovered from the input type);
  destructors are elimination forms typed in **infer** mode (omitted args
  recovered by inferring the principal argument's sort and matching a pattern).
  **Mode is a pure function of the head symbol** — the generator never guesses
  mode, only content.
- **The Switch rule is the one place conversion fires during checking**: at an
  inferable term used in checking position, infer its type `T` and test `T ≡ U`
  against the goal.
- **Matching modulo rewriting.** Because sorts contain terms, recovering erased
  args requires matching a pattern against the *head-normal form* of the inferred
  type — decidable only when strongly normalizing.
- **Guessing points (Antigen's hard branches, ranked).**
  1. **Principal-argument synthesis for a destructor** (dominant): synthesize a
     sub-term whose inferred sort head-normalizes to the destructor's pattern
     (a Π-type for application, a `Vec`/`Eq`-type for the recursors).
  2. **Constructor choice** at a check goal, gated by whether the constructor's
     **index pattern** unifies with the goal's index.
  3. **Ascription / motive invention** — inventing whole sorts (the domain `A`,
     codomain family `B`, eliminator motive `P`) to make constructor-headed terms
     inferable.
  4. **Index-constraint satisfaction** — non-erased args must be chosen so the
     forced index `≡` the goal's index (couples the arguments; backtracking).
- **Well-behavedness = our infer/check assays.** Soundness (bidirectional ⇒
  declarative), annotability/completeness, infer determinism (`t⇒T₁ ∧ t⇒T₂ ⇒ T₁≡T₂`),
  conversion stability, subject reduction — all runnable properties.
- **Gap.** Rewrite-based conversion only; **η-laws and definitional proof
  irrelevance not covered**. If Cure's NbE has η, supply an η-aware oracle.

### 9. Certify Conversion Checker — directly on the mutual-recursion hole
- **Central result.** Soundness (positive + negative) of a conversion checker
  needs only **injectivity** (of type constructors + term-level), provable in a
  meta-theory *weaker* than the object theory. **Normalization is needed ONLY for
  termination.** ⇒ our mutual-recursion hole breaks **termination specifically**;
  the checker stays *sound but can loop*.
- **The exact failure.** Reduction-to-WHNF's well-founded order **assumes the term
  reaches a normal form** (Lemma 16) — precisely what our faulty totality
  certifier falsely guarantees. A wrongly-certified mutually-recursive global
  δ-unfolds forever ⇒ conversion loops. "Dangerous congruences" are
  *eliminator* congruences (eliminator meets constructor fires a reduction); our
  δ-analogue is unfolding a certified-total global.
- **Sharpest cheap probe.** **Reflexivity `conv(t,t)` ⟺ deep normalization.** A
  reflexivity timeout *is* a non-normalization detection — the single cheapest,
  independent assay for our hole.
- **Typed vs term-directed asymmetry.** They have *different* termination
  footprints; a looping global may hang one mode but not the other. Run both;
  divergence is itself a signal.
- **Completeness landmines.** Unit / unit-like types (`ℕ→(Σx:⊤.⊤)`), strict
  propositions / proof irrelevance — term-directed conversion needs **full**
  neutral completeness at *all* types. Relevant only if Cure has η/irrelevance.
- **Runnable invariants (assays).** Reflexivity, symmetry, transitivity (the
  subtle one — relates through ill-typed intermediates), conv-respects-reduction
  (`conv(t, reduce t)`), stability under weakening/strengthening, injectivity /
  no-confusion, and per-rule pre/postcondition preservation (their Fig. 6).

### 10. Type-level PBT TyDe'24 — architecture (least directly applicable)
- **Transferable architecture.** **Generate-the-index-then-the-value** (dependent
  pairs): context ⇒ type ⇒ term; family index ⇒ inhabitant. A **capability
  interface** (`Traceable`) — one small adapter per object family, generic
  generation/property machinery reused, backend swapped by swapping the `Gen`
  monad. State/context-sensitive constructor weighting. Depth-indexed bounded
  generation with a failure **trichotomy** (real bug / bound too small / generator
  gap).
- **Generator-coverage caveat.** Their generator never emitted one valid
  operation ⇒ that branch was never tested. "QuickChick is no silver bullet."
- **Where we must diverge.** Their power comes from reusing *one* spec across
  model/impl/test — for a *trusted kernel tester* that coupling is fatal (the
  checker would validate its own bug). **Keep the oracle independent of the kernel.**

### 11. INRIA proposal — motivation only
- Dual checker+generator principle; the generate-then-filter anti-pattern;
  polarized mutation testing (seed *real* bugs, confirm assays catch them). No
  algorithms — mechanics are in #4 and #5.

---

## 3. Cross-cutting synthesis

### 3.1 Three generator lineages, one universal breaking point
- **Goal-directed rules-as-generation** (#1 → #2): read typing rules backwards.
- **Enumerate-and-prune** (#3): FEAT + predicate inversion + uniformity.
- **Derive-from-the-relation** (#4/#5): narrow an inductive relation into a
  certified generator.

Every one assumes **type-checking is cheap and syntactic**. MLTT's **NbE
conversion** breaks that, and (given our totality hole) checking may not even
terminate. Consequences: #2's store has no conversion; #4's narrowing forbids
function-application premises (so conversion premises degrade to `Dec` checks);
#3's lazy pruning is defeated by NbE forcing; #7's cheap-inference economics
invert. **Convergent conclusion:** use the **bidirectional rules (#8) as the
generator skeleton**, invert them for the structural fragment, and discharge
conversion premises via the kernel's own conv-checker **under a budget** (itself
an assay).

### 3.2 The generator skeleton
- **Bidirectional inversion (#8):** head symbol ⇒ mode; generate content, never
  mode. `gen_check(Γ, A)` and `gen_infer(Γ) → (t, A)` are the two entry points
  (they *are* Cure's existing `check`/`infer` split, read backwards).
- **INDIR (#1) tames the dominant guessing point:** for any elimination, pick the
  head from context first and walk its Π-telescope, substituting each chosen
  earlier arg into later goal types. Head-first shape survives dependency; only
  "arguments independent" breaks.
- **Keep a plain application/elimination rule (#1)** so redexes remain reachable —
  subject_reduction and normalization are worthless without firing redexes (#6).
- **Interleave generation with checking (#7)** to prune ill-typed prefixes early;
  **generate normal forms directly** for the NF-fixture assays.
- **Generate shadowing contexts deliberately (#1 blind spot)** to exercise
  substitution/α-conversion — the gap that hid a capture bug.
- **Health gate (#6, #5):** track binder-usage rate, reduction activity (redexes
  fired, δ-unfoldings triggered), and **discard rate**. A green assay on a batch
  with near-zero activity is false confidence — flag, don't count.

### 3.3 The oracle problem — the central tension no paper faces
Every paper's oracle is an **independent second artifact**. Antigen's kernel would
be *its own checker*, so a soundness bug is invisible (a broken checker validates
its broken output). Three escapes, mapping to assay tiers:
1. **Differential / self-consistency** (subject_reduction, infer_check_agreement,
   normalization_stability): check the kernel against *itself* in different modes;
   a bug that breaks the consistency is caught with **no external oracle**.
2. **Independent structural invariants (#9):** injectivity, no-confusion, and
   especially **reflexivity `conv(t,t)` ⟺ deep normalization** — provable in a
   weaker meta-theory, so they don't require trusting the checker under test.
3. **Known-label generation** (totality, positivity): sidestep the oracle by
   construction — generate an object with a known correct label and assert the
   kernel agrees.

### 3.4 Trusting the generator itself (#5, #4)
- Adopt the **set-of-outcomes** discipline informally: for each generator,
  characterise its **support set** (what it can / can't produce). Soundness = a
  runnable meta-test (`check all x <- gen: assert valid?(x)`). Completeness = a
  **coverage + corpus** argument (never a theorem — the finite PRNG forbids it).
- **Make `Antigen.Gen` a reified, inspectable AST** (not opaque closures) so
  support sets compute by structural recursion (`support(bind) = ⋃ support(f a)`);
  `bind`'s continuation is a function so its support is only *over-approximable* —
  same limit #5 hits.
- **Tag generators `unsized` / `size_monotonic`** to license the clean bind
  reasoning and prevent false-completeness claims across sizes.
- The permanent counterexample corpus *is* the operational form of completeness:
  a counterexample the generator can't reach is a completeness hole.

### 3.5 On the confirmed mutual-recursion hole (#9)
The hole breaks **termination, not soundness**. The cheapest, independent detector
is **reflexivity-as-normalization** (`conv(t,t)` within budget). Run conversion in
**both typed and term-directed modes** and flag divergence. This validates the
existing `conversion_termination` assay and adds a sharper sibling.

---

## 4. Design implications for Antigen (locked conclusions)

1. **Generator = bidirectional inversion (#8) + INDIR (#1) + plain elim rule
   (#1) + interleaved checking (#7) + direct NF generation (#7).** Discharge
   conversion premises via the kernel conv-checker under a budget. Deliberately
   generate shadowing contexts.
2. **`Antigen.Gen` is a reified inspectable AST** with `unsized`/`size_monotonic`
   tags, so per-generator support sets are analyzable (#5). Backend
   (`Antigen.Backend`) stays swappable (StreamData now).
3. **Health gate** on every assay batch: binder-usage, reduction activity,
   discard rate (#6, #5). Vacuous green is flagged, not counted.
4. **Oracle strategy per assay:** differential/self-consistency, independent
   invariant, or known-label — never "trust the kernel against itself."
5. **Totality + positivity are the schema-directed sweet spot** (#4 proven-good
   class): known-label generation, no general term generator, no oracle problem.
6. **Reflexivity-as-normalization** (`conv(t,t)` in budget) is a near-free,
   independent, sound-without-normalization probe for the confirmed hole (#9).
7. **Shrinking = type-preserving moves incl. β-reduction** (#1); the shrink moves
   *are* reductions the kernel already implements.

### Two-tier phasing (confirmed by the reading)
- **Tier A — no general term generator, no oracle problem.** Totality +
  positivity (known-label, #4 sweet spot) + reflexivity-as-normalization probe
  (#9). Proves the whole pipeline (Gen DSL, backend, explorer, corpus, tmp
  reports, shrink→antibody) end-to-end on the *known* mutual-recursion hole.
- **Tier B — needs the bidirectional-inversion term generator.** The differential
  trio (subject_reduction, infer_check_agreement, normalization_stability) — no
  external oracle, but gated on the health gate so they don't pass vacuously.
  Then conversion_termination (δ-seeded contexts, both modes) and
  erasure_preservation.

---

## 5. What the corpus does NOT answer (open frontier)

- **A general well-typed *dependent* term generator.** No turnkey solution
  exists. Every paper handles the syntactic/structural fragment; **conversion in
  premises and indexed-family index constraints are the genuinely new work**
  (#2's polymorphism failure mode predicts index families will be worse).
- **The kernel-as-its-own-checker oracle.** No paper faces it; §3.3's three
  escapes are our own synthesis, not a cited method.
- **η / definitional proof irrelevance** in conversion (#8, #9 gap) — only if
  Cure's NbE has them; needs an η-aware oracle if so.
- **Distribution/coverage as a theorem.** Impossible in our setting (finite PRNG,
  no proof assistant); completeness is always empirical/corpus-based (#5).

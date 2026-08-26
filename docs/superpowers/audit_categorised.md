# Raw Audit — Categorised

> **FINAL STATE (2026-07-08) — Tier-1 Core cleanup COMPLETE on the soundness
> dimension.** All K1–K14 are resolved: soundness content LANDED or kernel-enforced
> (K1a, K2 §G.1, K3, K4, K5a, K6 545/599, K11a, K12 slices 1–2, K13, K14); the
> remainder are faithfulness-only representation choices DECLINED-with-proof
> (K1b/`{:rewrite}` Phase B, K2 `{:prim}`→delta migration) or large parity FEATURES
> deferred to their own design (K7 universe-level polymorphism, K12 qualified `Sym`,
> K5b canonical transport). A separate E-layer declaration-hygiene sweep closed eight
> silent-overwrite/shadowing holes beyond the audit, and all six dependent-soundness
> axes were probed sound. See spec §J.1 for the per-clause terminal-state table.

Source: `docs/superpowers/raw_audit.txt` (~640 findings). This index groups the
findings, flags the heavy cross-document duplication, and separates the
**Tier 1** kernel cleanup (the "stuff only we have" — the near-term focus) from
the **Tier 2** broad compiler/stdlib/tooling hygiene sweep.

## Document structure

The file is **two documents concatenated**:

- **Doc 1 — "Cure Issues" (items 1–18)** — a curated, pre-deduplicated cleanup
  plan for the dependent kernel; each item has Goal / Change / Main files.
  Item 18 = recommended implementation order.
- **Doc 2 — items 1–640** (prefixed "0. Correction from earlier diffs") — a raw
  full-system sweep. Internal runs:
  - **1–520**: broad compiler / stdlib / codegen / tooling / security audit.
  - **521–569**: "Cure vs Lean/Agda/Idris references" — kernel divergences.
  - **570**: "immediate priority vs references" note.
  - **571–639**: granular kernel/elab code-level findings.
  - **640**: "most urgent kernel-surrounding cleanup" note.

**Key dedup fact:** Doc 1 (18 items) is a distilled view of Doc 2's kernel
portion (521–640). Doc 1's own items 1–17 also re-appear inside Doc 2's 1–520
run (e.g. legacy Pi/Sigma, Nat==Int). Below, each Tier-1 category lists the
Doc 1 items and the Doc 2 items that restate them, so we plan once per concept.

The audit names its own priorities: **Doc 1 item 18**, **Doc 2 item 570**, and
**Doc 2 item 640** are the three "do this first" notes — cross-check any plan
ordering against them.

---

# TIER 1 — Dependent kernel / Core soundness ("only we have")

These are the divergences from real dependent languages. This is the focus.

## K1 — Primitive equality, the `refl` atom, and the rewrite node
Retire primitive `{:eq}/{:refl}/{:rewrite}` + `:veq/:vrefl/:cure_refl`; use the
builtin inductive `Eq`/`refl` end-to-end; lower surface `rewrite` to an Eq
eliminator/transport. **This is the single most-duplicated theme.**
- Doc 1: **2** (remove primitive eq/refl/rewrite), **3** (rewrite → Eq
  eliminator), **4** (proof-token equality).
- Doc 2: **521** (primitive prop-equality layer), **522** (rewrite emits
  primitive nodes), **523** (ad-hoc rewrite "bridge step"), **552** (elaborator
  hardcodes `"Eq"`/`"refl"`), **560** (three competing equalities), **567**
  (erasure = evaluating rewrite away), **568** (`Eq` not fully inductive),
  **577** (kernel accepts both prim + inductive Eq), **578** (Eq recognition
  hardcoded to `:Eq`), **589** (termination still knows prim eq/rewrite), **590**
  (positivity still knows prim rewrite), **260** (legacy equality = blind
  structural subst), **261** (`:cure_refl` still exposed), **37** (runtime `Eq`
  protocol not segregated from propositional Eq), **442** (examples depend on
  `:cure_refl`).
- **Phase A LANDED + green. K6 UNBLOCKED + eq/refl RATCHET LANDED (2026-07-08).
  Phase B (rewrite→:case) is the remaining crux.** Full state in spec
  `2026-07-04-identity-type-as-inductive.md`. Phase A (surface `Eq`/`refl` → genuine
  inductive `{:data,:Eq}`/`{:ctor,:refl}`; `ensure_eq`/`eq_parts` bridge) fixed the
  observable symptom (`refl/rf03,rf04,rf05` accept/accept/same). **K6 (b355753):**
  `infer({:ctor})` now reads params riding the spine (§E.1), making the inductive
  refl inferable. **bridge_step (f3b0e73):** migrated off the primitive `{:refl}` to
  the inductive ctor via param-in-spine — the LAST primitive-`{:refl}` producer, so
  {:refl} (and {:eq}, already producerless) are now DEAD-PRODUCERS. **K1a ratchet
  (0e75a13):** split `no_eq_node` — {:eq}+{:refl} flipped to `:reject` in
  `release_config` (enforced on every program's final Core, program.ex:272 ⇒ green
  suite PROVES no program emits them); {:rewrite} split to `no_rewrite_node` :warn.
  **Phase B (retire the `{:rewrite}` Core NODE → `:case`) — DECLINED per
  analysis-discipline, with empirical proof (2026-07-08).** SURFACE rewrite
  semantics are ALREADY Idris-faithful (via `rewrite_plan`: occurrence analysis,
  direction/symmetry, no-match rejection, and the definitional-occurrence bridge).
  Retiring the `{:rewrite}` node is pure Core-REPRESENTATION change: it buys no
  soundness (the kernel types `{:rewrite}` transport correctly) and no surface
  behaviour. TWO empirical attempts proved it also RISKS parity and needs
  load-bearing analysis ported onto `:case`:
  1. **Naive Core body-shift** (d44edb8→reverted c635e8c): shift the outer-context
     body +1 into the refl branch. INCOMPLETE — only type-checks when the body's
     endpoint refines to the branch witness (variable endpoints); drifted
     `frp01_par_assoc` (computed endpoints) accept→reject.
  2. **Surface match-desugar** (`rewrite p in t` ⟿ `match p {refl()->t}` through
     `elaborate_match`, diagnostic-only, reverted): re-elaborates the body in-branch
     (fixes computed endpoints) but (a) REGRESSES the bridge case —
     `lib/std/proof.cure` `S(plus(n,Z))` vs `S(n)` definitional occurrence the
     syntactic motive can't capture; (b) is MORE PERMISSIVE than Idris — drifts
     `rw03_no_occurrence` (accepts a no-op rewrite `rewrite_plan`/Idris reject) and
     changes the error taxonomy (`rewrite_plan_audit`). A hybrid (match primary +
     `{:rewrite}` bridge fallback) still failed 3 tests for these reasons and would
     leave a permanent two-path system without flipping the ratchet.
  Per the design-fork-prose-preference ("if it's just semantics, prefer the
  lower-risk option") — and this IS just semantics (identical surface behaviour
  either way; only the Core node representing transport differs) — the LOWER-RISK
  option (keep the sound `{:rewrite}` eliminator + `rewrite_plan`) is chosen.
  `no_rewrite_node` stays `:warn` as an accepted, documented Core-representation
  divergence from Idris TT. REVISIT only if a kernel-conversion improvement removes
  the need for `bridge_step`, or if TCB-rule-count reduction becomes worth the
  reimplementation risk. Phase C (removing dead `{:eq}/{:refl}/{:veq}` kernel
  clauses) remains available independently but is low-value (K4-style defensive
  handling stays regardless). **Net K1 state: soundness-clean — the faked
  primitive equality nodes `{:eq}`/`{:refl}` are retired + ratcheted (K1a); the
  sound `{:rewrite}` transport node is a deliberate, proven representation choice.**

## K2 — Primitive operations in Core; type them properly
`{:prim, op, args}` should not be the operation model; ops need real typed
signatures before entering Core. Includes Bool-as-hardcoded-atoms.

> **2026-07-09 UPDATE — the migration LANDED.** The decline below stands as
> recorded (correct on the soundness criterion), but task #15 re-opened K2 on
> the PARITY criterion (Lean reduce_nat / Idris Builtin-op) and landed the
> `{:prim}`→builtin-op-globals migration: 25 registry-keyed op defs (incl. the
> A1 `struct_eq`/`struct_ne` structural pair), certified-δ literal
> acceleration, full node strip, `no_prim_node: :reject` in wave0 + release.
> Decision record: `2026-07-09-prim-delta-globals-design.md` §0/§1-A. The
> `no_prim_node stays :off` sentence below is superseded (it was also a
> recorded doc/code drift — validator.ex had `:warn`).
- **ASSESSED — §G.1 soundness rules ALREADY MET + now fully pinned (b8668de);
  `{:prim}`→delta-global migration is spec-deferred cleanliness, DECLINED (proof).**
  The genuine soundness content of K2 is spec §G.1's two rules, and the kernel
  already satisfies both: (1) *partial ops non-reducing when undefined* — a SINGLE
  reducer (`Eval.fold`) returns `:stuck` for `div`/`rem`/float-`div` on a zero
  divisor (→ neutral `{:nprim,…}`), a total catch-all never raises, and conv
  (`conv_neutral?`, conv.ex:138) compares the stuck neutral SYNTACTICALLY;
  (2) *BEAM-faithful ints* — folds compute with Elixir arbitrary-precision ints
  (Erlang `div`/`rem` truncate-toward-zero = AtomVM), and Bool folds yield the
  INDUCTIVE `{:vctor, :True/:False, []}` (so #55 "Erlang booleans" is not a kernel
  issue). normalise/conv do NOT fold prims separately — no second unguarded
  reducer. Completed the regression coverage (int div-by-zero was pinned; added
  int rem + float div by zero). #607 (div typed total) and #608 (numeric eq/ne) are
  NOT soundness holes — the spec keeps `div : Int→Int→Int` sound via the
  non-reducing fallback (NonZero-proof div is an optional stdlib layer), and
  numeric eq/ne are legitimate decidable-equality delta-ops (intentionally kept).
  The `{:prim}`-node DELETION → typed delta-global constants is a REPRESENTATION
  change that spec §G itself defers to "the K2 wave spec" (unwritten) and that buys
  NO additional soundness (the node is already sound) — declined under the analysis
  discipline; `no_prim_node` validator clause stays `:off` until that migration.
  Bool-as-prim sub-cluster (546/579/627/631/55/559) is largely handled: connectives
  retired to Std.Bool, kernel Bool folds are inductive ctor values; residual
  `:True`/`:False` literals in fold are a plumbing choice guarded by the Task-10
  antibody (agreement with Builtins schemas), not a soundness gap.
- Doc 1: **13** (remove `{:prim,op,args}` as op model), **14** (proof-producing
  comparison APIs).
- Doc 2: **527** (prim ops = separate node vs typed constants), **528** (partial
  arithmetic folded into defeq too loosely), **607** (`infer_prim` types div as
  total), **608** (`infer_prim` still accepts numeric `:eq`/`:ne`), **609** (prim
  op fallback stuck in evaluator), **33** (prim ops spread across layers), **34**
  (div/rem weakly typed), **35** (float prim reduction policy).
- Bool-as-prim sub-cluster: **546** (Bool split: hardcoded atoms vs registry),
  **579** (`:True`/`:False` hardcoded in kernel), **627** (CoreBridge → bare
  `:True`/`:False`), **631** (Reduce folds bool ops at surface), **55** (constant
  folding uses Erlang booleans vs inductive Bool), **559** (runtime/protocol Bool
  mismatch).

## K3 — Holes in final Core
Allowed during elaboration; must never survive into final/trusted Core.
- Doc 1: **1** (final-Core holes).
- Doc 2: **524** (kernel accepts holes as terms), **102** (emit hole-check erases
  before checking), **292** (`_` in value position treated as hole), **293**
  (hole numbering only walks 3-tuples), **20** (`Types.Holes` → new policy),
  **323** (`Holes.render` uses legacy display).

## K4 — The `absurd` marker lives in Core syntax
Should be elaborator-only unreachable marker, not a Core term.
- Doc 2: **566**, **571**.
- **LANDED (35da361, 34aecae, 16718f6, 651821b).** §H empty-case ex-falso in 3
  steps: (1) kernel `check_coverage` accepts a constructor OMITTED iff provably
  `:impossible` at the scrutinee's indices (Agda/Idris index-contradiction; relies
  on K5a-hardened `:impossible`); (2) elaborator OMITS impossible branches (all 5
  sites) instead of `{cname,ar,{:absurd}}` bodies; (3) validator `no_absurd_node`
  → `:reject` in `release_config`. `{:absurd}` is gone from the grammar
  (`Term.term?` already excluded it), producers, and final Core. Full purge of the
  residual DECLINED with proof (analysis discipline): `infer` has no catch-all, so
  its `infer({:absurd})→:error` clause is load-bearing for kernel totality
  (removal would crash, not tighten); serialize/emit handling likewise retained as
  antibody-covered defense for the grammar-excluded shape.

## K5 — Index unification / branch-skipping / coverage (soundness-critical)
The heart of dependent `match`; conservative and known-incomplete.
- **ASSESSED (2026-07-08) — K5a LANDED; K5b rides the deferred Eq cluster;
  residuals are hygiene/addressed/legacy.** K5a (acute unifier soundness) landed:
  #573 length guard, #574 `unify_spine` mismatch→`:impossible`, #575 drop-
  `:undecided` declined-with-proof. Coverage is now sound (K4 rewrite): the Core
  `check_coverage` accepts an uncovered ctor IFF provably `:impossible` at the
  scrutinee indices — so #636 (impossible-vs-missing) IS distinguished, and #543
  (set-inclusion) is superseded. #635 (duplicate-branch) is harmless: the MapSet
  dedups so a duplicate can't corrupt coverage; both bodies are still checked
  against the same refined context (redundant, not unsound — a lint, not a hole).
  #254-257 (exhaustiveness treats pin/unknown as wildcard; hardcoded
  Option/Result/List/Bool) reference the LEGACY `lib/cure/types/pattern_checker.ex`
  (K10 territory), not the Core kernel. **K5b = canonical `Eq.rec`/transport,
  joined with K1b** (spec §E.2) → rides the Eq cluster, DEFERRED (faithfulness,
  K6-blocked — see K1). No un-blocked Core-soundness work remains in K5.
- Doc 1: **15** (keep practical indexed matching, don't chase full Agda).
- Doc 2: **532** (skips "impossible" branch bodies), **533** (arity mismatch
  ignored), **534** (defeq ignored except syntactic), **572** (`check_case_branches`
  skips bodies), **573** (`unify_indices` no length check), **574** (`unify_spine`
  mismatch → success), **575** (drops `:undecided`), **576** (`branch_unify`
  `:impossible` on unknown ctor/family), **635** (coverage: no duplicate-branch
  check), **636** (impossible vs missing ctor not distinguished), **543**
  (`check_coverage` = set inclusion only), **563** (no principled
  coverage+unification report), **601–606** (branch-subst internals:
  `replace_branch_vars` catch-all success, `specialize_branch_context` reify/eval,
  `bind_index` binds outer vars, 100 000-depth bound, `occurs_index?`
  over-approx, `strongly_rigid_occurs?` only ctor/data spines), **254–256**
  (exhaustiveness treats pin/unknown-ctor as wildcard; redundancy calc broken),
  **257** (pattern checker hardcodes Option/Result/List/Bool).

## K6 — Flat data values / lost constructor identity
Values flatten params++indices; ctors carry no family/param identity → forces
checking mode and repeated re-splitting.
- Doc 2: **531** (quoted data lossy without signature), **544** (flatten
  params/indices in values), **545** (parameterized ctors can't infer), **597**
  (case repeatedly splits flattened data), **598** (ctor values lack
  family/param identity), **599** (kernel rejects parameterized-ctor inference),
  **600** (result params/indices computed by eval, opaque rep).
- **545/599 LANDED (b355753 + f3b0e73). Rest resolved-by-design; grade-coupled polish deferred.**
  Per spec §E.1 the flat spine `{:ctor, sym, args}` split-by-signature IS the
  target (Lean's kernel form); 544/597/600 are explicitly accepted costs, and
  598's "lost identity" is recovered via the ctor name→signature lookup (fully via
  `sym`/K12). **545/599 — param-bearing ctors were rejected in inference
  (`:ctor_requires_checking_mode`) — is now FIXED (b355753):** §E.1's form landed —
  when the P params RIDE THE SPINE ahead of the fields (`length(args) == pc + arity`),
  `infer({:ctor})` reads + re-checks them from the family's param telescope (no TCB
  metavar inference) and synthesizes the vdata; the fields-only spine still forces
  checking mode (SOUND — a bare `{:ctor}` with no field determining an implicit
  param genuinely can't be inferred). Additive/backward-compatible (arg-count
  disambiguation), so no fixture churn. First consumer: the Eq `bridge_step`
  inductive refl (f3b0e73). Pinned: `test/cure/core/k6_param_ctor_infer_test.exs`,
  `test/cure/core/param_index_split_test.exs:101`. The `ctor_signature` validator
  clause (params-at-grade-0 self-identification) stays `:off` — that final polish is
  coupled to the grade-on-binders reshape (the erasure SEMANTICS already exist as
  `:erased`/`:present` quantities; grade-on-binders is a 4-tuple representation
  change, assessed separately). K6's soundness + inference-completeness content is
  DONE.

## K7 — Universes / levels
- Doc 1: **9** (remove fixed `Type 0..2` ceiling), **10** (universe-polymorphic
  globals + level params).
- Doc 2: **525** (universe machinery far short of Lean/Agda/Idris), **563** (no
  level-metavar/universe-constraint integration in unification), **592**
  (field-level universe check too simple), **593** (`infer_sort` only exact
  `{:vtype}`), **611** (type formation doesn't reduce aliases before
  `infer_sort`), **612** (no cumulative coercion).
- **ASSESSED — soundness already MET + pinned; the level-expression/polymorphism
  reshape is a large PARITY FEATURE (not soundness), DEFERRED with proof.** The
  current universe system (`Cure.Core.Universe` + kernel `infer_sort`) is SOUND:
  predicative `Type ℓ : Type (ℓ+1)` (never `Type:Type`, so not Girard-inconsistent),
  cumulative (`le?`, `l1<=l2` upward only), correct `lmax` for Π/Σ (`Universe.max`),
  and the two-universe rule `check_field_levels` (every field-TYPE level
  `<= fam_level`) is exactly the Girard-avoiding constraint — already PINNED
  (`inductive_wf_test.exs:50` → `:universe_level`). #592 is therefore not a hole.
  The remaining items are EXPRESSIVENESS, not soundness: #9 unbounded hierarchy
  (the `@ceiling 2` is a conservative YAGNI cap — bounding is safe, never unsound;
  removing it standalone is a half-measure the spec ties to the reshape), #10/#525
  level polymorphism, #563 level metavars/unification, #612 cumulative coercion,
  #593/#611 δ-whnf-before-`infer_sort` (completeness — conservative rejection is
  sound). The spec §C target (level-expr `lzero/lsucc/lmax/lvar` + `{:global, sym,
  levels}` polymorphism) is a large reshape COUPLED with K12's `Sym` work and
  needing level-metavar unification — a parity FEATURE deserving its own
  design/plan pass, not incremental cron surgery. Deferred per the analysis
  discipline; `level_expr` validator clause stays `:off`. Same category as the
  K6 ctor-rep and K12-Sym deferrals.

## K8 — Normalizer / conversion / defeq discipline
- Doc 2: **529** (frozen stuck-case expansion is bespoke), **530**/**583**/**409**
  (fuel in process dictionary, not nest-safe), **582** (`:fuel_exhausted`
  returned as term-like), **410** (option validation raises), **550**
  (`Types.Reduce` parallel normalizer), **557** (reify WHNF/NF without
  signature-aware quote in public paths), **558** (η for functions but not
  records/Σ), **584** (same-neutral-before-δ shortcut), **585** (no principled
  transparency mode), **547** (norm/quote can produce terms kernel rejects),
  **610** (`{:global}` eval always opaque; δ only in norm/conv), **630** (Reduce:
  CoreBridge then structural surface recursion).

## K9 — Metavariables / unification / elaborator internals
- Doc 2: **535** (metas not contextual enough), **536** (Miller solver emits
  unchecked solutions), **537** (final-Core meta rejection not centralized),
  **538** (multiple non-reference fallback elaboration strategies), **614**
  (`MetaCtx` stores type but not local context), **615** (WHNF pre-reduction
  disabled under binders), **616** (WHNF lambda-from-non-lambda), **617** (Miller
  detection lacks explicit spines), **618** (Miller peels Pi syntactically),
  **619** (Miller solutions not type-checked against meta type), **620/621**
  (`has_meta?` catch-all false; ignores motives/branches), **622**
  (`finish_global_app` swallows expected-type unify failure), **623**
  (`elaborate_free_name` → global fallback for any unknown), **624**
  (`elaborate_type` unknown var → data family), **625** (`elaborate_named_call`
  spine of unknown globals), **626** (a second elaborator subset at file bottom),
  **554** (`System.get_env` inside elaboration).

## K10 — Legacy parallel dependent systems (Pi/Sigma/Reduce/CoreBridge/legacy SMT)
Second dependent calculus that shadows the real Core; mostly off the main path
already, but still referenced (esp. by Antigen oracles).
- **ASSESSED (2026-07-08) — legacy dependent machinery is DELEGATED away (sound);
  the residual soundness question reduces to `dependent?/1` classifier
  completeness (#12), flagged for a focused probe.** The compiler and
  `Types.Checker.check_module` BOTH gate on `Cure.Elab.Program.dependent?(ast)`:
  dependent modules route to `check_dependent_module` → `Cure.Elab.Program.check_ast`
  (the sound Core kernel) for checking (checker.ex:92) and to `dependent_codegen`
  → `check_ast_with_locals`/`Emit` for codegen (compiler.ex:229). The legacy
  `Types.Dependent`/`Pi`/`Sigma`/`Reduce` calculus is NEVER invoked to CHECK a
  dependent program — so its weaknesses (16 Sigma-admits-Any, 15 weak Pi subst,
  632/633) are latent in a self-contained subsystem (`lib/cure/types/`, no
  external refs to Pi/Sigma/Reduce/CoreBridge from the main path), i.e.
  cleanliness-to-eventually-delete, not a live dependent-soundness hole. The one
  genuine open question is #12: `dependent?/1` is a SYNTACTIC classifier — a
  module that relies on a dependent SAFETY guarantee (e.g. `vhead : Vec(S n) -> A`
  applied to a non-empty vector) but carries no local dependent syntax
  (`indexed_type`/`sigma_type`/`rewrite`/implicit-param/`Eq`/`refl`/pair-proj)
  could be misclassified as non-dependent and checked by the weaker legacy
  simple-type path, bypassing the dependent guarantee. Whether such a program is
  constructible-and-unsoundly-accepted is a concrete PROBE (next fire), not a
  parity reshape. NOTE: making `dependent?` more inclusive is risky (Core does not
  yet cover every non-dependent surface construct the legacy checker does), so any
  fix must be targeted. The Antigen-oracle references to the legacy system are
  test-only. 69/70/629 (CoreBridge `String.to_atom`) mirror the K12 decode-DoS
  concern on the legacy path — same bounded-interning fix if that path is kept.
- **#12 PROBED + RESOLVED — the misclassification is real but FAIL-SAFE (pin
  041152f, `test/cure/k10_classifier_failsafe_test.exs`).** Confirmed `dependent?`
  returns FALSE for a module that only calls a dependent fn (`head(empty())`), so
  it IS misclassified to the legacy path. But the legacy checker rejects it —
  `{:arity_mismatch, "function 'head' expects 3 arguments, got 1"}` — because it
  does NOT insert implicit arguments, and dependent values/functions pervasively
  carry implicit type/index params (`{a}`,`{n}`). So both consuming (`head …`) and
  even *constructing* (`empty()` has implicit `{a}`) a dependent value in a
  misclassified module hits an arity reject, never an unsound accept. The
  soundness invariant — a misclassified unsafe dependent call is never ACCEPTED by
  the legacy path — is pinned. Residual (contrived, un-weaponizable): a dependent
  fn with ZERO implicits and concrete indices called with a likewise-implicit-free
  arg — not constructible from real dependent APIs (all use implicit indices).
  **CONCLUSION: no practical Core-soundness hole; the legacy system is
  cleanliness-to-delete.**
- Doc 1: **11** (legacy SMT-backed dependent system).
- Doc 2: **548** (legacy dep system not comparable to Agda/Lean/Idris), **549**
  (Pi/Sigma = second calculus), **550** (`Types.Reduce` parallel), **551**
  (CoreBridge surface vars → globals), **12** (legacy routing misses constructs),
  **13** (legacy `Nat == Int`) + **508** (`Std.Nat` and `Nat==Int` coexist),
  **14** (Pi/Sigma parallel), **15** (Pi erasure/subst too weak), **16** (Sigma
  admits `Any`), **17** (type-level reducer parallel), **288–291** (legacy
  compat: missing constraints "compatible", no implication proof, VC truncation,
  no value-param subst), **69/70** (CoreBridge vars→globals, interns atoms),
  **89** (CoreBridge + SMT parallel type-level semantics), **318** (still creates
  globals for unresolved names), **629** (function calls → globals via
  `String.to_atom`), **632/633** (legacy Pi zip; Sigma `:any` fallback).

## K11 — Trusted boundary: certification, final-Core invariant, subject reduction
- Doc 1: **12** (Core totality certificates authoritative), **17** (final-Core
  invariant enforced globally).
- Doc 2: **555** (`check_def` runs before final-readiness), **556** (certify /
  certificate pipeline too weak for trusted reduction), **562** ("kernel
  re-checks it" used as substitute for elaborator invariants), **586**
  (`check_def` doesn't enforce final-Core invariants), **587**
  (`validate_certificate` insufficient while `Env.certify` public), **588**
  (termination call graph walks proof/type positions), **411** (totality counts
  globals in non-computational positions), **637** (no final-Core grammar
  boundary), **638** (no subject-reduction regression harness), **639** (no
  progress-style final-Core gate), **140** (`Env.certify/2` public, proves
  nothing), **49** (Antigen needs final-Core invariant assays), **48** (artifact
  format should encode final-Core invariants).

## K12 — Bare-atom globals/constructors & missing symbol table (kernel-relevant)
- Doc 2: **526** (globals are bare atoms), **634** (kernel/elab depend on
  bare-atom ctor/family collisions), **578** (`:Eq` hardcoded — see K1), **97**
  (Core env silently overwrites defs/families/ctors), **98** (ctor namespace
  global + unqualified), **99** (nullary ctor collides with atoms), **100**
  (imported dependent globals emit as local calls), **129** (source-name→atom is
  pervasive; needs a compiler symbol table), **70** (CoreBridge interns names).
  *(The broad `String.to_atom` sweep is Tier-2 §T10; only the kernel-facing
  subset is here.)*
- **IN PROGRESS — bounded slices landed; full Sym migration + collision-detect
  deferred.** K12 is the largest representation change (qualified `Sym` for
  `:global`/`:data`/`:ctor`/branch heads + bounded symbol table), so it is landing
  in slices:
  - **Slice 1 LANDED (7dbc71b)** — bounded interning at the serialize DECODE
    boundary (`sym_atom/1` = `String.to_existing_atom`, fail-closed to
    `:unknown_symbol`): kills the unbounded-`String.to_atom` atom-table-exhaustion
    DoS on untrusted C2 s-expr input (spec §D "kill `String.to_atom` in decode").
  - **Slice 2 LANDED (cd634b8)** — same hardening for `Term.from_external` (the
    JSON-able interchange decode; `to_external` is the Lean encoder's output).
    Unknown symbol raises, consistent with the fn's already-partial contract.
  - **Slice 3 — #97 collision-detect ASSESSED, DEFERRED (proof).** The audit's
    "Core env silently overwrites defs/families/ctors" is on inspection the
    DELIBERATE two-pass forward-declaration mechanism: `register_signature`
    (declarations.ex:38) installs a `{:hole,"__pending__"}` stub, then
    `elaborate_function_body` (:61) overwrites it with the real lambda — the
    self/mutual-recursion path; `declare` likewise registers empty-ctors
    (forward-ref) then the full family. A blanket collision-reject BREAKS the
    compiler. A nuanced stub-aware check (reject only real→real rebind) is a real
    tightening but risks the `_lean`/type-synonym add_def paths and — decisively —
    the collision it guards (two modules' same-named `foo`) is what qualified
    `Sym` identity STRUCTURALLY prevents (§D). So collision-detect lands WITH the
    Sym migration, not as a dynamic stopgap. `register_builtin` already enforces
    the single-registration invariant for builtin keys.
  - **Slice 4 (full structural `Sym`) — ASSESSED: TCB-part = cleanliness (defer);
    one genuine E-LAYER gap flagged.** The kernel keys by bare atoms, but the
    collision-freeness it relies on is delivered by the E-layer `Resolution`
    module (Approach B, the LOCKED type-shadowing decision): family/ctor
    collisions between modules are RE-KEYED to `:"Mod#Name"` and unqualified
    ambiguous use errors. So for families/ctors the bare-atom keys reaching Core
    are already collision-free ⇒ the full structural `Sym` migration is
    **cleanliness for the TCB, not soundness** — deferred with proof. Slices 1–2
    (decode-boundary DoS, both in `lib/cure/core/*`) are the sound Core content.
    **Genuine finding (E-layer, out of Core-cleanup scope):** GLOBALS (function
    defs) are NOT protected symmetrically — `Resolution.rekey_term` leaves
    `:global` bare, `merge_env` (program.ex:544) silently `Map.merge`s `defs`
    (right-wins), and the ambiguity machinery covers `families`/`ctors` only, not
    `defs`. So two imported modules that both define `foo` silently overwrite, and
    qualified `A.foo`/`B.foo` both collapse to bare `:foo` (resolve_qualified
    tries `:"Mod#foo"` then bare, but defs are never under the re-keyed key). This
    is a real fail-silent gap, but it is E-LAYER (`lib/cure/elab/*`), and closing
    it extends the LOCKED Approach-B design to globals (re-key? def-ambiguity
    error? qualified globals?) — a design choice FLAGGED for the operator, not
    landed unilaterally under the Core-cleanup cron.

## K13 — Refinements / SMT trusted only as lint, not proof (dependent/final mode)
- Doc 1: **7** (refinements + SMT are warning-only in final/static/dependent).
- Doc 2: **262/263** (refinement base types via legacy resolver; result can't
  represent unknown), **30** (guard refinement/exhaustiveness advisory when
  solver absent), **87/88** (Path/PatternRefinement ignore unsupported guards),
  **192** (`Std.Refine` predicates are runtime Bool, not proofs), **502**
  (`Std.Refine.PositiveFloat`/`Probability` use Float predicates).
  *(Aligns with the locked "Z3 out of the TCB" decision — keep as untrusted lint.)*

## K14 — `Any` removed from the sound modes
- Doc 1: **8** (remove gradual `Any` from static/dependent/final mode). The
  pervasive `Any` escapes elsewhere are Tier-2 §T2; this item is the kernel-mode
  policy that governs them.

---

# TIER 2 — Broad compiler / stdlib / tooling / security sweep (Doc 2, ~1–520)

Not the current focus, but catalogued so nothing is lost. Grouped by theme with
representative Doc 2 item numbers/ranges.

- **T2 — `Any` gradual-typing escapes (non-dependent checker):** 18, 19, 22–29,
  38–41, 178–181, 349, 353–355, 402–407, 448–462, 484–487.
- **T3 — Effects & totality/partiality typing (functions typed pure/total that
  aren't):** 4–11, 71–80, 85–86, 234, 356/490, 460, 463–476, 491–498; extern
  effect/arity 6–8, 82.
- **T4 — Stdlib type-fidelity (signatures lie about shapes):** 36, 182–198,
  230–233, 240–242, 264–265, 473–520 (large `Std.*` cluster), 519–520 (map/set
  ordering).
- **T5 — Codegen / lowering soundness (unknown → `:undefined`/`:ok`/`inspect`):**
  45, 60–66, 114–116, 146–152, 199–202, 210, 350–352, 408, 412–419, 199, 60.
- **T6 — Optimizer / PGO not rechecked after type-checking:** 51–54, 84,
  106–110, 51.
- **T7 — Protocols / sessions / FSM / temporal semantics:** 46, 56–59, 153–172,
  211–222, 281–283, 313–317.
- **T8 — Trace / replay / runtime instrumentation (unsafe deser, global dbg,
  public ETS):** 203–204, 223–229, 375–378.
- **T9 — Packaging / registry / release / signing / transparency / MCP
  (supply-chain trust):** 42–44, 90, 119–129, 245–253, 266–270, 306–308,
  327–346, 388–393, 431–437, 359–360.
- **T10 — Untrusted `String.to_atom` interning (DoS / atom-table exhaustion):**
  70–72, 115, 121, 127–129, 141, 168–171, 173, 196, 243–244, 304, 309, 333, 339,
  342, 445 — audit's own remedy note at **129** (compiler symbol table).
- **T11 — LSP / MCP / docs / CLI tooling (parse-only, not checked; crashes):**
  41, 266–280, 299–305, 321–325, 361–372, 379–387, 394–401, 420–430.
- **T12 — Build-mode / trust configuration (checking off by default):** Doc 2
  **1** (release defaults to no type checking), **2** (opt-out must be
  mode-gated), **3** (stdlib preload ignores compile failures), 21 (`unsafe`
  keyword needed), 47–50, 91–94, 477–487, 513–517.
- **T13 — Antigen harness updates:** 49, 205, 309–312, 442; plus embedded
  "update Antigen" clauses in Doc 1 items 1 & 2.
- **T14 — SMT tooling (parser/solver plumbing, distinct from K13 policy):**
  67–68, 206–207, 284–287, 322, 144.

---

# Cross-cutting duplicate clusters (plan once, touch many)

1. **Equality/refl/rewrite** (K1) — the biggest: ~19 findings across Doc 1
   {2,3,4} and Doc 2 {37,260,261,442,521,522,523,552,560,567,568,577,578,589,590}.
2. **Primitive ops + Bool-as-atom** (K2) — Doc 1 {13,14} + Doc 2
   {33,34,35,55,527,528,546,559,579,607,608,609,627,631}.
3. **Holes** (K3) — Doc 1 {1} + Doc 2 {20,102,292,293,323,524}.
4. **Index unification / coverage** (K5) — Doc 2 {254–257, 532–534, 543, 563,
   572–576, 601–606, 635, 636}.
5. **Legacy parallel dependent systems** (K10) — Doc 1 {11} + Doc 2 {12–17,
   69,70,89,288–291,318,508,548–551,629,632,633}.
6. **Fuel-in-process-dictionary** — Doc 2 {409, 530, 583} are the same defect
   reported three times.
7. **`String.to_atom` interning** — K12 (kernel) + T10 (broad) are one root
   cause; a compiler symbol table (Doc 2 #129) closes both.
8. **Trusted boundary / final-Core invariant** (K11) — Doc 1 {12,17} + Doc 2
   {48,49,140,411,555,556,562,586,587,588,637,638,639}.

# The audit's own priority notes
- **Doc 1 §18** — recommended implementation order for the kernel cleanup.
- **Doc 2 §570** — "immediate priority versus references."
- **Doc 2 §640** — "most urgent kernel-surrounding cleanup from this pass."
Reconcile any plan ordering against these three before locking sequence.

---

# Tackle order (Tier 1), reconciled across §18 / §570 / §640

The three priority notes agree strongly. The key consensus: **all three lead with
a final-Core grammar + validator, not a removal** (§570 #1, §640 #1) — "remove
primitive X from final Core" only has teeth once a validator rejects X everywhere
(eval/normalise/certify/emit/serialize/release/publish). That validator is the
ratchet that makes every later removal enforceable and regression-proof, so it is
Wave 0.

Two deliberate deviations from the raw notes:
- Pull the validator to **Wave 0** (stronger than §18, which buries the grammar
  mid-list) because it de-risks everything after it.
- Split **K1** and **K5** into "acute now / deep later" so cheap soundness wins
  land early without waiting on canonical transport and the coverage report.

## Wave 0 — Enabler (before any removal)
1. **K11a — Final-Core grammar + validator scaffold** (grammar #637, validator run
   everywhere, subject-reduction #638 + progress #639 harness). *Consensus #1 in
   §570 and §640.*

## Wave 1 — Cheap, high-consensus trust-boundary removals (localized)
2. **K3 — Holes out of final Core.** *§18 Phase 1 #1; one kernel clause + emit check.*
   **LANDED (Option B):** `Validator.release_config/0` ratchet (`no_hole: :reject`)
   enforced at both release exits (`Emit.reject_holes`, `Program.check_codegen_ready`)
   over the *pre-erase* Core term — closing the #102 erased-position leak (a hole in
   a rewrite-proof / eq / refl / prim arg that `Erase.erase` dropped). Dev-time
   `check_def` stays lenient so `?name` sketches still typecheck + emit `:hole_goal`.
   The `unsafe` keyword + 3-kind (type/proof/body) taxonomy + node reshape
   `{:hole,name}`→`{:hole,name,safety}` are DEFERRED to their own spec, sequenced
   with the grade wave (proof-vs-body = erased-vs-relevant) and the retirement of
   the legacy `Types.Holes` 3-tuple (Doc-2 #20/#323) to avoid a 3-tuple alias.
3. **K1a — Kill primitive `{:eq}/{:refl}/{:veq}/{:vrefl}`; temporarily reject
   surface `rewrite`.** *#2 in both §570/§640. Inductive `Eq` already exists
   (task #90). §18's temp-reject device (Phase 1 #3) resolves the
   rewrite→primitive back-bridge; canonical transport is Wave 5.*
4. **K5a — Acute index-unifier soundness fixes** (`unify_spine` mismatch→success
   #574, stop dropping `:undecided` #575, length-check #573). *§640 #3/#4.*
   **LANDED (ea669e2, 3b04ec3):** #573 was the live bug — `unify_indices` zipped
   the result/scrutinee index vectors with `Enum.zip`, silently truncating a
   length mismatch to :trivial/:solved; now length-guarded → :impossible. #574:
   `unify_spine` length-mismatch catch-all `{:ok}`→:impossible (defensive;
   unreachable given caller length-guards). #575: analysed + DECLINED with proof —
   dropping :undecided is conservative here (trusted case-checker skips a branch
   body only on :impossible; a dropped/partial subst makes `expected` MORE general
   ⇒ body-check STRICTER ⇒ only false rejection, never false acceptance). Proof
   recorded as comments at both drop sites so it is not regressed into propagation.
5. **K13 — Reject unknown SMT/refinement obligations in final mode.** *§18 Phase 1
   #7; matches the locked "Z3 out of the TCB, lint-only" decision.*
   **LANDED (228d71d):** the untrusted SMT lint rendered any untranslatable AST
   node to a marker-`true`; today that accidentally breaks the query so Z3 returns
   :unknown, but the safety was an artifact of Z3 rejecting a malformed comment.
   Added `Translator.fully_translatable?/1` (shared markers) and guarded
   `Solver.prove_implication` / `prove_with_counterexample` to fail closed to
   :unknown BEFORE running any query — deterministic, Z3-independent. The
   refinement checker already treats :unknown as first-class not-proven, so its
   final/release policy applies (no separate mode flag needed; SMT-refinement is a
   lint layer outside the dependent-Core TCB and outside Idris parity).
6. **K14 — Ban `Any` in static/dependent/final mode.** *§18 Phase 2 #8; mostly
   enforced for free by the Wave-0 validator.*
   **LANDED-by-construction (pin test only, no production change).** The gradual
   `Any` (top type, universal subtyping) is a *semantic* escape living solely in
   the old non-dependent `Cure.Types` checker (Tier-2 §T2). The dependent Core
   cannot express it: no `Any` node in the term grammar, the builtin registry
   holds only genuine inductives (bool/nat/eq), and the surface→Core index bridge
   (`core_bridge.ex` `to_core(_other) -> :error`) fails closed. Manufacturing a
   `no_any` validator clause would be WRONG — it would have to key on the name,
   but Idris/Agda/Lean all permit a type named `Any`; the ban is on the gradual
   top-type semantics, which Core structurally lacks. Pinned by
   `test/cure/core/no_gradual_any_test.exs`. The pervasive `Any` gradual escapes
   in the non-dependent checker remain Tier-2 §T2 — out of scope for the
   dependent-Core-to-Idris-parity cleanup.

## Wave 2 — Bounded representation cleanups the kernel leans on
7. **K4 — `absurd`: encode as checked empty-elimination / elaborator-only marker.**
   *§640 #5. Shallow.*
8. **K6 — Flat data values → params/indices stored separately + constructor family
   identity.** *§640 #7.*
9. **K12 — Bare atoms → qualified symbol IDs (+ compiler symbol table).** *§570 #5,
   §640 #6. The one heavy structural lift early; also removes K1's `:Eq`
   hardcoding; prerequisite for universes (globals carry level args).*

## Wave 3 — The primitive model
10. **K2 — Typed primitive globals** (registry: type/effects/totality/reducer/
    lowering; classify logic-total / runtime-total / partial / effectful / unsafe;
    rework emit/eval/Antigen; finalize Bool-as-inductive). *§18 Phase 4, §570 #3,
    §640 #9.*

## Wave 4 — Universes
11. **K7 — Universe polymorphism** (level exprs/metas/constraints, cumulativity,
    level params on globals, universe-poly `Eq`). *§18 Phase 3, §570 #4. Gated on
    K12.*

## Wave 5 — Collapse legacy + practical dependent payoff
12. **K10 — Collapse legacy Pi/Sigma/Reduce/CoreBridge/legacy-SMT dependent out of
    the trusted path.** *§640 #10. Mostly dead-code deletion once the Antigen
    oracle is repointed at real Core.*
13. **K1b + K5b — Canonical `Eq.rec`/transport; rewrite→transport (undo Wave-1
    temp reject); deep indexed-pattern/impossible-branch strengthening;
    proof-producing comparisons.** *§18 Phase 5 — the phase that pays off the
    FRP-paper goal.*

## Continuous hygiene (fold in, do not gate on)
- **K8** normalizer/conversion (fuel-out-of-process-dictionary is trivial;
  principled transparency-mode is bigger).
- **K9** meta/elaborator internals (type-check Miller solutions, complete
  `has_meta?`).
- **K11b** authoritative certification + relevance/erasure integrated into binders
  (§570 #9).

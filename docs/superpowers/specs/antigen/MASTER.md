# Antigen — Condensed Master Spec

**Date:** 2026-07-21

**Scope.** This document condenses all 35 design specs in `docs/superpowers/specs/antigen/`
into one authoritative reference intended to replace reading the individual files.
Antigen is Cure's property-based metatheory/soundness testing engine for the
dependent-type kernel (TCB = `Cure.Core.*`): it generates *antigens* (challenges with
ground-truth labels), runs *assays* (invariant checks), and banks *antibodies*
(counterexamples frozen as permanent regressions). The folder covers the engine's core
architecture, known-label kernel verticals, the Tier-B typed-term generator,
mutation/fault-injection machinery, triage and shrinking, corpus infrastructure,
coverage and directed generation, meta-testing of the assays themselves, the
untrusted-machinery program (V1–V6), and several TCB/language design specs that live
here because Antigen antibodies gate them. Organized by theme; supersessions noted
inline; only final designs kept. Statuses reflect each spec's last recorded state.

---

## 1. Engine core — vocabulary, architecture, locked decisions

Source: the umbrella design (2026-07-01) — motivated by a **real** soundness hole:
a mutually-recursive `f→g→f` pair was certified total — plus Tier A.

**Vocabulary (locked):** *antigen* — a generated challenge; *assay* — an invariant
check over a challenge; *antibody* — a counterexample banked as a permanent
regression; *infection* — an assay violation. Deliberate violations carry an
`{:expected, _}` tag ("immune response" convention), so intentional negatives
never count as findings.

**Locked design decisions:**
- **Known-label generation is the core discipline.** Challenges are built *by
  construction* with ground-truth labels — the generator IS the oracle. Oracle
  flavors: differential, independent-invariant, known-label. Generator strategy:
  bidirectional-inversion.
- **Reflexivity oracle:** `conv(t, t)` ⟺ deep normalization terminates — a
  non-termination detector, verdict-blind by contract. Assays must use two
  structurally **distinct** but convertible terms to defeat the
  `same_neutral_no_delta?` shortcut (Tier A).
- **Reified `Antigen.Gen` DSL** (its own AST), swappable backend. StreamData is the
  live backend. **No `filter` primitive** — generation must be total. Size-hygiene
  tags on combinators.
- **StreamData quarantine (architectural invariant):** no `StreamData` literal may
  appear under `Antigen.Generators.*` / `Antigen.Assays.*`; grep-enforced by
  `architecture_test`.
- **Op-map injectable seams:** assays receive kernel operations via an op-map
  (`run/1` → `run/2`); no `:meck`; **no TCB edits ever** for testability — a kernel
  injection point would be an unsoundness lever inside the TCB.
- **Budget model:** fixed committed fuel decides verdicts (`@gen_fuel 500`,
  `@assay_fuel 500_000`); the wall-clock killswitch is safety-only, never
  verdict-bearing. `:fuel_exhausted` semantics are per-assay (infection for V3;
  vacuous for confluence).
- **Two-tier capture:** scratch under `tmp/`, committed corpus in
  `test/antigen/*.sexp`; atomic append. Run modes: explorer / generate / replayer.
  A health gate runs over campaign statistics.
- **Tests are immutable once green.**
- **Triage loop discipline:** ill-typed-accepted = fix + antibody;
  well-typed-rejected = report to the operator. Never silently dropped.
- Prior art grounding: ESOP'15 well-typed-term generation, Pałka et al., QuickChick.

**Tier A (the first vertical, 2026-07-01):**
- Four assays: `totality/terminating`, `totality/diverging`, `positivity`,
  reflexivity-as-normalization. Coverage key = a semantic feature vector;
  **plateaus by design** — ~95.2% kernel-cover is an honest ceiling; don't chase
  or fake it (real code coverage is a separate subsystem, §6).

## 2. Corpus & replay infrastructure

**Stores (committed, never silently pruned):**
- `test/antigen/corpus.sexp` — fuzz-found antibodies.
- `test/antigen/seeds.sexp` — coverage seeds.
- `test/antigen/reach.sexp` — reach pins (must-eventually-accept records).
- `test/antigen/reach_reify_split.sexp`.
- Codec: `Cure.Core.Serialize` s-expressions. Verdicts are pure; **no xfail
  mechanism** — expected violations use the `{:expected,_}` tag.

**Human-readable corpus format (approved).**
- Records became readable on disk: pieces as `id::(sexpr)`; notes plaintext
  percent-escaped (**escape order load-bearing**: `%`→`%25` FIRST, then tab→`%09`,
  newline→`%0A`; a literal `"-"` note escapes to `%2D` vs the nil sentinel `-`);
  a readable `fault=` assoc-list (keys sorted) popped out of the Base64 scaffold.
- **Supersession:** §3.0 of that spec supersedes its own earlier plan — no new
  `Antigen.SExpr` module; reuse `Cure.Core.Serialize` (already a byte-identical
  codec). Atom-safety declared MOOT (`Serialize.decode` mints via `String.to_atom`,
  the same posture as before; hand-edit typos minting atoms = accepted limitation;
  safe decode = YAGNI follow-up).
- Fault codec dispatches per-VALUE. Two special shapes: `:out_of_scope_var`'s scope
  2-tuple `(scope (5 5))`; `:universe` heads as Core terms (`(type 0)`).
- `Challenge` struct untouched (pop/merge at the Corpus layer); `dedup_key`
  unchanged (Serialize binary) → migration lossless, byte-identical keys.
  De Bruijn stays positional; scaffold/key stay Base64. Migration via idempotent
  `Mix.Tasks.Antigen.Migrate` (`reach_reify_split.sexp` was the last legacy
  holdout).

**Fixture/corpus hardening.**
- The suspected flake mechanism was FALSIFIED; the real fix was deterministic test
  rewrites.
- `@known_atoms` interning hazard is precisely in `String.to_existing_atom` inside
  `from_pieces`/`decode_record` — every new kind/atom (`:data_split`,
  `:reify_distinct`, `:reify_eq`, `:loop`, `:List`/`:Nil`/`:Cons`/`:A`, …) must be
  added or decode fails. Unbanked kinds (`:closure_env`, `:smt_query`,
  `:unify_problem`) need only a typespec union entry + `@known_atoms`.

**Staleness handling (approved 2026-07-10; supersedes the initial term-migration
draft — a rewrite engine was found YAGNI).**
- **Locked decision: split by provenance; neither branch rewrites terms.**
- Generator-derived records (`seeds.sexp`, `reach.sexp`) → **regenerate**
  (`mix antigen.regen-seeds`, replace-not-append, dedup by coverage key).
- Fuzz-found antibodies (`corpus.sexp`) → **prune** (`mix antigen.prune`): decode +
  replay each through the live kernel; keep if `:ok`, else move to the append-only
  `test/antigen/retired.sexp` with the failure reason. Never rewrite; never
  silently delete — retired records stay reviewable as a "should this become a
  generator cell?" worklist.
- Rationale: the coverage manifest made **generators the shape authority** — a
  stale shape is re-derived, and a retired antibody's shape-class, if still
  valuable, becomes a cell. The rare re-expressible precious antibody is
  hand-migrated. No `schema=` versioning, no rule registry.
- Workflow is manual + git-reviewed; tests never mutate committed stores;
  `corpus_replay_test` remains the ultimate gate. `mix antigen.merge` (already
  built) is unchanged; sequence: merge → prune / regen.

## 3. Known-label kernel verticals (Tier A lineage)

**Indexed/case vertical.**
- Branch-family discipline: challenges add a foreign-ctor branch additively;
  coverage exactness enforced. Two documented kernel gaps found: the
  compound-index refinement gap (`branch_index_subst/4` drops non-variable result
  indices) and motive well-formedness (an under-applied motive CRASHES
  `Eval.apply` — a separate hardening item).

**Rewrite/eq vertical.**
- The refl check has TWO conjuncts; both are probed. Key insight: rewrite is
  proof-erasing, so **all** obligations are TYPING obligations — 4 obligations,
  12 challenges. A fixed battery, not in `default_gen`; BOTH registries (assay +
  replay) updated.

**Mutation corpus (ill-typed challenges).**
- LOCKED: **construction-guaranteed ill-typedness must be decidable from the
  edit** — each operator mutates a checked position with a decidable witness
  (`:head` / `:index` / `:level` / `:scope`).
- 7 operators (post reach-expansion, §4); the assay uses `infer`;
  `reason_diversity` measured on `fault.kind`; steady state = 0 survivors.

**Pre-port banking (directives D1–D4, waves W1–W6).**
- D1: bank must-rejects from the literature *before* porting a feature. D2: pin
  reach gaps in `reach.sexp`. D3: labels state mathematical truth, not current
  behavior. D4: audit-first. Waves: adversarial diverging shapes; reach pins;
  occurs/deletion; positivity escapes; universes; hygiene.

**Deep fault propagation (shipped).**
- `deepen(ctx, term, fault, depth)` wraps a faulty core in 6 checked-wrapper kinds
  so faults are exercised at depth, not only at the root. Constraints: no binder
  over the hole; a bare pair crashes `infer` (no `:pair` clause) so pairs
  self-wrap. Fault records gained `depth`/`wrap_path`; legacy seeds decoded via
  defensive `Map.get(fault, :depth, 0)`.

**Conversion at depth.**
- Both polarities (`conv_reject` / `conv_accept`); the index hidden behind a real
  redex `plus (S^a Z) (S^b Z)`; `conv_depth` drawn first then split between the
  sides; carrier kinds `:conv_index` / `:conv_motive`. Load-bearing facts: `infer`
  returns **un-normalized** neutrals (reduction happens inside Conv), and the
  accept-side control row is load-bearing, not decoration.

## 4. Tier B — typed-term generator and differential assays

**Generator (Approach A, locked): interleaved mode-directed generation.**
- SigMenu `:v1`: Nat / Bounded / Vec families + certified `plus`, `dbl` globals —
  certified via the REAL `validate_certificate` (no faked certificates).
- Context in kernel order (index 0 innermost). INDIR rule.
  **Canonical-inhabitant fallback makes generation total** (no filter).
- Assays: `term/infer_check`, `term/subject_reduction`, `term/normalization`.
  Triage rule: an infer-failure on a generated term → reach pin or generator fix,
  never dropped.

**Reach expansion (2026-07-04; three sequential phases. Its header records V1–V6
complete and both V4 findings fixed 2026-07-04.)**
- **Phase 1 — richer menu:** Π/Σ goal seeds + parametric `List(A)` (Nil/Cons) as an
  ADDITIVE extension of `:v1`. Resolved: no `:v2` menu needed — banked seeds carry
  only the sig atom; replay resolves `env_of(:v1)` fresh. `:List/:Nil/:Cons/:A`
  added to `@known_atoms` (banking is automatic via `explore/1`).
- **Phase 2 — `term/erasure_preservation` assay.** Blocking precondition fixed
  first: `env_of(:v1)` had ZERO `:erased` quantities, so erase was identity and the
  assay vacuous → `vcons`'s `n` arg marked `:erased`
  (`[:erased, :present, :present]`), safe and additive (arity/types unchanged).
  Property: commutation `nf(erase(t)) ≡ erase(nf(t))` — PROVED for ctor-level
  erasure. Boundary: does NOT extend to erased global-def parameters (δ-unfold
  happens before erase) — out of scope; `plus`/`dbl` stay all-present. Erase never
  removes binders → same eval env. Distinct `{:fuel_exhausted, stage}` violation
  class (shared global fuel counter; the two nf calls do unequal work).
- **Phase 3 — new mutation operators:** `pair_component` (MUST self-wrap — bare
  pair at depth 0 raises FunctionClauseError in infer); `lam_body_type` /
  `app_result` (codomain-side faults on real generator-drawn Π terms,
  complementing `app_domain`); `type_param_mismatch` (must NOT be a bare ctor —
  param-bearing families always give `{:error, :ctor_requires_checking_mode}` in
  infer even when well-typed; wrap in an identity app with `list_nat_t()` domain;
  deepen wrappers are all Nat→Nat — skip deepen or add a List wrapper).
  Load-bearing per-operator check: the un-mutated analog must be accepted.
- Corrected finding: **Vec has NO case-eliminator today** (`case_rule` covers only
  Nat/Bd) — List shipped intro-only; List + first Vec eliminators tracked as
  follow-up.

**Value shrinking (Tier 1).**
- `Antigen.Shrink.minimize/3`; the predicate pins the violation TAG
  (`same_shape?` on element 0) so shrinking never wanders to a different bug.
- 4 rules: subterm→atom; numeral decrement; ctx-drop with asymmetric shifts;
  structural unwrap.
- Monotone, deterministic, budget-bounded; seed via
  `:erlang.phash2({kind, payload})`.

**ChoiceSeq backend — REFERENCE ONLY, not scheduled.** Hypothesis-style
choice-sequence backend documented as the fallback if value-shrink proved
insufficient. Supersession: value-shrink + Triage (§5) made it unnecessary;
expected to stay shelved.

## 5. Triage infrastructure (Run D, approved)

`Antigen.Triage.minimize/3` extends minimization to ALL challenge kinds (Shrink
alone covered only `:typed_term`/`:mutant_term`), riding the kind-agnostic
`Challenge.to_pieces/1` / `from_pieces/7` bridge.

- **Component 1 — shrink-all-kinds:** Shrink's candidate rules re-seated on pieces;
  ctx-drop retained verbatim; de-Bruijn-carrying kinds only.
- **Component 2 — `Antigen.Bisect`:** greedy 1-minimal ddmin over name-referenced
  lists (defs / ctors / families). **Focus cleanup must be atomic with a def
  drop** — otherwise the assay crashes on `Env.get_def` nil and `safe_pred`
  silently rejects every drop. Safety = the predicate itself, not static analysis.
  **No reindexing** (name-referenced invariant; tested via a byte-identical
  sibling).
- `:elab_program` = triage no-op (payload is surface strings; surface-string shrink
  is a follow-on).
- **Interleaving:** ONE accepted step at a time over
  `bisect_candidates ++ shrink_candidates` — never nested fixpoints (Shrink's
  `candidates/1` / `reseed/1` become module-visible for this).
- Generalized `Triage.size/1` = Σ over pieces of (node_count +
  numeral_magnitude) + list lengths, defensively 0 when absent; deliberately ≠
  `Shrink.size`. Strict decrease per accepted step ⇒ termination independent of
  budget. The Runner's infection branch routes ALL kinds to Triage; reports gain
  a `triage: size 27→9 · bisect −2 elems · shrink −11 rewrites` line.
- Non-goals: git-bisect over commits (operator-declined fork); a ddmin granularity
  ladder.

## 6. Directed generation, coverage, and fuzzing

**Run A — health-adaptive directed generation.**
- Coverage-key enrichment: former-histogram + binder-depth folded into the flags
  component; arity stays a 4-tuple.
- `SeedPool` crossover restricted to closed `:typed_term` seeds only.
- Health-adaptive group biasing over groups T/M/F; **group F is never reweighted**.
- An 11-branch position→group guard test locks `default_gen` ordering (updated in
  lockstep whenever branches are added — see Run B).
- `bias: false` = a single draw call.

**Coverage manifest (2026-07-10, approved/implementing).**
- Motivation: four kernel soundness findings (S8 positivity app/λ-headed negative,
  S9 coverage param-in-result-index, family-level universe ceiling, premature
  termination certification) slipped past Antigen even though each finding's assay
  existed and fired constantly — the vulnerable **shape** was never generated.
  Neither `:cover` line coverage nor the plateauing feature key can see this class.
- Design: a **coverage cell** = a stable generator-chosen atom naming one
  shape/path an assay must exercise; a **coverage point** = `{assay_id, cell}` (one
  generator can feed several assay ids). `Challenge` gains `:cover_tag`
  (atom | nil) — run-time metadata, NOT semantic identity: not serialized; replayed
  records carry nil; generators stamp it at construction.
- Participants declare `cover_cells/0`; `Antigen.CoverManifest.expected/0` unions
  them. Initial participants: Totality, Positivity, BranchUnify, Universes — the
  four the gap bit (Universes gains a `gen/0` to match the uniform contract).
- Gate test (`cover_manifest_gate_test.exs`): (1) cell completeness — heavy
  sampling of each participant's `gen/0` must hit every declared cell, failure
  lists missing points; (2) explorer wiring — each pool participant reachable from
  `Mix.Tasks.Antigen.default_gen/0` (Universes is curated/seed-only, exempt);
  (3) dead-assay detection — every id in `Runner.registered_assays/0` is either
  sampled from `default_gen/0` or on an explicit `@curated_assays` allowlist.
- Deliberately non-faking scope: cell-completeness only for opt-in assays (grows
  incrementally); focused soundness-relevant cell sets; no kernel-clause→assay
  obligation map (option C rejected as unmaintainable). Red-green proven via a
  synthetic missing cell. The four gap cells (`:app_head_negative`,
  `:param_solved`, `:family_ceiling`, `:pending_sibling`) are in the manifest.
  Post-#18 state: 310 cells / 30 assays.

**Coverage-guided fuzzing (approved: "both, staged … we want the real thing").**
- **Phase 1 — real code coverage:** `Antigen.Cover` instruments `@cover_modules`
  (Kernel, Normalise, Conv, Eval, Quote, Inductive, Serialize, Certificate;
  data-only modules excluded), runs an explore campaign, and emits a deterministic
  markdown cold-lines report grouped by function (`mix antigen cover`).
  Constraints: `:cover` is a VM-global singleton — dedicated serial mode, NEVER
  mixed into `mix test`; try/after cleanup mandatory; cover-touching tests
  `async: false`; `compile_beam` is in-memory only (escript/AtomVM artifacts
  untouched); assert debug_info at startup; cold-line→function mapping requires the
  abstract_code chunk.
- **Phase 2 — `--guided` (libFuzzer-style):** batch per-round coverage-delta gates
  with precise per-challenge re-attribution when a round is interesting
  (`--precise` forces always); edge-minimal corpus `test/antigen/edge_corpus.sexp`;
  feedback = seed-pool crossover (must re-run
  `Process.put(:antigen_seed_pool, …)` mid-run — the pool is otherwise populated
  only at startup) + edge-novelty group reweighting replacing health bias; a
  jackpot (new edge + violation) = ONE report carrying a coverage-delta line.
  Known weakest link: the indirect generative coupling between edges and seeds;
  fallback = feature-key-correlated biasing.

## 7. Meta-testing the engine itself

**Run B — kernel σ-law assays (approved, shipped).** Three relational assays
reusing `:typed_term`:
- `kernel/shift_subst` — 4 substitution laws lifted from Autosubst/PLFA:
  shift-zero identity; shift composition; shift/subst commutation (for `c ≤ j`:
  `shift(subst(t,j,r),a,c) == subst(shift(t,a,c), j+a, shift(r,a,c))`);
  subst-fresh-index no-op. Each law empirically confirmed on 500 real generated
  terms + hand-built cases *before* shipping — a false law would be the
  highest-severity error the suite could make.
- `kernel/weakening` — success-preservation floor + type agreement
  `quote(v', len+1) == shift(quote(v,len),1,0)`; ill-typed input is vacuous `:ok`.
- `kernel/confluence` — `nf == whnf-then-nf`; fuel exhaustion vacuous; non-vacuity
  proven (189/500 generated terms have real head redexes) plus a health-line
  backstop.
- Mechanism: widen `Term.typed_term/1`'s guard from `assay_id in @assay_ids` to
  `is_binary(assay_id)` — deliberately NOT growing `@assay_ids` (which drives
  `default_gen` sampled by the health gate). `default_gen` 11→14 branches; the
  Run-A group table updated in lockstep (`t: [4,5,6,9,10,11,12,13,14]`).
- Correctness ladder (documented, not scheduled): Tier 1 = this run; Tier 2 = Cure
  paper-model; Tier 3 = self-hosted; Tier 4 = Idris differential reference.

**Run C — sensitivity matrix (design-approved).** Mutation-testing the assays
themselves:
- Mechanism: one-rule permissive kernel weakenings injected via the per-assay
  op-map seam (`Antigen.Meta.WeakKernel.real/0` / `weaken/1`). Seams additive
  (`run/1` byte-identical); no TCB edits; no `:meck`. Boundary-only reach —
  kernel-internal transitive weakening is an explicit meck follow-on.
- Key structural fact: **permissive weakenings are only caught by
  negative-expectation assays; purely-positive assays are structurally blind** —
  this predicts CAUGHT vs SLIP a priori.
- 7 weakenings; 8-row curated matrix: 6 CAUGHT, 2 SLIP. Row 3
  (`check_accepts_all` vs `term/infer_check`) = genuine gap, motivates a
  negative-check follow-on. Row 7 (`conv_always_true` vs reflexivity) = by-design
  blind spot (reflexivity is a verdict-blind non-termination detector — why
  `stuck_elim_delta` exists); row 8 (`conv_exhausts_fuel`) IS caught by
  reflexivity — rows 7+8 together prove its contract honest.
- Test discipline: each row = a baseline assertion on the real kernel
  (load-bearing) + a weakened assertion; fixed hand-built fixtures; SLIP cells
  asserted `:ok` openly. Honesty line: evidence of sensitivity, not proof of
  soundness.

## 8. Untrusted-machinery program (V1–V6) — COMPLETE

**Umbrella (2026-07-03, operator-requested design draft).**
- Motivation: Antigen coverage was kernel-concentrated, with ZERO coverage of
  `Elab.{Elaborator,Unify,Erase,TotalityClosure,Emit,Subst}`,
  `Types.{Reduce,Unify}`, and `SMT.*`; the existing elab assay was completeness,
  not soundness — it trusted elaborate's own `:ok`.
- **Organizing principle: the kernel is the oracle.** Two assay flavors —
  differential and intrinsic-law. **Polarity rule:** untrusted-accepts-but-oracle-
  rejects = soundness infection; untrusted-rejects = incompleteness (lower
  severity, a reach gap).
- Open questions ALL operator-resolved 2026-07-03: lead with V3 (highest value,
  cheapest); include intrinsic laws over the untranslatable fragment; keep V6
  unconditional; V2 covers BOTH unifiers. Phase order:
  **V3 → V1 → V2 → V5 → V4 → V6** — V1–V6 complete per the reach-expansion spec's
  header; both V4 findings fixed 2026-07-04.

**V3 — elaborator soundness.**
- Property: `elaborate` accepts ⟹ every def in `env.defs` re-checks in the kernel.
- Ctor exception: use `Kernel.check` (infer errors `:ctor_requires_checking_mode`).
- `Normalise.with_fuel(@assay_fuel)`; `:fuel_exhausted` IS an infection here.
- An elaborator reject is NOT a V3 infection; a crash IS.

**V1 — normalizer soundness (`Types.Reduce.normalize/2` + `equal?/3`).**
- `equal?` is front-door definitional equality — a false `true` is real
  unsoundness with no kernel backstop.
- Untrusted surface: `do_substitute`, `CoreBridge.to_core`/`from_core`,
  `structural_congruence` (arithmetic delegates to the trusted kernel).
- **Independence fix (locked):** using the same `to_core` as the oracle is circular
  (blind to to_core bugs and to `do_substitute`) — the generator builds
  `{ast, bindings, core_expected}` triples with a SECOND generator-owned
  surface→Core encoder, bindings folded in at generation time.
- V1a: differential normalize (result Conv-equal to the kernel's).
  V1b: differential `equal?` ⟺ Conv — `true`-side mismatch = `{:equal_unsound,…}`
  hard infection; `false`-side = completeness (weaker).
  V1c: intrinsic laws for the untranslatable fragment — monotone non-increase
  (moduledoc verbatim) and idempotence (inferred intent, tagged as such).
- Op-map includes a `substitute` hook; a negative control proves the
  do_substitute-blindness gap is closed. Open items: `term_size` on the triple
  payload; `Challenge`/`Corpus` banking wiring; the second encoder is itself a new
  false-positive source (smoke-corpus sanity required).

**V2 — unifier soundness, BOTH engines (operator-locked).**
- **V2a `Elab.Unify` differential (oracle = Conv).** Master property:
  `unify → {:ok, ctx'}` ⟹
  `Conv.conv?(zonk(t1,ctx'), zonk(t2,ctx'), [], 0, sig)`.
  **CLOSEDNESS is a hard precondition** — every catalog entry closed, no
  `{:var,_}` (grounded on `delta_convertible?`). Intrinsic assays: occurs
  (independent helper via op-map `eu_solution`; `occurs?/3` is a defp), idempotent
  zonk, meta-closed — scoped to metas unified against different terms (reflexive
  meta-vs-itself legitimately stays unsolved). The umbrella's raw "well-scoped"
  property is unobservable black-box (`escapes?` gates before store) — covered by
  the soundness differential. Accepted scope limit: closed binders cannot exercise
  genuine free-var re-leveling — do NOT relax closedness to chase it.
- **V2b `Types.Unify` intrinsic + fixpoint.** **No external oracle by design** —
  the `:any` type, one-directional int→float widening, refinement-strip, and
  named-vs-record accepts are exactly why. Fixpoint property: re-unify substituted
  sides ⇒ `s' == s` (verified across all accept clauses); intrinsic occurs /
  idempotent-apply / var-elim. No determinism property (pure ⇒ tautology). The
  fixed catalog MUST exercise int/float and named-vs-record cases.
  `:unify_problem` kind is typespec-only (unbanked).

**V5 — totality-closure driver (`Elab.TotalityClosure`; the kernel's
`validate_certificate` is trusted and NOT tested).**
- V5a soundness: a diverging fn in a type position must be rejected end-to-end —
  `{:ok,_}` → `{:diverging_certified,…}`; also catches the closure MISSING the fn
  entirely (a vacuous pass). Strictly stronger than `totality/diverging` (exercises
  reachability + submission, not just the certificate check).
- V5b completeness: `type_level_fns ⊇` an independent Antigen-owned reachability
  walk (`{:closure_missed, name}`); superset-or-equal only.
- Minimal construction preferred: `loop : Int -> Int = λx. loop x` (int_type-only —
  no `Inductive.declare`, no unknown_family masking). Vessel family/ctor = bare map
  literals patched onto `Env.empty()` — NOT a raw `%Env{}` (missing
  `certified: MapSet` breaks `Env.certify`). Masking risk sidestepped by the
  int_type construction: certify maps EVERY `validate_certificate` error to
  `{:totality_required,…}`, so a `check_def` failure would vacuously satisfy the
  expectation.
- **Verified blind spot:** `collect/1` AND `Certificate.calls?/2` have NO `:prim`
  clause — globals inside prim args are silently dropped. The independent walk MUST
  derive its checklist from `Cure.Core.Term`'s full taxonomy, never transcribe
  `collect/1`. (`:loop` added to `@known_atoms`.)
- Umbrella reconciliation: the existing `totality/terminating` already covers the
  umbrella's incompleteness bullet.

**V4 — erasure/relevance.**
- Found a **VERIFIED REAL BUG**: the erase ctor clause re-zips the full quantity
  vector against already-shrunk args — with ordering `[:erased, :present]` a second
  erase drops the surviving arg. Same hazard on the global app-head path.
- Catalog entries were expected to legitimately FAIL → STOP-and-report discipline
  (both findings fixed 2026-07-04).
- V4b relevance: the 4 rejection sites (return / present-arg / scrutinise / apply
  of an erased binder) + a clean control. No Runner catch-all.

**V6 — SMT lint (`Cure.SMT.Solver`), final vertical.**
- Framed by the LOCKED SMT-trust-boundary decision (Z3 OUT of the TCB): lint
  soundness, not completeness; `:unknown` is always legal. **UNCONDITIONAL** —
  Z3 is guaranteed toolchain; never gated on `available?/0`, no skip path.
- Oracle: an Antigen-owned bounded evaluator `eval_pred(ast, x)` over the committed
  `@domain -32..32` (sound one direction; the converse never fires).
- V6a `{:false_discharge,…}` — `prove_implication` true ⟹ no bounded
  counterexample. V6b `{:false_unsat,…}`. V6c `{:bogus_counterexample,…}` — a
  returned model must genuinely refute, evaluated at the actual witness value
  (unbounded).
- Must NOT pass `:hot`/`:cold` PGO hints (`:cold` remaps unknown→sat).
- Documented real out-of-scope soundness gap: `Translator.do_translate`'s catch-all
  approximates unknown nodes as literal `true` → `(not true)` collapses a subtype
  query to unsat → a false discharge from a *translation* gap. The catalog is
  restricted by construction to fully-translatable one-variable QF_LIA forms; any
  future widening must re-litigate this. Confirmed parser bug (open item):
  `parse_model` truncates Z3's negative witnesses — `(- 99)` → `%{"x" => "(- 99"}`
  via the `[^\)]+` regex; the plan pins a defensive re-parse OR
  non-negative-witness baselines. `:smt_query` kind is typespec-only.

## 9. Elab-tier call-site wiring vertical — dot-forcing (2026-07-08)

The pattern-setting design for **call-site-wiring properties that value-level shims
structurally cannot probe.**

- Why: the existing `forcing/dot` value oracle enters *below* the check's call
  sites (via `forced_check_probe/7`), so it can never observe a caller that forgets
  to invoke the check — exactly the C-a defect (`elaborate_carried_eq_branch` never
  called `check_named_implicits`). Fix: a generator family one tier up, entering at
  `Cure.Elab.Program.elaborate/1` via the existing `:elab_program` kind
  (`Antigen.Assays.Elab`), mirroring `ElabErasure`'s catalog + metamorphic shape.
  Rejected alternative (recorded): raising the shim to
  `elaborate_matched_branch/10` — reconstructing 10 args of elaborator-internal
  state drifts from the real caller.
- Known-label discipline survives the move up: the generator writes both the
  forced solution and the written dot value, so cells are accept/reject by
  construction; no Idris consulted at assay time.
- Six catalog cells: {plain, carried} × {right, wrong} on the forced axis +
  {bind_erased, bind_relevant} on the unforced quantity axis. The unforced axis is
  deliberately NOT crossed with dispatch path (the named-implicit split is computed
  once before the plain/carried fork — dispatch-invariant).
- **Carried cells MUST source from the Task-2 unit-test fixtures
  (`named_implicit_tail_test.exs`) — NOT `nidot` ni03/ni07**: ni03/ni07 landed as a
  simplified directly-invertible family that never reaches the carried dispatch (an
  earlier draft's misattribution, corrected). The landed fixture wins on any
  divergence. Branch bodies use `-> Z()`, never `-> j` (erased implicit — would
  confound the two axes).
- Expected-error heads pinned: `:forced_pattern_mismatch` (forced-axis wrong),
  `:erased_used_relevantly` (bind_relevant — a Relevance error).
  `:named_implicit_unforced` is explicitly out of scope. A reject for the wrong
  reason = `{:dot_forcing_wrong_reject_reason,…}`, not a silent pass.
  **Non-tuple hardening:** parser failures return a **list** while lexer failures
  are tuples — the head check must guard `is_tuple(e)` or it crashes.
- Metamorphic forms: `:flip` — `corrupt_dot` (the causal C-a pin) and `promote_use`
  (proves the C-c quantity gate load-bearing); `:same` — α-rename +
  prepend-unused-implicit-param. Transforms operate on the probe-fn body ONLY,
  never preamble+body (load-bearing for regex first-match safety). Two fixed
  preambles (`H`/`app`/`G` forced axis; Vec/Pack unforced) via `module/2`.
- Wiring parity with `ElabErasure` = one dedicated test file
  (`test/antigen/elab_dot_forcing_test.exs`); verified: no runner/corpus/
  health-gate wiring exists for the `elab/*` family (re-grep at implementation).
- If elaborator behavior contradicts a catalog label: STOP-and-report — never a
  license to patch `lib/cure/`. Future candidates for the pattern: splice-site
  reconstruction (C-b), dispatch inheritance, guard-check wiring.

## 10. TCB / language design specs housed in this folder

Authored from Antigen worktrees because Antigen antibodies gate them; kernel /
elaborator designs rather than Antigen internals.

### 10.1 Bool eliminator (implemented on `autopilot/lean-shape-matching`, NOT merged)

- `{:bool_elim, scrut, motive, tt, ff}` = Lean `Bool.rec` — the ONLY missing kernel
  primitive for branching on primitive values (`{:prim}` comparisons are already
  typed at Bool and evaluated). Everything else (if / guards / literal patterns)
  is expressible in the untrusted elaborator over it.
- Total by construction: exactly two mandatory nullary branches — no coverage rule,
  no default. ι-rules; result type `motive @ scrut`; subject reduction immediate.
- Deliberately only Bool.rec: the infinite prims (Int/Atom/Float) never enter the
  kernel as matchable literals — compare via `{:prim}`, eliminate the Bool result.
- Soundness closure: `certificate.ex` `calls?`/`guarded_node?` catch-alls would
  hide a branch self-call from the termination checker → explicit clauses added;
  antibodies `diverging_bool_elim_branch` / `terminating_bool_elim_branch` banked.
- **The gate caught a real conversion hole:** the initial conv.ex compared tt/ff
  via `conv_closure?`, whose fresh-binder prepend is correct for the motive but
  wrong for arity-0 branches — it masked a captured variable to the same fresh var
  on both sides, so `T(Int)` was accepted at `T(Bool)`. Fixed via the nullary
  `conv_branch_bodies?(0, …)` path (same as `:ncase`). **Lesson: a symmetric
  prepend can mask differing values to the same fresh var.**
- Follow-ups (untrusted, separate increments): surface desugaring; BEAM codegen
  lowering of `bool_elim`.

### 10.2 Identity type as inductive (TCB-central; ACTIVE)

- Problem: Cure's equality was faked as kernel primitives `{:eq}` / `{:refl}` /
  `{:rewrite}`; `refl`-matching (`sym Refl = Refl`) rejected while Idris accepts.
  All real systems make equality an ordinary inductive with a matchable
  constructor and rewrite-as-sugar (verified against vendored source).
- Locked decisions: (1) homogeneous `Eq : (a:Type) → a → a → Type`, single ctor
  `refl : {w:a} → Eq(a,w,w)` with `w` **erased**, seeded like Bool/Nat
  (heterogeneous Idris-style rejected); (2) refl-matching = ordinary dependent
  pattern matching through the index unifier — no generated recursor (Lean-style
  `Eq.rec` rejected: new TCB surface for no gain); (3) the `rewrite` keyword stays,
  demoted to sugar; (4) **K/UIP adopted, `--without-K` rejected — operator signed
  off 2026-07-04** (no Prop universe, no proof-irrelevance or K-like reduction
  accelerations).
- Status: Phase A LANDED (rf03/rf04/rf05 flipped reject→accept); Phase B′ stdlib
  fakery retirement LANDED (`:cure_refl` stubs → real inductive proofs; module
  renamed `Std.Equivalent` / `reflexive`; unprovable stubs dropped, not faked).
- 2026-07-08 revision: the K6 blocker is STALE — params-on-spine saturated-ctor
  inference landed (`b355753`), so the inductive refl IS inferable; the primitive
  `{:eq}`/`{:refl}` have NO producers left.
- Phase-B encoding amendment (post-B1 empirical STOP): re-elaborating the body
  inside the refl branch is UNIMPLEMENTABLE for propositional rewrites (both
  indices bind one witness; stuck computed endpoints degrade to `:undecided`).
  **Adopted encoding = the standard J/subst transport:**
  `{:case, proof, λ(x y p). (motive@x) -> (motive@y), [reflexive(w) -> λh. h]}`
  applied to the body elaborated OUTSIDE at `motive@A` — verdict-preserving by
  construction, no de Bruijn body shift; all seven `{:rewrite}` producer sites
  reduce to one identity-transport helper. Behavioural pin covers rewrite/refl/frp
  (sentinel `frp01_par_assoc`) AND with/withmulti (two producer sites are the
  with-clause sibling transport).
- Phase C (subtractive): strip dead `{:rewrite}`/`{:eq}`/`{:refl}`/`{:veq}`
  clauses; flip `no_rewrite_node`/`no_eq_node` to `:reject`; full TCB gate with
  the Eq-inductive antibody (equates-no-distinct-normal-forms obligation).

### 10.3 Forced/dot patterns + forced-argument erasure (roadmap #5; K+P+E)

- Gap: matching a ctor whose result indices repeat one variable
  (`mrefl : MyEq(w,w)` vs scrutinee `MyEq(a,b)`) should force `b := a`; Cure's
  `unify_indices` silently drops the second equation (`bind_index` degrades two
  distinct plain variables to `:undecided`) → a solved-but-incomplete subst.
- Kernel (TCB): add Agda's **Solution step** — resolve-before-bind in `bind_index`
  (recursive re-unify on the existing-key path; record forced scrutinee-var
  entries with occurs guard), Injectivity, Conflict/Cycle → `:impossible`.
  Obligations: two DISTINCT termination measures (equation-list recursion + the new
  bind-chase bounded by `map_size(subst)`; the antibody must build chains of
  depth > 1); no cross-key binding cycles; no distinct-normal-form collapse.
- Parser: leading-`:dot` `parse_prefix` case for `.x` / `.(expr)`. Patterns and
  expressions share ONE grammar (no `parse_pattern` exists), so the restriction is
  semantic — reject `{:forced_pattern,…}` outside pattern positions; infix
  module-path dots don't collide.
- Elaborator: route the forced substitution into the branch context BEFORE
  elaborating the body — kernel-only is provably insufficient (the body's implicit
  solve fails `{:unsolved_metavariables}` before any kernel re-check). Written dot
  values checked convertible to the determined value
  (`{:forced_pattern_mismatch,…}`); forced positions bind nothing.
- Erasure: in `Cure.Elab.Erase` keyed off **per-branch** forced marks — NOT in
  codegen, and NOT via the ctor's shared `quantities` (declaration-static vs
  match-site-specific; overloading it would erase at every construction site —
  unsound). Conservative: unforced ⇒ keep present.
- The blocking **auto-generalization defect** (Type-parametrized family + ctor
  repeating a free index var across ≥2 index positions rejected at declaration)
  was FIXED by `dc2b6355`; re-verified 2026-07-17: all `dotpat` relations `same`.
- Idris fixture caveat: naive separately-named explicit LHS pattern vars are
  spuriously rejected by Idris itself; faithful fixtures keep them implicit —
  never "fix" this by switching relation to `cure_stricter`.

### 10.4 Retire the Boolean connective prims (proposed, for the TCB agent)

- Move `and`/`or`/`not` + Bool-operand `eq`/`ne` out of
  `Eval.fold`/`Kernel.infer_prim` into prelude case-defs over the inductive Bool
  (Agda/Lean alignment; smaller TCB).
- The substantive win: **definitional computation on open terms** — the case-def
  reduces by splitting, so `and(True, b) ≡ b` holds by refl. **Correction
  (verified, `1b5e510`):** `not (not b) ≡ b` is NOT definitional (stuck
  case-of-case) — only the four one-step equations are definitional wins.
- What stays primitive: arithmetic and numeric comparisons (native BEAM Int/Float
  have no constructors to case on); only `as_bool/1` + the connective/Bool-eq
  clauses are deleted; a residual `{:prim, :and, …}` → `{:unknown_prim, :and}`.
- Highest-risk piece: `==`/`!=` are operand-type-directed — numeric operands keep
  the prim; Bool operands lower to `booleq`/`boolne`. Do not collapse the paths.
- Performance: recognize saturated applications of the five defs in `emit.ex` and
  lower to native BEAM ops; recommend `:andalso`/`:orelse` (an observable
  short-circuit refinement, benign in pure Cure — call it out).
- Downstream Antigen effect: the connective-prim coverage slice becomes moot; the
  v1 menu already seeds Bool — no Antigen changes required; coordinate timing.

### 10.5 Mutual size-change (#13; K — pre-approved under the TCB blanket)

- Replace the blanket mutual-recursion reject (`mutually_recursive?` → false) with
  real cross-function size-change, porting Idris `addFunctions`/`SCSet` + Agda
  CallGraph.
- Algorithm: SCC via existing `called_globals`/`reaches?`; non-square `m×k` change
  matrices per intra-group call (same `arg_relation`); transitive closure (compose
  when dimensions agree, worklist, dedup by `(f,g,matrix)`); certify the whole
  group total iff EVERY idempotent endo-edge `M_{f→f}` has a strictly-decreasing
  diagonal — one bad loop fails the whole group.
- Soundness: the `diverging_mutual_pair` antibody (`d13d718`) becomes the PRIMARY
  witness. Composition partiality is sound (base edges + closure still expose
  every bad loop). Single-function groups reduce exactly to landed #14.
- Non-goals: higher-order/non-variable decreasing args; any
  `assert_total`/`assert_smaller` escape hatch.
- (Per the memory ledger this LANDED as `a4f071fb` — whole-SCC certification via
  `Certificate.total_group/3`.)

### 10.6 Local type shadowing (E-layer; Approach B approved — kernel NOT modified)

- Problem: the registry keys families/ctors by bare atom with zero provenance —
  after `use Std.Nat`, a local `type Nat = Zero|Suc` overwrites `families[:Nat]`
  but never disowns `Z`/`S` from `ctor_to_family` → `{:missing_branch, :S}`.
  Representation-faithful Approach A (Idris NS / Agda QName qualified naming)
  deliberately rejected; B is behavior-faithful, zero TCB/AtomVM-format impact.
- Collision detection over **distinct resolved module identities** — dedup FIRST:
  the same module reached twice (auto-prelude + explicit `use`, or the stdlib's
  real `Vector→Nat` diamond) is ONE source. Over-detection is the
  highest-probability risk (it hits the most common import pattern).
- Losers re-keyed to `:"Mod#Name"` across families / ctors / `ctor_to_family` /
  defs — **including `:case` branch tags**, a bare-atom position distinct from
  `{:ctor,…}` (missing it reintroduces the coverage bug inside the losing import).
- A resolution table maps qualified paths → registry keys (R4 collapse: `Std.Nat`
  in a type slot ⇒ its `Nat`) and carries shadowed/ambiguous name sets, consulted
  BEFORE the ordinary not-found fallthroughs (else diagnostics silently degrade).
  Import-vs-import ambiguity = hard error `{:ambiguous_name,…}`, never silent
  clobber. Runtime ctor tags stay BARE (AtomVM invariant) — codegen strips the
  `Mod#` prefix; the only C-layer touch, escape-hatch path only.
- Critical intercept correction: the parser flattens `Std.Nat.Z(x)` into a
  dotted-**string** function-call name before any `attribute_access` node exists —
  resolution must be wired into all three call sites (`constructor_pattern`,
  `elaborate_named_call`, `idx_to_core`'s `function_call` clause), not just the
  `attribute_access` (nullary-reference) path.
- Diagnostics anchor: post-re-key a shadowed ctor is *absent*, so intercept at the
  `{:unknown_pattern_constructor}` gate → `{:shadowed_ctor, …, hint:
  "Std.Nat.Z"}`; `{:missing_branch,_}` can never be a shadow artifact after
  re-keying.

---

## Source specs

| File | One-line description |
|---|---|
| `2026-07-01-antigen-design.md` | Umbrella design: vocabulary, layered architecture, oracle strategies, fuel/killswitch, corpus tiers, prior art. |
| `2026-07-01-antigen-indexed-case-design.md` | Indexed/case vertical: branch-family discipline, compound-index refinement gap, motive-crash hardening item. |
| `2026-07-01-antigen-tier-a-design.md` | Tier A: first four assays (totality ×2, positivity, reflexivity), Gen DSL, coverage key, run modes. |
| `2026-07-02-antigen-choiceseq-backend-design.md` | Hypothesis-style choice-sequence backend — reference only, gated behind value-shrink, expected shelved. |
| `2026-07-02-antigen-conversion-at-depth-design.md` | Conversion probed at depth behind real redexes, both polarities, load-bearing accept-side control row. |
| `2026-07-02-antigen-deep-propagation-design.md` | `deepen/4` checked-wrapper fault injection at depth; fault depth/wrap_path metadata. |
| `2026-07-02-antigen-eq-rewrite-design.md` | Rewrite/eq vertical: both refl conjuncts probed; proof-erasing ⇒ all obligations are typing obligations. |
| `2026-07-02-antigen-mutation-corpus-design.md` | Ill-typed mutation corpus: construction-guaranteed ill-typedness decidable from the edit; 7 operators. |
| `2026-07-02-antigen-pre-port-banking-design.md` | Pre-port banking directives D1–D4 and waves W1–W6 (literature must-rejects, reach pins). |
| `2026-07-02-antigen-tier-b-term-generator-design.md` | Tier B interleaved mode-directed typed-term generator, SigMenu v1, differential term assays. |
| `2026-07-02-antigen-value-shrink-design.md` | `Shrink.minimize/3`: violation-tag-pinned, 4 rules, monotone/deterministic/budget-bounded. |
| `2026-07-03-antigen-directed-generation-design.md` | Run A: coverage-key enrichment, SeedPool crossover, health-adaptive group biasing (F never reweighted). |
| `2026-07-03-antigen-elab-soundness-design.md` | V3: every elaborator-accepted def kernel-re-checked; crash = infection, reject ≠ infection. |
| `2026-07-03-antigen-erasure-relevance-design.md` | V4: erasure idempotence re-zip bug (verified real, later fixed) + the four relevance rejection sites. |
| `2026-07-03-antigen-fixture-corpus-hardening-design.md` | Corpus hardening: flake falsified, `@known_atoms` hazard pinned, legacy-format migration. |
| `2026-07-03-antigen-human-readable-corpus-design.md` | Readable on-disk records; supersedes its own SExpr-module plan (reuse `Cure.Core.Serialize`); lossless migration. |
| `2026-07-03-antigen-kernel-law-assays-design.md` | Run B: shift/subst σ-laws, weakening, confluence assays; laws pre-validated on 500 real terms. |
| `2026-07-03-antigen-normalizer-soundness-design.md` | V1: differential normalize/`equal?` vs Conv with an independent second encoder; intrinsic laws. |
| `2026-07-03-antigen-sensitivity-meta-testing-design.md` | Run C: WeakKernel permissive weakenings mutation-test the assays; 6 CAUGHT / 2 explained SLIPs. |
| `2026-07-03-antigen-smt-lint-design.md` | V6: bounded-evaluator oracle over −32..32, unconditional Z3, translator catch-all gap documented. |
| `2026-07-03-antigen-totality-closure-design.md` | V5: diverging-in-type-position end-to-end reject + independent reachability walk; `collect/1` `:prim` blind spot. |
| `2026-07-03-antigen-triage-infrastructure-design.md` | Run D: shrink-all-kinds + Bisect ddmin over pieces, one-step interleaving, generalized size. |
| `2026-07-03-antigen-unifier-soundness-design.md` | V2: `Elab.Unify` differential vs Conv (closedness precondition) + `Types.Unify` intrinsic/fixpoint. |
| `2026-07-03-antigen-untrusted-machinery-design.md` | Umbrella for V1–V6: kernel-as-oracle, polarity rule, operator-resolved phase order V3→V1→V2→V5→V4→V6. |
| `2026-07-03-bool-eliminator-tcb.md` | `{:bool_elim}` kernel primitive (Lean Bool.rec); gate caught the conv fresh-binder masking hole. |
| `2026-07-04-antigen-tierb-reach-expansion-design.md` | Tier B phases: Π/Σ/List menu, erasure_preservation assay (vcons `:erased` fix), new mutation operators. |
| `2026-07-04-coverage-guided-fuzzing-design.md` | Phase 1 `:cover` cold-lines report + Phase 2 guided fuzzing (edge corpus, mid-run seed-pool feedback). |
| `2026-07-04-forced-patterns-design.md` | Forced/dot patterns: `unify_indices` Solution step, `.e` syntax, per-branch forced-arg erasure; auto-gen defect fixed. |
| `2026-07-04-identity-type-as-inductive.md` | Retire primitive Eq/refl/rewrite → seeded inductive + J/subst-transport sugar; K/UIP adopted. |
| `2026-07-04-local-type-shadowing-design.md` | Approach B type/ctor shadowing: re-key losers to `Mod#Name`, resolution table, bare runtime tags. |
| `2026-07-04-mutual-size-change-design.md` | Cross-function size-change over SCCs (non-square matrices, idempotent-loop criterion), replacing the blanket reject. |
| `2026-07-04-retire-boolean-connective-prims-design.md` | Move and/or/not + Bool eq/ne to prelude case-defs; type-directed `==` split; native-op lowering kept. |
| `2026-07-08-antigen-elab-dot-forcing-design.md` | Elab-tier dot-forcing catalog at `Program.elaborate/1` — the call-site-wiring assay pattern (C-a class). |
| `2026-07-10-antigen-coverage-manifest-design.md` | Shape/cell coverage gate: `cover_cells/0` manifest, `cover_tag`, dead-assay detection. |
| `2026-07-10-antigen-migration-design.md` | Staleness handling: regenerate seeds, prune antibodies to `retired.sexp`; no rewrite engine (YAGNI). |

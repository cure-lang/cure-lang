# Handoff spec — the OPEN elaborator gaps

**Status:** execution-ready. Extracts the still-open items from the full catalog
`2026-07-17-proof-authoring-elaborator-ergonomics-design.md` (findings E1–E11 + K1) and
organizes them for a single agent. Read that spec for the deep repros/history; this one is
the scoped work list, the unifying theme, the priority order, and the discipline.

## 0. Framing (read before touching anything)

Every gap below is a **completeness / ergonomics REACH gap**, never a soundness gap: Cure
sometimes rejects a well-typed term Idris accepts (`cure_stricter`), forcing an author to
restructure a proof. The trusted kernel stays sound throughout; these live in the UNTRUSTED
elaborator (`lib/cure/elab/*`) and the kernel re-checks whatever it produces. So the bar is
"widen what elaborates without admitting anything ill-typed" — the kernel re-check is your
safety net. A fix that makes the kernel accept a bad term is a bug, not a win.

Two of these (E9, E10) touch the E/K boundary. Any change to `lib/cure/core/*` is HARD-STOP:
red-green + a new Antigen antibody + full Antigen + full suite, reviewed as its own run. Prove
NO untrusted (elaborator-only) fix works before proposing a kernel change (elaborator-hard-stop
principle) — for E9/E10 an elaborator-side reflection/normalisation may suffice.

**Two-pipeline steer (non-negotiable):** all dependent machinery is `lib/cure/elab/*` +
`lib/cure/core/*`. IGNORE `lib/cure/compiler/*` (`codegen.ex`, `pattern_compiler.ex`) and
`lib/cure/types/*` (`checker.ex`, `unify.ex`) — those are the NON-dependent lowering/checker
pipeline and their same-named symbols are decoys. Confirm every "it's missing / not retained"
conclusion against `lib/cure/elab/` + `lib/cure/core/` before reporting it.

## 1. The unifying theme

E1/E2/E6/E8 are ONE family: **index existentials + sibling/context refinement.** They share a
root — pattern/constructor elaboration binds a constructor's VALUE but not its (erased) index
existentials, and refinement/solving is scoped per-match or per-ctor instead of across the whole
clause/application. Idris avoids the whole family because it solves each clause as ONE
simultaneous unification problem and threads one metacontext. So the deep, principled fix is
mostly shared:

- **Clause-simultaneous / accumulated-substitution matching** → closes **E8** and much of **E9**'s
  constraint scoping.
- **One shared metacontext threaded through the application tree** → closes **E6-residual**.
- **Surface named-implicit binders on constructor patterns** → closes **E2-residual**.

E9 additionally needs constraint reflection + identity-type injectivity; E10 and E11-Stage-2 are
independent (conversion-reduction and name-resolution respectively). A team that lands the shared
matching/metacontext work knocks out several of these at once.

## 2. The open gaps

### E9 — Stuck-index equation not retained as a proof on GADT match  *(highest recurring tax)*

- **Symptom.** Matching `acc : Accepts(PTimes(a,b), MkMS(Z,Z,Z))` as `ATimes(m1,m2,…)` — whose
  result index is the STUCK app `msadd(m1,m2)` — leaves `m1,m2` abstract with NO term witnessing
  `msadd(m1,m2) = MkMS(Z,Z,Z)`. Inversion (`m1=m2=empty`) is impossible. Constructor injectivity of
  the identity type (`MkMS(p,q,r)=MkMS(Z,Z,Z) ⊢ p=Z`) is also not derivable from a `reflexive` match
  (`:conversion_failure`).
- **Root cause + layer.** E/K boundary. When a ctor's index is a non-constructor (stuck function
  app), the match introduces the unification constraint but neither (a) refines the existentials nor
  (b) reflects the constraint as an `Equivalent` the branch can eliminate.
- **Idris accepts** (via `with`-style abstraction). Reach gap: YES.
- **Proposed fix.** Reflect the residual index constraint as a branch hypothesis
  `Equivalent(I, ctorIndex, scrutIndex)` (Agda/Idris `with`), and provide a derived, TCB-neutral
  constructor-injectivity eliminator for the identity type. Prefer an elaborator-only reflection
  (synthesize the eq into the branch context) before any kernel change.
- **Current status.** OPEN, but **routed around at the proof level** this era via the
  index-generalization technique (generalize the family index, carry `q : idx = concrete` as an
  explicit argument — see `intrinsic-dependent-elab-order-fixes` / the Brzozowski completeness
  proofs). A real fix would delete that boilerplate from every inversion proof. **Definition of done:**
  the pre-generalization `nullable_complete`/`deriv_complete` shape elaborates directly.

### E6-residual — shared metacontext through the application tree  *(architectural)*

- **Symptom.** A nullary indexed ctor whose index is an implicit of an ENCLOSING application is left
  unsolved. Repro: `star_fold(APlusR(ATimes(MkMS(S(Z),Z,Z), MkMS(Z,Z,Z), AAtomA(), AStar0())))` →
  `:unsolved_metavariables, AStar0`. `star_fold`'s `{a}` IS solved from the deep sibling `AAtomA`
  (fixing `a = PAtom(TA)`), but the also-deep `AStar0 : Accepts(PStar(a), 0)` is elaborated in its own
  nested `finish_ctor_app`, which zonks+finalizes its metavars EAGERLY (`elaborator.ex` ~7156,
  `has_meta?` → `:unsolved_metavariables`) BEFORE the outer application solves `a`.
- **Root cause + layer.** E. Per-ctor eager finalization: the inner ctor's metavar lives in the
  OUTER metacontext but is finalized in an inner, isolated one.
- **Idris accepts** the enclosing-function case (E6 family). Reach gap: YES.
- **Proposed fix.** ARCHITECTURAL: thread ONE shared metacontext through the whole application tree
  (or postpone per-ctor finalization to the top-level solve), not per-ctor eager finalization. NOT a
  bounded edit. The E6 CORE (a direct sibling determines the index) is already fixed
  (`check_ctor_args` postponement); this is the enclosing-application residual.
- **Workaround (keep using until fixed).** Bind the sub-term to a typed helper
  `fn h() -> T(concrete indices) = <ctor>` (checking-mode annotation pins the index).
- **NOT in scope / do not "fix":** the *floating-OUTPUT-index* variant — a "can-step" wrapper
  `PStep : SStep(l,r,l2,r2) -> Progress(l,r)` where the target `l2,r2` are floating implicits of the
  wrapper — is rejected by **Idris too** (verified 2026-07-18: minimal `PStep StMsg` REJECTS in
  Idris2). It is NOT a reach gap; the correct answer is REFORMULATION (give the index family only its
  INPUT indices, e.g. `PStepSR : Progress(SSend(t,lk), SRecv(t,rk))`). Record this as authoring
  guidance, not an elaborator bug.

### E8 — Sequential-match refinement does not compose across independent scrutinees

- **Symptom.** After `match pat` (binding `PTimes(a,b)`), a SEPARATE `match acc → APlusR(ar) →
  match ar → ATimes(m1,m2,…)` forcing `m ≡ msadd(m1,m2)` does NOT update the goal; a later
  `rewrite msadd_assoc(m1,m2,…)` fails `:rewrite_no_match` (goal still `msadd(m, singleton(t))`, `m`
  unrefined). A control WITHOUT the outer `match pat` refines `m` correctly.
- **Root cause + layer.** E (same family as E1). Each match desugars to its own motive; the second
  match's substitution (`m ↦ msadd(m1,m2)`) is scoped to its own elaboration and not back-propagated
  into the return type the earlier match already specialized.
- **Idris accepts** (one clause = one simultaneous unification). Reach gap: YES.
- **Proposed fix.** Elaborate a `match` under the accumulated index substitutions of enclosing
  matches — or adopt clause-simultaneous matching (the Lean-shape spec). Overlaps the E1 fix.
- **Workaround (in use).** Helper-delegation: move the evidence match into a function whose `acc` is
  a PARAMETER (e.g. `deriv_sound`'s `ds_times`/`ds_star` matching `acc` directly, mutual-recursing).

### E2-residual — surface named-implicit binders on constructor patterns

- **Symptom.** A RELEVANT index existential can't be named in a proof body — `CRStep`'s `t` (needed
  for an `MCons t …` congruence), `SStep`'s split counts (needed for a measure). E2's erased-slot
  fix landed; the relevant-existential case remains.
- **Root cause + layer.** E. Pattern matching binds a ctor's value, not its index existentials, as
  named term variables.
- **Idris accepts** (bind implicits `{t}` in patterns). Reach gap: YES.
- **Proposed fix.** Surface named-implicit BINDERS on constructor patterns (an `as`/named-index
  binder). Subsumed by the E1 context-refinement work for many uses.
- **Workaround (in use).** Add the value as an EXPLICIT constructor FIELD (`CRStep : (t:Tag) -> …`)
  so a data-match binds it, plus a small congruence helper (`mcons_cong`) instead of an inline
  `reflexive` over the unnameable index.

### E10 — Higher-order function argument not reduced in a dependent index position

- **Symptom.** Free-monad `Eff(a)` monad laws: a goal mentioning `bind(m, <function>)` fails to
  reduce the applied function. (a) a LAMBDA in an `Equivalent` index — `Equivalent(Eff, bind(m,
  fn(y) -> Pure(y)), m)` — crashes normalisation (`Eval.apply: … is not a function`, `y` mis-resolved
  to a global); (b) a NAMED fn `bind(m, ret)` → `:branch_type` (`bind(Pure(x), ret)` not reduced
  through `ret` in conversion); (c) a PARTIAL app `bind(m, kcomp(f,g))` not reduced. TERM position
  works — it is specifically the index/conversion path.
- **Root cause + layer.** K (normaliser) + E. Reducing `bind` applied to a concrete continuation in a
  TYPE/INDEX position needs β/δ of the applied function under the motive; kernel conversion doesn't
  drive it for a lambda (closure mis-captures the binder), a δ-name, or an under-applied global.
- **Idris accepts** (reduces applied functions in conversion). Reach gap: YES.
- **Proposed fix.** Normalise applied functions (β for lambdas, δ for names, saturation for partials)
  inside conversion when they occur in an index, and fix the lambda-closure capture on that path.
  HARD-STOP if it lands in `lib/cure/core/*`.
- **Workaround (in use).** First-order MONOID formulation (no continuation function) — `Otp.Meta.EffAlgebra`
  proves `seq` identity+associativity. The value-returning free-monad `bind` laws stay blocked.

### E11 — Stage 2: type-directed tie-breaking for a bare ambiguous applied-def head

- **Symptom.** A BARE ambiguous applied def head (`plus`, defined in several modules) in a type/index
  position doesn't resolve by context; the qualified spelling is required. Stage 1 (qualified head →
  value namespace; bare-unique → key; bare-ambiguous → clean `:ambiguous_name`) is FIXED.
- **Root cause + layer.** E (`declarations.ex`). No type-directed disambiguation of the bare case.
- **Idris accepts** (resolves by argument/expected types). Reach gap: partial.
- **Proposed fix.** TYPE-DIRECTED tie-breaking per the approved `overloading-and-argument-labels-spec`:
  resolve a bare ambiguous applied def by the argument/expected types instead of requiring the
  qualified spelling.

### E12 — `rewrite`'s occurrence-finder is δ-blind (target hidden under an unreduced defined function)

- **Symptom.** `rewrite n1 in …` with `n1 : role_eq(fr,r) = F` against goal `project(GMsg(fr,to,t,k),
  r) = project(k,r)` fails `:rewrite_no_match`. The redex `role_eq(fr,r)` is NOT syntactically present
  in the goal — it appears only after `project` δ-unfolds one step and its inner `case` exposes the
  scrutinee. `abstract_term`'s occurrence search walks the goal WITHOUT unfolding defined functions,
  so it finds nothing to abstract.
- **Distinct from E8** (same `:rewrite_no_match` tag, different mechanism): E8's redex is
  PRESENT-but-unrefined (an outer match failed to refine `m`); E12's redex is ABSENT-until-unfolded
  (buried under a defined-function application). Do not conflate them.
- **Root cause + layer.** E (`elaborator.ex`, the rewrite/`abstract_term` path). The kernel's
  conversion DOES see through `project` (δ/ι) — the concrete-cased `reflexive` version checks fine —
  but the elaborator's rewrite occurrence-finder does not WHNF/δ-normalise the goal to expose targets
  that sit as `case` scrutinees under a defined function.
- **Idris accepts** the direct `rewrite p1 in rewrite p2 in Refl` (its evaluator WHNF-reduces `project`
  to the exposed `case`). Reach gap: YES.
- **Proposed fix.** WHNF/δ-normalise the goal (or candidate subterms) during rewrite-occurrence search,
  matching Idris. E-only; no kernel change (kernel conversion already handles it).
- **Workaround (in use).** Case the scrutinees concretely (`match r`/`match fr`/`match to`) so
  `role_eq`/`project` reduce and lean on kernel conversion via `reflexive`. Verified on
  `branch_merge.cure` `proj_bystander_msg` (27-leaf concrete case; Idris mirror uses the direct rewrite).

### E1-sub — scrutinee variable not substituted in branch-BODY term occurrences

- **Symptom.** `match r { RA() -> reflexive(project(k, r)) … }` gives `:conversion_failure`: the branch
  refines the GOAL to `project(k, RA)`, but the hand-written `r` in `project(k, r)` still dereferences
  the abstract binder (`nvar`), not `RA`. Writing the literal `project(k, RA())` fixes it.
- **Relation to E1.** The E1 family is framed as sibling/context refinement (refining OTHER binders'
  types). This is the MATCHED variable itself, in TERM position in the body, not being linked to its
  pattern — which Idris/Agda get free via clause substitution. Same root (refinement scoped too
  narrowly), new surface; track as an E1 sub-case, not a dup.
- **Root cause + layer.** E. The branch substitution refines the motive/goal but is not applied to
  term-level occurrences of the scrutinee variable in the branch body.
- **Idris accepts** (clause substitution replaces `r` with `RA` everywhere in the branch). Reach gap: YES.
- **Proposed fix.** Extend the branch substitution to rewrite the scrutinee variable to its pattern in
  the body's elaboration context, not just the goal. Subsumed by the E1 context-refinement rework.
- **Workaround (in use).** Write the concrete constructor literal in the branch body instead of the
  matched variable. In use across `branch_merge.cure` concrete-cased lemmas.

### E13 — reflexive/diagonal GADT constructor doesn't propagate its index identification to the goal

- **Symptom.** A reflexivity constructor `SubRefl : Sub(l, l)` (both indices the SAME var). Matching
  `sub : Sub(a, b)` against `SubRefl` unifies `a = b`, but when a subsequent match (or an already-matched
  sibling scrutinee) refines `b` to a concrete shape (e.g. `b := LSel(kL,kR)` from matching `st :
  LStep(b, b2)`), that refinement does NOT flow back to `a` in the goal. Reconstructing a term over `a`
  (`MkStepTo(LStSelL(), …)` or reusing `st : LStep(a, b2)`) then leaves the constructor's index metavars
  unsolved (`:unsolved_metavariables, LStSelL`). Minimal repro: a `sub_step` that, in the `SubRefl` case,
  must produce a `Step(a, _)` — fails; the structural cases (which bind `a`'s shape via the constructor
  pattern) succeed.
- **Root cause + layer.** E. `SubRefl`'s two-occurrences-of-`l` index unifies `a` and `b` as a symmetric
  equation but the elaborator keeps them as distinct metavars linked only one-directionally; a later
  refinement of one is not mirrored onto the other, so the goal's copy of `a` stays unsolved.
- **Idris accepts** the identical proof (its unifier treats `a = b` symmetrically and propagates). Reach
  gap: YES.
- **Consequence.** Blocks the IMPLICIT-continuation form of `sub_step_l` (subtyping simulates local
  reduction with the step target inferred), which in turn blocks any theorem that must invoke it with a
  NEUTRAL/unnameable continuation — the multi-step simulation `sub_run` and the natural
  implicit-`g2` `config_subst`.
- **Proposed fix.** In GADT-pattern unification, record a reflexive index identification (`a = b` from a
  repeated-variable constructor index) as a two-way link so a later refinement of either side updates
  both, and re-solve dependent goals. E-only.
- **Workaround (in use).** Make the shared continuation EXPLICIT so it never needs reflexive
  reconstruction: `config_subst` takes `g2` explicit, so the spec continuations `project(g2, role)` are
  writable and thread as `sub_step_l`'s explicit `b2` — avoiding `SubRefl` entirely (`7d0ccad1`).

### K-bug 3 — MISDIAGNOSED (NOT a Cure gap); it exposed a real ORACLE-rigor gap instead

- **Original claim (WRONG).** The faithful n-ary branch-merge `merge`/`union_branches`/`insert_branch`
  (where `union_branches(bs1, BCons(t,k,rest)) = insert_branch(t, k, union_branches(bs1, rest))` and
  `insert_branch` calls `merge(k, k2)` on a shared label) fails to certify total in Cure, and "Idris
  accepts it" — implying Cure's size-change is more conservative than Idris.
- **Corrected (verified 2026-07-18).** The "Idris accepts" evidence was bogus: `idris2 --check` does
  NOT hard-fail on totality — under `%default total` it prints `Error: … is not total | is not
  covering | not strictly positive` yet **exits 0**. The definitive `:total merge` REPL query shows
  Idris ALSO rejects this group ("not total, possibly not terminating due to recursive path
  insert_branch → merge → merge → union_branches → insert_branch"). So **Cure is correctly conservative
  and ALIGNED with Idris — both reject.** There is no Cure size-change bug. The insert-into-a-recursive-
  result pattern is genuinely beyond plain size-change in both languages; the fix is to author it
  differently (POSITIONAL PAIRING recurses on structural subterms only and certifies in both — used for
  `otp_nary_merge_idem`, `01b75884`).
- **The REAL finding + fix (LANDED).** The oracle's `idris_verdict` decided `:accept` purely on
  `idris2 --check` exit status, which is totality-blind. For an oracle over PROOFS totality is
  soundness (`foo : P; foo = foo` proves anything), so a type-check pass is not enough. `oracle.ex`
  now rejects when `--check` output matches `is not total|is not covering|not strictly positive`,
  matching the Cure side (which certifies totality before it will δ-reduce a proof). Re-ran the whole
  `otp` cluster under the stricter check: ZERO positive probes flipped (every proof is genuinely total
  on the Idris side too), `verdicts.json` unchanged, replay green — so all shipped `rel=same` results
  are now validated as total-proof on BOTH sides. NOTE: other clusters' frozen verdicts predate the
  stricter check; the change is monotonic (only catches genuinely non-total Idris proofs), so a full
  re-generation across clusters is a hygiene follow-up, not a correctness regression.
- **Unrelated ordering note (still valid).** A plain FORWARD reference (a fn calling a helper declared
  *below* it) defers certification until the end-of-module sweep, so a dependent proof checked before
  the sweep sees the caller non-reducing — same class as the mutual-recursion cert bug (`a4f071fb`) but
  for non-mutual forward refs; workaround is define-before-use ordering.

## 3. Recommended order

1. **E9** — highest leverage; a real fix deletes the index-generalization boilerplate from every
   inversion proof. Try elaborator-only reflection first; kernel change is HARD-STOP.
2. **E6-residual** (shared metacontext) — architectural but unblocks the nullary-ctor-through-enclosing-app
   class; overlaps nothing else and removes a common `:unsolved_metavariables`.
3. **E8** — closes the helper-delegation tax on `deriv_sound`-style proofs; shares the E1 simultaneous-
   matching machinery, so pairs naturally with any E1/E9 matching rework.
4. **E2-residual** — surface named-implicit binders; smaller, high ergonomic payoff.
5. **E10** — unblocks the free-monad laws; K-touching, HARD-STOP, do last.
6. **E11-Stage-2** — smallest; type-directed overload for the bare applied-def case.

The E1/E2/E6/E8 cluster is one body of work (index existentials + refinement + shared metacontext);
scoping them together and landing the shared machinery is more efficient than one-at-a-time.

## 4. Discipline (per gap)

- **Red-green, oracle-anchored.** Each gap has a concrete `cure_stricter` repro above — turn it into a
  paired `.cure`/`.idr` oracle probe (Idris ACCEPTS, Cure currently rejects), fix until Cure accepts
  and `mix cure.oracle` reports `rel=same`, then a scoped `mix test <file>` for the elaborator unit
  test. Replay green before commit.
- **Antibody per fix.** Add a NEGATIVE test proving the fix still rejects a genuinely ill-typed
  version (the widening must not admit unsound terms).
- **HARD-STOP for K.** E9 and E10 may reach `lib/cure/core/*`. If so: red-green + new Antigen antibody
  + full Antigen + full suite, as a reviewed run. Prove no elaborator-only fix works first.
- **Ghost commits, explicit pathspec.** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`,
  no Co-Authored-By; `git add -- <path>`.
- **Stop and report** on an unanticipated failure or a would-be kernel change — do not improvise.
  Report the exact diff, red→green evidence, oracle output, and an honest generality statement (which
  proofs now elaborate directly that previously needed a workaround).

## 5. Definition of done (whole thread)

For each landed gap: the workaround it replaces is removed from at least one real module
(`otp_mailbox_pattern.cure` for E8/E9, an `Eff` module for E10, etc.), that module still `rel=same`,
and the elaborator unit test + antibody are green. The catalog spec's status line for the finding is
flipped to ✅ FIXED with the commit. The floating-OUTPUT-index E6 variant is NOT a target — it is
recorded as authoring guidance (both Cure and Idris reject; reformulate the index family).

# Lean-Shape Dependent Pattern Matching (for Safe FRP Types) — Design

**Date:** 2026-07-02
**Status:** Approved design (Lean shape; replace A/B/C; kernel work authorized).
**Governing memories:** `dependent-types-frp-initiative`, `reactive-runtime-design-bible`, `transliteration-program-p0`, `elaborator-hard-stop-principle`.
**Domain skill:** `cure-porting` (differential-oracle TDD loop, K/E/P/A/C layer map, TCB HARD-STOP discipline).

## 1. Goal

Give Cure **real Lean-style dependent pattern matching** — one unification-driven,
context-generalizing `match`/`with` mechanism that **subsumes today's three
fragmented paths** (A = value-abstraction `with`, B = eq-transport `with` proof,
C = index-inversion LHS-rematch) — so that Cure can express and *statically check*
the type system of Sculthorpe & Nilsson, **"Safe Functional Reactive Programming
through Dependent Types" (ICFP'09)**, and run the resulting programs on BEAM/AtomVM.

This is the enabling capability for the dependent-types-FRP initiative: replacing
Cure's faked dependent types with machinery strong enough for indexed signal-function
families.

## 2. Why this shape (paper-grounded)

The paper's type system rests on **one heavily-indexed inductive family**
`SF : SVDesc → SVDesc → Dec → Set` whose constructors carry **computed indices**:

- `_≫_  : … → SF as cs (d₁ ∧ d₂)`
- `_∗∗_ : … → SF (as ++ bs) (cs ++ ds) (d₁ ∧ d₂)`
- `loop : … → SF (as ++ cs) (bs ++ ds) → SF ds cs dec → SF as bs d`

Indices are **`++` on type-level lists** and **`∧`/`∨` on `Dec`** — *functions*, not
constructors. The operational semantics (paper Fig. 4) and every combinator are
defined by **dependent pattern matching on this family, refining computed indices
per branch**. §8 records that the authors abandoned Haskell for Agda specifically
because of **"problems encoding associativity of vector concatenation."**

That is the crux and the acceptance driver: matching/composing on `SF (as ++ bs) …`
leaves the index a **stuck application** (`++` with an unknown split), so unification
does **not** reduce to a substitution — the equation must be **carried** and
discharged by an **associativity/identity `rewrite`**. Cure's current
substitution-only rematch (path C) *cannot* do this.

**Correction (grounded against `~/Develop/lean4/src/Lean/Elab/Match.lean:210-284`):**
this is *not* something Lean's automatic equation compiler does. Lean's own
"discriminant refinement" procedure supports only three equation shapes — `x = t`,
`t = x`, `ctor … = ctor …` — and its doc comment gives the structurally identical
case (`f a ∈ [f b]`, a stuck non-injective application) as the example it
**deliberately refuses** to auto-generalize, "to ensure information is not lost."
Genuinely stuck index equations in real Lean are either auto-discharged by
`generalizeIndices`/`unifyEq?` (`src/Lean/Meta/Tactic/{Cases,UnifyEq}.lean`) or the
match **hard-fails** ("Dependent elimination failed"). The *only* Lean mechanism
that leaves a user-visible carried `Eq` is the opt-in `match h : e with`
(`withEqs`) — which is a named scrutinee-value equation the user asks for, not an
automatic stuck-index fallback. Cure already has this exact mechanism, shipped,
zero-TCB: capability B (`with … proof <name>`, the Eq-arrow motive
`λw. Eq(T,e,w) → G[e↦w]`). What Phase 2 proposes is a **Cure-specific
automation** of that opt-in idiom — generalizing capability B's proven
scrutinee-*value*-equation mechanism to computed-*index* equations — inspired by,
but going beyond, what Lean's compiler does automatically. It must stand on its
own soundness case (see Phase 2), not on a claim that this is inherited Lean
behavior.

### Why Lean shape over Agda shape (for Cure specifically)

Both mature systems solve this; the tie-break is architectural fit:

1. **Reuses Cure's just-verified trusted core.** Rematch already routes through
   `{:case}` + `unify_indices` + `specialize_branch_context` + a re-checking
   `Kernel.check`. Generalizing *that* engine is a continuation, not a new subsystem.
2. **Handles the ++-associativity crux natively** via carried equalities in the motive.
3. **Composes with Cure's existing `rewrite`** (rw07, bridge lemmas) instead of
   redefining `rewrite` as with-sugar (the Agda model would disrupt shipped machinery).
4. **Matches Cure's "elaborator proposes, kernel disposes" model** — both systems keep the
   kernel as the soundness backstop, but the concrete *mechanism* differs and this design
   follows Cure's own, not Lean's: per `src/kernel/inductive.cpp` (`add_inductive_fn`),
   Lean's kernel *authors* a single recursor per family from scratch (re-deriving
   `nparams`/`nindices`, checking positivity, building the reduction rules itself), and
   all `match`/`cases` compile down to ordinary *applications* of that kernel-owned
   recursor — checked by the kernel's generic Pi-application and iota-reduction rules,
   with no bespoke "case" typing rule at all. Cure has no single kernel-derived recursor;
   `{:case, scrut, motive, branches}` is a **primitive Core construct** with its own
   bespoke kernel rule (`check_case_branches`/`unify_indices`/`check_motive_wf`,
   `kernel.ex`) that re-checks whatever case-tree the elaborator emits directly — this is
   the Idris2 (`Core/Case/CaseBuilder.idr`)/Agda (`Rules/LHS.hs`) case-tree style, which
   this project's own `reference/MANIFEST.md` already correctly attributes to Idris2/Agda,
   not Lean. What genuinely *is* Lean-shaped here is narrower than point 4's original
   phrasing claimed: the params/indices split stored in the signature (Phase 5) and the
   general TCB philosophy — not the case-construct mechanism itself.

(Agda-shape with-function generation would be the more literal transliteration of the
paper's *source*, but a worse fit for Cure's architecture and shipped `rewrite`.)

## 3. Layer map & the trusted-kernel discipline

- **K (TCB, `lib/cure/core/*`):** the changes in Phases 1 (only if its audit finds a real
  gap), 2 (only if its E-first attempt hits a proven wall — see Phase 2), and 5 (a TCB
  change is expected here regardless: signature-aware `Quote.reify`). Each **is**, or
  **would become** if triggered, HARD-STOP-and-review: red-green + a new Antigen antibody
  proving the change terminates and **equates no distinct normal forms** + full Antigen
  suite + full test suite + an **independent adversarial-verification subagent** pass
  (fresh context, tries to break soundness, re-derives from code) BEFORE the task is done.
  Per the project's `elaborator-hard-stop-principle`, Phases 1 and 2 must first prove no
  untrusted (E-only) term closes the gap before any TCB diff is opened for them.
- **E (`lib/cure/elab/*`):** Phase 3 (the equation-compiler front-end) and the A/B/C
  retirement. Emits only kernel-checkable Core; the kernel re-check is the soundness
  backstop.
- **P/C:** minimal (surface already supports `match`/`with`/`rewrite`).
- **A (Antigen):** grows an antibody per TCB change.

**No auto-merge.** The full human review of all TCB changes is at merge time (consistent
with "authorize kernel work" + autopilot). Per-change the automated soundness gate above
must be green.

## 4. Architecture — one generalizing, unification-driven match

A single elaborator path (an equation compiler) that, for a `match`/`with` on scrutinee(s):

1. **Generalizes the dependent context into the motive — two distinct mechanisms, both
   required, not one uniform rule** (disambiguating an earlier draft's conflated
   phrasing): **(1a) dependency-based context reversion** — sibling context entries whose
   *type* depends on the scrutinee's free variables (including its computed indices) are
   reverted into Π-binders, so per-branch index-refinement reaches them (Lean's automatic
   `generalize`, `Match.lean:879-916`; Cure's existing `specialize_branch_context` /
   capability-C convoy); **(1b) syntactic occurrence-abstraction** of the scrutinee
   *expression itself* within the goal, independent of whether its type has indices
   (Cure's existing `abstract_term`/`motive_for`, capability A — closer to Lean's manual
   `generalize`/`kabstract` idiom than to Lean's automatic `match` step, per §2's
   correction). A match/with that needs both (e.g. an indexed with-rematch whose goal also
   names the scrutinee's value directly) must run **(1a) and (1b) together** into one
   combined motive — Phase 3 must specify the composition, not assume either mechanism
   subsumes the other.
2. **Runs the full first-order unifier per branch** (Phase 1, already landed — see
   correction there): the five rules — **solution** (`x := t`), **injectivity**
   (`c ū = c v̄` → unify `ū,v̄`), **conflict** (`c … = d …`, c≠d → `:impossible`, discharge
   `{:absurd}`), **cycle** (occurs-check → `:undecided`, degrades to the conservative
   fall-through — never `:impossible`; see Phase 1's correction), **deletion**
   (definitionally-equal sides → drop).
3. **Carries stuck equations** (Phase 2): when neither solution nor injectivity applies
   (e.g. `as ++ bs` vs a variable/other stuck term), inject an explicit `Eq` hypothesis
   into the branch (motive-carried), rather than failing — the FRP crux. (This is a
   Cure-specific automation of Lean's *opt-in* `match h : e with` idiom, generalized
   from scrutinee values to computed indices — real Lean has no automatic version of
   this for stuck, non-injective index applications; see §2's correction.)
4. **Emits nested case trees** (`{:case, …}`, possibly nested) the kernel re-checks.
5. **Discharges carried equalities** via Cure's existing `rewrite` + a stock of
   type-level lemmas (Phase 4): `++` assoc/right-identity, `∧`/`∨`/`<:` laws.

Capabilities A/B/C become special cases of this path and are retired once each is
provably subsumed (their existing tests stay green as the subsumption proof).

**Capability-B indexed-scrutinee boundary (completeness check):** capability B's
restriction to non-indexed scrutinees (`elaborator.ex:533`) is very likely a
**heterogeneous-equality (`HEq`) gap, not an arbitrary limitation**: `Eq(T,e,w)` only
type-checks when `e` and `w` share one type `T`, which holds today only because `T` can't
vary across branches for a non-indexed family. For an indexed scrutinee, a branch's
pattern value has a type with refined indices, genuinely different from the scrutinee's
outer type — the same "green slime" problem Lean's `withEqs` solves with `HEq`, not `Eq`
(`mkEqHEq`, `Meta/Match/Match.lean:128-143`). Cure's kernel has **only homogeneous `Eq`**
(`kernel.ex:102`; no `HEq` anywhere in `kernel.ex`/`elaborator.ex`/any spec). Capability
C's convoy avoids this because it only equates *index* values (fixed type across
branches), never the scrutinee value itself. **Before Phase 3 claims to subsume capability
B onto indexed scrutinees** (which Pass 7's ordering note above already flags as a
plausible need for the rematch+proof combination): confirm whether Phase 6's actual FRP
port ever needs a *named* proof-equation over an indexed `SF`-scrutinee. If yes, adding
`HEq` to the kernel is a new TCB item this plan does not currently list anywhere and must
be scoped (own HARD-STOP gate) before Phase 3 can honestly claim full A/B/C subsumption.
If capability C's convoy already covers every indexed case the paper needs, say so
explicitly and scope capability B's generalization to non-indexed scrutinees only,
permanently — not as a temporary restriction to be lifted later.

## 5. Phased plan (each phase = independently testable; TCB phases gated)

**Ordering contingency (found during review):** phases are listed 0-6 as a default
sequence, but two forward dependencies are plausible, not ruled out: Phase 2's named
TCB-escalation trigger ("an Eq endpoint that is itself an indexed-family value") is
exactly Phase 5's fix, and Phase 3's required (1a)+(1b) motive composition (§4 point 1)
may need the same capability if a with-rematch (capability C, indexed) is combined with a
carried proof-equation over the indexed scrutinee itself (today's `elaborate_with_rematch`
takes no `proof_name` at all — the combination is untested and unimplemented). **If Phase
2's escalation or Phase 3's composition hits this wall before reaching Phase 5, pull
Phase 5 forward** rather than treating 0-6 as a rigid sequence; don't force Phase 2/3 to
route around a gap that Phase 5 exists to close.

- **Phase 0 — Acceptance oracle (E/none; non-TCB).** A minimal faithful transliteration
  of the paper's `SF as bs d` family with `++`/`∧` indices + one combinator whose result
  index is `as ++ bs`, as paired `.cure`/`.idr` oracle probes (cluster `frp`). Currently
  **red in Cure** (the stuck-`++`-index case), green in Idris — this anchors "done" and
  proves the gap. Also a red unit test at the elaborator level.
- **Phase 1 — Unifier audit (TCB; gated only if a gap is found).** **Correction (verified
  against `lib/cure/core/kernel.ex:787-885`, ancestors `f16d008`/`5646c63` already on this
  branch):** the five-rule first-order unifier is **already landed**, not solution-only —
  `unify_indices`/`unify_one`/`unify_spine`/`bind_index` implement solution (both
  directions), injectivity, conflict (rigid-head-clash/same-key-merge ⇒ `:impossible`), an
  occurs-check, and syntactic deletion. Phase 1 is therefore an **audit** of the existing
  unifier against this spec's needs (does it expose enough for the generalizing front-end
  in Phase 3?), not new construction. Its antibody must **not** require occurs-check
  (cycle) to yield `:impossible` — the already-reviewed
  `2026-07-01-case-index-unification-design.md` §5 deliberately makes cycle/uncertainty
  degrade to `:undecided`, never `:impossible` ("uncertainty is never `:impossible`"), and
  real Lean has no general "cycle ⇒ this branch is impossible" rule either (its
  `occursCheck` is generic metavariable-assignment machinery, not a case-splitting
  impossibility signal). Corrected antibody: unifier terminates + never equates distinct
  normal forms + **conflict** (not cycle) ⇒ `:impossible` soundly. If the audit finds no
  gap, Phase 1 closes with no TCB diff.
- **Phase 2 — Carried equalities (E-first; escalate to TCB only on a proven wall).**
  Stuck unification carries an `Eq` into the motive instead of falling through unrefined.
  **Correction:** `check_motive_wf` (`kernel.ex:597-689`, the `defc6cb` fix) already
  accepts `Π(Eq(ty,a,b), G)`-shaped motives generically, *including* an indexed-family
  `ty` — capability B (`with … proof`) already proves the kernel takes this shape with
  **zero TCB change** for scrutinee-*value* equations. The FRP crux's actual carriers
  (`as,bs,cs,ds : SVDesc = List(Sig)`, `d : Dec`) are plain non-indexed ADTs, so the known
  `Quote.reify` collapse (which only bites indexed-family Eq *endpoints*, reach-pinned by
  `reify_split_gap_reach_test`) does not apply to them. Per the project's
  `elaborator-hard-stop-principle`: attempt the **E-only** route first — generalize
  capability B's mechanism from scrutinee-value equations to computed-index equations —
  and only declare TCB-required after that hits a concrete, named blocked kernel
  judgement (expected candidate: an Eq endpoint that is itself an indexed-family value,
  which is Phase 5's territory, not this one). Antibody (if a TCB change proves
  necessary): a carried-eq branch is sound iff the kernel can independently re-derive the
  equation's use-site well-typedness; if no TCB change proves necessary, Phase 2 closes as
  E-only and the Layer map's Phase-2 TCB listing (§3) is removed at that point.
- **Phase 3 — Generalizing match front-end (E).** The equation compiler (context
  generalization + per-branch unifier + carried eqs + nested case-tree emission).
  Subsume + retire A, then B, then C (each: prove its suite still green under the unified
  path, then delete the special-case code). Differential oracle: `match`/`with` clusters
  stay `same`.
- **Phase 4 — Type-level lemma stock + `rewrite` composition (E/C).** `++` assoc/identity,
  `∧`/`∨`/`<:` as total type-level functions + refl-bridge lemmas; make `rewrite` discharge
  carried stuck-index equalities. **Phase-0 probes flip to accept here** (oracle `frp` → `same`).
  **Scaling caveat (hidden-assumption check):** the only *proven* discharge technique in
  this codebase is the rw07 bridge-lemma pattern (refl-bodied lemma + a two-rewrite chain),
  and it is explicitly documented (`elaborator-hard-stop-principle`,
  `transliteration-program-p0` memories; `2026-07-02-idris-parity-roadmap.md` row 6) as
  closing **only the single-reducible-inner-occurrence case** — multi-occurrence / deep
  up-to-conversion rewriting is a separately reach-pinned, still-open gap. `_∗∗_`'s and
  `loop`'s indices plausibly need more than one occurrence rewritten per goal (an
  interchange-law shape, not a single associativity substitution). Real Lean/Agda give no
  shortcut here either — per `src/Lean/Meta/Tactic/UnifyEq.lean:60-136`, Lean's own
  equation solving is single-shot discharge-or-fail; multi-step algebraic rewriting is
  always a human-composed proof, never automatic. Phase 4 must budget for this as *unproven
  reach*, not a natural extension of rw07: if the `_∗∗_`/`loop` goals need multi-occurrence
  discharge, that is new work (closing the multi-occurrence reach gap) gating Phase 6, not
  a corollary of the lemma stock existing.
- **Phase 5 — Signature-aware `Quote.reify` (TCB; gated).** The reach-pinned repair (recover
  the params/indices split from the signature, Agda/Lean-style) — closes the residual
  Eq-endpoint incompleteness (`reify_split_gap_reach_test` migrates red→green-forcing).
- **Phase 6 — FRP capstone (E + probes).** Port the real `SF` + `≫`/`∗∗`/`loop`/`switch`
  + decoupledness (`Dec`) + initialisation (`Init`) indices. Oracle confirms: well-formed
  nets **accept**; instantaneous (undecoupled) cycles and uninitialised-signal escapes
  **reject** — the paper's safety property, checked by Cure. **Scope-expansion flag
  (internal-consistency check):** `switch` and `Init` are new here — §1/§2 ground `SF`
  as the 3-index family `SVDesc → SVDesc → Dec → Set` over exactly three constructors
  (`≫`,`∗∗`,`loop`); `Init` adds a fourth index dimension (arity change) and `switch` a
  fourth constructor, neither defined or index-designed anywhere above (`Init` is named
  in the `reactive-runtime-design-bible` memory's `FlowDesc(Init/Dec/clock/type)`, but this
  spec never connects it to `SF`). Before Phase 6 starts: re-derive `Init`'s index algebra
  and `switch`'s computed-index shape from the paper the same way §2 did for `≫`/`∗∗`/
  `loop`, and confirm Phases 1-5's mechanisms (unifier, carried-eq, lemma stock,
  signature-aware `reify`) generalize to a 4-index family without new gaps — don't assume
  it folds in for free.

## 6. Acceptance criteria

- **Differential oracle** `frp` cluster: well-formed signal-function nets `accept`
  (Cure = Idris), the paper's two bad-program classes (instantaneous cycle; uninitialised
  escape) `reject` in both; every entry `same` (or a written, sound `cure_stricter`).
- The ++-associativity composition (`_∗∗_`, `loop`) type-checks in Cure — the crux the
  authors switched languages for.
- **A/B/C retired**: the unified path subsumes them; `with_abstraction`, `with_rematch_*`,
  and dependent-`match` suites remain green with the special-case code deleted.
- Every TCB phase: its Antigen antibody green + full Antigen + full suite + independent
  adversarial verification, TCB diff reviewed at merge.
- 0 regressions vs the branch baseline at each phase gate; full suite green at Stage 5.

## 7. Skeptical-review directive (operator-mandated)

**At the top of EVERY skeptical-review pass (spec review and plan review), the reviewer
must first re-check how Lean implements the relevant mechanism** by reading the actual
`~/Develop/lean4` source (`src/Lean/Elab/Match.lean` for the equation compiler / motive
generalization / `withEqs`; `src/kernel/` for the checked eliminator; the unifier in
`src/Lean/Meta/`), and ground each finding against that reference rather than against
memory or assumption. A finding that contradicts Lean's actual behavior is itself suspect.

## 8. Non-negotiable constraints

- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`,
  no `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only** (`git add -- <path>`); a concurrent agent may share
  the origin worktree. This build runs on an isolated `autopilot/<topic>` worktree.
- **One build at a time.** Never run two `mix` suites concurrently (a past concurrent
  full-suite run panicked the kernel). Scoped `mix test <file>`; full suite once, alone, at gates.
- **Tests immutable once green**; behavioral, not implementation-coupled.
- **Reference-grounded:** verify against vendored Idris2/Agda AND `~/Develop/lean4` source,
  never memory.

## 9. Deferred (out of scope for this run)

- Forced/dot patterns as a first-class surface feature (`f (k+k)`) beyond what carried
  equalities already give (ledger #5) — revisit if Phase 6 needs it.
- Multiple/nested `with` beyond what the equation compiler yields for free.
- Universe polymorphism (the paper works around its absence in Agda; Cure mirrors the
  workaround, not the feature).
- Codegen/runtime of the FRP combinators on-device (Phase 6 is type-checking; the runtime
  is the reactive-runtime-design-bible's separate staged roadmap).

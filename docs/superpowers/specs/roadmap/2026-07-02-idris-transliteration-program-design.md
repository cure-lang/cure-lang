# Idris-transliteration program — closing the parity ledger by porting reference algorithms

**Status:** program-level design (a charter, not a single-run implementation
spec). Defines the shared method — transliteration briefs, differential oracle,
audit-first rule, acceptance gates — plus a charter per port cluster. Each
cluster still graduates into its own design spec + autopilot run, per the
roadmap's process; those specs cite this one instead of re-deriving the method.

Related:
[`2026-07-02-idris-parity-roadmap.md`](2026-07-02-idris-parity-roadmap.md)
(the ledger this program executes against),
[`2026-06-30-cure-dependent-types-frp-design.md`](2026-06-30-cure-dependent-types-frp-design.md)
(the kernel architecture the ports must respect),
[`2026-07-01-antigen-tier-a-design.md`](2026-07-01-antigen-tier-a-design.md)
(the assurance apparatus every port banks antibodies into),
[`2026-07-02-antigen-pre-port-banking-design.md`](2026-07-02-antigen-pre-port-banking-design.md)
(the bank-now half of the antibody discipline: everything expressible before
the ports, banked before them; runs before P1),
[`reference/MANIFEST.md`](../../../../reference/MANIFEST.md)
(the pinned reference snapshot; at `~/Develop/esp32-beam/reference/`).

## 1. Goal and non-goals

**Goal.** Close the remaining reach/ergonomics rows of the Idris-parity ledger
(#3–#7, #10/#11, #13/#14, #17) by **transliterating the corresponding
algorithms from the vendored Idris 2 / Agda reference sources** into Cure's
existing architecture, instead of deriving each row from first principles.
The reference algorithms are published, battle-tested, and small (the entire
port surface is ~8k lines of source across six clusters); porting them is
faster and lands closer to Idris semantics than independent re-derivation.

**Non-goals (explicit, load-bearing):**

- **No kernel transliteration.** Cure's kernel (~2.9k lines, `lib/cure/core/`)
  is at parity for everything it covers and carries the Antigen antibody
  corpus. Idris 2's core is ~10× larger, QTT-threaded, intrinsically scoped,
  and architecturally entangled (no small-TCB split). A wholesale port would
  trade an audited TCB for an unaudited one. Ports land in the untrusted
  elaborator wherever possible; the two exceptions are scoped in §6 (P1) and
  the roadmap's ④ (`{:absurd}` leaf — since landed in `3b24829`).
- **No QTT, no universe changes, no new capability domains** (roadmap §4).
- This spec does not design the individual ports. Each cluster's spec does
  that; this spec fixes the shared machinery, the cluster boundaries, the
  sequencing, and the per-cluster acceptance gates.

## 2. Verified findings that shape the design

All checked against this tree (branch `autopilot/case-index-unification`,
roadmap commit `dd76d22` and later).

1. **The reference snapshot already exists and is well-curated.**
   `~/Develop/esp32-beam/reference/{idris2,lean4,agda}` — gitignored sources,
   tracked `MANIFEST.md` pinning upstream commits (Idris2 `fd405085b`, Lean 4
   `28b99ec`, Agda `7273757e5e`) and assigning per-concern authority (e.g.
   Agda primary for index unification, Lean for the trust split). The briefs
   in §4 cite these paths; the manifest's caveats are incorporated verbatim.
2. **Ledger row #7 (rewrite motive inference) is substantially implemented.**
   `Cure.Elab.Elaborator.rewrite_plan/5` (`lib/cure/elab/elaborator.ex:174`,
   landed in `decc93f`) already normalizes the goal, abstracts occurrences of
   an equality endpoint to build the motive, and synthesizes symmetry when the
   goal mentions the LHS — the core of Idris' `elabRewrite`. The roadmap's ⬜
   is stale. What remains is at most an audit-level delta (P0).
3. **Ledger row #13 (mutual-recursion soundness hole) is closed on this
   branch.** `Cure.Core.Certificate` conservatively rejects any cycle through
   a sibling global (`d13d718`), and the banked `diverging_mutual_pair`
   antibody replays `:ok` (`test/antigen/assays/totality_test.exs:11`,
   verified green 2026-07-02). The roadmap's 🔴 is stale. What remains of
   #13/#14 is **reach**: well-founded mutual recursion and multi-argument /
   lexicographic descent are currently *rejected*, not unsoundly accepted.
4. **Termination certification lives in the kernel, not the elaborator.**
   The roadmap attributes #13/#14 to layer E, but the descent check is
   `Cure.Core.Certificate.terminating?/3` (K); `Cure.Elab.TotalityClosure`
   (E) only decides *which* globals need certification. P1's landing spot and
   TCB consequences follow from this (§6, D6).
5. **Snapshot gaps.** Three files the program needs are not vendored:
   `idris2/src/TTImp/WithClause.idr`, `idris2/src/TTImp/Elab/Case.idr`,
   `agda/.../TypeChecking/With.hs`. All exist in the local clones the
   manifest points to; refreshing is a copy (P4 prerequisite, cheap to do in
   P0).
6. **④ has landed on this branch, and it built P2/P3's seams.** The
   `{:absurd}` discharged-branch leaf is in the kernel (`3b24829`), the
   parser recognizes `-> impossible` (`d770aa1`), and the elaborator's
   coverage/discharge pass is committed (`f068943`): `elaborate_branches`
   now iterates *every* declared constructor of the scrutinee's family, consults
   `Cure.Core.Kernel.branch_unify/4` per constructor, discharges impossible
   omitted/marked branches to `{:absurd}`, and rejects `missing_branch`,
   `reachable_impossible`, `foreign_ctor`, and `duplicate_branch`. Two
   consequences for this program: (a) that pass is the single-level
   coverage baseline P2 generalizes rather than a green field; (b)
   `constructor_pattern/1` now *returns* `{:error, {:unsupported_pattern,
   shape}}` for non-constructor patterns — the precise rejection point P2
   (nested patterns) and P3 (`_`, literals, as-patterns, dots) replace with
   real handling. Ledger rows 2/8/16 flip as these pieces commit.

Findings 2 and 3 generalize: **two of two ledger rows checked in depth were
stale.** Hence design decision D5 (audit-first) below.

## 3. Design decisions

- **D1 — Port algorithms, not the system.** Each cluster transliterates one
  bounded algorithm from the reference sources onto Cure's existing term
  representation and module boundaries. "Transliteration" here means faithful
  re-derivation of the algorithm's structure and case analysis — literal
  line-by-line porting is impossible (see the mapping table, §5) and is not
  the goal; *semantic* fidelity checked by the oracle (D4) is.
- **D2 — The kernel is the backstop.** Ports land in the untrusted elaborator
  wherever the architecture allows. A buggy elaborator port produces Core
  terms the kernel rejects — an error, never unsoundness. This is what makes
  single-run ("one-shot") ports viable at all.
- **D3 — One transliteration brief per cluster,** committed at
  `docs/superpowers/ports/<cluster>.md` before the cluster's autopilot run.
  The brief is the port run's standing context: exact vendored source paths,
  target modules, the representation mapping (§5), manifest caveats, and the
  acceptance gates. The cluster's design spec and brief may be one document
  when the cluster is small.
- **D4 — Differential oracle with banked verdicts.** A corpus of paired
  programs — the same program in Idris surface syntax and Cure surface syntax
  — with accept/reject verdicts compared mechanically (§7). The `idris2`
  binary is built once from the pinned clone (`~/Develop/Idris2` at
  `fd405085b`); oracle runs happen locally at port time, and the resulting
  verdicts are committed as fixtures so CI replays the comparison without the
  Idris toolchain. This catches "plausible but wrong" ports that tests
  written by the same run would miss.
- **D5 — Audit-first.** Every cluster's run begins by verifying the ledger
  rows it targets against the current tree (does the claimed gap still
  exist?) and ends by updating the roadmap ledger. Findings 2/3 above are the
  motivating precedent.
- **D6 — Size-change termination extends the kernel's `Certificate` (TCB
  growth accepted).** Termination certification already lives in K (finding
  4). The alternative — an E-side analysis producing a K-checkable witness —
  was considered and rejected: the natural SCT witness (the completed
  call-matrix graph) costs as much to verify as to recompute, so it buys no
  TCB reduction. Instead: the existing single-argument structural check stays
  as the fast path; SCT runs as the fallback for mutual groups and
  multi-argument descent; the addition is ~300–400 lines of a published
  algorithm (Lee–Jones–Ben-Amram), gated by A1/A9 antibodies.
- **D7 — Sequential clusters, not one mega-run.** The clusters have real
  dependencies (#17 needs #3; #5 needs #4; ④ interacts with P2), each
  deserves its Antigen gate before the next builds on it, and a six-algorithm
  diff is unreviewable. Six bounded runs sharing this charter is the version
  of "one-shotting Idris" that converges.

## 4. The transliteration brief — required contents

Each brief must contain, concretely for its cluster:

1. **Sources:** exact vendored paths + line counts, and which reference is
   authoritative where they disagree (default: the manifest's per-concern
   table; the brief may override with a reason).
2. **Targets:** the Cure modules touched, with current line counts, and
   whether any file needs splitting first (house rule: keep units bounded).
3. **The representation mapping (§5),** plus any cluster-specific rows.
4. **Manifest caveats** that apply (QTT, universes, trust split).
5. **Acceptance gates (§8),** instantiated: which antibodies get banked,
   which oracle corpus entries exist, which ledger rows flip.
6. **The audit step (D5):** what to verify before writing code.

## 5. The shared representation mapping

The impedance table every brief includes. Left: what the reference source
says. Right: what the port writes.

| Reference construct | Cure construct |
|---|---|
| Idris `RigCount` / multiplicities on every binder and env entry | **Delete.** Read Idris' core as "everything ω, erased = 0". Cure has no QTT; erasure is `Cure.Elab.Erase`'s concern. |
| Idris intrinsically-scoped terms (`Term : List Name -> Type`, `thin`/`weaken`/`embed`); Agda's `Substitute` machinery | Plain de Bruijn integers + `Cure.Core.Term.shift/3` and `subst/3`. Scope safety that the reference gets from its metalanguage types must be re-established by tests — this is the port's primary silent-failure surface, and the reason gates (§8) are non-negotiable. |
| Idris `Core` effect monad (mutable `Ref Ctxt`/`UST` state, catchable errors); Agda's `TCM` | Explicit threaded state + `{:ok, …} / {:error, …}` returns, in the style of `Cure.Elab.MetaCtx` / `with` chains. Restructures every signature; the algorithm's control flow is what survives. |
| Idris `Glued`/lazy values, `NF` | Cure's NbE: `Cure.Core.Eval` / `Value` / `Quote` / `Conv` (strict; `Conv.conv_within?` fuel where the reference relies on laziness). |
| Idris library `Equal` + `%rewrite` hints; Agda's `Id` | Kernel-primitive `{:eq, ty, a, b}` / `{:refl, a}` / `{:rewrite, proof, motive, body}`. Motive-building algorithms port; where they *land* differs. |
| Idris/Agda infer datatype parameter positions (`ProcessData` uniformity analysis) | **Skip.** Cure declares the split: `type Vec(a: Type) indices (m: Nat)` fixes params vs indices at the surface, and `{:data, name, params, indices}` carries it in Core. Ports must respect the split, and drop the reference's parameter-inference code paths. |
| Idris `Name`/namespaces, machine-generated names | Atoms; generated names via the elaborator's existing conventions. |
| Case trees as the *definition form* the checker consumes (Idris) | A **lowering pass**: Cure's kernel `{:case, scrut, motive, branches}` already nests; decision trees are elaborator output, not a kernel form (P2). |

## 6. Port clusters

Sizes are the actual vendored files (`wc -l`, this snapshot).

### P0 — audit + program setup (ledger #7, ledger hygiene)

- **Sources:** `idris2/src/TTImp/Elab/Rewrite.idr` (154).
- **Targets:** `lib/cure/elab/elaborator.ex` (`rewrite_plan/5` region);
  `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md`;
  `reference/` snapshot.
- **Scope:** (a) refresh the snapshot with the three missing files (finding
  5) and record it in the manifest; (b) build `idris2` from the pinned clone
  and stand up the oracle harness skeleton (§7) with a first corpus of
  rewrite programs; (c) diff `rewrite_plan` against `elabRewrite` — known
  candidate deltas: Idris' distinct "rewriting did not change type" error,
  occurrence matching up to conversion vs. syntactic-on-normal-forms,
  behavior under binders — fix what's real, with a red test per fix per the
  house TDD rule; (d) correct ledger rows #7 and #13 to reflect the tree,
  and flip rows 2/8/16 (④'s pieces are committed — finding 6).
- **Gates:** oracle fixtures for the rewrite corpus banked; roadmap accurate;
  any fixes covered red-green.
- **Why first:** calibrates the brief format and the oracle at near-zero port
  risk, and institutionalizes D5.

### P1 — size-change termination (ledger #13-reach, #14)

- **Sources:** `idris2/src/Core/Termination/{SizeChange,CallGraph}.idr`
  (339 + 414); semantic cross-check
  `agda/.../Termination/{CallGraph,Order}.hs` (269 + 327) — Agda's is the
  more faithful Lee–Jones–Ben-Amram implementation (composable call
  matrices).
- **Targets:** `lib/cure/core/certificate.ex` (per D6), driver unchanged in
  `lib/cure/elab/totality_closure.ex`.
- **Scope:** per-call-site size-change matrices (argument-to-argument `<` /
  `≤` / `?`), call-graph completion, the LJB criterion (every idempotent
  component has a strictly decreasing diagonal entry). Structural check stays
  the fast path; SCT is the fallback that turns today's conservative
  mutual-cycle rejection into acceptance of well-founded mutual and
  lexicographic recursion. Diagnostics must name the offending cycle.
- **Gates:** the pre-port banking run (W1/W2 of its spec) has landed first —
  P1 is developed against its adversarial diverging set (which must keep
  replaying `:ok`, `diverging_mutual_pair` included) and is accepted by
  migrating its reach pins (well-founded mutual, lexicographic, permuted
  descent) from `reach.sexp` into the main corpus; oracle corpus of paired
  mutual/lex-descent programs; TCB diff reviewed as such. This is the one
  cluster with no kernel backstop, so the pre-banked net is the primary
  defense (§10).

### P2 — decision-tree pattern compilation (ledger #3, #17)

- **Sources:** `idris2/src/Core/Case/{CaseBuilder,CaseTree}.idr`
  (1,272 + 301), `idris2/src/Core/Coverage.idr` (471); index-aware splitting
  semantics from `agda/.../TypeChecking/Coverage.hs` (1,588) — manifest marks
  Agda primary for index unification during matching.
- **Targets:** new `Cure.Elab.CaseTree` (or similar) lowering pass; the match
  path of `elaborator.ex` / `declarations.ex`. Kernel unchanged.
- **Scope:** clause-matrix → nested kernel-`:case` compilation (defaults,
  specificity, dependency order of scrutinees), and coverage diagnostics over
  nested patterns computed from the tree. **Baseline to generalize, not
  bypass (finding 6):** ④'s `elaborate_branches` already does
  all-declared-constructors enumeration with per-constructor
  `Kernel.branch_unify/4` verdicts and `{:absurd}` discharge at a single
  level. The tree compiler must apply that verdict/discharge logic at *every
  split node* (this is exactly where the manifest marks Agda's `Coverage.hs`
  primary), and ④'s error vocabulary (`missing_branch`,
  `reachable_impossible`, `foreign_ctor`, `duplicate_branch`,
  `unsupported_pattern`) is the diagnostics contract to preserve and extend
  with nested-position paths.
- **Dependencies:** ④ committed on this branch (done — `f068943`);
  `TTImp/Elab/Case.idr` vendored (P0) for expression-level match lifting.
- **Gates:** existing single-level match corpus unchanged (refactor safety);
  nested-pattern oracle corpus; Antigen `indexed/case` antibodies extended to
  nested splits.

### P3 — dot / forced patterns (ledger #4, #5)

- **Sources:** `idris2/src/TTImp/ProcessDef.idr` (1,079; the LHS-elaboration
  fragment) + `checkDots` in `idris2/src/Core/UnifyState.idr` (713);
  cross-check `agda/.../Rules/LHS.hs` (2,153) + `LHS/Problem.hs`.
- **Targets:** `lib/cure/elab/unify.ex`, pattern elaboration in
  `declarations.ex`/`elaborator.ex`, `lib/cure/elab/erase.ex` (forced-argument
  erasure).
- **Scope:** elaborate LHS patterns with metavariables; positions unification
  *solves* are forced (checked, not matched) — covering `_`, literals, and
  as-patterns in dependent positions (#4) as the degenerate cases; erase
  forced arguments (#5). The surface entry point is ④'s
  `constructor_pattern/1` rejection (`{:unsupported_pattern, shape}`,
  finding 6) — P3 turns those rejected shapes into elaborated patterns.
- **Dependencies:** P2 (patterns flow through the new lowering pass).
- **Gates:** roadmap row 24's `forcing` vertical becomes real (a dot-pattern
  Antigen vertical); oracle corpus of forced-pattern programs.

### P4 — with-abstraction (ledger #6)

- **Sources (post-refresh):** `idris2/src/TTImp/WithClause.idr`, cross-check
  `agda/.../TypeChecking/With.hs`.
- **Targets:** parser (`lib/cure/compiler/`), elaborator; desugars to an
  auxiliary top-level definition with the scrutinee abstracted from the goal.
- **Scope:** surface syntax (its cluster spec designs the Cure form),
  goal abstraction, auxiliary-def generation. Mostly syntax-directed.
- **Dependencies:** P2 (generated matches use the match path); P0's refresh.
- **Gates:** oracle corpus; surface `.cure` regression corpus (feeds roadmap
  A7/#25).

### P5 — Miller patterns + postponed constraints (ledger #10, #11)

- **Sources:** the pattern-unification fragment and constraint queue of
  `idris2/src/Core/Unify.idr` (1,663) + `UnifyState.idr` (713) — port the
  *algorithm*, not the module (it is entangled with `Glued` laziness);
  cross-check `agda/.../TypeChecking/MetaVars.hs` (2,052).
- **Targets:** `lib/cure/elab/unify.ex` (147 lines today; its moduledoc
  already names Miller patterns as the extension point) + `MetaCtx` (grows a
  constraint queue).
- **Scope:** solve `?m x₁ … xₙ = t` for distinct bound variables (invert,
  occurs- and scope-check); postpone genuinely flex-flex constraints in a
  queue retried on solution progress; unsolved-at-zonk stays an error.
- **Dependencies:** none hard; scheduled last per roadmap §5 (ergonomics).
- **Gates:** antibodies for scope-escape and ill-scoped inversions (extends
  roadmap A2's occurs/deletion antibodies); oracle corpus of
  implicit-inference programs.

## 7. The differential oracle

- **Layout:** `test/oracle/<cluster>/<name>.{idr,cure}` + a committed
  `verdicts.json` per cluster: for each pair, the Idris verdict
  (`accept`/`reject`), the Cure verdict, and the *expected relation*.
- **Relation, not equality:** the default expectation is `same`, but pairs may
  be marked `cure_stricter` / `idris_only` with a one-line reason — the two
  languages legitimately diverge (universes: Cure's fixed 0–2 hierarchy vs.
  Idris' permissive levels; features Cure deliberately lacks, roadmap §4;
  totality-by-default vs. Idris' opt-in `%default total`, so Idris corpus
  files carry the pragma). A pair whose divergence has no recorded reason
  fails the harness.
- **Two modes:** `live` (runs `idris2 --check` from the pinned build;
  developer machines, port runs) regenerates `verdicts.json`; `replay` (CI,
  no Idris toolchain) asserts Cure's current verdicts against the committed
  fixtures. Idris verdicts change only when the pin changes.
- **Scope discipline:** each corpus exercises exactly its cluster's feature;
  cross-feature programs join the corpus of the *later* cluster.

## 8. Acceptance gates (every cluster)

1. **Audit first** (D5): ledger claims verified against the tree before code;
   ledger updated after.
2. **Red-green TDD** per the house testing rule — each behavioral delta gets
   a failing test first.
3. **Kernel green:** full existing suite + Antigen corpus replay untouched.
4. **Antibodies banked, in polarity order:** every new rule/acceptance the
   port introduces gets named Antigen challenges (the port's durable
   regression net). Ordering discipline:
   - Everything expressible with *pre-port* surface/Core forms is banked
     **before** the port by the pre-port banking spec — must-reject
     antibodies (whose only failure window opens when the port makes the
     checker more permissive) plus reach pins in `test/antigen/reach.sexp`
     whose ground-truth labels the port must achieve. The port's acceptance
     migrates its reach pins into the main corpus; it never edits them.
   - **Syntax-gated challenges** — those inexpressible until the cluster's
     own new surface forms exist — are authored *inside* the cluster's run:
     after the minimal syntax/representation lands, **before** the semantic
     logic they guard. Concretely: P2's nested-pattern split challenges
     (extending `indexed/case`), P3's dot/forced `forcing` vertical
     (roadmap row 24), and P4's `with` surface corpus.
5. **Oracle:** the cluster's paired corpus exists with committed verdicts;
   replay green.
6. **TCB discipline:** any K-layer diff (only P1 expected) is called out as
   such in the run report and kept minimal.

## 9. Sequencing

**P0 → pre-port banking run → P1 → P2 → P3 → P4 → P5** (④'s former gate on
P2 is discharged — its pieces are committed, finding 6). The pre-port banking spec absorbs
roadmap items A1–A4/A9 and must precede P1, whose gates consume its W1/W2
stores; P0 and the banking run are otherwise independent and may swap or
overlap. A8's term generator multiplies the value of every antibody the ports
bank, so landing it early remains attractive. P1 no longer jumps the queue
for soundness — the hole is closed — but stays early because its source is
small, its net is pre-banked, and it retires two ledger rows at once.

## 10. Risks

- **Silent de Bruijn errors** (the mapping's riskiest row): mitigated by the
  kernel backstop (D2), the oracle (D4), Antigen replay, and — once roadmap
  A8 lands — generated-term coverage. For P1, which lacks the kernel
  backstop, the antibody gate is the primary defense; the pre-port banking
  spec's W1 adversarial diverging set (banked before P1 runs) is that
  defense, deliberately authored independently of the port.
- **Reference drift:** the manifest pins commits; refreshes are recorded
  there. Briefs cite the snapshot, never the live clones.
- **Ledger staleness** (already observed twice): D5 makes the audit a gate,
  so a stale row costs an hour, not a mis-scoped port run.
- **Two references disagree:** the manifest's authority table decides; the
  brief records any override and why.
- **Oracle false confidence:** verdict pairs check accept/reject, not
  runtime semantics. Clusters whose features have runtime behavior (P2, P3
  erasure) must add evaluation assertions to their `.cure` corpus, not rely
  on the oracle alone.

## 11. Out of scope

Everything in roadmap §4 (QTT, interfaces at Idris depth, elaborator
reflection, named/auto implicits, totality pragmas as surface); Antigen items
A2–A6, A8, A10 (they proceed on their own track); any kernel refactor beyond
P1's bounded `Certificate` extension; performance work on the reference
algorithms beyond what correctness needs.

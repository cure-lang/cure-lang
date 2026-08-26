# Roadmap Master — condensed index of all roadmap specs

**Date:** 2026-07-21

**Scope.** This document condenses every spec in `docs/superpowers/specs/roadmap/` into one
read: the Idris-parity programme (ledger + transliteration method), the classic-pipeline
deletion (#18), the value-surface parity programme (#23) that unblocked it, and the editions /
migration layer. It preserves locked decisions, per-item completion status, and remaining open
work at full fidelity while dropping the per-spec mechanics of already-completed stages. It is
organized by theme, not file; supersessions are noted inline. The source specs remain the
archive of execution detail (exact anchors, gate transcripts, antibody lists).

---

## 1. Idris-parity programme

**Framing.** "Parity" = for a feature Cure already implements, match Idris in *soundness*,
*reach*, *ergonomics*, and *assurance*. Layers: **K** trusted kernel (`lib/cure/core/*`),
**E** untrusted elaborator (`lib/cure/elab/*`), **P** parser/lexer, **A** Antigen,
**C** eval/codegen/erase. The ledger (`2026-07-02-idris-parity-roadmap.md`) is the source of
truth for "what is left"; individual rows graduated into their own specs + autopilot runs.

### 1.1 Parity ledger — final state: ALL 28 ROWS ✅

(The prose "honest headline" section in the source predates the final closures; the per-row
status column is authoritative. Zero live soundness holes throughout the endgame.)

| # | Capability | Status + residual |
|---|---|---|
| 1 | Dependent case unifier (K) | ✅ incl. Agda Cycle rule (`f9406b6`): strongly-rigid cyclic index eq → `:impossible`; guard is ctor/data-spine-only (conservative-sound) |
| 2 | Impossible clauses + `-> impossible` | ✅ |
| 3 | Nested/deep patterns → matrix compiler (E) | ✅ Augustsson/Maranget lowering, depth + multi-column + outer catch-all; named catch-all over non-var scrutinee pinned `mt21` |
| 4 | Pattern forms (`_`, literals, as-patterns, tuples, records, guards, literals-via-`bool_elim`) | ✅ everything landed (records incl. dependent/parameterized/update, auto-generalization, forward refs/mutual, polymorphic ctors both modes, GADT/Fin/dependent-pair construction, cross-arg + deferred-domain implicit solving `bc08ce0`, return-type flow `3c0d9ee`, type + function-type aliases, nested ctor guards, non-var guarded scrutinee via bind-once β-redex). Sole residual: join-point *sharing* of a duplicated default — efficiency-only (Cure is total; duplication changes code size, never values) |
| 5 | Forced/dot patterns + forced-arg erasure | ✅ CLOSED 2026-07-08. Kernel forced-equation Solution step (Agda `unifyIndices`) + union-find cycle guard; explicit dot = named-implicit `{k = .e}` (`5409184` + `dotsyntax-tail`); bare positional `.e` proven structurally inexpressible (forced indices are always erased implicits) — no further syntax warranted. Forced-arg erasure vacuously satisfied |
| 6 | `with`-abstraction | ✅ A (goal refinement) + B (`proof` Eq-binding) + sibling transport + indexed LHS-rematch convoy (no TCB) + nested `with` + multiple-`with` sugar + named/dependent ctor args. Residual reach (shared with Idris): computed non-invertible result indices (`NVv(add(k,k))`); named binders only in ctor arrow-chain domains |
| 7 | `rewrite` motive inference | ✅ GRADUATED — identity type fully inductive (`Equivalent`/`reflexive`); primitive `{:eq}/{:refl}/{:rewrite}` Core forms RETIRED; rewrite desugars to J/subst transport; proofs runtime-free via collapsible-family erasure; K/UIP definitional via index unifier (operator sign-off 2026-07-04). rw07/rw08/rw09 all `same` via lazy-unfolding fix |
| 8 | `Void`/absurd (`{:absurd}` kernel leaf) | ✅ |
| 9 | First-order metavariable engine | ✅ |
| 10 | Miller pattern unification | ✅ (`miller_solve` + dependent `(x:A)->B(x)` syntax + scoped applied head + lambda-at-meta-Π). Reach: ambient-variable Miller via non-lambda argument still cleanly rejected |
| 11 | whnf-before-compare + postponement | ✅ whnf-pre landed (reduce-before-compare is the references' primary mechanism); **simultaneous unification** landed 2026-07-19 (component-wise `unify_data_components` + deferred-eq fixpoint). ⚠️ OPEN reach-pinned residual **variant A**: computed-index ctor at a CONCRETE goal fails `:ctor_arity` (params/indices split bug in `declarations.ex` signature lowering) — blocks `Otp.Meta.MailboxPattern` explicit→implicit index conversion. Abel–Pientka postponement design (A postponement / B pruning + strongly-rigid occurs / C Σ-flattening) retained as a DEFERRED menu, all E-layer |
| 12 | Single-arg structural descent | ✅ |
| 13 | Mutual-recursion termination | ✅ soundness closed `d13d718` (antibody permanent); reach landed `88452193` — cross-function/mutual size-change (Idris `SizeChange.idr` `addFunctions` port, SCC groups) |
| 14 | Multi-arg / lexicographic size-change | ✅ landed `b871b37` (TCB `certificate.ex`, full gate + Idris cross-check both directions) |
| 15 | Kernel exhaustiveness | ✅ |
| 16 | Surface exhaustiveness w/ discharge | ✅ |
| 17 | Coverage over nested patterns | ✅ via #3 (per-level kernel check; `mt10` reject/reject) |
| 18 | Strict positivity checker + vertical | ✅ |
| 19 | Nested/through-ctor/arrow-left positivity | ✅ W4 audit — sigma-hidden + through-constructor were live holes, fixed `6148aff`, antibodies banked |
| 20 | Universes (cumulative, no Type:Type) | ✅ |
| 21 | Known-label regression net | ✅ |
| 22 | Term-generator metatheory engine (A8) | ✅ Tier B (`gen_term(Γ,T)` + 3 differential assays + health gate, 0 infections). Reach open: `conversion_termination`/`erasure_preservation` assays, ill-typed mutation corpus, `ChoiceSeq` backend, richer menu (Pi/Sigma goals, type params) |
| 23 | Occurs-check/deletion antibodies | ✅ W3 (TCB gap in `Term` fixed en route, `360402b`) |
| 24 | `forcing` dot-pattern Antigen vertical | ✅ built + green (`Antigen.Assays.DotForcing`; K/E scope only, not P-layer parse) |
| 25 | Surface `.cure` regression corpus for ④ | ✅ 137 `.cure`↔`.idr` probes / 23 clusters + `impossible` cluster. Optional polish: CORPUS.md manifest |
| 26 | Expression-level / inline `match` | ✅ checked + inference-position (non-dependent) + let-blocks + `let…in` + bind-once shadowed `let`. Residuals all faithful or efficiency-only: dependent inference-position match needs annotation (Idris too, `im04`); multi-line indented inner match in parens unauthorable by lexer design (brace form at parity); non-shadowing let-duplication efficiency-only |
| 27 | First-class functions | ✅ arrows→native Π, checked lambdas, lambda-as-argument, chained application, closure codegen. Beyond scope: whole-program Miller inference for un-annotated HOF composition |
| 28 | Infer/check coherence (kernel) | ✅ `check = infer + conv` routing for params-on-spine ctors (`f7fd3e0`+`603d541`); sibling ctor-spelling value dichotomy RESOLVED **fields-only** (Agda-aligned, `7b7f071`, audited FIELDS-ONLY SAFE, antibody-gated) — do not reopen |

### 1.2 K-layer TCB notes (all closed via reviewed TCB runs)

1. **Stuck-eliminator normalization** (`d37721f`): stuck `case`/`fst`/`snd` over certified-global
   spines now δ-reduce their target and fire ι. Does NOT retire rw07's bridge (`plus(n,Z) ≡ n`
   genuinely non-definitional).
2. **`check_motive_wf` reify-collapse** (`defc6cb` + B3): `infer_type_value_sort` value-recurses;
   signature-aware `Quote.reify(sig)` recovers the param/index split for Eq endpoints.
   Conversion stays flat — the collapse only ever false-rejected, never false-accepted.
3. **Lazy unfolding of stuck recursive globals**: keep applications FOLDED when unfolding is
   unproductive (dual of note 1) — one canonical stuck shape, fixing multi-occurrence rewrite
   (rw08). Freezing only makes normal forms more distinct; sound by construction.

### 1.3 Antigen expansion ledger

Verticals in place (strength): stub (meta), totality/terminating+diverging (solid),
positivity (strong), reflexivity/normalization (solid), indexed/case (strong), rewrite/eq
(strong), universes (strong), forcing/dot (row 24).

| # | Expansion | Status |
|---|---|---|
| A1 | Mutual-recursion hole → green | ✅ `d13d718` |
| A2 | Occurs/deletion antibodies | ✅ |
| A3 | Positivity escape-hatch antibodies | ✅ (2 live holes found+fixed) |
| A4 | Universes vertical | ✅ |
| A5 | Conversion/def-eq vertical (distinct NFs never equal) | ⬜ OPEN (medium) |
| A6 | Ctor-formation vertical (`check_ctor` rules) | ⬜ OPEN (medium) |
| A7 | Surface `.cure` Antigen vertical through `Elab.Program` | ⬜ OPEN (medium; row 25's plain corpus exists) |
| A8 | Term-generator engine | ✅ Tier B |
| A9 | Broader mutual-recursion challenges | ✅ (subsumed by W1 adversarial set) |
| A10 | Wire existing verticals onto generated stream | 🟡 PARTIAL — `:typed_term` feeds the three Tier-B assays; feeding the known-label verticals (totality/positivity/universes) from a generated stream remains OPEN |

### 1.4 Locked decisions + out-of-scope (roadmap §4)

- **Z3 is NEVER a trusted elaborator surface** (LOCKED): only ever an untrusted lint (can
  reject, never unsoundly accept). SMT-in-proofs, if ever, goes via SMTCoq-style proof
  reconstruction (kernel re-checks the emitted proof).
- Roadmap-excluded capability domains: QTT, interfaces at Idris depth, `%default total`
  surface pragmas, elaborator reflection, named/auto implicits. (Some were later delivered by
  *separate* initiatives outside this roadmap — QTT grades, #21 typeclasses — the exclusion
  was scope discipline, not a permanent veto.)
- **Builtin-inductive foundation** (§4.2): built as its own gated TCB effort — Bool as a real
  inductive (retiring `bool_elim`), and Nat→Int runtime erasure Phase 2 LANDED
  (canonical Std.Nat → BEAM machine ints, nominal-only, `elab/nat_rep` assay).
- Someday ledger: real `Ordering` view + `compare` for kernel-real trichotomy coverage
  (needs inductive `Ordering` first); recorded so it is not re-litigated.

### 1.5 Transliteration programme (the method that executed the ledger)

Charter (`2026-07-02-idris-transliteration-program-design.md`): close reach/ergonomics rows by
**transliterating reference algorithms** from pinned Idris2/Agda/Lean snapshots
(`reference/MANIFEST.md`), not first-principles derivation. Decisions (all locked):

- **D1** port algorithms, not the system; **D2** kernel is the backstop (ports land in E;
  a buggy port yields kernel-rejected terms, never unsoundness); **D3** one committed
  transliteration brief per cluster; **D4** differential oracle — paired `.idr`/`.cure`
  programs with committed verdicts (`same`/`cure_stricter`/`idris_only`, reasons required),
  live vs replay modes; **D5** audit-first (every run verifies ledger rows against the tree
  before code — two of two rows checked in depth were stale); **D6** size-change termination
  extends kernel `Certificate` (TCB growth accepted; E-side witness rejected as no cheaper to
  verify); **D7** sequential clusters, not one mega-run.
- Shared representation mapping (per brief): delete RigCount (no QTT), intrinsic scoping →
  plain de Bruijn + tests (the primary silent-failure surface), Core monad → threaded
  state/`with`, Glued/NF → strict NbE + fuel, library Eq → kernel Eq (since inductive, row 7),
  no parameter-position inference (Cure declares the split), case trees = lowering pass.
- Clusters, all delivered via the ledger rows they targeted: **P0** audit + oracle harness
  (row 7 audit, rows 2/8/16 flipped) ✅; **P1** size-change termination (rows 13/14) ✅;
  **P2** decision-tree pattern compilation (rows 3/17) ✅; **P3** dot/forced patterns
  (rows 4/5) ✅; **P4** with-abstraction (row 6) ✅; **P5** Miller + postponed constraints
  (rows 10/11) ✅ except row 11's variant-A residual (§1.1).
- Standing acceptance gates (kept for future ports): audit-first, red-green TDD, kernel +
  Antigen replay green, antibodies banked in polarity order (pre-port bankable ones BEFORE
  the port; syntax-gated ones inside the run before the semantics), oracle corpus committed,
  TCB diffs called out.

---

## 2. Classic pipeline deletion (#18)

**Operator decision (2026-07-09):** the classic (non-dependent) pipeline is **deleted**, not
kept alongside. The dependent pathway (`Elab.Program`/`Elaborator` → `Core` → `Elab.Emit`) is
the sole compiler. `2026-07-09-classic-ripout-design.md` **supersedes** the earlier
A-cut/B-port fork analysis in `2026-07-09-classic-pipeline-deletion-design.md`: everything
classic-only dies with **NO porting** (features return kernel-founded later if wanted);
#21 typeclasses is NOT a prerequisite.

**Status: EXECUTED** (`07b65ed`): `Types.Checker` + `Codegen` + fsm/actor/sup/app compilers +
session-typed protocol + bless + optimizer/PGO + observe/top + temporal all deleted; dependent
pipeline is sole. The first rip-out attempt STOPped on the value surface (stashed 257-file
WIP); it re-ran after the #23 waves closed the gaps (§3). #21 typeclasses followed separately
(Equatable/Ord/Show restored as real interfaces).

**Refinement posture (locked, from the umbrella spec):** SMT-discharged `{x:T|φ}` refinements
are **dropped**, not relocated or certified (certifying-replay rejected: nonlinear `th-lemma`s
have no reconstructible certificate). Refinement-shaped obligations discharge via
(1) computation on concrete/decidable predicates, (2) indexed types (`Fin`/`Vector n` —
refinement-by-construction), (3) manual proofs against a proposition + arithmetic-lemma
prelude (the real gating work; not throwaway — a future SMTCoq port becomes a proof-finder for
the same propositions). Optional middle rung, ledgered not scheduled: a verified
linear/Presburger decision procedure by reflection.

**Load-bearing constraints from the rip-out (still relevant to future deletions):**
- `lib/cure/core/` diff must be EMPTY; elab changes enumerated only; parser/lexer/beam_writer
  front end STAYS (load-bearing for the dependent pipeline).
- `proto`/`impl` could never be a macro (macros are type-blind) — typeclasses are an
  elaborator feature; fsm/actor/sup/app were to be macros (per the umbrella spec) but were
  deleted un-ported per the rip-out order.
- Stdlib rule: any `lib/std/*.cure` that cannot dependent-elaborate is DELETED (git history is
  the archive); classification of tests/modules is by what they call, never by filename.
- Follow-ups explicitly left open at cut time: parser grammar removal for dead keywords
  (fsm/actor/… still parse then fail elaboration), curated replacement error for raw
  spawn/receive, REPL type-inference on the dependent pipeline.

---

## 3. Value-surface parity programme (#23)

Teaches the dependent pipeline the value surface classic `Codegen` compiled, so #18 could
re-run without amputating the language. Backing inventory:
`2026-07-09-value-surface-gap-matrix.md` (G1–G12); sequencing:
`2026-07-09-value-surface-roadmap-design.md`. **Outcome: the programme succeeded — the ratchet
climbed from 8/39 KEEP modules far enough that the rip-out re-ran and landed (§2).**

**Program invariants:** firewall test (`8d7a5eb`) — no elab/core file may reference any classic
module (classic files are the *semantics reference* only); monotone stdlib-disposition ratchet;
classic tests as behavioral oracles; TCB discipline (kernel-touching waves get antibodies +
review); ghost commits, red-green, tests immutable.

**Locked cross-cutting decisions:**
- **D1 — List is a builtin inductive family with native-cons emit** (NOT plain Std.List, NOT
  native-only): seeded `List(a)` `Nil`/`Cons`, emit `Nil→[]`, `Cons(h,t)→[h|t]` — the
  Bool→atom / Nat→int / Sigma→2-tuple precedent. Kernel-checkable AND `:lists`/FFI-interoperable.
- **D2 — `@extern` reuses the builtin-op registry mechanism**: bodyless global with an
  `extern: {m,f,a}` marker; emit lowers saturated applications to remote calls. Extern stays
  entirely out of the kernel.

**Gap matrix (final disposition):**

| Gap | Verdict |
|---|---|
| G1 `@extern` | ✅ Wave 3 |
| G2 `pickup` | ✅ Wave 1 |
| G3 List + patterns | ✅ Wave 2 (+ Wave 4 checked-body dispatch) |
| G4 String + `<>` | own wave (new `{:string_type}`/`{:string_lit}` Core nodes — genuinely new nodes needing eval/normalise/conv clauses, unlike List) |
| G5 Atom literals | mostly subsumed by ADT ctors + extern; flagged as the single highest-leverage ~1-clause follow-on (flips system + test) |
| G6 Lambda-in-inference | last-mile for `list` (checked-mode already worked) |
| G7 tuples ≥3 | nested-Sigma sugar or builtin (closes `match`, `pair`) |
| G8 Maps | new builtin or extern-backed opaque (wave-spec decision) |
| G9 interpolation | rides String |
| G10 comprehensions/ranges | desugar to List + recursion (separate AST tag `{:comprehension}`, untouched by list desugar) |
| G11 binary/bitstring | DEFERRED (own track, low unlock) |
| G12 send/throw/try/async | DEFERRED to Effect-in-Core + typed-BEAM-process-algebra tracks |

Out of the 39 std modules, 10 are excluded from the ratchet denominator (5 concurrency-runtime
+ 5 proto/impl modules — deleted in the rip-out, never wave targets); completion gate =
every remaining FAILS is G11/G12-only, checked mechanically.

**Waves (as executed — Wave 3 reordered extern ahead of lambda on scout evidence; Wave 4 is
an inserted dispatch wave, not the roadmap's original "String" Wave 4):**

1. **Wave 1 — `pickup`** ✅ (`f3c0b46`): pure desugar to right-nested `:conditional` (reusing
   Bool-guard + branch-join checks verbatim); three terminator shapes handled; PINNED: no
   type-level `:pickup` clause. Ledgered inert scoping gap: guard-introduced bindings visible
   in own RHS (PICKUP §5.4) is inexpressible through the desugar — currently unreachable;
   re-derive if standalone-assignment-as-expression ever lands.
2. **Wave 2 — List** ✅: seeded `:list` schema + `@builtin(:list)` declaration in
   `std/list.cure` (seed, NOT auto-prelude — decided) + one early `:list`→ctor desugar pass
   (locked: option i) + native cons emit/branch clauses + `builtin_list_drift_test` (the real
   seed/source reconciliation check — the mechanism is a skip via `declared_type_names`, not a
   reconcile). Mid-execution scope REVISION: nested list patterns are IN (the matrix compiler
   from parity #3 already lowers them — the original "lift doesn't exist" premise was false).
   Ledgered gap "Finding A": bare top-level `[]` body infer-only (`:unsolved_metavariables`).
3. **Wave 3 — `@extern`** ✅: elaborator accepts bodyless extern (marker replaces the
   `__pending__` hole; skips body/Kernel/Relevance checks); emit synthesizes remote-call
   wrapper from arity (never peels a lam); `TotalityClosure.certify_type_level` filters
   extern-marked globals (certification is a category error for an FFI postulate; reusing
   `builtin_op` as marker carrier was analyzed and REJECTED — three consumers assume op atoms).
   Trust framing (keep): **Claim A** kernel-code-free (extern is an opaque uncertified global)
   vs **Claim B** the declared Π is an asserted axiom — the standard FFI-postulate boundary;
   a wrong signature that runs without crashing is silent unsoundness; never call this
   "TCB-free" unqualified.
4. **Wave 4 — checked-body dispatch** ✅: added `:list` + `:pickup` to `elaborate_body`'s
   whitelist and `:list` to `elaborate_branch_body` (the "third-dispatch-layer" gotcha),
   closing Finding A. Scope rule: add ONLY what a failing function demands (no speculative
   `:pickup` arm clause). Known next blocker documented: `Std.List` `uncons`/`split_first`'s
   undeclared `Tuple` return type → `:tuple` infer gap.
5. **Remaining tail (revised order from Wave 3 §0):** atom-literals → string-literals + `<>`
   → lambda-inference → Map/tuples≥3/interpolation/comprehensions. These were closed under
   the broader #23/#18 follow-on work (dep-pipeline survey: 41 committed-green; rip-out
   re-ran) — see the value-surface program memory for the post-spec trail; G11/G12 remain
   deferred to their own tracks.

---

## 4. Editions & migration (`2026-07-10-editions-design.md`)

**Status:** design approved (brainstorm 2026-07-10), buildable; extends the *landed* migration
facility (rule engine, Trivia + lossless Printer, registry, git-guard, `cure migrate`).
Reverses exactly one facility decision — §5.5 single-pass — and only for the edition-crossing
migrate path.

**Locked decisions:**
1. Scope = syntax editions + rewrite-only stdlib (no edition-conditional stdlib resolver —
   renamed names error with a "run `cure migrate`" hint; transparent compat rejected).
2. Edition identity = calendar-year string (`"2026"`), closed allow-list, total order.
3. Precedence: file `@edition("YYYY")` pragma (file-leading only, hard parse error elsewhere)
   > `Cure.toml` `[project].edition` > compiler default. Per-file resolution enables
   incremental migration.
4. Default when undeclared = latest (pre-1.0; freezes post-1.0).
5. Rule `tier: :machine | :review | :manual` REPLACES `tolerate_safe?` — the single
   warn/rewrite/normalize authority. Retagging if/elif→pickup, `@group`-hoist, and
   module-rename to `:machine` is a deliberate capability upgrade (build now normalizes them);
   `uppercase-type-var→lowercase` stays `:review` (unsafe to normalize in-memory).
6. Error-later = the edition boundary: `since` warns, `enforced_in` hard-errors; `--strict`
   is an opt-in preview promoting `:machine`/`:review` only, never `:manual`.
7. Migrate verify = reparse + comment preservation only (no elaboration coupling), bounded
   fixpoint (`run_to_fixpoint`, `@max_passes` backstop) + monotone-rewrite law (idempotence
   property test; rules must never ping-pong). `cure build` stays single-pass.
8. Editions start at `"2026"`; `proto`/`impl` → `interface`/`implementation` is the first
   forward deprecation (`:machine`, `retires_keywords: ["proto","impl"]`, `enforced_in: nil`
   — warns + rewrites, keyword stays live until a future edition schedules it).

**Mechanics:** keyword set is a function of edition, derived from the migration registry
(`retires_keywords` + `enforced_in`), never duplicated in the lexer. `cure migrate` crossing
X→Y: phase 1 runs mandatory (`enforced_in <= Y`) + all `:machine`/`:review` (`since <= Y`)
rules to fixpoint (`:review` included — it differs from `:machine` only in build-normalization
and run-report annotation); phase 2 bumps the declared edition, refused while any `:manual`
item with `enforced_in <= Y` remains. Build order: Edition module → rule-model refactor →
edition-parameterized lexer/parser → fixpoint engine → proto→interface rule → edition-crossing
migrate. Out of scope v1: transparent stdlib compat, per-rule maturity switches, minting
"2027", elaboration-level verify, cross-edition dep interop policy.

---

## Source specs

- `2026-07-02-idris-parity-roadmap.md` — the 28-row parity ledger (per-row status, residuals,
  TCB notes), Antigen coverage + expansion ledger A1–A10, locked Z3/out-of-scope decisions,
  sequencing. Source of §1.1–§1.4.
- `2026-07-02-idris-transliteration-program-design.md` — the porting charter: D1–D7 method
  decisions, representation mapping, clusters P0–P5, differential-oracle design, acceptance
  gates, risks. Source of §1.5.
- `2026-07-09-classic-pipeline-deletion-design.md` — umbrella cutover spec: one-pipeline end
  state, five enablers, the locked drop-SMT refinement posture + lemma-prelude plan, cutover
  sequencing. Partially superseded by the rip-out spec (porting cancelled).
- `2026-07-09-classic-ripout-design.md` — the executed no-porting deletion order: 8 decision
  records, DELETE/CUT-DOWN/KEEP cut line, stdlib disposition rule, test accounting,
  grep/diff/STOP gates. Supersedes the A-cut/B-port fork.
- `2026-07-09-value-surface-gap-matrix.md` — scout inventory: Core-target gaps G1–G12,
  std-module → gap ratchet map, classic behavioral-oracle pins, flagged ambiguities.
- `2026-07-09-value-surface-roadmap-design.md` — #23 programme: invariants (firewall,
  ratchet), locked D1 (List builtin/native-cons) + D2 (extern registry marker), wave ordering,
  completion → #18 re-run condition.
- `2026-07-09-wave1-pickup-design.md` — pickup → nested-`:conditional` desugar; terminator
  shapes; type-level pin; the ledgered guard-scoping gap.
- `2026-07-09-wave2-list-design.md` — List seed/declare/desugar/emit; drift test; mid-run
  scope revision (nested patterns IN via matrix compiler); Finding A ledgered.
- `2026-07-09-wave3-extern-design.md` — extern reorder rationale, marker contract, remote-call
  emit, TotalityClosure filter, the Claim A/B trust framing.
- `2026-07-09-wave4-checked-body-dispatch-design.md` — the third-dispatch-layer whitelist fix
  closing Finding A; the `Std.List` `Tuple` next-blocker finding; cascade-map deliverable.
- `2026-07-10-editions-design.md` — Rust-style editions on top of the migration facility:
  locked decisions 1–8, tier model, fixpoint + monotone law, two-phase edition-crossing
  migrate, build order.

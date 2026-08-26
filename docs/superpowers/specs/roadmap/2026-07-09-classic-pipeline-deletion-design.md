# Classic Pipeline Deletion — Dependent Pathway + Macros as the Sole Compiler

**Date:** 2026-07-09
**Status:** design (operator-directed). Umbrella / cutover spec — it owns the
*deletion mechanics, sequencing, and refinement posture*. The four enabling
subsystems have their own specs (§4).

**Decision (operator, 2026-07-09):** the classic compilation pipeline is
**deleted**, not kept alongside the dependent one. The dependent pathway
(`Cure.Elab.Program`/`Elaborator` → `Cure.Core` → `Cure.Elab.Emit`) plus the
macro facility becomes the one and only path from source to BEAM. Every
construct the classic pipeline compiles by hand — fsm, actor, sup, app — comes
back as a user-level macro, and `proto`/`impl` come back as a real elaborator
typeclass feature (§4). "Replace literally every custom-compiled construct."

---

## 1. Why

Today Cure has two disjoint pipelines selected per-module by
`Cure.Elab.Program.dependent?/1` (`compiler.ex:283`). Keeping both means every
language feature is built twice, the two typing environments never agree, and
the interesting constructs (concurrency, protocols) are locked out of the
dependent world. Collapsing to one pipeline is what makes the macro facility's
"own every construct" ambition real, and it removes a whole class of
divergence bugs. The prerequisites that made this infeasible before are now
either designed or landed (§4).

**One correction to "every construct is a macro":** `proto`/`impl` are the
exception. Macros are type-blind (upstream of the elaborator), so a macro can
only emit *runtime* dispatch — not real, type-directed typeclasses. `proto`/
`impl` therefore become an **elaborator feature** (dictionaries as Core records,
resolution in the E-layer, lowered to direct calls during elaboration), specified separately as
the fifth enabler (§4). fsm/actor/sup/app remain macros; they are effectful code
generators, which is exactly what the macro facility is for.

## 2. End state

- **One entry path.** `compiler.ex` always elaborates through
  `Elab.Program`/`Elaborator`; `dependent?/1` and the classic branch are
  deleted. Ordinary non-dependent code is just the degenerate case the
  elaborator already handles (a function is a Π with no interesting indices;
  ADTs/records already elaborate — `declarations.ex` handles `function_def`,
  enum/struct containers, `type_annotation`, `indexed_type`).
- **One typing environment.** `Core.Context` only; `Types.Env` is gone.
- **One emission path.** `Elab.Emit` + `BeamWriter`; `lift module` for
  OTP-behaviour containers. The `dispatch_container` table and the bespoke
  compilers are gone.
- **Containers (fsm/actor/sup/app) are macros**, shipped with the language, not
  compiler modules. **`proto`/`impl` are an elaborator typeclass feature** (§4),
  not a macro.

## 3. Delete / absorb / keep — requires a per-module adjudication pass

The classic surface is large and **not uniformly classic-only**. The cutover
must classify each module, not `rm -rf lib/cure/types`. Initial classification
(to be confirmed module-by-module during implementation):

**Delete (classic-only):**
- `lib/cure/types/checker.ex` — the classic checker.
- `lib/cure/compiler/codegen.ex` — incl. `dispatch_container`, protocol
  dispatch codegen (`:471-601`), derived-record expansion.
- `lib/cure/{fsm,actor,sup,app}/compiler.ex` — the four bespoke compilers
  (their `runtime.ex`/`state.ex`/`builtins.ex` **stay** — the runtime shims
  are what the emitted OTP modules call into).
- `Cure.Elab.Program.dependent?/1` and the `compiler.ex` classic branch.
- Classic-only type machinery once nothing references it: `refinement.ex`,
  `path_refinement.ex`, `pattern_refinement.ex`, `guard_refinement.ex`,
  `effects.ex` (surface `!` inference — superseded by `Effect`), `synth.ex`,
  `reduce.ex`. (`protocol.ex`/`protocol_registry.ex` — the classic runtime-dispatch
  protocol machinery — are deleted and *replaced* by the elaborator typeclass
  feature, §4; not simply removed.)

**Absorb / verify-still-needed (shared or Core-consumer):**
- `core_bridge.ex` — Core-grammar consumer (already carved out by the Sigma
  D2 work); keep, it's part of the dependent pathway.
- `derive.ex` — `@derive(Show/Eq/Ord/Json)`. Either reimplement as a macro or
  keep as an elaborator pass; adjudicate.
- `type.ex`, `unify.ex`, `equality.ex`, `pi.ex`, `sigma.ex`, `env.ex`,
  `stdlib.ex`, `holes.ex`, `totality.ex`, `dependent.ex`, `pattern_checker.ex`
  — some are already dependent-pathway infrastructure, some classic. Each gets
  a keep/delete/merge call.

**Keep (untouched):** lexer, parser, `beam_writer.ex`, `dep_graph.ex`, the
`{fsm,actor,sup,app}` runtime/state/verifier modules, `pattern_compiler.ex`.

The adjudication pass is itself a deliverable (a table: module → verdict →
who-references-it), produced before any deletion, because a wrong "delete"
here breaks the build silently.

## 4. The five enablers and their status

| enabler | role | status | spec |
|---|---|---|---|
| `Effect` inert type former | sound effectful handler bodies | **spec'd** (this session) | `2026-07-09-effect-type-former-design.md` |
| macro facility + `lift module` + §14 OTP ADTs | sole emission for fsm/actor/sup/app containers | **spec'd** | `macros/2026-07-08-macro-facility-design.md` §14 |
| typeclasses as an elaborator feature | `proto`/`impl` done properly (dicts=records, E-layer resolution, monomorph erasure) | **spec'd** (this session) | `2026-07-09-typeclasses-elaborator-feature-design.md` |
| single sound global registry (K12) | one collision-safe def/ctor/family table | **landed, unmerged** — commit `1d31446` on `autopilot/kernel-parity-batch` | `global-def-collision-gap` memory |
| refinement posture | what replaces SMT refinements | **decided** (§5) | this doc |

K12 must be merged forward into `feature/idris-parity` before the cutover
lands (the audit's "flagged, not landed" K12 slice-4 wording is **stale**).

## 5. Refinements — dropped, not relocated or certified

SMT-discharged `{x: T | φ}` refinements live only in the classic checker.
Deleting classic would kill them; the operator decision is to **drop them for
now**, not relocate the Z3 lint and not build certificate reconstruction yet.

**Why not certifying-replay (Z3 proof → kernel term):** it is incomplete on
exactly the useful cases. An abstract nonlinear obligation — e.g.
`scale(x: {v|v≥0}, k: {v|v≥0}) -> {r|r≥0} = x * k`, i.e.
`∀ x k. x≥0 → k≥0 → x*k≥0` — makes Z3 emit a nonlinear `th-lemma` with no
reconstructible certificate. It would be rejected despite being true and
beginner-obvious. Certificate work waits for a real SMTCoq port (see the
superseding note in the `smt-trust-boundary-decision` memory).

**What refinement-shaped obligations discharge through instead — three
existing, kept paths:**

1. **Computation** on concrete/decidable predicates — whnf + the delta-globals
   table, zero solver, no goal surfaced. This is the `board` macro's path
   ("every pin is a literal, the obligation discharges by pure computation").
   Every closed/literal refinement already works this way, without Z3.
2. **Indexed types** — `Fin`/`Bounded`, `Vector n`, the FRP `Dec`/`Init`
   indices: refinement-by-construction, the Agda/Idris idiom. Already in the
   language.
3. **Manual proofs** for abstract/quantified obligations, written against a
   **proposition + arithmetic-lemma prelude** that must be stood up (§5.1).

**Why this is safe for the roadmap:** the beginner-surfaces/macro initiative
was architected to discharge computationally and *never hits the solver*, so
dropping SMT breaks none of it. Only advanced abstract-arithmetic refinements
lose automation. This posture is also more faithful to Cure's Agda/Idris/Lean
north star (F\*/Dafny are the SMT-centric outliers).

### 5.1 The proposition + lemma prelude (the real gating work)

For manual proofs to be *possible* (not just painful), the propositions must
exist as real types: inductive order relations and an arithmetic-lemma prelude
to prove against. Integers are proof-hostile vs Nat (no clean structural
induction), and Cure refinements are usually stated over `Int` — so the
prelude design must decide how much reasoning routes through Nat vs. provides
Int lemmas directly. **This prelude is not throwaway:** a future SMTCoq port
becomes a proof-*finder* for these same propositions, so the foundation is
built now and automation is added later with nothing rewritten.

### 5.2 Optional middle rung (post-cutover, pre-SMTCoq)

If pure-manual proof for the linear fragment proves too harsh, a **verified
linear/Presburger decision procedure** (`Dec`/reflection, Idris-style) recovers
most ergonomics soundly with no solver — it *is* a proof, by reflection. It
slots on top of the §5.1 prelude without changing anything. Ledgered, not
scheduled.

## 6. Cutover sequencing

Deletion is last, not first — you cannot delete a construct's compiler until
its replacement can emit the equivalent. Order:

1. **Merge K12 forward** into `feature/idris-parity`.
2. **Land `Effect`** (kernel nodes + elaborator door-closing + emit).
3. **Land the macro facility core** + `lift module` + §14 OTP ADTs.
4. **Reimplement the containers as macros, one at a time, behind the
   still-present classic path**, validated on the generic-unix loop against the
   bespoke output: `sup` first (near-pure config, no effects, no interesting
   indices — proves the pipeline cheaply), then `app`, then `actor`, then `fsm`
   (callback + simple mode).
4b. **Land the elaborator typeclass feature** and reimplement `proto`/`impl`
   through it (dicts as records → E-layer resolution → monomorph erasure),
   behind the still-present classic runtime dispatch, validated against the
   existing protocol examples. Independent of steps 2–4 (no `Effect`/`lift`
   dependency); can proceed in parallel.
5. **Stand up the proposition/lemma prelude** (§5.1) and migrate any stdlib /
   examples that relied on SMT refinements to computational/indexed/manual
   form; inventory and report what can't migrate.
6. **Flip the entry point** — route all modules through the elaborator; delete
   `dependent?/1`.
7. **Run the per-module adjudication pass** (§3) and delete, module by module,
   rebuilding + running the full gate (kernel suite, oracle ledger, phase35
   coverage, on-unix demos) after each removal.

Each construct in step 4 is independently shippable and independently
reversible. The point of no return is step 6.

## 7. Risks / open decisions (ledger)

1. **Per-module adjudication (§3)** — the highest-risk mechanical step; a
   wrong "delete" breaks the build. The verdict table is a required
   pre-deliverable.
2. **Error-message parity** — the classic checker emits many tuned diagnostics
   (E004/E025/E031/E043 …). Routing everything through the elaborator must not
   regress error quality; some messages need reimplementing on the Core side.
   Inventory required.
3. **Stdlib written against classic** — `lib/std/*.cure` and the 55 examples
   must all elaborate through the dependent pathway. Some may use refinements
   or protocol/derive forms that change. Full recompile-and-run inventory.
4. **`derive.ex`** — macro vs. kept elaborator pass (§3). Affects `@derive`
   ergonomics.
5. **Effects surface `!` discipline** (`types/effects.ex`, the parked
   sound-effect-discipline spec) — superseded by `Effect`; confirm nothing
   still depends on the old inference before deleting.
6. **Refinement-using programs that don't migrate** — need a clear
   rejection/`unsafe` story (ties to the holes/`unsafe` taxonomy) rather than
   silent behaviour change.
7. **Discipline-index generalization** (FRP index algebra → fsm state/protocol
   typing) is **Tier-2, out of scope here** — fsm-via-macro without it is
   exactly as safe as today's bespoke fsm. Deferred, not part of the cutover.

## 8. Non-goals

- **Not** building SMT-certificate refinements (post-SMTCoq).
- **Not** the Tier-2 dependent state/protocol safety upgrade (separate later
  spec).
- **Not** touching the runtime shims (`{fsm,actor,sup,app}/runtime.ex`) or the
  AtomVM/BEAM tags — the emitted code still calls the same runtimes.
- **Not** a rewrite of lexer/parser/`beam_writer`/`dep_graph`.

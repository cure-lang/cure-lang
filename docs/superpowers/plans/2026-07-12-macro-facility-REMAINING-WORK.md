# Macro Facility — Remaining Work (Handoff Spec)

> **Purpose.** A self-contained hand-off for an agent picking up the macro-facility
> build. It enumerates exactly what is left, in order, with the grounded facts already
> probed so the next agent does not re-derive them. The accreting running log is
> `2026-07-12-macro-facility-autopilot-state.md` (the durable resume point — read its
> tail for the latest firing); this document is the *forward* view. Where they disagree,
> the running state file's newest entry wins.
>
> **Date:** 2026-07-12. **Branch:** `core-let-binder` (accumulating stack; deliberate
> deviation from autopilot's nested-worktree default — the macro work builds on the
> landed Effect/graded-binder/Std.Otp stack here). Work in the worktree root
> `.claude/worktrees/core-let-binder`, never the parent clone.

---

## 0. Non-negotiable invariants (apply to EVERY remaining item)

1. **TCB delta ZERO.** No changes to `lib/cure/core/*`. Macro output is re-elaborated and
   kernel-checked exactly like hand-written code. The elaborator (`lib/cure/elab/*`) and
   the frontend (`lib/cure/compiler/*`) are UNTRUSTED — changes there are fine. If a slice
   seems to *need* a `lib/cure/core/*` change, it is mis-scoped → **HALT** and re-plan.
2. **Ghost commits.** `git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>"`,
   NO `Co-Authored-By`, no Claude signature.
3. **Explicit pathspec only.** `git add -- <path>` / `git commit -- <path>`; NEVER `-A`/`.`
   (a concurrent agent may share the worktree). Revert `test/antigen/**/seeds.sexp` +
   `corpus.sexp` banking noise before committing.
4. **One build at a time.** Never run two `mix` suites concurrently (a past concurrent
   full-suite run kernel-panicked). Prefer scoped `mix test <file>`; run the full suite
   once, alone, at the gate.
5. **`mix` runs from the worktree root**, not the parent clone — the parent lacks the macro
   code and gives phantom "regression" failures.
6. **Per-slice autopilot chain:** Stage 2 write plan (`superpowers:writing-plans`) → Stage 3
   plan review (Sonnet `recursive-skeptical-review`, 2 clean passes, commit hardened) →
   Stage 4 execute inline TDD on Opus (commit per task) → Stage 5 code review (Sonnet
   `recursive-skeptical-review` over the diff, red-test-first fixes) → Stage 6 full suite
   green. Commit each stage/task. Update the running state file after every landed step.
7. **User-facing surface syntax is DEFERRED** (operator: easiest to change) — use the
   design's current notation as a placeholder; do not bikeshed spelling.
8. **Reference specs (source of truth for behaviour):**
   - `docs/superpowers/specs/macros/2026-07-08-macro-facility-design.md` (base; §3 quoted-AST,
     §5 hygiene, §6 name res, §7 import scope, §8 reflection API, §13 Tier 5, §14 BEAM/OTP).
   - `docs/superpowers/specs/macros/2026-07-11-self-proving-macros-design.md` (§3 exhaustive explain,
     §4 generative proof, §5 required examples).
   - `docs/superpowers/specs/macros/2026-07-12-racket-syntax-parse-comparison.md` (error machinery).
   - `docs/superpowers/specs/tooling/2026-07-12-tier3-computed-by-execution-design.md` (Tier-3 exec arch).
   - `docs/superpowers/specs/tooling/2026-07-12-generator-typeclass-pbt-architecture.md` (SP3 arch).
   - `docs/superpowers/plans/2026-07-12-macro-facility-program.md` (the 6 SPs + gates).

---

## 1. What is already DONE (do not re-open)

- **SP1 COMPLETE** (Stage-6 green: 4128 passed). Minimal facility, Tiers 1–2:
  - Tier-1 `literal` units (`500ms`→`Duration.ms(500)`), Tier-2 hygienic `syntax` templates,
    `<fresh Name>` hygiene, two-phase parse (harvest local `macro` defs → `active_macros`/
    `literal_macros`), the T8 soundness firewall (expansions re-elaborate identically to
    hand-written on BOTH pipelines), and the §2 default error-machinery floor (friendly
    diagnostics, never raw tuples/crashes).
- **SP2 partial:**
  - **M1** exhaustive `explain` → `missing_diagnosis` — COMPLETE (unwired check).
  - **M3** required examples → `rule_unpinned` (presence) + `example_mismatch` (expansion
    equality) — COMPLETE (unwired checks).
  - **Tier-3 slice 1** parse `computed by <fn>` → `%{kind: :computed, …}` (inert) — COMPLETE.
  - **Tier-3 slice 2** `Std.Syntax` value + reflection bridge — **plan hardened `ae0fa62`,
    NOT yet executed** (see §2.1 below — this is the immediate next item).

The three self-proving checks (M1 + M3) exist as standalone functions in
`lib/cure/compiler/macro_validate.ex` but are **not yet invoked by the compile pipeline** —
that is the WIRING slice (§2.5).

---

## 2. Remaining SP2 work (finish the spine first)

SP2 = "Tier-3 + self-proving Mechanisms 1 & 3". M1/M3 are done as unwired checks; what
remains is Tier-3 execution, the typed reflection API, the author-`fail` guard, and the
wiring that makes the checks fire in real compiles.

### 2.1 Tier-3 slice 2 — `Std.Syntax` value + reflection bridge  ⟵ IMMEDIATE NEXT
**Status:** Stage 2+3 DONE (plan hardened `ae0fa62`). **Do Stage 4 → 5 → 6.**
**Plan:** `docs/superpowers/plans/2026-07-12-macro-facility-sp2e-plan.md` (execute verbatim;
its code was patched-and-run by the reviewer).
**Deliverables:**
- **Task 1** — `lib/std/syntax.cure`: the generic reflection ADT. `@group(:core)`, `use Std.String`.
  ```
  type Syntax =
    | Node(Atom, List(Attr), List(Syntax))   # {tag, meta, [children]}
    | Leaf(Atom, List(Attr), SynLit)         # {tag, meta, scalar}
  type Attr = KV(Atom, SynLit)
  type SynLit = SInt(Int) | SFloat(Float) | SStr(String) | SBool(Bool) | SAtom(Atom) | SOpaque
  ```
  `meta` is LOAD-BEARING (function names/operators/subtypes live in meta, not tag/children) →
  `attrs` field is mandatory or reflection loses names. Exotic `third` (regex `{body,flags}`,
  string-interpolation part-list) → `SOpaque` (shape-only round-trip). Test mirrors
  `json_elaborates_test` (`Std.Json`'s nested `type Value` proves the positivity).
- **Task 2** — `lib/cure/compiler/macro_syntax.ex`: `to_syntax(parser_ast)` / `from_syntax`
  Elixir bridge over a mirror repr; lossless round-trip up to `:line`/`:col`. Round-trip test
  uses `strip/1` (drops `:line`/`:col`) and asserts `strip(from_syntax(to_syntax(ast))) == strip(ast)`.
  **Grounded corrections already in the plan:** a `~r/foo/` node has TAG `:literal` (not `:regex`)
  with `{:subtype, :regex}` in meta → its round-trip is `{:syn_leaf, :literal, attrs, :s_opaque}`
  with `{:subtype, {:s_atom, :regex}} in attrs`.
**Gate:** `Std.Syntax` elaborates; round-trip preserves names + attr order + child order; full suite green.
**No execution yet** — this is only the value model + bridge.

### 2.2 Tier-3 slice 3 — compile-time EXECUTION pass (the big one)
**Status:** architecture LOCKED (`…tier3-computed-by-execution-design.md`), plan NOT written.
Start at Stage 2.
**Architecture (locked, revisable by operator):**
- **A. Execute by ELABORATE + NORMALISE, not compile-and-load.** Elaborate the elab ref → apply
  it to the quoted input (a `Syntax` Core value) → `Cure.Core.Normalise.whnf`/full normalise →
  the normal form IS the computed expansion. Reuses the trusted normaliser (verified callable);
  TCB-zero (normaliser unchanged; output re-elaborated by the K3 firewall). Elabs are size-change
  total → normalisation terminates.
- **C. `:computed` expands at ELABORATION time, not parse time.** Parser harvests `:computed`
  rules and emits a deferred `{:computed_use, meta, [elab_ref, bound_input_syntax]}` node at
  use-sites WITHOUT expanding. A compile-time pass in `lib/cure/elab/*` (untrusted → TCB-zero),
  hooked into `Program.elaborate`/`check_ast` before declaration elaboration and recursing into
  nested exprs, walks for `{:computed_use}` and for each: build the `Syntax` input value
  (`to_syntax`) → elaborate `elab_ref` → `normalise(app(elab, input))` → `from_syntax` the result
  → splice the surface AST in place → normal elaboration checks it.
**Files (expected):** parser (harvest `:computed`, emit `{:computed_use}`), a new elaborator pass
module under `lib/cure/elab/`, reuse `lib/cure/compiler/macro_syntax.ex` (slice 2 bridge).
**Verify before/early in Stage 2 (open questions §6 of the exec-design note):** where the pass
hooks in `Program.elaborate`; that `app(elab, syntax_value)` reduces to a `Syntax` normal form
(prototype this first — the crux); that the elab signature is `Syntax -> Syntax` (not
`-> Effect(Syntax)`); a recursion/fuel backstop for a computed output that contains more macro uses.
**Gate:** a `computed by` macro whose elab returns a constant `Syntax` expands, elaborates,
kernel-checks; full suite green. End-to-end Tier-3.

### 2.3 Tier-3 — TYPED per-rule derived record (the elab-facing API)
**Status:** operator-steered, plan NOT written. Land **with or immediately after** slice 3 so no
throwaway stringly API ships. Start at Stage 2.
**Operator steer (2026-07-12, binding):** the elab AUTHOR must see a TYPED derived record, NOT a
stringly `field("name")` accessor. From a rule's holes, synthesise `rec RuleSyntax { <hole>:
Syntax(<Kind>), … }` (a `...` group → `List` of a sub-record) and thread it as the elab's parameter
type, so authors write `a.name` / `a.messages.map(fn(m) -> m.body)` — typed record projection,
compile-checked (a misspelled field is a compile error, not an elab-run-time failure). The generic
`Syntax` value (slice 2) is the SUBSTRATE each typed field holds underneath — slice 2 is unchanged
and un-wasted; what is REJECTED is shipping a generic `field` accessor as the elab API. This corrects
the `a.field("name")` shorthand in the §14.6 `actor` sketch — the real spelling is `a.name`.
**New machinery:** type-derivation from the grammar (leans on the landed dependent-records support).
**Gate:** an elab written against `a.name` compile-checks; a misspelled field is a compile error;
a `computed by` macro using the typed record expands + kernel-checks.

### 2.4 Tier-3 — `check … else fail C` (author semantic guards)
**Status:** plan NOT written (base §3.4). Start at Stage 2.
**Scope:** semantic guards inside elabs that raise an author-defined `Diagnosis` point
(`fail C(args)`), tying Tier-3 to M1's exhaustiveness (every `fail C` must be `explain`-described).
Plus computed-rule example checks (a `computed by` rule's `example … expands …` runs the elab and
compares) — fold in here or with the wiring slice as convenient.
**Gate:** an elab that `fail`s an undescribed point → `missing_diagnosis` at macro-compile; a
described `fail` renders its author message; example checks pass on green fixtures.

### 2.5 SP2 WIRING slice — make the checks fire in real compiles
**Status:** plan NOT written; SEQUENCING already grounded. Start at Stage 2. **This is what turns
the three unwired checks into enforced obligations and completes SP2.**
**Scope (absorbs several previously-separate items):**
- Invoke `MacroValidate.check_explain_exhaustive/1` + `check_rules_pinned/1` + `check_examples/1`
  during compilation (so a macro with an undescribed failure point / unpinned rule / mismatched
  example FAILS TO COMPILE).
- **Example expansions kernel-check** in module env. GROUNDED: a self-contained expansion (`x + x`)
  elaborates via `Program.elaborate`, but a real example referencing the macro's target
  (`Timer.repeat(500)`) fails `:unknown_global` in isolation — the macro's IMPORT CONTEXT isn't in
  scope. So example-kernel-check needs the elaborate-in-module-env machinery this slice builds. (This
  is why the once-planned standalone "slice 2c" was folded in here.)
- `{:type, ast}` type-only example pins (§5.2 — needs `Program.elaborate` on the expansion).
- **Pin the SP1 example-less test macros** (they have no `explain`/`example` and would now fail the
  enforced checks) — add the required blocks so the suite stays green.
**Gate (this completes the SP2 program gate):** the 3 macro-compile errors (`missing_diagnosis`,
`rule_unpinned`, `example_mismatch`) fire on red fixtures and are ABSENT on green ones; example
expansions kernel-check; full `mix test` green. → **SP2 Stage 6 → SP2 COMPLETE.**

---

## 3. SP3 — Generative expansion proof (self-proving Mechanism 2)
**Status:** ARCHITECTURE decided (operator design session), spec at
`…generator-typeclass-pbt-architecture.md`. Plan NOT written. Depends on SP2 (Tier-3 elabs + grammar
to fuzz) + the Antigen generator. Start at Stage 2.
**Architecture (locked "for now" — the MIDDLE / Hegel pattern):**
1. A **`Generator(a)` TYPECLASS** with stdlib conformance + `deriving` = the user-facing PBT magic
   (`forall` on any type, generator auto-resolved). Lives in Cure `Std.Gen`/`Std.Test`, RUNTIME,
   unaffected by the engine choice. (Operator: "all Std lib types have a generator typeclass
   conformance" — excellent for users.)
2. **Separate ENGINE from DOMAIN.** SP3's macro fuzzer = compile-time Antigen (the host engine)
   invoking the SAME Cure `Generator` instances to fill typed holes → assert each expansion
   elaborates to well-typed Core. User PBT = `Std.Test.forall` at runtime. ONE generator system,
   two runners by phase. **REJECTED:** reimplement-Hypothesis-in-Cure; literal external-Python
   Hypothesis server (breaks the self-contained BEAM toolchain).
3. **The one new engine:** type-directed term generation — extend the Antigen generator with "term
   of a required type" to fill typed holes.
4. **Phase 2 (LATER, operator "rewrite on top of a ported conjecture"):** port Hypothesis's
   choice-sequence CONJECTURE model → internal/free composable shrinking for every conforming type
   (incl. derived) + example-DB unified with Antigen's corpus/replay; re-base both runners; the
   `Generator` interface survives unchanged. NOT part of SP3's first cut.
**Open questions to verify before the foundation slice:** Antigen's current shrinking model; whether
the host engine can invoke a Cure `Generator` at compile time; how much `deriving` already exists; a
`Gen(a)` repr that survives the Phase-2 re-base.
**Gate:** a macro whose `becomes`/elab drops a hole's type is REJECTED at macro-compile with a shrunk
counterexample; a correct macro passes; a per-macro coverage manifest reports coverage; caching by
macro definition; full suite + Antigen campaign green.

---

## 4. SP4 — Tier 4 reflection API
**Status:** not started, plan NOT written. Depends on SP2 (Tier-3 elab host). Independent of SP3.
**Scope (base §8):** the read-only advisory API — `resolve`, `constructors`, `infer`, `expand`, and
`lift` (the append-only write member) — enough for `reducer`/`flow`/`view` macros. Nothing returned by
the API is trusted (a lie from it still yields a rejected-not-unsound program). Builds on the typed
reflection record from §2.3.
**Gate (Dogfood Gate 2):** a `reducer`-style macro builds GADT match arms via `constructors`/`resolve`
and its output kernel-checks; `lift` hoists a declaration; full suite green.

---

## 5. SP5 — §14 BEAM/OTP container ownership (`behaviour`/`callback` + `lift module`)
**Status:** not started, plan NOT written. Depends on SP2 (+ SP4 for callback-body elaboration).
**Scope (base §14):** the closed callback vocabulary as Cure ADTs (§14.3); `lift module` minting a
compiled unit as a VALUE (§14.4–.5, pure — no compile-and-load); the first OTP container fully owned
by a macro (Gate 1b: `sup` under a fresh name). Callback bodies are `Effect`-typed (ties to the
landed effect stack). **This is what gives `Std.Otp` its ceiling** — `spawn`/`start_link` minting
typed handles + gen_server behaviours compiled from a Cure `process`/`actor` macro.
**North star (design §14.6):** the `actor`/`fsm`/`sup` container macros — `computed by` macros whose
elab (with the typed reflection API §2.3 + `lift module`) builds a gen_server/supervisor, authored
against `a.name`-style typed reflection.
**Gate:** a `sup`-style macro emits a gen_server/supervisor behaviour that RUNS on generic-unix AtomVM
(observable), all through `lift module`, no bespoke Elixir backing it. Then `actor`/`fsm` re-expressed
(Gate 1) and their bespoke compilers become deletable.

---

## 5.1 SP5.1 — Quasiquotation (`quote` / `$( )`)  ⟵ NON-OPTIONAL PREREQ FOR SP6 (promoted 2026-07-16)
**Status:** promoted from the former optional "slice 4". Plan NOT written. Start at Stage 2.
**Scope:** a `quote { … }` surface lifting ordinary Cure syntax to a `Syntax` value, with
`$(expr)` single-node and `$(xs …)` repeated-group splices + splice position/category checking.
Becomes the DEFAULT authoring surface for `computed by` expanders; the `Std.Syntax` typed
builders / `Std.Syntax.Raw` drop to the escape hatch. Reuses the landed `to_syntax`/`from_syntax`
bridge (no second AST model).
**Gate:** a `derive_actor`-class expander rewritten with `quote`/`$()` produces byte-identical Core
to the hand-built version; a wrong-category splice is a compile error; full suite green.

## 5.2 SP5.2 — Cross-module macro import (was §7 "T9")  ⟵ NON-OPTIONAL PREREQ FOR SP6 (promoted 2026-07-16)
**Status:** promoted out of "deferred" — a hard prerequisite for SP6, not a convenience. Plan NOT written.
**Scope (base §7 import scope + §6 name res):** `use SomeModule` brings that module's
`syntax`/`macro`/`syntax family` grammars into scope at the USE site. The HARD architectural piece —
cross-module resolution (`import_source_env`/`module_slice_env`, `program.ex:699/799`) runs at
ELABORATION, but macro expansion is at PARSE time, so imported-macro grammars need the PARSER to
locate+parse imported modules (couples parser to import resolution).
**Gate:** a DSL macro defined in module A, `use`d from B, expands + kernel-checks in B; a same-keyword
grammar conflict across imports is a real diagnostic (not a raw parser error); full suite green.

## 5.3 SP5.3 — Scope-set hygiene (was §7 "T7b")  ⟵ NON-OPTIONAL PREREQ FOR SP6 (promoted 2026-07-16)
**Status:** promoted out of "deferred". Plan NOT written.
**Scope:** replace string-gensym hygiene with Flatt's set-of-scopes model (uncopyable scope marks) and
turn on automatic full hygiene (auto-rename every template binder, no annotation), keeping the
`<capture>` escape hatch. Closes the two characterized gaps: (a) fresh-name = hole-name silent-drop
(`<fresh e>` where `e` is also a hole drops the arg); (b) backtick-gensym spoofing (`` `g$0` `` as a
use-site arg defeats string gensyms). These are exploitable-in-principle, not cosmetic.
**Gate:** red fixtures reproducing both gaps now pass; auto-hygiene renames binders with no annotation;
`<capture>` still binds into caller scope on demand; full suite green.

---

## 6. SP6 — Tier 5 + concrete DSL libraries
**Status:** not started. Depends on SP1–SP5 **and the non-optional SP5.1–5.3 prerequisites** as each
DSL requires. **LAST of the core spine** (only SP9 is scheduled after it).
**Scope (base §13):** module rules + raw holes (§13.1–.2), then the sibling DSL specs (`packet`,
`board`, `driver`, `protocol`, `parse`, …) as libraries on the finished facility. Each DSL is its own
small plan.

---

## 6a. SP7–SP9 — first-class, OFF the SP6 critical path
Unlike SP5.1–5.3 these do NOT gate SP6. Order by priority, not sequence. Full detail + gates in the
program roadmap (`2026-07-12-macro-facility-program.md`, SP7–SP9).
- **SP7 — Macro tooling** (stepper, expansion introspection, macro-aware errors). Startable NOW: rides
  the landed `source_line`/`source_col` provenance channel (2026-07-15). Absorbs the former Parked
  Elm-style error rendering. Highest adoption leverage per unit effort. `cure macro expand <file>`
  step view + `--trace-macros` + use-site error rendering.
- **SP8 — Composition soundness.** Extends SP3's generative proof from single-macro to macro∘macro
  composition (build against `macros/2026-07-08-macro-composition-design.md`) + proven expansion
  confluence/termination (today only fuel-bounded). Depends on SP3.
- **SP9 — Type-directed (elaboration-time) macros.** A distinct macro KIND that sees the expected type
  and emits into the elaborator (Lean 4 / Idris `%macro` posture) — overloaded literals, adaptive
  `do`-notation, type-driven deriving. The deliberate LAST, high-ceiling bet, after the SP1–SP6
  syntactic tier is proven. Depends on SP2 + reflection API (+ effect stack for `do`-notation).

---

## 7. Promoted out of "deferred" (2026-07-16)
The three items formerly parked here as optional/deferred SP1 enhancements are now first-class
non-optional sub-projects — see §5.1–5.3 and §6a above:
- former **T9** (cross-module macros) → **SP5.2** (§5.2), a non-optional prerequisite for SP6.
- former **T7b** (auto full hygiene + the two `<fresh>` gaps) → **SP5.3** (§5.3).
- former **Parked** Elm-style error rendering → folded into **SP7** (§6a).
No SP1 enhancements remain deferred.

---

## 8. DONE criterion + halt
**DONE (cancel cron + notify):** all core sub-projects through SP6 — SP1–SP6 plus the non-optional
SP5.1–5.3 prerequisites — implemented, code-reviewed, full `mix test` green, with an end-to-end proof —
a user-defined macro parses, expands, is generatively proven (full fuzz) to expand to well-typed Core,
and its expansion runs. (SP7–SP9 are first-class follow-on, NOT part of this DONE bar: SP7/SP8
recommended before the facility is called polished; SP9 is the horizon bet.) Then `CronDelete` the
autopilot cron + `PushNotification` naming the final commit.
**HALT:** hard blocker, a would-be `lib/cure/core/*` change, or a review loop hitting pass 15 without
convergence → update the running state file with the blocker + what's needed, `PushNotification`, STOP.
Never guess or accept an unconverged artifact.

---

## 9. Ordering summary
```
SP2 (finish): slice2 exec ▸ slice3 execution ▸ typed-record ▸ check…else fail ▸ WIRING ▸ Stage6  ⟵ NOW
   └─▶ SP3 (generative proof) ─────────────────────────▶ SP8 (composition soundness)
   └─▶ SP4 (reflection API)     ┐ fan out from SP2; order by priority
   └─▶ SP5 (behaviour/lift ▸ Std.Otp ceiling)  ┘
         SP5.1 quasiquote          ┐
         SP5.2 cross-module import  ├─ NON-OPTIONAL prereqs ─▶ SP6 (Tier 5 + DSL libraries)  ⟵ last of core spine
         SP5.3 scope-set hygiene   ┘
Off critical path: SP7 (tooling) — startable NOW ▸ SP9 (type-directed macros) — LAST.
```
SP1→SP2 is the spine (SP2 nearly done). SP5 unblocks the `Std.Otp` ceiling; SP3 delivers the
self-proving headline; SP4 unblocks the flagship reducers. SP5.1–5.3 are non-optional prerequisites
for SP6 (quasiquote authoring, cross-module distribution, non-spoofable hygiene). SP7 (tooling) rides
the landed provenance channel and can start now; SP8 extends SP3; SP9 (type-directed macros) is the
last, high-ceiling bet. One SP's full plan — red-green, gated, committed — before the next.

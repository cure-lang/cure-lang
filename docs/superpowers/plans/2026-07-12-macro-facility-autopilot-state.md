# AUTOPILOT STATE — Macro Facility Build (base + self-proving extension)

**Started:** 2026-07-12. **Branch:** `core-let-binder` (staying in the accumulating
stack — the macro work builds on the landed Effect/graded-binder/Std.Otp stack here;
deliberate deviation from autopilot's nested-worktree default, per
autopilot-worktree-preference). Cron-driven; this file is the durable resume point.

## Stage 0 — DONE (design approved, specs committed)
- Self-proving design APPROVED by operator; specs committed:
  - `docs/superpowers/specs/macros/2026-07-11-self-proving-macros-design.md` (extension)
  - `docs/superpowers/specs/macros/2026-07-08-macro-facility-design.md` (base)
  - `docs/superpowers/specs/macros/2026-07-12-racket-syntax-parse-comparison.md`
  - `docs/superpowers/plans/2026-07-12-macro-facility-program.md` (SP decomposition)
  - `docs/superpowers/plans/2026-07-12-macro-facility-sp1-grounding.md` (parser map + architecture)

## The program: 6 sub-projects (run the autopilot chain per SP, in order)
SP1 minimal facility (container+grammar+Tiers1-2) → SP2 Tier3+typed errors+examples →
SP3 generative expansion proof → SP4 reflection API → SP5 behaviour/lift-module (Std.Otp
ceiling) → SP6 Tier5+DSLs. SP1→SP2 spine; SP3/4/5 fan out from SP2.

## Autopilot chain PER sub-project
Stage 2 write the SP plan (writing-plans) → Stage 3 plan review (Sonnet subagent,
recursive-skeptical-review) → Stage 4 TDD execute (Opus) → Stage 5 code review (Sonnet
subagent) → Stage 6 verify (full suite). Commit per stage/task. Stage 1 spec review is
DONE for the shared specs (self-reviewed); each SP plan still gets Stage 3.

## Locked decisions carried into every SP
- **TCB delta ZERO** — macro output is re-elaborated + kernel-checked; NO `lib/cure/core/*`
  changes. Any SP that thinks it needs one is mis-scoped → HALT.
- **User-facing syntax DEFERRED** (operator: easiest to change) — use the design's current
  notation as a placeholder; do not block on surface spelling.
- **Port syntax-parse's machinery** for error quality (comparison doc §4): failure-SET →
  maximal-by-progress → report(message,context,at,within). **Thread progress from SP1
  task 1** (retrofitting it later is painful).
- Self-proving obligations: SP2 (typed exhaustive Diagnosis incl. `fail C`, required
  examples) + SP3 (full generative expansion fuzz on every macro compile).
- Two-phase parse (pre-pass seeds `active_macros` from `use`+local defs) = SP1's
  architectural core (grounding doc). Soft-keyword `macro`; `{:macro_def,meta,rules}` AST.

## CURRENT POSITION — 2026-07-16 (live pointer)

- **SP5.3 (auto full hygiene) COMPLETE** (`b6942c01` RED / `8d93fe39` GREEN /
  `d2ccf817` gate-fix / plan v9 `d02405f3`). Every unannotated ordinary binder in
  a Tier-2 `becomes` template is now auto-freshened by a scope-aware
  `scoped_freshen/5` walk (let/block, match-arm+guard, lambda, single-clause
  fn-def params, comprehension reverse-scope), with `<capture Name>` as the
  opt-out and map-shaped family-signature binders left untouched. Frontend-only,
  TCB delta zero. The full-suite gate caught one regression — freshened OTP
  `start_link` params produced `initial$0` gensyms the Printer/lexer couldn't
  round-trip — fixed by allowing `$` as an identifier continuation char
  (`lexer.ex`). Full suite green: **4235 passed / 1 skipped / 0 failed**, antigen
  318/318. This clears the last non-optional SP6 prerequisite.



**The live implementation state is the `ORDERED TRANSPARENT BEAM PLAN` below plus the
dated status blocks under `OPEN GATE — automatic message-code derivation` (current
through 2026-07-15). Read those for detail; this is the map.** Where the branch
actually stands:

**Structured production update (2026-07-19).** Reusable syntax families now
support source-defined token productions and typed indented child sections.
`Std.Fsm` uses that generic facility for the release-facing
`State --Event--> State` graph: it derives nominal `State` and `Event` types,
emits direct nested callback matches, preserves data by default, and accepts a
local edge `update` expression. No FSM token rule or runtime table interpreter
was added to the compiler. The same nested-production mechanism is the parser
foundation required by the `knit` algebra's section/row grammar. Focused parser,
printer, expansion, and live `gen_statem` tests are green.

**Typed FSM architecture decision (2026-07-19).** The remaining FSM work is
specified by `../specs/beam/2026-07-19-typed-fsm-as-constrained-actor-design.md`.
An FSM normatively derives a finite state/event reducer and expands through the
same source-defined `ActorBehavior` substrate as `actor`. The ordered FSM work
is: shared actor substrate; FSM-to-actor lowering; typed event payloads; graph
policy and verification; guards; effects/notifications; lifecycle/timers;
optional operations; cleanup and full gates. Legacy `on_transition`, raw Atom
events, and the opaque caller/meta/payload runtime container are not compatibility
requirements.

**Shared actor substrate update (2026-07-19).** `Std.ActorBehavior` now owns
the transparent behavior-module construction boundary. `Std.Actor` delegates
both its state-aliased and state-polymorphic forms to that substrate, while
all three `Std.Fsm` emitters delegate to its constrained `gen_statem` strategy.
Architecture guards prohibit either public macro from calling
`lift_module_isolated` directly and prohibit host Builtins/runtime indirection
in the substrate. The 120-module standard library and 16 focused architecture,
actor-family, and live typed-FSM tests pass. The next ordered FSM item is typed
event payload production; richer process APIs/lifecycle remain governed by the
FSM specification.

**Typed actor contract (2026-07-19).** The actor-first work required before
further FSM expansion is specified by
`../specs/beam/2026-07-19-typed-actor-behavior-design.md`. The checked OTP carrier
must distinguish asynchronous messages from synchronous requests on the same
server PID; `actor` then derives nominal message/request/reply codes and thin
typed adapters over that algebra. State remains the immutable accumulator of
OTP's suspended mailbox loop. Universal state inspection, hidden caller state,
the process dictionary, and a mandatory runtime registry are excluded. The
ordered work is: honest server handle; generated actor API; modern typed
message/query grammar; lifecycle/failures; optional capabilities; cleanup and
the shared FSM gate.

**Typed actor algebra update (2026-07-19).** Phase 1 now has an erased
`RawServerPid(message, request, reply)` carrier and the checked
`ActorServer`/`DepActorServer` aliases. `actor_cast`, `actor_call`,
`actor_call_dep`, and `actor_stop` keep asynchronous and synchronous protocols
distinct; focused negative tests prove neither code can be used in the other's
operation. Sixty-one OTP, actor, FSM, golden, and architecture tests pass. The
typed-startup seam is now closed by guarded `BeamTerm` observation and
`StartResult`: only a two-tuple tagged `:ok` whose payload passes the native PID
guard receives actor protocol indices; `:error`, `:ignore`, and malformed terms
remain explicit outcomes. Structured actors now emit nominal Message/Request/
Handle declarations plus validated `start`, typed `send`/`stop`, and (for the
current uniform-reply path) typed `request`; live and negative tests cover state
evolution and mailbox rejection. Phase 2 remains open for dependent `ReplyOf`
query adapters and generic lifted-module declaration publication to sibling
Cure code in the same compilation.

**Typed actor grammar update (2026-07-19).** Phase 3 now accepts preferred
`on_message` folds. Constructor heads with typed payload binders derive the
nominal message ADT through ordinary reflection; a real BEAM test covers an
`Add(Int)` message changing multiple record fields and a nullary reset. The
compiler remains unaware of actor vocabulary. An explicit `reply ReplyOf`
family now selects the dependent actor path: the generated callback and client
adapter preserve request-indexed reply types, validated by heterogeneous live
calls and a wrong-branch negative test. Automatic `ReplyOf` derivation and
named query adapters remain the next Phase-3 seam.

- **Transparent BEAM plan:** Phases 0, 1, 2, and 2.5 are COMPLETE. Phase 3 (`beam_ops`)
  is unblocked (2.5 done) and substantially landed. Phase 4 has replaced all four OTP
  forms — `sup`, `actor`, `fsm`, `app` each now lower through a source-defined
  `syntax family` + expander (the structured-family surface, 2026-07-15). Phase 5/5a
  (reusable family surface + beginner-friendly `Std.Syntax` builders) is in progress;
  Phase 6 end-to-end / AtomVM verification remains.
- **Open work:** the `contextual` proof exemption on `beam_ops self` is now
  RETIRED (`a543cfb9`, via parametric-erased acceptance — NOT the earlier
  reply-channel-derivation idea, which was unnecessary). Remaining optional polish:
  finish the safe-vs-`Std.Syntax.Raw` split and multi-channel `handle_call` reply
  typing. (Scope-aware hygiene for ordinary generated binders is DONE — SP5.3, see
  the current-position pointer above.)

**DONE-gate assessment (2026-07-16, verified against source + green tests).** The
host-side spine is functionally COMPLETE and green. Concretely proven this fire:
- `test/cure/compiler/actor_computed_test.exs` (36 green with
  `declaration_macro_expansion_test.exs`) executes the FULL DONE chain for a
  user-defined `actor` macro: `Cure.Compiler.compile_and_load/2` runs
  parse→expand→**derive** (message type + reply contract from handler clauses)
  →elaborate→codegen→load real BEAM, then `start_link` →
  `:gen_server.cast(pid, :Inc)` → `:gen_server.stop(pid)` runs the expansion as a
  LIVE GenServer. "A user-defined macro parses, expands, and its expansion runs"
  is met on the host BEAM (≡ AtomVM semantics per CLAUDE.md).
- Structured `actor`/`fsm`/`sup`/`app` surfaces, the safe-vs-`Std.Syntax.Raw`
  boundary (`unsafe_*` + `validate_expansion/1`), and scope-set hygiene (SP5.3)
  are all landed and green.
- **Generic-unix AtomVM runtime gate VERIFIED for ALL EIGHT surfaces this fire.**
  `mix test --include atomvm test/cure/compiler/atomvm_container_test.exs` = **1
  passed** ("Return value: ok"). That test compiles the legacy `actor`/`sup`/`app`/
  `fsm` AND the structured `Std.Actor`/`Std.Fsm`/`Std.Supervisor`/`Std.App`
  expansions to real BEAM, packs them with `packbeam` + estdlib into an `.avm`,
  and RUNS them on the real generic-unix AtomVM binary via `start_link`/`start`.
  (Supersedes the older "Structured application status" note that claimed the
  generic-unix run only for supervisor/application — it now covers actor + fsm
  too.) AtomVM ≡ OTP semantics per CLAUDE.md, so this is the strongest
  host-reachable form of "the expansion runs on the actual VM."

**The remaining residuals are all optional or out-of-host-scope — NONE is a bug:**
1. *Multi-channel `handle_call` reply typing* — an ENHANCEMENT, not a gap.
   `infer_reply_tail` (`actor.cure:355`) today rejects arms with differing reply
   types (`:inconsistent_reply_types`), which is the recorded fork-#1 default
   ("reject rather than guess") WITH an explicit escape (the
   `actor … call … returns <reply_type>` rule, `actor.cure:77`). Accepting a
   *union* reply type would be sound (Erlang replies are heterogeneous) but is a
   deliberate behavior-widening decision, not a defect — deferred; keep as-is
   (lower-risk) absent an operator call.
2. *`contextual` retirement* — CLOSED for the nullary-parametric case
   (`beam_ops self`, `a543cfb9`, see the gate-(a) block below). The remaining
   `contextual` rules supply arguments and are intrinsically use-site-bound —
   not a gap.
3. *Safe/raw helper migration* — additive; existing helpers stay source-compatible.

**GATE (a) CLOSED for `beam_ops self` — 2026-07-16 (`a543cfb9`).** The SP3
generative proof now PROVES the nullary all-erased-implicit case instead of
exempting it. `check_expression_expansion` (`macro_fuzz.ex`) accepts a bare
nullary global call whose every parameter is erased when the sole obstruction is
`{:unsolved_metavariables, name}`: an erased binder is computationally
irrelevant, so the expansion is well-typed at a schematic type for every
instantiation by parametricity (the same reason an ungeneralized polymorphic term
type-checks). Realized as a pure predicate `parametric_erased_call?/3` reading the
callee signature from `Env.get_def` (`quantities` all `:erased` + an all-erased Pi
spine of matching arity, non-Pi codomain) — no elaborator error-contract change,
no new user surface, TCB delta ZERO. `beam_ops self` (`otp.cure:13`) dropped its
`contextual` qualifier and now flows through the ordinary proof batch; both guards
(bare-nullary shape, every-parameter-erased) are unit-tested directly. Full suite
**4237 passed / 1 skipped / 0 failed**, Antigen 318/318. The chosen approach
supersedes the earlier option-A/option-B framing — neither was needed. The
*remaining* `contextual` `beam_ops` rules (`tell`/`call`/`cast`/`spawn`/… ) all
SUPPLY arguments and are legitimately contextual (their typed-pid/reply obligations
are only discharged at a real use site); they are NOT nullary-parametric and stay
exempt by design. So gate (a) is now closed for the only rule where it is soundly
closable use-site-free; the SP3 exemption that remains is intrinsic, not a gap.

**One gate remains between here and the REMAINING-WORK §8 DONE bar** (do NOT
`CronDelete` until it closes): (b) ESP32 **hardware** verification —
the project's raison d'être, a distinct observable-flashing work mode, not a host
`mix test`. The generic-unix half of the runtime story is now CLOSED (verified
above, all eight surfaces), so gate (b)'s residual is specifically the physical
ESP32 flash + serial-observed run — which per CLAUDE.md must be observable and
is realistically operator-driven; an autonomous host fire can build/package the
`.avm` but cannot observe the board. With gate (a) now closed for `self` (above)
and the remaining `contextual` rules intrinsically use-site-bound, the only
autonomous host work left is optional polish — multi-channel reply typing and
safe/raw helper migration. The DONE bar is otherwise met on host; hardware is the
last real gate.

The SP1–SP6 records below are the historical foundation log — superseded as the
*current* pointer by the summary above, but retained for provenance.

## SP1 MILESTONE-1 RECORD (historical)
SP1, Stage 2 DONE for milestone 1 (macro-definition front-end): plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp1-plan.md` (`6f76a94`), tasks 1-3
with complete anchored code (soft-keyword `macro`, `syntax` rules, typed holes →
`{:macro_def, meta, rules}` progress-slotted AST). Parser anchors verified & recorded in
the plan's Global Constraints (Token/state/helpers, soft-keyword dispatch at
parser.ex:292-340, parse_fsm template at :3894).

Stage 3 DONE — plan hardened + committed `6dedd96` (4 passes, 2 clean). Reviewer caught
& fixed two CRITICAL defects and VERIFIED the corrected code for real (scratch-applied,
6/6 new tests pass, `test/cure/compiler/` suite = 625 passed, then reverted):
- `Parser.parse/2` returns the BARE node, never a list → tests use `node = parse!(...)`.
- `end` is a reserved keyword no container consumes; Cure containers close by DEDENT →
  the macro sources have NO trailing `end` (`macro Every\n`, not `macro Every\nend\n`).
- Token atoms `:lt`/`:gt`/`:colon` confirmed correct; all anchors verified exact.
Use the HARDENED plan (`6dedd96`) for execution — it is proven to work.

Stage 4 milestone-1 DONE — SP1 tasks 1-3 executed inline TDD (red→green per task),
committed `c381e7a` (container skeleton), `8f07931` (bare-keyword syntax rules),
`77cbd6d` (typed holes). `test/cure/compiler/macro_def_parse_test.exs` = 6 passed; full
`test/cure/compiler/` = 625 passed / 1 skipped (baseline, no regression). The
macro-definition front-end is live: `macro Name` → `syntax kw <hole: Kind> becomes tmpl`
→ `{:macro_def, [name,line,col], [%{kind: :syntax, keyword, segments: [{:lit,_}|{:hole,%{name,kind,line}}], template, progress: nil, line}]}`.

Stage 5 milestone-1 code review DONE — 7 passes (6 clean). Found + fixed ONE real defect:
`##` doc-comments (always `:doc_comment` tokens, not gated by preserve_comments) broke the
container — a doc-comment as first body line silently emptied the rule list; between rules
it threw spuriously. Fix `4295479`: `skip_macro_trivia/1` (newline + doc/line comments) at
every container-body skip point + 2 red tests. `test/cure/compiler/` = 627 passed;
`--warnings-as-errors` clean; macro non-breaking in all positions verified.

MILESTONE 1 (macro-definition front-end, SP1 tasks 1-3) is COMPLETE through Stage 5:
commits `c381e7a` `8f07931` `77cbd6d` `4295479`.

SP1 milestone 2 Stage 2 DONE — plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp1b-plan.md`. It scopes the milestone to
the **critical path to "a local macro expands"** (the observable spine), with T4/T7/T8/T9 as
noted subsequent increments:
- **Task 1 (T5) — two-phase parse:** `active_macros: %{keyword => [rule]}` on parser state;
  `parse/2` runs a harvest pass (parse once, keep only `{:macro_def}` nodes via
  `collect_macro_defs/1`) then an authoritative pass seeded with it. LOCAL macros only (`use`
  inert at parse time → imported grammars deferred to T9). Test pins no single-pass regression.
- **Task 2 (T6a) — zero-hole use-site expansion:** guarded `:identifier` dispatch
  (`is_map_key(state.active_macros, name)`) → `parse_macro_use/2` → `expand_rule/2`
  (`subst_holes/2` walks the template). `now` → `Clock.now()`.
- **Task 3 (T6b) — hole matching + substitution + progress:** `match_segments/4` walks
  `{:lit}`/`{:hole}` segments, binds holes via `parse_expr`, records progress (syntax-parse
  maximal-by-progress hook), substitutes. `every <t: Code>` → `Timer.repeat(t)`.

SP1 milestone 2 Stage 3 DONE — sp1b plan HARDENED + committed `e6883fe` (6 passes, 2
consecutive clean). Reviewer verified every claim against the REAL parser (ran `Parser.parse/2`
on live source) and caught 2 real defects + added coverage:
- **CRITICAL fixed:** Cure has NO `def` keyword (it's `fn`). The Task 2/3 fixtures `def f() = …`
  parse to a bare `{:variable,_,"def"}` + `{:assignment}`, never `{:function_def}`. All fixtures
  changed to `fn f() = …`; `find_fn_body` pinned to the CONFIRMED shape (no more asserted-then-
  verify hedge).
- **HIGH fixed:** the macro-use dispatch clause is checked FIRST in `parse_prefix/1`'s
  `case token.value do`, ahead of `sup`/`app`/`macro`/`with`/`assert_type`/`rewrite`. A local
  macro named `sup` would silently disable the supervisor container module-wide. Guarded with
  `@reserved_macro_keywords` (`name not in @reserved_macro_keywords`) + a red collision test.
- **Coverage added:** Task 3 shipped 3 behaviors (hole-bind, literal-match, literal-mismatch
  error) with only 1 named red test → added 2 more (two-literal-segment match; literal mismatch
  asserting `:macro_use_mismatch`), each verified genuinely red against baseline.
- Harvest-pass fragility (soft spot a) reviewed: judged acceptable for v1 (recovery surfaces the
  `{:macro_def}` nodes); constrain-def-before-use / structural-prescan is the noted enhancement.

Use the HARDENED plan (`e6883fe`) for execution — its code snippets were mechanically
syntax-checked (`Code.string_to_quoted!`) and the reserved-keyword guard is in the plan.

SP1 milestone 2 Stage 4 DONE — all three tasks executed inline TDD (red→green), committed:
- **T5 `d66bf57`** — `active_macros: %{}` on parser state; two-phase `parse/2` (harvest pass →
  `harvest_active_macros/1`/`collect_macro_defs/1` → authoritative pass). `test/cure/compiler/`
  628 passed.
- **T6a `0bd320f`** — guarded `:identifier` dispatch (`is_map_key(active_macros,name) and name
  not in @reserved_macro_keywords`) → `parse_macro_use/2` → `expand_rule/2`/`subst_holes/2`.
  `now` → `Clock.now()`. Reserved-keyword collision (`sup`) test proves the guard. 630 passed.
- **T6b `94c33a6`** — `match_segments/4` walks `{:lit}`/`{:hole}` segments, binds via
  `parse_expr`, records progress, `{:error,progress,state}` recovery emits `:macro_use_mismatch`.
  `every <t>` → `Timer.repeat(500)`; `say hello` literal match; `say goodbye` mismatch error.
  633 passed / 1 skipped, `mix compile --warnings-as-errors` clean.
- **Test-helper fix during execution (flag for reviewer):** the plan-provided `has_supervisor?/1`
  helper had a provably-wrong first clause — `{:container, meta, _}` matched the enclosing MODULE
  container and short-circuited to `false` without recursing into children (where the supervisor
  lived). The behavior under test (parser produces the supervisor despite the macro collision) was
  CORRECT — verified by raw-tree probe. Fixed the helper to check container_type AND recurse. This
  is a legitimate immutability exception (test helper wrong, not the impl); Stage-5 should confirm.
- **Wrong-directory hazard recorded:** `mix` MUST run from the worktree root
  (`.claude/worktrees/core-let-binder`), NOT the parent clone `/Users/ch/Develop/esp32-beam/cure-lang`
  — the parent lacks the macro code, so running there gives phantom "macro front-end regressed"
  failures. Never `cd` out of the worktree for a build.

SP1 milestone 2 Stage 5 DONE — Sonnet code review over the Stage-4 code diff (`754e8d0..94c33a6`),
converged 3 passes (2 clean). Found + fixed ONE genuine defect red-test-first:
- **`6e01715`** — `subst_holes/2` only recursed into a node's `children` (3rd tuple elem), never
  its `meta` (2nd elem). `match_arm` stores pattern/guard in META, so a hole referenced from a
  template's match-arm guard (`check <x> becomes match 1 { y when x -> 1, ... }`) survived
  expansion as a dangling `{:variable,_,"x"}`. Fix walks meta values too (`subst_holes_meta/2` +
  `subst_holes_meta_value/2`), scalar-safe. Red test `"a hole referenced inside a template
  match-arm's guard is substituted"` added.
- Reviewer cleared the other scrutiny points: harvest is order-independent module-wide by design
  (use-before-def works); reserved-keyword list exactly matches the 6 hard-coded soft-keyword
  clauses; greedy hole-then-literal either just-works or errors loudly (T4-deferred, not silent
  corruption); error-recovery arm has guaranteed forward progress (no infinite loop); the
  Stage-4 `has_supervisor?` helper fix confirmed legitimate.

SP1 milestone 2 Stage 6 DONE — **full `mix test` green: 4099 passed / 2 skipped, 3 doctests**,
159 expected immune responses, antigen shape-coverage 328/328 ✓. Parser change globally safe.

**MILESTONE 2 (local macro use-site expansion) COMPLETE** through review+verify: a locally-defined
macro now parses, and its use-site EXPANDS to substituted surface AST (zero-hole, single-hole, and
literal-segment forms), re-checked by the existing elaborator/kernel (TCB delta zero). Commits
`d66bf57` `0bd320f` `94c33a6` `6e01715`.

SP1 T8 Stage 2 DONE — plan committed at `docs/superpowers/plans/2026-07-12-macro-facility-sp1c-plan.md`.
**Scoping decision:** split the planned "T7+T8" round — this plan is **T8 alone** (the soundness
firewall, the DONE-criterion spine "expands to well-typed Core"); T7 (hygiene) is deferred to its
own plan `…-sp1d-plan.md` because it is a distinct red-green feature (gensym + capture-avoidance)
needing its own grounding. Keeps each plan a coherent testable unit.

T8 grounding is LIVE-PROBED, not assumed — ran `Cure.Elab.Program.elaborate/1` (`program.ex:16`,
returns `{:ok, Env}` / `{:error, term}`) on real macro programs. Because expansion is a PARSE-TIME
surface rewrite, expanded AST flows through the unchanged elaborator+kernel, and macro programs get
the IDENTICAL verdict to their hand-written equivalents:
- `zero`→`0` as Int ⇒ accept (== hand-written `fn f() -> Int = 0`).
- `inc <x>`→`x + 1` on Int param ⇒ accept.
- `bad`→`nonexistent_thing` ⇒ reject `:unknown_global` (== hand-written, identical term).
- `tt`→`true` as Int ⇒ reject `{:conversion_failure, {:data,:Bool,[],[]}, {:int_type}}` (== hand-written).
Error terms are position-free → exact `==`. T8 = a firewall test (`test/cure/elab/macro_expansion_
soundness_test.exs`) asserting verdict-equality, **zero production delta** (expansion already re-
elaborates). Honestly framed as characterization/firewall (green-from-green, like the milestone-2
Task-1 pin + `emit_hole_firewall_test`), with a red-first NEGATIVE CONTROL step proving the equality
has teeth. Flagged for the Stage-3 reviewer: validate the firewall-not-red-green TDD framing and that
verdict-equality can't pass trivially (accept-sense + reject-sense pins guard that).

SP1 T8 Stage 3 DONE — plan hardened + committed `2f878af` (4 passes, 2 clean). Reviewer verified
all four verdicts live and surfaced a CRITICAL scoping finding: `Program.elaborate/1` is the
DEPENDENT entry, but `cure build`/CLI (`Cure.Compiler.compile_string/2`) routes NON-dependent
programs (all four T8 examples classify non-dependent per `dependent?/1`) through the CLASSIC
`Types.Checker` + classic Codegen — so Task 1 alone doesn't firewall what `cure build` does today.
Reviewer honestly rescoped the plan + flagged it as a driver/operator decision (did NOT silently
patch).

**FORK RESOLVED (driver decision `36a3289`, prose per convention):** firewall BOTH entry points.
Live-probed that classic `compile_string` verdict-equality ALSO holds (line-stripped, all four
`equal=true`). Task 1 = permanent dependent firewall (the "well-typed Core" path the DONE criterion
names; survives classic rip-out). Task 2 = TRANSITIONAL classic firewall (delete when
classic-pipeline-deletion lands) giving `cure build` real protection now. Both test-only, zero
production risk.

SP1 T8 Stage 4 DONE — both firewalls executed, negative-control-proven teeth, then committed:
- **`3a7383d`** `test/cure/elab/macro_expansion_soundness_test.exs` — dependent firewall, 6 tests
  (4 verdict-equality + accept-sense + reject-sense). Negative control failed as predicted (`:accept`
  ≠ `{:reject, conversion_failure}`) then deleted.
- **`52b997c`** `test/cure/compiler/macro_expansion_classic_soundness_test.exs` — transitional classic
  firewall, 6 tests, line-stripped verdict-equality. Negative control failed then deleted.
- **ZERO production delta confirmed** (`git status` showed only the 2 new test files; no `lib/**`) —
  this IS the empirical proof of TCB-delta-zero: macro expansion re-elaborates on BOTH pipelines with
  no code change. Full `mix test` **4111 passed / 2 skipped**, antigen 328/328, seeds/corpus untouched.

SP1 T8 Stage 5 DONE — Sonnet code review over the T8 test diff (`36a3289..HEAD`, two files),
converged CLEAN (2 consecutive clean, zero findings, no commits). Reviewer EXERCISED not just read:
parsed each macro_src to confirm the expansion is textually faithful to the hand-written body (proved
`bad`→`nonexistent_thing` genuinely expands to `{:variable,_,"nonexistent_thing"}` — rejection driven
by the EXPANSION, not a coincidental both-sides parse failure); traced `strip/1` (no over/under-strip);
confirmed async-safety (`Program.elaborate` Process-local; `compile_string`'s `Cure.M.beam` write is a
pre-existing inert last-write-wins convention, nothing reads it back); ran an adversarial 5th case
(`inc true` vs `true + 1`) — verdicts matched both pipelines. 12/12 pass across seeds {0,1,42,999};
`test/cure/compiler`+`test/cure/elab` together = 1481 passed. Confidence high.

**SP1 T8 COMPLETE** (all stages): dependent firewall `3a7383d` + transitional classic firewall
`52b997c`, plan `99b8be6`/`2f878af`/`36a3289`. The DONE-criterion clause "expands to well-typed Core"
is now permanently guarded on both pipelines with the zero-production-delta proof of TCB-delta-zero.

SP1 T7 Stage 2 DONE — plan committed at `docs/superpowers/plans/2026-07-12-macro-facility-sp1d-plan.md`.
Grounded LIVE (not assumed): capture bug PROVEN — `addtmp <e> becomes let tmp = 100 in e + tmp` +
`fn f(tmp) = addtmp tmp` expands to `let tmp = 100 in tmp + tmp` where the hole-substituted param `tmp`
is CAPTURED by the template's `let tmp` (computes 100+100 regardless of arg). Parser facts probed:
`<fresh g>` tokenizes `:lt id("fresh") id("g") :gt` (`fresh` not reserved); template parsed via
`parse_expr` at `parser.ex:4120`; `parse_prefix/1` (now at `:381`) has no `:lt` case, bare `:lt`
hits default `{:unexpected_token}` at `:560`; infix `<` never reaches prefix (comparisons safe); the
`:lbrace` case `:545` is the window-lookahead idiom to mirror; expansion at `parse_macro_use`/
`expand_rule`/`subst_holes` `:195-221`.

**Scoping:** T7 = the EXPLICIT `<fresh Name>` primitive (design §5's named mechanism, deterministic
gensym `name$N` via a `fresh_counter` in parser state; freshen BEFORE hole-subst so use-site material
is never freshened; walks meta too, mirroring the T8-review `subst_holes` fix). AUTOMATIC full hygiene
(auto-rename every template binder, no annotation — §5 headline) needs template scope analysis → deferred
to **T7b** own plan. `<capture>` escape also deferred. Two tasks: T1 parse `<fresh Name>` → `{:fresh_name,
meta,name}`; T2 freshen at expansion (red = the capture repro with `<fresh g>`; green = binder gensym'd,
param `g` uncaptured). TCB delta ZERO.

SP1 T7 Stage 3 DONE — plan hardened + committed `5c903d3` (4 passes, 2 clean). Reviewer verified live
(patched parser.ex, ran, reverted) and caught 3 real TEST-CODE defects that would have caused false
failures at execution:
- **HIGH:** `find_fresh/1` helper couldn't reach the template — a macro rule is stored as a plain Elixir
  MAP (`%{template:...}`), not an AST tuple, so the generic tuple-recursion never descends. Test could
  never go green. Fixed: added `defp find_fresh(%{template: t}), do: find_fresh(t)` clause.
- **MEDIUM:** freshening walker didn't mirror the real `subst_holes_meta_value`'s `is_tuple`/`is_list`
  split — a `<fresh>` inside a raw-list meta value (e.g. `with`'s `:parent_patterns`) would leak
  unrewritten. Fixed: added `collect_fresh_names_value`/`apply_freshening_value`.
- **LOW:** vacuous `refute match?({:fresh_name,_,_}, assign)` (outer tuple can't match) → replaced with
  `refute find_fresh(body)`.
Verified SOUND (no finding): capture-bug AST shape is EXACTLY as planned (byte-for-byte); `<fresh g>`
tokenization; `parse_prefix` has no `:lt` case + infix `<` non-interference; parse paths; determinism
(harvest phase-1 never expands, `active_macros` defaults `%{}`); `expand_rule/2` has exactly one caller.
**Executor: trust the hardened plan `5c903d3` — its test code is now live-verified.** The real capture-repro
expanded AST (for Task-2 assertions): `{:block,_,[{:assignment,[let: true,...],[{:variable,_,"tmp"},
{:literal,_,100}]}, {:binary_op,[operator: :+,...],[{:variable,[line:4],"tmp"}, {:variable,[line:3],"tmp"}]}]}`.

SP1 T7 Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `af005b0`** — `:lt` case in `parse_prefix/1` recognizing the `<fresh Name>` window
  (`:lt id("fresh") id(name) :gt`) → `{:fresh_name, meta, name}`; else keeps `{:unexpected_token}`.
  `test/cure/compiler/` 641 passed.
- **T2 `cddf534`** — `fresh_counter` on state; `expand_rule/3` runs `freshen` BEFORE `subst_holes`;
  `freshen`/`collect_fresh_names(+_meta/_value)`/`apply_freshening(+_meta/_value)` mint one deterministic
  gensym `name$N` per distinct fresh name, rewrite markers + plain refs, walk children AND meta+list-meta.
  The capture repro is FIXED: `addg <e> becomes let <fresh g> = 100 in e + g` + `f(g) = addg g` expands so
  the binder is `g$0` (freshened), the param `g` stays uncaptured, template ref = `g$0`, no leftover marker.
  `test/cure/compiler/` 642 passed / 1 skipped; `macro_use_test` (milestone-2) still green (freshen is
  identity for non-`<fresh>` templates); `mix compile --warnings-as-errors` clean. TCB delta ZERO.

SP1 T7 Stage 5 DONE — Sonnet code review over the T7 diff (`5c903d3..HEAD`), converged CLEAN (5 passes,
2 consecutive clean, NO code changes). Core logic VERIFIED correct via live probes: two use-sites of the
same macro mint distinct `g$0`/`g$1`; harvest phase-1 never expands (counter untouched); repeated parse of
identical source → byte-identical ASTs (determinism); multiple fresh names sorted+independent (`a$0`,`b$1`);
all refs of one fresh name converge on one gensym; nested `addg(addg(1))` distinct inner/outer; two macros
same fresh spelling don't collide; freshening traversal mirrors `subst_holes` exactly (children+meta+list-meta);
non-`<fresh>` templates byte-identical; comparisons `a < b` unaffected. Full suite 4113 passed / 2 skipped,
antigen 328/328, warnings-clean.

**SP1 T7 COMPLETE** (`af005b0`+`cddf534`): `<fresh Name>` explicit hygiene primitive prevents ACCIDENTAL
capture (the proven `let tmp` capture bug is fixed). Two gaps found + characterized (NOT fixed — deferred to
**T7b** by design):
- **Fresh-name = hole-name silent-drop:** `syntax m <e> becomes let <fresh e> = 0 in e` called `m(99)`
  silently drops `99` — freshen rewrites the template `e`→`e$0` before `subst_holes` (keyed on "e") can bind
  it → `let e$0 = 0 in e$0`, no error. Genuinely silently wrong. T7b must add a fresh∩hole-name collision
  diagnostic (reject at parse, or freshen-after-subst ordering).
- **Backtick-gensym spoofing:** `` `g$0` `` (backtick ident accepts arbitrary chars incl `$`) as a use-site
  arg to a macro's FIRST invocation collides with minted `g$0` → real capture. Fundamental limit of STRING
  gensyms; robust fix = Racket-style uncopyable scope marks (T7b). Note: a NON-backtick user cannot produce
  `$`, so accidental capture IS prevented; only deliberate exact-gensym backtick-spelling defeats it. Connects
  to the general backtick-spoof trap ([[anonymous-adts-landed]]).
- Minor pre-existing (not T7): a stray `<fresh h>` OUTSIDE a template parses to an unhandled `{:fresh_name}`
  node and `cure compile` fails exit-1 with no diagnostic — general unrecognized-node-type gap, not T7-specific.

**SP1 SCOPE (re-confirmed against program-doc SP1 definition + GATE — do NOT skip to SP2):** SP1 explicitly
includes, beyond the done milestone1/2/T7/T8: **Tier-1 literal rules** (T4), **import scoping + same-keyword
conflict error** §7 (T9), **two-pass name resolution** §6, and the **default error-machinery FLOOR** §2 —
wrong-arity/unknown-category macro uses must produce a DIAGNOSTIC, not a raw parser error (currently
`:macro_use_mismatch` is raw-ish). SP1 GATE: a Tier-1 AND a Tier-2 macro compile+expand+kernel-check, bad
uses give a default-machinery diagnostic, full `mix test` green. So SP1 is NOT near-done; jumping to SP2
(self-proving typed errors) would skip real SP1 scope. Architecture note (T9 grounding, probed): cross-module
resolution (`import_source_env`/`module_slice_env`, program.ex:699/799) runs at ELABORATION, but macro
expansion is at PARSE time — so imported-macro grammars need the PARSER to locate+parse imported modules
(couples parser to import resolution). T9 is the hard architectural piece; sequence it after the tractable T4
+ error-floor.

SP1 T4 Stage 2 DONE — plan committed at `docs/superpowers/plans/2026-07-12-macro-facility-sp1e-plan.md`.
**Key grounding correction (probed live):** NO lexer change needed — `500ms` ALREADY tokenizes
`[integer: 500, identifier: "ms"]` (`500 ms` identical; whitespace dropped). So T4 is PARSER-ONLY (lower
risk than the "numeric-suffix lexer" I'd assumed). Design fork resolved: it's a `literal` RULE KIND (base
§111/§194 `literal <n: Number> ms becomes Duration.ms(n)`), not a lexer unit-tag. A `literal` rule = leading
number-hole + `{:lit, suffix}` segment (reuses `parse_rule_segments`), but dispatches on a NUMBER use-site
(not a keyword). Two tasks: T1 parse `literal` rules (add `"literal"` clause to `parse_macro_rules/2` :4184;
`parse_literal_rule` skips the keyword, `suffix = first lit after hole`); T2 harvest by suffix into new
`literal_macros` state map + dispatch in `parse_prefix` `:integer`/`:float` (:386) → `maybe_literal_macro`
→ `expand_literal_rule` (binds number to hole, reuses `match_segments`/`expand_rule` so `<fresh>`+hole-subst
+T8 firewall apply). Anchors verified: `parse_macro_rules` only knows `"syntax"` today; `harvest_active_macros`
now guarded to `:syntax`-only + sibling `harvest_literal_macros`. TCB delta ZERO.

SP1 T4 Stage 3 DONE — plan hardened + committed `8b2ab36` (5 passes, 2 clean). Reviewer fixed a stale
line-number citation (`:integer`/`:float` at `:466-470` not `:386-390`), added a `:float` dispatch test + a
non-empty-map regression (`500 + 3` with `ms` macro defined), and TRACED suffix-consumption live (consumed
exactly once by `match_segments`, never double).

SP1 T4 Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `8c217da`** — `"literal"` clause in `parse_macro_rules/2` + `parse_literal_rule/1`/`literal_suffix/1` →
  `%{kind: :literal, keyword: nil, segments: [hole, {:lit,suffix}], suffix, template}`. 643 passed.
- **T2 `dfcf315`** — `literal_macros` state map seeded in authoritative `parse/2`; `harvest_literal_macros/1`
  (by suffix) + `harvest_active_macros/1` guarded to `:syntax`; `:integer`/`:float` dispatch →
  `maybe_literal_macro` → `expand_literal_rule` (binds number to hole, reuses `match_segments`/`expand_rule`).
  `500ms`→`Duration.ms(500)`, `3.5s`→`Duration.s(3.5)`; bare numbers + `500 + 3` unaffected. 647 passed /
  1 skipped, warnings-clean. TCB delta ZERO.
- **BUG CAUGHT BY TDD (flag for Stage-5 reviewer):** the hardened plan's harvester code had a latent
  `BadArityError` — the multi-clause inner `Enum.reduce` reducer `fn %{...} = rule -> ... ; _ -> acc end`
  dropped the accumulator param (a reducer needs `(element, acc2)`) and referenced the outer `acc`. Elixir
  doesn't catch mismatched anon-fn arity at compile time; the red test surfaced it immediately. Fixed to
  `fn %{...} = rule, acc2 when guard -> Map.update(acc2,...) ; _rule, acc2 -> acc2 end` in BOTH harvesters.
  This would have broken ALL parsing (harvest runs every parse) had it shipped — the Stage-3 review missed it
  (valid-looking multi-clause code), Stage-4 TDD caught it. Stage-5 should confirm the fix + look for similar
  arity issues.

SP1 T4 Stage 5 DONE — Sonnet code review over the T4 diff (`8b2ab36..HEAD`), converged CLEAN (2 passes,
NO fixes). Verified LIVE against a byte-for-byte pre-diff comparison worktree (`8b2ab36` snapshot): hot-path
`:integer`/`:float` dispatch byte-identical for EOF/index/list/negative/float/empty-map cases (the `{1,2,3}`
tuple-literal failure is PRE-EXISTING, not a regression); arity fix correct in both harvesters (no similar
latent mistakes); suffix/keyword collision deterministic (`500foo`→literal, bare `foo`→syntax, no crash);
reserved-word suffix inert; token consumed exactly once, multi-segment ok; malformed nil-suffix rules skipped;
two-phase harvest seeds `literal_macros` on authoritative state only, deterministic; `<fresh>` in a literal
template threads distinct gensyms (`x$0`/`x$1`); existing `syntax` rules had `kind: :syntax` pre-diff so the
guard is safe by construction. Full suite 647 passed. High confidence. (Minor cosmetic non-finding: the
`in ["Duration.ms","ms"]` test alternative's `"ms"` branch is dead — always `"Duration.ms"`; left as-is.)

**SP1 T4 COMPLETE** (`8c217da`+`dfcf315`, plan `a2c6d10`/`8b2ab36`). Tier-1 `literal` units rule live:
`500ms`→`Duration.ms(500)`, `<fresh>`+T8-firewall apply.

**SP1 GATE STATUS** (program-doc): Tier-1 ✓ (T4) + Tier-2 ✓ (milestone-2 `syntax`) + expansions kernel-check ✓
(T8 firewall) — the ONE remaining GATE-CRITICAL piece is the **default error-machinery floor (§2)**:
"wrong-arity/unknown-category macro uses produce a (default-machinery) DIAGNOSTIC, not a raw parser error."
Currently a bad macro use emits raw `{:macro_use_mismatch, kw, :at_segment, progress, l, c}` /
`{:expected, :syntax_rule, …}` tuples — must become structured diagnostics with a MESSAGE, using the
syntax-parse machinery (failure-set → maximal-by-PROGRESS [already threaded from T6b] → report
message/context/at/within — see `macros/2026-07-12-racket-syntax-parse-comparison.md`). This is the SP1
FLOOR (default messages); SP2 adds the type-ENFORCED author-defined `Diagnosis`.

**OPERATOR DECISION (2026-07-12): Elm-style error rewrite — DON'T stage, PARK.** Operator asked whether to
stage the macro error work behind an Elm-style error-system rewrite. Decided NO: the existing renderer
(`Errors.format_error/2` + `format_diagnostic/5` at `errors.ex:1730` + `suggest/2`/`levenshtein` typo hints) is
already partway to Elm (structured `severity: category` / `--> file:line` hyperlink / `| message`). Every
diagnostic routes through the ONE `format_diagnostic`, so a future Elm rewrite (source snippets + carets +
regions) upgrades ALL errors — macro included — for free; building the floor on it now is forward-compatible,
not throwaway. A full Elm rewrite is cross-cutting (every error site), its own initiative — PARKED at
`docs/superpowers/specs/diagnostics/2026-07-12-elm-style-error-rendering-PARKED.md` (committed `82d64a8`), with a
forward-compat contract the floor obeys (route through the central renderer; message content in the
`format_error` clause).

SP1 §2 error-floor Stage 2 DONE — plan committed at `docs/superpowers/plans/2026-07-12-macro-facility-sp1f-plan.md`.
Grounded: the RAW tuples (fall to catch-all `errors.ex:374`) are `{:macro_use_mismatch, …}` (single emit site
`parse_macro_use/1` `parser.ex:232`, `rule` in scope) + `{:malformed_hole, …}` (`parser.ex:4358`);
`{:expected, :syntax_rule/:becomes}` already renders (`errors.ex:86`, not raw). Two tasks: T1 ENRICH
`:macro_use_mismatch` to `{…, keyword, expected, got, line, col}` (`expected` = `{:literal,w}`/`{:hole_kind,k}`/
`:nothing_more` via `Enum.at(rule.segments, progress)`) + add a friendly `format_error` clause (routes through
`format_diagnostic`; updates the T6b shape-assertion in `macro_use_test.exs` — legit shape evolution); T2 a
`:malformed_hole` clause explaining `<name: Kind>`. TCB delta ZERO.

SP1 §2 error-floor Stage 3 DONE — plan hardened + committed `2d9e7e9` (6 passes, 2 clean). Reviewer
live-verified the load-bearing facts: for `say goodbye` vs rule `say hello` the emitted tuple is
`{:macro_use_mismatch, "say", :at_segment, 0, 4, 16}` → `progress = 0`, `Enum.at(segments, 0) = {:lit,"hello"}`
(plan's indexing EXACT); catch-all `errors.ex:374` = `format_diagnostic("error","compilation error",file,0,
inspect(error))` so the raw tuple string literally contains `:macro_use_mismatch`/`:malformed_hole` (both
`refute` assertions genuinely red pre-fix). Two findings fixed: (a) `macro_expected_at/2`'s `{:hole_kind,k}`
+ `:nothing_more` branches are DEAD (a `{:hole,_}` segment never fails in `match_segments` — it unconditionally
parses+binds — so only `{:lit,w}` mismatch reaches the fn; documented so the implementer doesn't chase an
impossible test); (b) Architecture prose promised `suggest/2` hints neither clause uses → corrected to
"out of scope for this floor". `:macro_use_mismatch` confirmed SINGLE emit site; T6b shape-assertion the ONLY
test coupled to the old shape.

SP1 §2 error-floor Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `e926038`** — enriched `:macro_use_mismatch` emit (`{…, keyword, macro_expected_at(rule,progress),
  macro_got_desc(t), line, col}`) + `format_error` clause → "the `say` macro expected `hello` here, but found
  `goodbye`"; updated the T6b shape-assertion. `macro_expected_at/2`'s non-`{:lit}` branches kept (dead-but-total).
- **T2 `34fb3ab`** — `:malformed_hole` clause → "a macro hole is written `<name: Kind>` …". Both route through
  `format_diagnostic` (parked-Elm forward-compat contract honored). 649 parser tests, warnings-clean.
- **Execution wrinkle fixed:** placing `defp article/1` BETWEEN the new `format_error` clause and the catch-all
  split the `format_error/2` clause group → `--warnings-as-errors` "clauses not grouped". Moved `article/1`
  AFTER the catch-all (clauses contiguous). A reminder: non-adjacent same-name/arity `def` clauses warn.

**SP1 GATE MET** (pending Stage-5 review): Tier-1 ✓ (T4) + Tier-2 ✓ (`syntax`) + expansions kernel-check ✓
(T8 firewall) + default-machinery diagnostics ✓ (this floor). TCB delta ZERO throughout.

SP1 §2 error-floor Stage 5 DONE — Sonnet code review over the floor diff, converged (4 finding-passes +
2 clean). Found + fixed FOUR real `macro_got_desc/1` defects, all red-test-first (the "found X" desc
corrupting `format_diagnostic`'s single-line message): `1fe7ef8` structural tokens (newline/indent/dedent
splice raw values), `98d4957` `nil` keyword → empty backticks, `9846f65` `:char` → codepoint not spelling,
`f421887` ROOT CAUSE = no control-char sanitization → all descs now route through `escape_for_diagnostic/1`.
Plus 2 test-only hardening commits (`0a94a90` direct-tuple coverage of the dead-but-total `{:hole_kind}`/
`:nothing_more` render arms; `74c3a4b` dedent case via real parse). Verified: `macro_expected_at` reachability
claim correct (hole segments never fail in `match_segments`); T6b assertion matches the real tuple; clause
ordering + grouping clean; no other consumer of the old shape. 8 floor tests + all macro suites green,
warnings-clean, antigen untouched.

**OUT-OF-SCOPE FINDING (reviewer, pre-existing — fix before SP1 gate is honestly met):** `match_segments/4`'s
`{:lit, w}` clause `to_string(tok.value) == w` (T6b code, `parser.ex` ~line 190s) CRASHES
(`Protocol.UndefinedError`/`ArgumentError`) when a use-site token's value is a tuple/list — a `:regex` token
value is `{body, flags}`, a `:string_interpolation` value is a list of parts. So `say /foo/` or `say "x#{y}"`
at a macro mismatch THROWS instead of producing a diagnostic — worse than the raw error the gate forbids.
Small fix: guard the comparison so a non-binary token value simply doesn't match (fall to the `{:error,
progress}` mismatch path → the friendly diagnostic). Pre-dates the floor diff (old `:at_segment` code hit it
too); it's in T6b's `match_segments`, not the error-floor.

`match_segments` non-scalar-token crash FIXED `eb5c70c` (red→green): reproduced live — `say ~r/foo/`
(:regex value = `{body,flags}` tuple) and `say "hi #{name}"` (:string_interpolation value = list) CRASHED
`to_string/1` in BOTH the lit-match (`match_segments`) and the got-desc (`macro_got_desc_raw`). Fixed:
`lit_token_matches?/2` (only scalar binary/atom/number values compare; structured → no-match → mismatch path)
+ `macro_got_desc_raw` clauses naming :regex/:string_interpolation/any structured value. (Clause-grouping
warning hit again — moved `lit_token_matches?` after the `match_segments` group.) 657 parser tests, warnings-clean.

## ═══ SP1 COMPLETE ═══ (Stage 6 green: full `mix test` = 4128 passed / 2 skipped, 3 doctests, antigen 328/328)
SP1 (minimal facility, Tiers 1-2) gate MET end-to-end:
- **Tier-1 literal units** ✓ (T4 `8c217da`/`dfcf315`): `500ms`→`Duration.ms(500)`.
- **Tier-2 hygienic `syntax` templates** ✓ (milestone 1 front-end + milestone 2 use-site expansion: `c381e7a`
  `8f07931` `77cbd6d` `4295479` `d66bf57` `0bd320f` `94c33a6` `6e01715`).
- **`<fresh Name>` hygiene** ✓ (T7 `af005b0`/`cddf534`): capture-free template binders.
- **Expansions kernel-check** ✓ (T8 firewall `3a7383d`/`52b997c`): macro output re-elaborated identically to
  hand-written — TCB delta ZERO proven.
- **Default error-machinery floor** ✓ (§2 `e926038`/`34fb3ab` + review fixes `1fe7ef8`/`98d4957`/`9846f65`/
  `f421887` + crash fix `eb5c70c`): bad macro uses render friendly diagnostics, never raw tuples OR crashes.
- Two-phase parse (harvest local `macro` defs → `active_macros`/`literal_macros`) ✓. All TCB delta ZERO.

**Deferred SP1 "Includes" (NOT gate-blocking; post-gate enhancements):** T9 (import scoping §7 + two-pass
name resolution §6 — cross-module macros, the hard parser/import-resolution lift), T7b (automatic full
hygiene + the fresh∩hole & backtick-spoof gaps + `<capture>`). Parked: Elm-style error rendering (`82d64a8`).

## ═══ SP2 STARTED ═══ (self-proving headline; large → sliced)
SP2 = "Tier-3 + self-proving Mechanisms 1 & 3" decomposes into slices (SP1 done). Full SP2 scope:
**M1** exhaustive `explain` over derived+extensible `Diagnosis` (`missing_diagnosis`) [self-proving §3];
**M3** required per-rule `example … expands …` (`rule_unpinned` + example-mismatch) [§5]; **Tier-3** `computed
by fn(...)` total compile-time Cure + `check … else fail` + author `fail C(args)` [§3.4]. GATE (all slices):
the 3 macro-compile errors fire on red fixtures / absent on green; example expansions kernel-check; suite green.

Grounding done (read self-proving §3.1-§3.4 + §5 + program-doc SP2; probed tokenization): `explain` = soft-kw
identifier; `Duration =>` = `identifier`+`:fat_arrow`; `keyword "w"` = `identifier`+`string`. `Diagnosis` is
DERIVED from grammar: one point per typed hole (`{:hole_kind, Cat}`) + per literal (`{:keyword, w}`). Key design
decision RESOLVED: the obligation CHECKS run in a NEW frontend module `Cure.Compiler.MacroValidate` (TCB-zero),
NOT the parser — so SP1's explain-less test macros don't break (this slice does NOT wire the check into the
compile pipeline; wiring + pinning SP1 macros is a later slice).

SP2 slice-1 (M1 structural) Stage 2 DONE — plan committed at `docs/superpowers/plans/2026-07-12-macro-facility-sp2a-plan.md`.
Two tasks: T1 parse `explain` blocks → `%{kind: :explain, clauses: [%{point, body}]}` entry in `{:macro_def}`
rules (harvest ignores non-syntax/literal kinds); T2 `MacroValidate.check_explain_exhaustive/1` derives structural
points, checks coverage, emits `{:missing_diagnosis, uncovered}` + a friendly `format_error` clause. TCB delta ZERO.

SP2 slice-1 Stage 3 DONE — plan hardened + committed `8c4ab17` (3 passes, 2 clean). Reviewer patched the
plan's code into the tree + ran its own tests, fixing 3 findings:
- **CRITICAL:** `derive_points` only walked `rule.segments`, but a `:syntax` rule's DISPATCH KEYWORD (`every`)
  lives in the separate `keyword` field, NOT segments (probed: `%{kind: :syntax, keyword: "every", segments:
  [hole: …]}` — zero `{:lit}` for `every`). So the headline example derived ZERO keyword points → the check
  would pass vacuously. Fixed `derive_points` to special-case `%{kind: :syntax, keyword: kw}` → `{:keyword, kw}`.
- `parse_explain_point/1` had no fallback → `CaseClauseError` crashed the whole parse on a malformed point
  (`=> "x"`). Added total fallback (`add_error {:expected, :explain_point, …}` + non-advancing recovery) + a red test.
- Added "Tests immutable once green" to Global Constraints (matched sibling plans).
- CONFIRMED SOUND (no change): the indented `explain`-body parse works — `:indent` → `parse_block` unwraps a
  single-statement body to the bare expression; the clause loop lands on the next point/dedent correctly.

SP2 slice-1 (M1 structural) Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `f3fb1f1`** — `parse_explain_block/1`/`parse_explain_clauses/2`/`parse_explain_point/1` (with the total
  malformed-point fallback → `{:expected, :explain_point, …}` not a crash); `explain` dispatch in
  `parse_macro_rules/2` → `%{kind: :explain, clauses: [%{point, body}]}` entry. 659 parser tests.
- **T2 `8166c25`** — `lib/cure/compiler/macro_validate.ex`: `check_explain_exhaustive/1` derives structural
  points (holes + literals + the `:syntax` rule KEYWORD field per the Stage-3 CRITICAL fix), checks coverage,
  emits `{:missing_diagnosis, uncovered}`; `format_error` clause + `describe_point/1` (after catch-all). The
  "no explain block" test confirms BOTH `{:hole_kind,"Duration"}` AND `{:keyword,"every"}` are reported missing
  — the keyword-field fix works. 662 parser tests, warnings-clean. TCB delta ZERO.

**M1 structural mechanism LIVE (unwired):** a macro whose `explain` omits a failure point →
`MacroValidate.check_explain_exhaustive` returns `{:missing_diagnosis, [...]}` rendering a friendly diagnostic.
Not yet invoked by the compile pipeline (SP1 macros have no `explain`) — the wiring slice adds that.

SP2 slice-1 Stage 5 DONE — Sonnet code review over the diff, converged CLEAN (3 passes, NO defects, no code
changes). Verified LIVE: multi-rule + literal-rule (`keyword: nil` correctly skips keyword point; suffix+hole
derived) + trailing-literal derivation all correct; dedup deterministic (identical output twice; shared
hole-kind → one point); spurious explain clause ignored (matches design §3.2 exhaustiveness-only intent);
`covered?/2` total (only 2 point shapes producible); **malformed-point recovery tested vs 8 hostile inputs
under a 5s timeout — NONE hung** (`parse_expr` always consumes ≥1 token → loop progresses to dedent/eof);
empty explain block clean; `:explain` entry skipped by both harvesters + doesn't break expansion (`say hello`
still expands). Full `mix test` 4133 passed / 2 skipped, antigen 328/328, warnings-clean. High confidence.

## ═══ SP2 slice 1 (M1 structural exhaustive-explain) COMPLETE ═══
`f3fb1f1` parse explain + `8166c25` `MacroValidate.check_explain_exhaustive/1` + `missing_diagnosis` render.
A macro that omits a failure-point description → structured `missing_diagnosis` diagnostic. TCB delta ZERO.
Standalone (unwired) by design; the wiring slice enforces it in real compiles.

SP2 slice-2a (M3 presence, `rule_unpinned`) Stage 2 DONE — plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp2b-plan.md`. **Split M3 into 2a (presence) + 2b
(expansion-equality), since the α-renaming comparator + mini-expansion is substantial.** Grounded (probed
tokenization + §5.1/§5.2): `example`/`expands` = soft-kw identifiers; the `example` line is INDENTED under the
`syntax` rule (attach point = `parse_macro_rule` after `parse_expr` template); `expands : <Type>` = type-only
pin. Slice 2a = 2 tasks: T1 parse `example <use-site> expands <expected>` sub-blocks → capture use-site as RAW
TOKENS (names the macro's own keyword, can't expand at def-parse) + expected AST `{:expansion,ast}`/`{:type,ast}`,
attach `examples: [...]` to the `:syntax` rule map; T2 `MacroValidate.check_rules_pinned/1` → `{:rule_unpinned,
[keyword]}` for syntax rules with no example + `format_error` clause. `:literal` rules exempt (design §5.1 says
"every syntax rule"). TCB delta ZERO, standalone (unwired).

SP2 slice-2a Stage 3 DONE — plan hardened + committed `9617d16` (3 passes, 2 clean). Reviewer LIVE-VERIFIED
the highest-risk item (patched Task-1 code into real parser.ex, inspected AST): the indented-example attach
works — after the template's `:newline` the next token is `:indent`(4), `skip_macro_trivia` stops at it, the
`:indent` branch parses the example + `expect_dedent` consumes the inner dedent, leaving `parse_macro_block`'s
own `expect_dedent` the outer one; a TWO-rule source (`a` w/ example + sibling `b`) parses BOTH in order (`b`
as normal sibling with `examples: []`, not swallowed). Same indent/consume/`expect_dedent` idiom as
`parse_macro_block`/`parse_explain_block`. Only fix: stale `errors.ex:398` citation → content-anchored (catch-all
is ~line 409-411). Confirmed `examples: []` key doesn't break existing tests (they use `%{kind: :syntax}`
pattern-match, not full-map equality); `collect_until_expands` terminates; `expands : Type` branch correct.

SP2 slice-2a (M3 presence) Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `b7836c3`** — `parse_rule_examples/1`/`parse_example_lines/2`/`parse_one_example/1`/`collect_until_expands/2`;
  `example <use-site> expands <expected>` sub-blocks attach `examples: [%{use_site: [tokens], expected:
  {:expansion,ast}|{:type,ast}, line}]` to the `:syntax` rule map. 665 parser tests (the new `examples: []` key
  broke nothing, as the reviewer predicted).
- **T2 `15c36fc`** — `MacroValidate.check_rules_pinned/1` → `{:rule_unpinned, [keyword]}` for unexampled syntax
  rules (mixed-macro test: only `b` reported); `format_error` clause. 668 parser tests, warnings-clean. TCB delta ZERO.
- (Wrinkle: a background formatter kept re-touching `parser.ex` timestamps triggering stale Edit-state errors;
  `git status` showed parser.ex clean vs HEAD so content was intact — resolved by re-reading before editing.)

**M3 presence LIVE (unwired):** a syntax rule with no `example` → `check_rules_pinned` returns
`{:rule_unpinned, [...]}` rendering a friendly diagnostic. Standalone, same as M1 — the wiring slice enforces it.

SP2 slice-2a Stage 5 DONE — Sonnet code review over the diff, converged CLEAN (6 passes, NO defects, no code
changes). Verified LIVE all 8 items: multiple examples + syntax/literal/explain siblings after an example block
parse correctly (no dedent-swallow); missing-`expands`/empty-use-site/dangling — no crash/hang; `expands :ok`
correctly captured as `{:expansion, atom}` NOT a type pin (lexer makes `:ok` an `:atom`); `expands : Effect(Unit)`/
`List(Int)` full-type captured; `check_rules_pinned` exempts `:literal`-only macros (design §5.1 syntax-only);
M1+M3 checks coexist on one macro; use-site expansion unaffected. 668 tests, warnings-clean. High confidence.
- **Noted (not a bug, future polish):** an `example` line indented under a `:literal` rule → cascade of
  `{:expected, :syntax_rule}` errors (pre-existing one-token recovery), not a clean "literal rules take no
  example" diagnostic and not a crash. Out of scope. Also `expands :Int` (colon+uppercase, no space) lexes as
  atom `:Int` not a type pin — pre-existing whitespace-sensitive lexer behavior.

## ═══ SP2 slice 2a (M3 presence, `rule_unpinned`) COMPLETE ═══
`b7836c3` parse examples + `15c36fc` `check_rules_pinned/1`. Two of SP2's 3 gate errors now have live (unwired)
checks: **M1 `missing_diagnosis`** ✅ + **M3 `rule_unpinned`** ✅. TCB delta ZERO.

## OPERATOR DESIGN DECISION (2026-07-12): SP3 generator architecture — `Generator` typeclass + middle-path engine
Full spec: `docs/superpowers/specs/tooling/2026-07-12-generator-typeclass-pbt-architecture.md`. Decided across a design
session: (1) a `Generator(a)` TYPECLASS with stdlib conformance + `deriving` = the user-facing PBT magic
(`forall` on any type, generator auto-resolved) — lives in Cure `Std.Gen`/`Std.Test`, RUNTIME, unaffected by
any SP3 engine choice. (2) **MIDDLE PATH (Hegel pattern), chosen "for now":** separate ENGINE (drive-loop +
shrink + example-DB) from DOMAIN (the one shared `Generator` typeclass). SP3's macro fuzzer = compile-time
Antigen (host engine) invoking the SAME Cure `Generator` instances to fill typed holes → assert each expansion
elaborates. User PBT = `Std.Test` at runtime. ONE generator system, two runners by phase. REJECTED: reimplement
Hypothesis-in-Cure (Hegel's warned-against waste) AND literal-Hegel external-Python-Hypothesis server (breaks
self-contained BEAM toolchain). (3) **Phase 2 (later, operator: "rewrite on top of a ported conjecture"):** port
Hypothesis's choice-sequence CONJECTURE model → internal/free composable shrinking for every conforming type
(incl. derived), + example-DB unified with Antigen's corpus/replay; re-base both runners; `Generator` interface
survives unchanged. Enabler = SP2 Tier-3 (run Cure gens at compile time) + SP4 reflection (Code-hole gen) —
already SP3's prereqs, no reorder. OPEN Qs to verify before the foundation slice: Antigen's current shrinking
model; can the host engine invoke a Cure `Generator` at compile time; how much `deriving` is built; `Gen(a)`
repr that survives the re-base. Committed as a spec (this firing).

SP2 slice-2b (M3 expansion-equality, `example_mismatch`) Stage 2 DONE — plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp2c-plan.md`. Grounded LIVE: expansion of `every 500` =
`{:function_call, [name: "Timer.repeat", line:2, col:50], [{:literal, [subtype: :integer, line:3,col:16], 500}]}`
vs standalone `Timer.repeat(500)` — differ ONLY in `:line`/`:col` (semantic meta name/subtype identical). So
the α-comparator = **strip :line/:col from all meta + collapse `<fresh>` gensym suffix (`x$0`→`x`), then `==`**.
Two tasks: T1 `Parser.expand_example/2` (public driver — seeds `active_macros`/`literal_macros` from the rules
via a synthetic `[{:macro_def,[],rules}]`, builds a `%Parser{}` state on `use_site_tokens ++ [eof]`, calls
`parse_expr(state,0)` → the same expansion a real use-site gets, nested literal/`<fresh>` included); T2
`MacroValidate.check_examples/1` + `normalize/1` (strip_pos + degensym, mirrors subst_holes meta walk) →
`{:example_mismatch, [%{keyword,expected,actual}]}` + render clause. Scope: `{:expansion,ast}` pins only;
`{:type,ast}` type-only pins (§5.2, needs `Program.elaborate`) DEFERRED. Honest limit noted: gensym-suffix
strip is a first-cut α, not capture-aware de Bruijn. TCB delta ZERO, unwired.

SP2 slice-2b Stage 3 DONE — plan hardened + committed `16e0c2a` (3 passes, 2 clean). Reviewer patched the code
into the tree + ran it, catching a CRITICAL `normalize/1` bug: the two-clause version only stripped `:line`/`:col`
from nodes whose 3rd element is a LIST — but `:literal` nodes carry a SCALAR value (`{:literal, [subtype,line,col],
500}`), so they fell to the catch-all UNCHANGED, positions un-stripped → `check_examples` would reject virtually
every correct example (`2/4` tests failed live). Fixed with a third `normalize/1` clause for scalar-valued nodes
(`{t, meta, value} when is_list(meta)`); re-verified `4/4` + `672 passed`. Also confirmed live: `expand_example`
genuinely drives expansion (`every 500`→`Timer.repeat(500)`; nested `every 500ms`→`Timer.repeat(Duration.ms(500))`);
`normalize` keeps name/subtype/scope (so `f(1)`≠`g(1)`) while dropping positions; `$` not a legal Cure ident char
(degensym can't false-positive); the `for`-comprehension is valid; no-example/`{:type}` rules skip cleanly.

SP2 slice-2b Stage 4 DONE — both tasks executed inline TDD (red→green), committed:
- **T1 `e9acf58`** — `Parser.expand_example/2` (public): seeds `active_macros`/`literal_macros` from a synthetic
  `[{:macro_def,[],rules}]`, parses `use_site ++ [eof]` via `parse_expr` → the real expansion. 669 parser tests.
- **T2 `f76de41`** — `MacroValidate.check_examples/1` + `normalize/1` (3-clause, scalar-node fix) →
  `{:example_mismatch, [%{keyword,expected,actual}]}`; `format_error` clause. `every 500 expands Timer.repeat(500)`
  ✓, `…expands Timer.repeat(999)` → mismatch, position-modulo match ✓. 672 tests, warnings-clean. TCB delta ZERO.

**M3 FUNCTIONALLY COMPLETE (unwired):** `rule_unpinned` (2a) + `example_mismatch` (2b). SP2 now has live checks
for ALL THREE gate errors: `missing_diagnosis` (M1) + `rule_unpinned` + `example_mismatch` (M3).

SP2 slice-2b Stage 5 DONE — Sonnet code review over the diff, converged (6 passes; 1 finding-pass + 5 clean).
Found + fixed TWO real defects red-test-first:
- **CRITICAL `1fdc661`** — `<fresh>`-BINDER false mismatch: a `<fresh Name>` marker parses to `{:fresh_name,
  meta, name}` with NO `scope: :local` key (freshen reuses that meta when rewriting to `{:variable,meta,gensym}`),
  but a hand-written pin's identifier ALWAYS carries `scope: :local` — so `normalize` comparing full variable meta
  made every correctly-pinned `<fresh>`-as-binder example spuriously mismatch, defeating the headline `<fresh>`
  self-proving case. Fixed: `normalize` drops `:variable` meta ENTIRELY (α-equivalence for a reference = its
  degensym'd name alone).
- **`3cb7bd2`** — `expand_example` discarded the parser state, silently swallowing trailing use-site tokens (a
  typo'd extra word after the hole), so a garbage example could check `:ok`. Fixed: check `peek(state)` post-parse,
  wrap in a `{:example_use_site_not_fully_consumed,…}` sentinel when tokens remain.
- Confirmed sound: `normalize` handles match-arm-with-guard (meta-embedded ASTs stripped via `normalize_meta_value`);
  multi-example/multi-rule ordering; determinism; `{:type}` pins skip; independent from M1/M3-presence checks.
  674 passed, warnings-clean, antigen untouched. High confidence.

## ═══ SP2 slice 2b (M3 expansion-equality, `example_mismatch`) COMPLETE ═══
`e9acf58` `expand_example` + `f76de41` `check_examples`/`normalize` + review fixes `1fdc661`/`3cb7bd2`.
**M3 COMPLETE** (`rule_unpinned` presence + `example_mismatch` equality). SP2 now has live (unwired) checks for
ALL THREE gate errors: `missing_diagnosis` (M1) ✅ + `rule_unpinned` + `example_mismatch` (M3) ✅. TCB delta ZERO.

**SEQUENCING CORRECTION (this firing, grounded):** the planned standalone "slice 2c = example kernel-check +
`{:type}` pins" is FOLDED INTO THE WIRING SLICE instead. Probed live: a self-contained expansion (`x + x`)
elaborates OK via `Program.elaborate`, but a real example's expansion referencing the macro's target functions
(`Timer.repeat(500)`) fails `:unknown_global` in isolation — the macro's IMPORT CONTEXT isn't in scope. So a
standalone example-kernel-check would false-reject nearly every real macro; kernel-checking examples needs the
elaborate-in-module-env machinery the wiring slice builds anyway. → next = **Tier-3** (independent, headline).

SP2 Tier-3 slice 1 (parse `computed by`) Stage 2 DONE — plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp2d-plan.md`. Tier-3 (`computed by` = expansion COMPUTED by a
compile-time Cure elab fn over quoted input, vs `becomes`'s template subst — design §3, tier row 3) decomposes:
**slice 1 (this) parse `computed by <fn>`** → `%{kind: :computed, keyword, segments, elab, examples}` (NOT
harvested → inert until execution); then **quoted-AST `Syntax` value model** (§3, `quote`/`$()`); then
**compile-time elab EXECUTION** (quote input → run elab staged-on-host → splice output; K3 firewall re-checks
output, TCB-zero — the big one); then **`check … else fail C`** (§3.4, ties to M1); then computed-rule example
checks; then the WIRING slice. Grounded: `computed by build_it` = 3 identifiers; `parse_macro_rule` branches on
verb after `parse_rule_segments`; `:computed` kind excluded by all harvest/MacroValidate filters (auto-inert).
One task: split the verb branch → `parse_becomes_rule`/`parse_computed_rule`. TCB delta ZERO.

SP2 Tier-3 slice-1 Stage 3 DONE — plan hardened + committed `3c3fed7` (5 passes, 2+ clean). Reviewer patched
the Task-1 code into a scratch build + RAN it, catching a CRITICAL bug the plan missed: `parse_rule_segments/2`
swallows `computed`/`by` as `{:lit,…}` SEGMENTS before the verb branch runs (its stop clause matched only
`"becomes"`), so the `%Token{value: "computed"}` branch NEVER fired — the plan's own tests 1+3 failed live
(`{:expected,:becomes,:got,:newline,…}`). FIX folded in: extend `parse_rule_segments/2` stop-word to
`v in ["becomes","computed"]` (shared helper; `parse_literal_rule` never uses `computed` so safe). With it,
all 3 tests pass + `test/cure/compiler/` 677 + soundness 6, zero regressions. Also verified: `parse_expr(state,0)`
captures the elab ref without over-consuming (bare + dotted + example-after + last-rule); `:computed` inert
(harvest/MacroValidate all exclude it); `by`-missing recovers cleanly; example sub-blocks attach.

SP2 Tier-3 slice-1 Stage 4 DONE — Task 1 (only task) executed inline TDD (red→green), committed **`ce62b17`**:
`parse_macro_rule/1` splits the tier verb after `parse_rule_segments` → `parse_computed_rule/4` (new,
`%{kind: :computed, keyword, segments, elab, examples}`) / `parse_becomes_rule/4` (extracted, unchanged);
`parse_rule_segments/2` stop-word extended to `v in ["becomes","computed"]` (the load-bearing fix). `computed by
build_it` → `:computed` rule capturing `{:variable,_,"build_it"}` elab; `:computed` inert at use-sites (parses
as bare var, not harvested); `becomes` rules byte-identical. 677 parser tests / 1 skipped, warnings-clean. TCB
delta ZERO. Parse-only — a computed macro can't EXPAND yet (execution is a later slice).

SP2 Tier-3 slice-1 Stage 5 DONE — Sonnet code review over the diff, converged (4 passes, high confidence). One
minor finding: the new `computed` reserved tier verb means a `literal`/`syntax` rule can no longer match the
literal word `computed` as a token (exact parity with the pre-existing `becomes` restriction; nothing in-tree
relies on it) → doc-only comment `a23fb70`. Verified SOUND via real probes: `becomes`-extraction byte-identical
(zero-hole/hole+lit/missing-becomes); `:computed` inert + excluded by ALL harvest/MacroValidate filters (probed
against a real `:computed`+unpinned-`:syntax` macro — no cross-contamination); malformed `computed`/`by`/EOF
recover cleanly; `parse_expr` elab-capture no over-consume. 677 tests / 58 macro tests, warnings-clean, antigen
untouched.

## ═══ SP2 Tier-3 slice 1 (parse `computed by`) COMPLETE ═══
`ce62b17` (verb-branch split + segment stop-word) + `a23fb70` (doc). Tier-3 front-end live: `syntax … computed
by <fn>` → `%{kind: :computed, elab}`, inert until execution. TCB delta ZERO.

SP2 Tier-3 EXECUTION ARCHITECTURE GROUNDED (this firing) — design note committed:
`docs/superpowers/specs/tooling/2026-07-12-tier3-computed-by-execution-design.md`. Decisions (driver, revisable):
- **A: execute by ELABORATE + NORMALISE, not compile-and-load.** Elaborate the elab ref → apply to the quoted
  input → `Cure.Core.Normalise.whnf`/normalise → the normal form IS the expansion. Reuses the trusted normaliser
  (verified callable), Cure-native, terminates (elabs are total), TCB-ZERO (normaliser unchanged; output re-elaborated).
- **B: GENERIC `Std.Syntax` value FIRST**; typed per-category derived records (§3 ideal) DEFERRED as ergonomic
  sugar. `Syntax = Node(tag, children) | Leaf(tag, value)` reflecting the parser `{tag,meta,children}` node; a
  `to_syntax`/`from_syntax` reflection bridge (Elixir) round-trips (positions can drop — K3 re-elaborates output).
- **C: `:computed` expands at ELABORATION time, NOT parse time** (needs elaborator+normaliser, absent at parse).
  Parser harvests `:computed` + emits a deferred `{:computed_use, meta, [elab, input_syntax]}` node; a compile-time
  expansion PASS in `lib/cure/elab/*` (untrusted → TCB-zero) walks + expands them. Phase distinction from Tier-1/2.
Probed: normaliser `whnf` callable; NO existing Syntax/quote/staging infra (greenfield); elaborator touch OK (untrusted).

SP2 Tier-3 slice-2 (`Std.Syntax` value + reflection bridge) Stage 2 DONE — plan committed at
`docs/superpowers/plans/2026-07-12-macro-facility-sp2e-plan.md`. Grounded live (found + corrected a design flaw):
meta is LOAD-BEARING (node names/operators/subtypes live in meta, not just tag/children) → `Syntax` must carry an
`attrs` field, else reflection loses function names. ADT: `Syntax = Node(Atom, List(Attr), List(Syntax)) |
Leaf(Atom, List(Attr), SynLit)`, `Attr = KV(Atom, SynLit)`, `SynLit = SInt|SFloat|SStr|SBool|SAtom|SOpaque`
(exotic regex/interp `third` → SOpaque, round-trips shape-only). Template = `Std.Json` `type Value` (nested
positivity proven). Two tasks: T1 `lib/std/syntax.cure` (elaborates-test mirrors `json_elaborates_test`); T2
`Cure.Compiler.MacroSyntax.to_syntax`/`from_syntax` Elixir bridge over a mirror repr, lossless round-trip
(up to line/col). TCB delta ZERO. NO execution (slice 3).

**OPERATOR STEER (2026-07-12) — elab-facing reflection API = TYPED derived record, NOT stringly `field`.**
Operator asked: parameterise `Syntax` over the definition so an elab writes `a.name` (typed) not
`a.field("name")`. YES — that's design §3's typed per-category derived records. From a rule's holes, synthesise
`rec RuleSyntax { <hole>: Syntax(<Kind>), … }` (`...` group → `List` of sub-record), thread as the elab's param
type → `a.name` compile-checked, self-documenting. The generic `Syntax` VALUE (slice 2) is the SUBSTRATE a typed
field holds underneath → slice 2 UNCHANGED + un-wasted; what's rejected is shipping a generic `field` accessor as
the elab API. Recorded in the Tier-3 execution design note (Decision B + slice 6, elevated to "land with/right
after execution"). Type-derivation-from-grammar = the new machinery (leans on landed dependent records).

SP2 Tier-3 slice-2 Stage 3 DONE — plan hardened + committed `ae0fa62` (4 passes, 2 clean, high confidence).
Reviewer patched the exact code into scratch + RAN it, fixing 3 grounding errors: (1) CRITICAL — the regex test
asserted tag `:regex`, but `~r/foo/` parses to `{:literal, [subtype: :regex], {body,flags}}` (tag `:literal`);
test fixed to `{:syn_leaf, :literal, attrs, :s_opaque}` + `{:subtype,{:s_atom,:regex}}` attr. (2) `@group(:syntax)`
isn't a recognized Preload group → `@group(:core)` (like sigma/proof). (3) stale `strip_pos/1`→`strip/1` xref.
VERIFIED LIVE: `Std.Syntax` elaborates `{:ok}` with just `use Std.String` (nested `List(Syntax)` positivity fine,
forward refs fine, `SOpaque` nullary ctor fine); round-trip preserves function NAMES + attr key ORDER (strip==
non-vacuous); `:string_interpolation` recurses cleanly (parts are real nodes, no crash). 1021 tests pass.

SP2 Tier-3 slice-2 Stage 4 DONE — executed inline on Opus, strict red→green, 2 tasks committed (ghost author,
explicit pathspec, mix from worktree root):
- Task 1 `f66db9f` — `lib/std/syntax.cure` (`Syntax`/`Attr`/`SynLit` ADT, `@group(:core)`, `use Std.String`) +
  `test/cure/stdlib/syntax_elaborates_test.exs`. Red (no file) → green; stdlib suite 340 pass.
- Task 2 `979fb36` — `lib/cure/compiler/macro_syntax.ex` (`to_syntax`/`from_syntax` mirror-repr bridge) +
  `test/cure/compiler/macro_syntax_test.exs` (3 tests: attr-preserving to_syntax, lossless round-trip over 7
  exprs, exotic regex-tuple → `:s_opaque`). Re-probed all parser shapes LIVE before writing (tests immutable):
  `g(1,x)`→`{:function_call,[name:"g",…],[…]}`, `~r/foo/`→`{:literal,[subtype: :regex,…],{"foo",""}}`,
  `x+2`→`{:binary_op,[operator: :+,…],…}`, `:ok`→`{:literal,[subtype: :symbol],:ok}`. Red → green;
  compiler+stdlib regression 1021 pass / 1 skip; `mix compile --warnings-as-errors` clean (vector.cure `.cure`
  warnings pre-existing, not Elixir).

SP2 Tier-3 slice-2 Stage 5 code review DONE — Sonnet subagent converged after 7 passes (4 consecutive clean) over
diff `2faf559..HEAD`, committed `6eaf70d` (ghost author, explicit pathspec). Found + red-tested + fixed 2 real
defects: (A) composite-meta blind spot — `synlit/1` collapsed list/map/AST-valued meta (binary-segment `size`/`unit`,
selective-`use` item lists, an interface's `defaults` table) to `:s_opaque`; fixed by adding `{:s_list,_}`,
`{:s_syntax,_}`, `{:s_map,_}` variants + `SList`/`SSyntax`/`SMap`/`SynPair` ctors on the ADT. (B) `to_syntax/1`
raised `FunctionClauseError` on non-3-tuple parser output (`impossible` arm body `nil`, 4-tuple `named_implicit_pat`);
fixed by a total `{:syn_raw,_}` catch-all + `Raw` ctor (reflect opaquely, matching regex precedent). Stale moduledoc
fixed. All 9 tests green; **Stage 6 gate run by the reviewer: `mix test test/cure/compiler/ test/cure/stdlib/` =
1026 passed / 1 skip (pre-existing)**. NO seeds/corpus noise. Out-of-scope note (NOT fixed, pre-existing, flagged
for later): parser.ex's own `subst_holes_meta_value`/`collect_fresh_names_value` Tier-1 hole walkers have the same
map-valued-meta blind spot if ever fed one.

## ═══ SP2 Tier-3 slice 2 (`Std.Syntax` value + reflection bridge) COMPLETE ═══ (Stages 2–6 done; `6eaf70d`)
Reflection substrate live: `lib/std/syntax.cure` (`Syntax`/`Attr`/`SynLit` ADT, now incl. `Raw`/`SList`/`SSyntax`/
`SMap`/`SynPair`) + `lib/cure/compiler/macro_syntax.ex` (`to_syntax`/`from_syntax`, total + lossless up to line/col).
TCB delta ZERO. This is the VALUE a typed derived field holds underneath (operator steer, `a.name`) — NOT wasted.

SP2 Tier-3 slice 3 Stage 2–6 DONE — plan committed `4ba6189`; implementation committed in phases:
- **`57c3a00`** — parser harvests `:computed` rules and emits deferred
  `{:computed_use, meta, [elab_ref, {:macro_input, meta, ordered_hole_inputs}]}` nodes. Parser tests cover
  zero-hole and hole-bearing rules; the parse-time harvest never executes an elab.
- **`7fa0a51`** — `MacroSyntax.to_core/1` + `from_core/1` encode/decode the complete generic `Std.Syntax`
  mirror (constructors, lists, strings, nested syntax, maps, opaque values).
- **`45b4157`** — `Cure.Elab.MacroExpand` elaborates the elab reference, kernel-infers the application,
  normalizes it through the existing trusted normalizer, decodes the result, and recursively splices it before
  ordinary body elaboration. Function bodies containing computed uses are ordered after plain bodies so a
  referenced total elab is checked/certified before execution. Structured error formatting and end-to-end
  tests cover valid zero/hole inputs and invalid output.
- **`20e8880`** — review fix: recursively decode `Node` children from Core instead of only decoding the list
  spine. Scoped compiler/elab/stdlib gate: **1874 passed / 2 skipped**.
- Full gate: **`mix test` = 4165 passed (3 doctests) / 2 skipped**, 151 expected immune responses,
  Antigen shape coverage **328/328**, no seed/corpus noise, `mix compile --warnings-as-errors` clean.

**NEXT (SP2 continues):** `check … else fail C` + computed-rule example execution, then the MacroValidate
wiring slice. When ALL SP2 done → SP2 COMPLETE → **SP3 (read the SP3 GROUNDING section below FIRST)**.
Deferred post-gate SP1: T9, T7b.

## ═══ SP2 Tier-3 typed derived records (Stages 2–6) COMPLETE ═══
Plan `docs/superpowers/plans/2026-07-12-macro-facility-sp2g-plan.md` committed as `769f124`.
The typed-record implementation is complete in three committed phases:
- **`4db5ca9`** — parser metadata records `syntax_type` (`MkSyntax`) and ordered unique
  `syntax_fields` for each computed rule; `Program.declarations/1` synthesizes the ordinary
  `rec MkSyntax` declaration with each field typed as generic `Syntax`.
- **`c3f2393`** — `MacroSyntax.to_core_record/2` encodes the reflected macro-input children as
  the generated record constructor, with direct empty/populated Core-constructor tests.
- **`a8e4588`** — `MacroExpand` supplies the generated record to typed computed elabs, runs the
  existing Core type/infer/normalize/decode firewall, and retains a generic-`Syntax` fallback for
  existing computed elabs. End-to-end tests cover `a.x` projection, expansion back to the use-site
  AST, and `unknown_field` rejection.

This slice deliberately keeps fields at `Syntax` rather than category-indexed types, and does not
implement repeated groups, quote syntax, `check … else fail C`, computed-rule example execution, or
MacroValidate wiring. TCB delta remains ZERO: no `lib/cure/core/*` changes.

Verification after the slice: `mix test test/cure/compiler/` = 692 passed / 1 skipped;
`mix test test/cure/elab/` = 847 passed / 1 skipped; `mix test test/cure/stdlib/` = 340 passed;
`mix compile --warnings-as-errors` passed; full `mix test` = 4170 passed (3 doctests) / 2 skipped;
Antigen shape coverage 328/328; worktree clean.

## ═══ SP3 GROUNDING — READ THIS WHOLE SECTION BEFORE TOUCHING SP3 ═══
(Written 2026-07-12 by the prior agent with full machinery probed live, for a fresh/less-context
agent. Every path, module, and function name below was verified against the tree on this date. Re-verify
line numbers before editing — they drift — but the module + function NAMES are load-bearing and correct.)

### SP3 mission (one sentence)
Make **every macro compile run a full Antigen-style fuzz of its own expansion**: generate a statistically
thorough sample of the DSL programs the macro's grammar accepts (by filling each typed hole with a generated
well-typed Core term of that hole's type), expand each, kernel-check the expansion, and **fail the MACRO's
compile** (with a shrunk counterexample) if any valid parse expands to ill-typed Core. Spec = self-proving
design **§4** (`docs/superpowers/specs/macros/2026-07-11-self-proving-macros-design.md`, lines 174–241) — read §4.1–§4.5
verbatim; program-doc SP3 (`…-program.md`, "### SP3"). This is the **self-proving headline** and the clause of
the DONE criterion that reads "generatively proven to expand to well-typed Core." SP3 is the ONLY sub-project
that closes that clause — SP4/SP5/SP6 do not.

### Layer & TCB posture (NON-NEGOTIABLE)
SP3 is an **A + E/P-layer feature (untrusted): Antigen engine (`lib/antigen/*`) + the macro compile path
(`lib/cure/compiler/*`) + re-elaboration via the elaborator (`lib/cure/elab/*`).** TCB delta MUST be ZERO — do
NOT touch `lib/cure/core/*`. Soundness argument (spec §4.3): the generator emits well-typed Core, we assemble it
through the grammar, expand, and hand the expansion to the SAME trusted kernel checker that guards every other
program. A generator bug or a false "valid parse" can only make a macro **wrongly fail to compile** (a rejected,
not an unsound, program) — it can never admit ill-typed Core. If SP3 ever seems to need a kernel/core change, it
is mis-scoped → HALT and update this file.

### THE BIG WIN — the "one new engine" §4.4 calls for MOSTLY ALREADY EXISTS
Spec §4.4 says the single implementation cost is *type-directed* generation ("give me a well-typed term of type
`T`", stronger than "give me some well-typed term"). **That generator already exists and is callable:**
- `Antigen.Generators.Term.gen_term(ctx, goal)` (`lib/antigen/generators/term.ex:28`) → returns an
  `Antigen.Gen.t()` that samples a **well-typed Core term of type `goal`** in context `ctx`. It is mode-directed
  inversion of the kernel's bidirectional rules with a canonical-inhabitant fallback (`SigMenu.canon/2`) so it is
  **total** (never fails to produce *a* term). `@max_size 12`, fuel `@gen_fuel 500`.
- So SP3's real work is **WIRING** `gen_term` into per-hole filling — NOT building type-directed generation from
  scratch. The remaining generator work is only mapping a grammar hole `<n: Category>` → the Core `goal` type to
  pass to `gen_term`, and only for the hole categories a DSL actually uses (spec §4.4: base value/data types
  first; higher-order/dependent hole types a later increment; a hole type outside reach must be REPORTED as a
  coverage gap, per §4.2, not silently passed).

### Reusable machinery inventory (all verified present — do NOT reinvent)
- **Type-directed term gen:** `Antigen.Generators.Term.gen_term(ctx, goal)` (above). Context generation:
  `Antigen.Generators.Context.gen/1`; signature menu `Antigen.Generators.SigMenu` (`env_of/1`, `rebuild_context/2`,
  `canon/2`).
- **Gen monad combinators:** `Antigen.Gen` (`lib/antigen/gen.ex`): `return/1`, `member_of/1`, `one_of/1`,
  `frequency/1`, `bind/2`, `sized/1`. Interpreted by backend `Antigen.Backend.StreamData` (`sample/2`,
  `sample_seeded/3`). Use `bind`/`sized`/`return` to assemble a whole-program generator from per-hole `gen_term`s.
- **Shrinker (for the counterexample):** `Antigen.Shrink.minimize(challenge, pred, budget)`
  (`lib/antigen/shrink.ex:13`); `candidates/1`, `size/1`. It already shrinks `:typed_term` payloads — the
  counterexample a macro reports should be shrunk through this so the author sees the SMALLEST offending input.
- **Challenge record:** `Antigen.Challenge.new(kind:, assay:, label:, payload:, seed:)`. SP3 likely adds a new
  `kind` (e.g. `:macro_expansion`) with payload `%{macro: <name>, rule: <kw>, input: <generated parse>, expansion:
  <Core>, ...}` — or fuzzes OUTSIDE the Challenge/assay registry entirely (a per-macro-compile loop). DECIDE which
  (see Open Questions).
- **Coverage manifest:** `Antigen.CoverManifest` (`lib/antigen/cover_manifest.ex`): `expected/0`, `hit_points/1`,
  `missing/1`, `summary/1`, `report/1`. SP3 needs a **per-macro** manifest (which rules + which `fail`/`explain`
  points were exercised, at what depth). Model it on CoverManifest but keyed by macro definition, per spec §4.2.
- **Runner/campaign:** `Antigen.Runner` (`generate/1`, `replay/2`, `@registered_assays`). Relevant if SP3 registers
  an assay; skippable if SP3 runs its own per-compile loop.

### The expansion path SP3 must call (what "expand `p`" means concretely)
- **Tier-1/2 (template `becomes`, built in SP1):** `Cure.Compiler.Parser.expand_example(rules, use_site_tokens)`
  (`lib/cure/compiler/parser.ex:146`) parses a use-site token stream against a macro's `rules` and returns the
  expansion AST (it wraps a sentinel `{:example_use_site_not_fully_consumed,…}` if the input isn't a single full
  use — reuse that discipline). This is the exact function `MacroValidate.check_examples` uses to expand the
  worked examples; SP3 does the same but with GENERATED inputs instead of author examples. **A generated program
  is a token stream** (or an AST you can render to tokens) — the generator's job is to produce hole-fillers, splice
  them into the rule's use-site shape, and hand tokens to `expand_example`.
- **Tier-3 (`computed by`, SP2 slice 3 — NOT YET BUILT):** its expansion is the compile-time execution pass
  (`elaborate elab → normalise(app(elab, input)) → from_syntax → splice → re-elaborate`, see the SP2 NEXT block
  above and `…-tier3-computed-by-execution-design.md`). **SP3 CANNOT fuzz Tier-3 macros until SP2 slice 3 lands.**
  Program-doc confirms: SP3 "Depends on SP2 (needs Tier-3 elabs + the grammar to fuzz)." → **Sequence: finish SP2
  (incl. slice 3) FIRST.** SP3 CAN be prototyped against Tier-1/2 macros (which fully exist) to build the generator
  wiring + gate + manifest, then extended to Tier-3 once slice 3 exists.
- **Kernel-check the expansion:** re-elaborate the expansion on the dependent pipeline —
  `Cure.Elab.Program.elaborate/1` (returns `{:ok, env}` | `{:error, …}`). SP1 T8 already built the
  "expansion expands to WELL-TYPED Core" dependent firewall (commit `3a7383d`; see the transitional classic one
  in `test/cure/compiler/macro_expansion_classic_soundness_test.exs`). SP3 generalizes that single firewall to
  the fuzzed-input population. A kernel `{:error, …}` on a valid generated parse == the SP3 counterexample.

### The check host & the wiring seam (where the gate fires)
- SP2's self-proving checks live in **`Cure.Compiler.MacroValidate`** (`lib/cure/compiler/macro_validate.ex`):
  `check_explain_exhaustive/1` → `{:error,{:missing_diagnosis,points}}`, `check_rules_pinned/1` →
  `{:error,{:rule_unpinned,names}}`, `check_examples/1` → `{:error,{:example_mismatch,details}}`. **SP3 adds a
  fourth sibling here:** `check_expansion_proof/1 :: (macro_def) -> :ok | {:error,{:expansion_ill_typed, %{input, expansion, kernel_error, shrunk}}}`.
  Error atoms/formatting go in `lib/cure/compiler/errors.ex` alongside the other three.
- **WIRING CAVEAT (shared with SP2):** these `MacroValidate` checks are currently STANDALONE — grep shows only
  comments reference them from the compile pipeline; they are not yet invoked on every real compile. SP2's own
  "WIRING slice" (see SP2 NEXT block) is what threads `MacroValidate` into the compile path. **SP3's full-fuzz
  gate needs that SAME wiring seam.** Coordinate: either SP2's wiring slice lands the seam and SP3 hangs its
  check on it, or SP3's first slice builds the seam. Do NOT assume the checks auto-run — verify with a red test
  that a bad macro actually FAILS TO COMPILE (not just that `check_*` returns an error in isolation).

### Proposed SP3 slice decomposition (each slice = full autopilot Stage 2–6, red-test-first, committed)
Order chosen so each slice has a runnable red test and builds on the last. Adjust if grounding contradicts.
1. **Slice A — hole-type → Core-goal mapping + single-hole generation.** Given one rule with one typed hole
   `<n: Category>`, produce a `Gen` of a well-typed filler via `gen_term(ctx, goal)`. RED TEST: for a hole of a
   base type (e.g. `Int`/`Bool`/a simple ADT), the generator yields N terms that each `elaborate`/infer to that
   type. Report `:unsupported_hole_type` for a category outside reach (coverage gap, not a pass).
2. **Slice B — whole-parse assembly.** Splice per-hole fillers into a rule's use-site shape → a full generated
   use-site token stream; feed `expand_example` → an expansion AST. RED TEST: a generated parse for a known-good
   Tier-2 macro expands without the not-fully-consumed sentinel.
3. **Slice C — the property + gate.** For a batch of generated parses: expand each, `elaborate/1` the expansion,
   collect kernel errors. RED TEST (the headline): a **deliberately broken** macro whose `becomes` drops a hole's
   type (so a valid parse expands to ill-typed Core) is REJECTED at compile with a counterexample; a correct macro
   PASSES. This is the program-doc SP3 gate. Use a hand-written broken fixture macro as the negative control.
4. **Slice D — shrink the counterexample.** Route the failing generated input through `Antigen.Shrink.minimize/3`
   so the reported counterexample is minimal. RED TEST: the reported input for the broken macro is the minimal
   failing shape (assert size ≤ a bound, or equals a known minimal witness).
5. **Slice E — per-macro coverage manifest + caching.** Manifest records rules/`fail`/`explain` points exercised
   and depth; cache keyed by macro definition (same grammar+elabs ⇒ reuse prior PASS; edit ⇒ re-run full).
   RED TESTS: manifest lists all rules of a multi-rule macro; an unchanged macro's second compile does not re-fuzz
   (observable via a call counter/flag), an edited one does. Caching is "don't redo identical work," NEVER a
   weaker gate (spec §4.2).
6. **Slice F — wire the full-budget gate into every macro compile** (or hang on SP2's wiring seam) + extend to
   Tier-3 `computed by` macros once SP2 slice 3 exists. RED TEST: end-to-end, a user macro in a `.cure` source
   with a latent expansion bug fails `Cure.Elab.Program.elaborate/1` of the whole program with the SP3 error.

### SP3 GATE (from program-doc — the acceptance bar)
"A macro whose `becomes`/elab drops a hole's type is REJECTED at macro-compile with a shrunk counterexample; a
correct macro passes; the manifest reports coverage. Full suite green; Antigen campaign green." Plus the
DONE-criterion end-to-end proof: a user macro parses, expands, is generatively proven, and its expansion runs.

### Open questions to DECIDE early (don't guess silently — record the decision in this file)
1. **Assay-registered vs standalone loop?** Register a new `:macro_expansion` assay in `Antigen.Runner`
   (`@registered_assays`) and reuse the campaign/replay/corpus banking, OR run a self-contained per-macro-compile
   fuzz loop that only borrows `gen_term`/`Shrink`/manifest. Standalone is simpler and matches "gates every macro
   compile"; assay-registration buys corpus replay + the existing coverage campaign. Prior lean: **standalone loop
   that borrows the pieces** (macro fuzz is per-compile, not part of the kernel campaign) — but confirm against how
   heavy the full-budget run is and whether corpus banking is wanted. NOTE the standing rule: **revert
   `test/antigen/seeds.sexp` + `corpus.sexp` banking noise before committing** — if SP3 runs anything that banks
   seeds, scrub that diff.
2. **Grammar-hole → Core-type bridge.** How does a rule declare a hole's TYPE, and where is it stored on the
   `{:macro_def, meta, rules}` AST? Probe the harvested rule shape (`harvest_active_macros`, parser.ex:183) and the
   Tier-2 `syntax` rule's hole-kind field before Slice A — the mapping from a hole's declared Category to the Core
   `goal` term is the crux and is under-specified here.
3. **Budget/perf.** "Full budget on every compile" is a deliberate cost (spec §4.2). Pick a default draw count
   (Antigen defaults `count: 200`, `gen_term` size ≤ 12). Caching (Slice E) is the escape valve.

### Two-pipeline steer (put this in EVERY SP3 subagent brief — verbatim)
Dependent machinery lives ONLY in `lib/cure/elab/*` + `lib/cure/core/*`. IGNORE `lib/cure/types/*`
(`checker.ex`, `unify.ex`) and the codegen half of `lib/cure/compiler/*` (`codegen.ex`, `pattern_compiler.ex`) —
non-dependent lowering; same-named functions are decoys. For SP3 the RIGHT anchors are: the generator
`lib/antigen/generators/term.ex` (`gen_term/2`), the expansion entry `lib/cure/compiler/parser.ex`
(`expand_example/2`, `harvest_active_macros`), the check host `lib/cure/compiler/macro_validate.ex`, and the
kernel-check via `Cure.Elab.Program.elaborate/1`. A read-only scouting agent that greps by name will land in the
wrong pipeline and report phantom "type-directed generation missing" — it is NOT missing (`gen_term/2` is it).

### Standing rules recap (same as the rest of this run)
Ghost commits `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. Explicit pathspec
`git add -- <path>`, never `-A`. Revert `test/antigen/seeds.sexp`/`corpus.sexp` banking noise before committing.
ONE `mix` suite at a time (prefer scoped `mix test <file>`; full suite once, alone, at the gate). Commit per
stage/task. Reviews on Sonnet (`model: sonnet`, recursive-skeptical-review to two clean passes), implementation on
Opus. STOP + update this file + PushNotification on a hard blocker or pass-15 non-convergence — never accept an
unconverged artifact. Tests immutable once green.

### Cross-refs
- Spec §4: `docs/superpowers/specs/macros/2026-07-11-self-proving-macros-design.md:174-241`.
- Program-doc SP3: `docs/superpowers/plans/2026-07-12-macro-facility-program.md` ("### SP3").
- Tier-3 execution design (needed before SP3 can fuzz Tier-3): `docs/superpowers/specs/tooling/2026-07-12-tier3-computed-by-execution-design.md`.
- SP1 T8 expansion firewall (the single-case ancestor of SP3's fuzz): commit `3a7383d`,
  `test/cure/compiler/macro_expansion_classic_soundness_test.exs`.
- Antigen metatheory engine + coverage discipline: project memory `[[antigen-metatheory-engine]]`,
  `[[antigen-coverage-manifest]]`, `[[antigen-coverage-plateau]]` (~95% honest ceiling — SP3 inherits the same
  "statistical, not a formal proof for an infinite grammar" residual, spec §4.5; state it, don't overclaim).

## DONE criterion (cancel cron + notify)
All 6 sub-projects implemented, code-reviewed, full `mix test` green, with an end-to-end
proof: a user-defined macro parses, expands, is generatively proven to expand to
well-typed Core, and its expansion runs. Then CronDelete + PushNotification.

## HALT protocol
Hard blocker or a review loop hitting pass 15 without convergence → update THIS file with
the blocker + what's needed, PushNotification, STOP. Never guess or accept an unconverged
artifact.

## Live implementation state — 2026-07-12

The following slices have now landed in this worktree:

- SP2 type-only example pins and dependent-pipeline validation wiring are complete.
- SP3 slices A–F are implemented in `Cure.Compiler.MacroFuzz`: typed-hole generation, multi-hole use-site assembly, generated expansion checking, shrinking, proof manifests, persistent cache reuse, and computed-rule coverage are present. Built-in lexical domains use explicit native generators, and closed custom enum categories resolve from real module environments. The built-in `Code` proof domain is deliberately numeric to preserve the existing macro contract; arbitrary expression categories still require a later typed-domain extension.
- SP4 has an advisory reflection foundation in `Cure.Compiler.MacroReflection`: definition/type resolution, constructor inspection, dependent type inference, macro expansion, and pure declaration lifting.
- SP4 also has a reflection-backed reducer dogfood builder in `Cure.Compiler.MacroReducer`; it emits ordinary `pattern_match` AST and proves it through the dependent elaborator.
- SP4 reducer dogfood now shares exhaustive reflection dispatch with explicit `view` and `flow` builders.
- SP4 has a declaration-level reducer/view/flow bundle builder that derives all three ordinary AST outputs from one reflected constructor set.
- The transparent lift path has generic callback-shape and declaration validation, and pure `QuotedModule` lifting in `Cure.Compiler.LiftModule`; behavior vocabularies are no longer owned by a compiler-side OTP registry.
- SP5 also has a pure supervisor module builder with child/strategy validation and an explicit AtomVM availability probe; this worktree has no `atomvm` executable, so the runtime execution gate is not claimed.
- SP5's generated supervisor/application proof now builds and runs on the generic-unix AtomVM executable built from `/Users/ch/Develop/esp32-beam/AtomVM`, with AtomVM's estdlib runtime beams packaged alongside the generated Cure modules.
- SP6 has delimited raw-hole parsing, pure capture helpers, computed use-site integration, `is Category` rule metadata, and explicit module-rule markers.
- SP6 raw-hole proof fixtures now generate bounded raw text and preserve a synthetic `dedent` delimiter through `MacroFuzz`/`Parser.expand_example`.
- SP6 grammar segments now support line-oriented repetition (`...`) and optional groups, including generated-proof assembly and list-valued substitutions.
- SP6 module rules now execute to ordinary AST through `Cure.Compiler.MacroModule`, and open categories compose with duplicate-keyword and closed-category checks.
- SP6 has pure packet, board, and protocol library builders with dependency, capability, flash, role, and projectability validation.
- SP6 also has pure driver/register-map, units/literal, and property-check plan helpers for the next concrete DSL layer.
- SP6 has a pure parse-grammar builder with duplicate and left-recursion validation.
- The standard library now auto-preludes a `lens first`/`lens second` macro surface from `Std.Optic`; both expand to ordinary typed optic calls and are covered by parser and runtime tests.
- The generated expansion-proof gate now runs for the dependent pipeline and the transitional classic `compile_string` path; the classic soundness negative control and the full suite pass.
- Final verification before the transparent BEAM continuation: `mix compile --warnings-as-errors` passed; the current full gate passes with `4051 passed (3 doctests, 4048 tests), 1 skipped`, `138` immune responses, and Antigen shape coverage `318/318` across 31 manifests.
- SP3's built-in lexical categories now use native domains: numeric literal generators for `Number`/`Duration`, mixed typed expression generators for `Code`, and type-term generation for `Kind`. Unsupported categories remain explicit coverage errors.

The remaining work before the DONE criterion is genuinely satisfied is governed by
the ordered transparent BEAM plan below. The earlier SP1-SP6 work is an upstream
foundation; it does not satisfy the BEAM algebra, recursive expansion, or OTP
macro replacement gates by itself.

- Preserve the existing indexed module-category and generated-proof coverage gaps
  as explicit sub-tasks in the final SP6 verification pass.
- Complete the transparent BEAM plan in order, committing every phase before the
  next phase begins.
- Finish the AtomVM runtime gate, remaining embedded surface families, skeptical
  review, full test gate, and Antigen verification only after the replacement
  phases have landed.

Do not mark the DONE criterion complete until every item above is implemented and verified.

## ORDERED TRANSPARENT BEAM PLAN — 2026-07-13

Source of truth:
  `docs/superpowers/specs/macros/2026-07-13-transparent-beam-algebra-otp-macros-design.md`.

This is the execution order. Do not start a later phase while an earlier phase
has an unverified gate or uncommitted changes. Every phase ends with focused
tests, review, a clean worktree, and a highly descriptive commit.

### Phase 0 — Integrate the kernel-parity branch sequence

**STATUS: COMPLETE (2026-07-13).** `autopilot/kernel-parity-batch` was already
an ancestor of `feature/idris-parity` through the existing parity merge, so no
duplicate merge was created. The verified `feature/idris-parity` result was
merged into this branch as `9481b3c`; preserved user edits were committed as
`cd4cdaf`. The focused macro typed-record suite passed 5 tests and the
worktree was clean at the phase boundary.

This is a prerequisite to implementing against the final compiler shape:

1. Inspect the user changes in
   `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`.
2. Merge branch `autopilot/kernel-parity-batch` into `idris-parity`.
3. Resolve and test that merge on `idris-parity`; preserve the branch's deletion
   of bespoke container types and all unrelated user changes.
4. Merge the verified `idris-parity` result into `core-let-binder`.
5. Resolve integration conflicts in favor of the transparent macro architecture,
   not by restoring deleted compiler-owned OTP classes.
6. Run the focused compiler/elaborator suite and record the exact baseline.

Gate: both merges are complete in the specified order, no conflict markers
remain, tests identify any expected parity failures, and the worktree is clean.

### Phase 1 — Establish the checked BEAM algebra

**STATUS: COMPLETE (2026-07-13).** `Std.Otp.Raw` now owns the complete raw
effect-typed extern inventory currently required by the algebra: indexed raw
process identity, messaging, calls/casts, lifecycle, timers, monitors, links,
registry, liveness, and exits. `Std.Otp` is ordinary checked Cure over that
boundary, with transparent `Pid(m)` and `GenServer(q, r)` aliases, checked
message-code operations, and typed lifecycle wrappers. Parameterized aliases
now beta-reduce inside the type elaborator, with a two-parameter regression;
this is compiler support, not a runtime workaround. Focused coverage is 18
passing tests, and `mix compile --warnings-as-errors` is clean. No
`lib/cure/core/*` file changed. Process creation, supervision/application
descriptors, and raw-import visibility remain explicit Phase 2/3 work where
their transparent macro and module-context machinery belongs. The raw boundary
now also declares effect-typed `spawn` and `spawn_link`, with checked wrappers;
their behavior-specific message index still requires the callback context
planned for Phase 3.

Implement the foundation in standard-library code over `Std.Otp.Raw`:

1. Inventory and lock the honest raw extern boundary: identity, messaging,
   calls/casts, process creation, lifecycle, supervision, application,
   monitors, timers, links, and registry operations.
2. Add or complete erased message/reply codes and typed handles such as
   `Pid(messages)` and `GenServer(requests, replies)`.
3. Derive codes from declared message ADTs and callback patterns where the
   existing type machinery permits; record unsupported dependent cases instead
   of adding an `Any` escape.
4. Implement checked typed wrappers and explicit code computations for tag
   lookup, subset, union, and reply lookup.
5. Preserve the inert `Effect(T)` design and direct effect-chain lowering.
6. Add positive and negative tests for legal messages, wrong tags, wrong
   payloads, request/reply mismatches, effect order, and runtime erasure.

Gate: the algebra compiles as ordinary Cure, the raw boundary is the only
asserted foreign surface, negative typing tests fail for the intended reasons,
and no `lib/cure/core/*` change is needed.

#### Tier-3 hygiene audit (2026-07-14)

The dedicated audit of `Cure.Elab.MacroExpand` found no recursive-expansion or cycle-stack omission, but it identified a scope-model boundary that must be closed before declaration-producing macros are complete. `MacroSyntax.from_syntax/1` reconstructs generated identifiers as ordinary surface names and discards their generated origin. Existing `<fresh Name>` protects Tier-2 parser templates only; computed `Std.Syntax.variable/1` output has no scope mark or gensym contract. Generated binders, callback helpers, nominal declarations, and lifted-module names can therefore collide with use-site bindings. This is a hygiene gap in the macro bridge, not a kernel or evaluator defect.

The Tier-3 hygiene phase must add origin-aware syntax metadata, freshen generated binders and declaration names before use-site syntax is spliced, preserve the intended scope of reflected user syntax, and add capture, nested-expansion, duplicate-name, and deterministic-repeat tests. String post-processing or runtime renaming is not an acceptable substitute for scope information.

Suggested commit:
`feat(std): establish the checked BEAM process algebra over raw OTP externs`

### Phase 2 — Make macro expansion transparent and recursively inside out

**STATUS: COMPLETE (2026-07-13).** The compiler now expands
computed syntax inside out before the outer invocation, uses stack-scoped
structural cycle identities with source positions removed, defaults resource
budgets to infinity, and accepts explicit finite budgets for hosts/tests. The
lift-module parser also preserves a substituted identifier hole instead of
flattening it into a literal module-name string. A generic lift-module collector
now turns parsed callbacks into ordinary Cure functions, validates/checks them,
emits behavior-tagged independent units, rejects duplicate module names, and
loads/writes them through the common BeamWriter path. Raw body holes are
reparsed with the enclosing macro environment, so nested syntax macros inside
generated lifted declarations are normalized before validation. The macro
proof gate validates `lift_module` as a closed checked value and uses a
validated `ModuleName` filler category for generated proofs. Lifted module
imports now carry dependency metadata; generated units are deterministically
topologically ordered, generated-module cycles are rejected before emission,
and source provenance is retained on each quoted module. Generic callback
shape validation remains in the collector; behavior names, callback
vocabularies, and callback semantics stay in Cure standard-library macros so
the compiler remains OTP-agnostic (`408191ad`, 15 lifted-module surface
tests). Dynamic module-name
holes are also substituted as checked atom
literals inside generated ordinary declarations, which gives transparent
`start_link`/registry helpers a normal Cure value to consume. The main compiler
pipeline no longer dispatches through the legacy OTP container lowering branch,
macro proof checking no longer consults that branch, and the OTP container
parser fallback has been removed. Computed expansion now retains ordered
invocation provenance through execution, cycle, and finite-budget diagnostics
(`703e6536`). A generic delayed-slot floor now preserves delayed raw holes,
threads lexical behavior/callback/arity context through lifted callbacks, and
reparses delayed bodies after context introduction (`64bf2a79`). Remaining
Phase 2 also has an explicit language-level `Std.Syntax.Quoted` opacity
boundary through the reflection/Core bridge and recursive expander
(`79d7ac46`). Delayed callback slots now require exactly one body expression
and have an end-to-end proof where `beam_ops self` is reparsed after callback
context introduction and passes ordinary callback elaboration (`cd0943e8`).
The full compiler suite passed 693 tests and `mix compile --warnings-as-errors`
is clean. Phase 2's remaining gate is closed; typed operation-context
semantics continue in Phase 3.

Standard-library macro loading now performs a generic harvest pass followed by
a parse with the complete harvested grammar, so one standard-library macro may
invoke another without a compiler-owned composition case. This enables the
transparent actor, FSM, and supervisor starters to use `beam_ops` directly;
the startup vocabulary now includes `start_link`, `start_statem`, and both
zero-argument and argument-bearing supervisor startup forms. The full suite
after this slice passed 4007 tests, 3 doctests, and 1 skipped test, with
Antigen coverage 318/318. Computed expansion provenance, delayed callback
context, quoted-syntax opacity, and the delayed callback `beam_ops` proof are
covered by `703e6536`, `64bf2a79`, `79d7ac46`, and `cd0943e8`.

Build the generic expansion and lifted-module infrastructure before writing
`beam_ops`:

1. Change macro interpretation to return parsed AST or closed compile-time
   values containing parsed AST, never source strings, raw forms, or loaded
   modules.
2. Implement recursive normalization to a fixed point. For
   `outer(inner(value))`, normalize `inner` before `outer` receives it; recurse
   again through every AST generated by `outer`.
3. Traverse function bodies, patterns, declarations, `callback` bodies, and
   every `lift module` compilation unit. Keep explicit quoted syntax opaque.
4. Add delayed syntax slots for callback bodies whose behavior context is
   introduced by an outer transparent `lift module`; expand those slots after
   entering the context and before callback elaboration.
5. Add expansion identity, cycle detection, invocation/AST-size budgets,
   hygiene, deterministic fresh names, and source-to-generated provenance.
6. Finish checked `behaviour`, `callback`, and `lift module` parsing,
   elaboration, validation, module collection, dependency ordering, collision
   checks, and common multi-module emission.
7. Add nested expansion, quoted syntax, delayed context, cycle, provenance,
   hygiene, duplicate-module, and deterministic-repeat tests.

Gate: generated syntax is fully expanded before elaboration, all generated
code uses the ordinary checker, lifted modules are emitted without code-server
side effects, and no `__otp_container` behavior is required by the new path.
The generic compiler must not acquire knowledge of OTP behavior names,
callback vocabularies, actor/FSM/supervisor/application semantics, or OTP
specific lowering while implementing this infrastructure. Those vocabularies
and lowering rules must be defined in Cure itself through ordinary language
constructs, macros, checked algebra, and explicit foreign primitives. Moving
the same knowledge into an Elixir helper outside the compiler is not sufficient.

Macro-generated lifted units retain the macro template's lexical `use` imports,
so bare type and function references are resolved against the defining standard
library environment and emitted through the ordinary qualified-owner path. This
keeps macro authors from spelling every helper as `Std.Module.name`; a regression
now covers bare supervisor strategy helpers across an independent lifted module.
The parser now records direct imports visible around each macro definition and
propagates them into generated lifted modules automatically, including macros
defined inside user modules. This is generic lexical-scope propagation and does
not encode any standard-library or OTP name table.

Suggested commit:
`feat(compiler): add transparent inside-out macro expansion and lifted modules`

### Phase 3 — Implement `beam_ops` over the algebra

**STATUS: UNBLOCKED — Phase 2.5 COMPLETE (2026-07-15); implementation substantially
landed. Residual: retire the `contextual` proof exemption on `beam_ops self` via
reply-channel message-code derivation (see the `OPEN GATE` section).** `Std.Otp` now defines a closed initial
`beam_ops` vocabulary: `self`, messaging, call/cast, process creation, startup,
lifecycle, timers, monitors, and links all expand to ordinary checked
`Std.Otp` calls and are proven marker-free. The generic macro grammar now has a
`contextual` rule qualifier, which defers only context-free fuzz proofs while
requiring actual operation use sites to pass ordinary elaboration. The raw
process-creation floor is
present (`raw_spawn`/`raw_spawn_link` plus ordinary `Std.Otp` wrappers), along
with effect-typed `gen_server:start_link/4` and
`gen_statem:start_link/4` wrappers that
preserves the OTP result tuple. The elaborator now threads expected result types through
qualified and effectful calls, including through the `Effect` type former. The
public and raw OTP wrappers bind every phantom type index as an explicit erased
parameter, so a concrete `Effect(Pid(Atom))` goal solves the raw operation rather
than relying on a rigid free type global. `beam_ops self` is contextual because
an unannotated standalone polymorphic self operation has no sound message index.
Startup operations are now also exposed through the closed `beam_ops`
vocabulary and are used by the transparent actor, FSM, and supervisor
templates. The remaining operation work must introduce an explicit behavior
context so those wrappers can mint `Pid(m)` with the callback's message code
instead of leaving `m` undetermined:

1. Add a closed operation vocabulary for `self`, `send`/`tell`, `call`,
   `cast`, `spawn`, `start_link`, `stop`, timers, monitors, and links.
2. Expand each operation to ordinary typed `Std.Otp` calls and effect
   sequencing; do not emit raw BEAM forms.
3. Thread process, request/reply, state, and callback-result context through
   expansion and elaboration. Declared `Effect(...)` callback results now use
   the ordinary effect-aware elaborator, and effectful callback binds preserve
   checked constructor results through an erased Core `let` witness
   (`7b421759`).
4. Reject unknown operations, illegal targets/messages, wrong replies, and
   operations used in an invalid callback context.
5. Prove nested operation arguments and generated operation sequences expand
   inside out with source-order effect preservation.

Gate: `beam_ops` is a standard-library macro, its output is ordinary checked
AST, and its generated code contains no compiler-only OTP marker.

The operation vocabulary now has focused positive coverage for messaging,
startup, lifecycle, timers, monitors, and links (`1c40e265`, 17 algebra tests).
Lifted callback context now carries generic parameter names and whether a
return annotation was declared, without embedding Core type terms in macro
metadata (`4daae701`). The generic audit walker and report boundary also
traverse and render `Effect` types without changing trusted Core code.
The current public guides and observability/journal docs also describe the
transparent macro/lifted-module surface rather than retired generated classes
(`88ba711e`, 33 documentation/observability tests plus the glossary gate).

Suggested commit:
`feat(std): define beam_ops over the checked process algebra`

### Phase 2.5 — Establish canonical owner identity before further macro work

**STATUS: COMPLETE (2026-07-15).** Commits `c877edfa`, `5e46008d`, and
`6bb375f5` established canonical owner-qualified identities at elaboration,
removed post-hoc Core re-keying, and updated the resolution/emission,
coherence, union, macro, and cross-module test surfaces. The focused canonical
identity acceptance matrix passes 39 tests on this branch. The previous
resolver experiment attempted to repair collisions after module slices had
already been elaborated. That direction is rejected and must not be resumed.

The defect is structural, not a missing clause in the rewriter. The current
`Resolution.rekey_term/3` handles only seven Core formers while `Core.Term.t`
contains twenty-three. In particular, `let`, `effect_type`, `effect_pure`, and
`effect_bind` are traversed as opaque fallback values. An imported body such as
`derive_actor` can therefore retain `{:global, :map}` inside a `let` after the
`map` definition has been moved to `:"Std.List#map"`. This can either produce an
unknown-global error or, worse, silently bind to an unrelated bare `map` from
another slice. The ordinary emitter often hid this because non-local globals
were routed through `import_origins`; compile-time evaluation is the first
consumer that must read the definition table honestly.

Do not add more `rekey_term/3` clauses. A second hand-maintained traversal of the
trusted term language will drift again and fails open. Binding identity must be
established while a module is elaborated and must never be reconstructed from
already-elaborated Core syntax.

#### 2.5a — Introduce one canonical name contract

Add a small `Cure.Elab.Name` module that owns the spelling contract for global
identities:

- `qualify(owner, base)` produces the canonical atom, currently using the
  `Owner#name` spelling;
- `owner(canonical)` extracts the owner without open-coded string parsing;
- `base(canonical)` extracts the surface basename for diagnostics and lookup;
- builtins and deliberately ownerless primitives have explicit constructors and
  are never inferred from a string heuristic.

Keep Core's `{:global, atom()}` shape unchanged. The kernel treats the atom as
opaque, so this is elaborator identity, not a TCB or Core representation change.
Every new or moved global must use this module; no emitter, diagnostic, test
fixture, or Antigen assay may hand-write `"Module#name"`.

#### 2.5b — Canonicalize every namespace at registration

Assign canonical owner-qualified identity to all module-owned families,
constructors, and ordinary definitions, including a module's own definitions.
Do not leave local definitions bare while qualifying only imports: two imported
modules must be mergeable without collision by construction. Preserve `classify`
and ambiguity tracking as diagnostic machinery, but do not use it to decide
which already-built definition wins.

Give compiler-generated anonymous instance methods the same owner provenance.
`__impl_*` names currently lack module identity; `Implementation.register/2`
must receive the current owner and register those globals canonically. A
no-bare-globals invariant is false if this namespace remains an exception.

Canonicalize references at the point they are elaborated, including references
inside types, function bodies, patterns, effect terms, generated declarations,
interface defaults, and instance methods. Preserve lexical locals and explicit
qualified names. A canonicalized module slice must be independent of the module
that later imports it.

#### 2.5c — Remove fallback resolution instead of restricting it

With canonical identities established at birth, delete the bare-name fallback
from `resolve_qualified/3` rather than adding another gate around it. Delete
`resolve_bare_shadowed/2` once all elaboration call sites use canonical lookup.
The direct/transitive/ambiguous import rules remain real diagnostics, but they
must resolve to canonical bindings before Core is produced.

Update emission, erasure, totality certification, signing, coherence, inline
hints, and `import_origins` to consume `Cure.Elab.Name.owner/1` or the canonical
environment metadata. Do not recover ownership by parsing arbitrary atoms in
each consumer.

#### 2.5d — Delete post-hoc re-keying as one atomic change

After canonical registration and reference resolution are green, delete all of
the following together:

- `Resolution.rekey_term/2-3`;
- `Resolution.rekey_module_env/3-6` and its private re-key helpers;
- `drop_bare_family/2` and any residual-bare cleanup;
- `resolve_bare_shadowed/2` and the type-position workaround;
- tests whose contract is that a loser is renamed after elaboration.

Replace them with tests that prove canonical keys and fully traversed Core are
correct at creation time. The deleted traversal must not be replaced by a new
generic recursive walker.

#### 2.5e — Cache only context-independent real-file slices

Once canonical identities are assigned during module elaboration, cache parsed
and elaborated slices by real source identity/hash. This is a consequence of
context independence, not a workaround for recursive re-keying. Do not cache
lifted or derived modules whose scope depends on an enclosing unit; those must
remain explicitly non-cacheable until they have an independent identity.

#### 2.5f — Required acceptance matrix

Before Phase 3 resumes, pin all of these:

1. An imported body containing `let`, `Effect`, and a shadowed global resolves
   to the owning definition, with no dangling or wrong-binding reference.
2. A diamond import of one owner is not ambiguous; two distinct owners are
   ambiguous and produce a diagnostic.
3. Auto-prelude duplicate imports deduplicate by module identity.
4. The auto-prelude self-import cycle (`Std.Bounded` through `Std.Binary` and
   `Std.Char`) terminates and does not self-requalify.
5. Interface and instance method resolution works across modules, including
   higher-kinded interfaces.
6. A lifted module resolves inherited declarations in its enclosing scope and
   is excluded from the real-file slice cache.
7. A structural walk over every merged slice proves that no non-primitive bare
   global remains before certification.
8. Full legacy, macro, Antigen, emission, and runtime gates pass after the
   deletion, not only the staged resolver tests.

Suggested commits, in order:

- `feat(elab): establish canonical owner-qualified global identities`
- `refactor(elab): remove post-hoc global re-keying`
- `perf(elab): cache context-independent module slices`
- `test(elab): pin canonical identity and no-bare-global invariants`

Gate: every family, constructor, definition, and anonymous instance method has
canonical identity before Core production; no post-hoc Core rewriter exists;
all consumers use the canonical owner contract; and the acceptance matrix is
green. Only then may Phase 3's operation-context and automatic message-code
derivation work continue.

### Phase 4 — Replace the four OTP forms in their Cure files

Implement these in dependency order, using the generic Phase 2 primitives and
Phase 3 operations:

#### Phase 4a — `sup` capability proof

**STATUS: LANDED — structured `syntax family` surface (2026-07-15); see "Structured
supervisor status" in the `OPEN GATE` section. The 2026-07-13 transparent-rule expansion
described below was the first replacement, since refined into the family surface.**
`lib/std/supervisor.cure` now expands
`sup` into a transparent `lift module` with checked `Supervisor.init/1`, an
ordinary `start_link/0`, dynamic module atoms, a typed `ChildSpec` value, and
the real checked `supervisor:start_link/3` boundary. The common
collector/emitter and generic AtomVM packaging path are exercised end to end;
the child constructor rejects non-atom module identifiers through ordinary
elaboration, and restart, shutdown, and child-kind policies are now closed
Cure values converted by standard-library functions. Closed strategy/child
validation now routes strategy lowering through a closed Cure `Strategy` value;
generated supervisor callbacks explicitly import the standard-library helper
module so independent lifted units resolve those definitions through the common
path. Restart intensity may be zero while restart period is represented by the
closed positive `Positive` type and rejects zero through ordinary elaboration
(`93d71a66`, 48 focused object tests). Transparent `child_spec` syntax captures
typed startup arguments and the common runtime proof starts a generated actor
under a generated supervisor (`27b3554d`, `648c75bf`, 50 focused object tests).
Top-level lifted
sources now emit the lifted unit as the primary
module, imported standard-library calls route remotely through the common
emitter, and the printer round-trips transparent lift syntax.
The child-spec boundary now distinguishes homogeneous typed arguments from
explicit raw BEAM terms. `child_spec ... with ...` checks one element type and
maps each element through `raw_arg`; heterogeneous lists require the distinct
`child_spec ... raw with [raw_arg(...), ...]` form. `ChildSpec` stores
`List(RawTerm)`, while direct `child_with_args` remains homogeneous and
preserves its `List(a)` result for typed callers (`6bd50db9`, `5b4424da`, 83
focused transparent-object tests).

Define `sup` in `lib/std/supervisor.cure` using `Supervisor`, `callback`, and
`lift module`. Validate child specs, strategy, intensity, period, restart,
shutdown, and child type through closed values. Prove a generated supervisor
module emits and runs through the common path.

#### Phase 4b — `actor`

**STATUS: LANDED — structured `syntax family` surface (2026-07-15); see "Structured
actor status" (and the call/info/lifecycle status blocks) in the `OPEN GATE` section.
The 2026-07-13 transparent-rule expansion described below was the first replacement,
since refined into the family surface.** The public `actor` syntax now expands
to an ordinary lifted `GenServer` module and starts through the typed
`Std.Otp.start_link` wrapper. In addition to the bootstrap form, the
standard-library macro now accepts an explicit `state <Type>` clause and
emits a module-local `State` alias shared by every state-bearing callback;
the ordinary checker rejects a mismatched callback result. The bootstrap and
typed floors are tested structurally and through the generic Unix runtime
path.

The actor floor also has explicit `init` and `handle_info` callback-body forms
with delayed single-expression bodies, sharing the module-local state alias
and ordinary callback result checking (`92b9ec43`). Callback contracts now use
erased `Effect(...)` result types, so nested `beam_ops` binds are checked and
the generated BEAM callback still returns the ordinary OTP tuple
(`7b421759`). Full message-code derivation and callback context remain open. A
`call` form now accepts
independent request and reply types and emits a checked `handle_call` callback
(`12227f4c`).
The actor floor now also accepts an explicit `messages <Type>` clause for
`handle_info`, so the generated callback and nested algebra use a shared
message type; an illegal send through that typed handle is rejected before
emission (`8bacfbe2`). The FSM floor has the corresponding explicit `events
<Type>` clause for `handle_event`, giving callbacks a concrete event type.
The actor floor now also accepts transparent typed `handle_cast` callback
bodies. Its callback result is a source-level effect alias, so ordinary
`pickup` message dispatch can be checked without hiding the body in a
compiler callback implementation; legal and wrong-state results are covered
by the focused suite (`94a0540e`, 53 tests).
The typed actor/FSM starters now pass scalar initial state data directly to
the OTP `init/1` callback instead of introducing an extra list layer. Unix
runtime assertions and the generic-unix AtomVM package proof cover the
corrected state shape (`dd1afe6b`, 55 focused object tests).
The actor macro now also exposes transparent delayed-body forms for the
remaining user lifecycle callbacks, `terminate/2` and `code_change/3`, with
source-level effect result aliases and negative state-result coverage. These
callbacks are reparsed, elaborated, and emitted through the same lifted-module
path (`9a4e47bc`, 59 focused object tests).

The Tier-3 inferred actor path now derives nullary constructor message heads
in `Std.Actor`, preserves each handler body as ordinary syntax, and emits the
generated unit with an isolated explicit import surface. It rejects payload,
guarded, catch-all, and duplicate heads until a typed payload view is
available; the shared nominal message type is proven at an external
`Pid(ActorMessage)`/`beam_ops tell` call (`7da653b0`, `f75e4ec1`).

The actor floor now also has a generic `handle_cast` form without a forced
payload literal, preserving the ordinary polymorphic state/message relationship
for user-defined actors whose initial state is supplied by `start_link/1`.
The FSM floor now has an explicit `initial <state>` plus `transition` callback
form whose checked result is the full `{next_state, state, data}` tuple. These
forms keep payload-preserving transition actions in Cure source rather than
requiring a compiler-owned handler representation; focused tests cover both
the generic actor runtime loop and the explicit FSM transition result. The
Explicit message/request/reply types and polymorphic callback forms are now
covered through standard-library signatures. Automatic message-code derivation
from arbitrary handler bodies and richer behavior-specific callback context
remain source-language work; the compiler must not grow an OTP map to provide
them.

Define `actor` in `lib/std/actor.cure`. Derive message codes from handlers,
emit `GenServer` callbacks and ordinary helpers, and expand nested `beam_ops`
inside start, message, and stop bodies. The generic callback floor now carries
explicit checked return types through `lift module`, and the typed actor floor
shares one explicit state alias across all state-bearing callbacks. The final
callback contract must still derive request/message/reply types from handlers,
keep `from`, reason, version, and extra values distinct where their behavior
requires it, and thread callback operation context. `Any` is permitted only at
an explicitly marked raw BEAM/FFI boundary; it is not a universal callback
type and must not be used to erase these relationships. Add positive and
negative tests proving cross-callback state/result mismatches are rejected
before this sub-phase is complete. All four transparent object floors now
also have a nested `beam_ops self` proof: the operation is reparsed inside
each generated lifted module and executes through the ordinary typed wrapper.

#### Phase 4c — `fsm`

**STATUS: LANDED — structured `syntax family` surface (2026-07-15); see "Structured
FSM status" in the `OPEN GATE` section. The 2026-07-13 transparent-rule expansion
described below was the first replacement, since refined into the family surface.**
The public `fsm` syntax now expands to
an ordinary lifted `GenStatem` module and starts through the typed
`Std.Otp.start_statem` wrapper. In addition to the bootstrap form, the
standard-library macro accepts an explicit `state <Type>` clause and emits a
module-local `State` alias shared by `init/1` and the event callback data
slot; ordinary elaboration rejects mismatched callback results. The
bootstrap and typed floors are tested structurally and through the generic
Unix runtime path. Transition-table lowering, payload preservation,
event/state derivation, and callback-context typing remain required. The FSM
floor now also has explicit `init` and `handle_event` callback-body forms with
delayed single-expression bodies and ordinary transition-result checking
(`43a0b947`).

Define `fsm` in `lib/std/fsm.cure`. Preserve transition-table and callback
mode compatibility, derive shared message/state information, emit the
appropriate closed behavior callbacks, and express dispatch and helpers as
ordinary declarations. The first transition-table slice is now language-owned:
`Transition` is a checked ADT, `transition` rows are transparent syntax, and
`fsm ... transitions [...]` dispatches through a polymorphic recursive Cure
function (`7e2f033b`, 51 focused object tests). Full callback event/state
derivation, payload-preserving transition actions, and lifecycle vocabulary
remain open. A direct tuple-destructuring implementation was rejected by the
existing elaborator with `:escaping_variable`; the supported path intentionally
uses the checked ADT rather than hiding that language gap behind a compiler
special case.
Transition-table `init/1` now derives its initial state from the first checked
row, and a generic Unix `gen_statem.cast` probe confirms that a table beginning
at `:locked` enters `:unlocked` on `:coin` (`6d3a29ad`, 53 focused tests).
Custom FSM callback bodies now also use source-level `InitResult` and
`EventResult` aliases for their erased effect contracts. This keeps direct
`pickup` callback expressions in the transparent Cure source while preserving
ordinary result checking; a focused `handle_event` pickup test covers the
alias-backed path (`3019b4bc`, 56 focused object tests). **The direct `Effect(T)`
case-motive kernel gap is now CLOSED (`6a7bf46f`) and the aliases have been
REMOVED (`1eef8b33`)** — see "RESOLVED GATE" at the end of this document. FSM
callbacks now declare `returns Effect(...)` inline.
The FSM macro now also exposes delayed-body forms for `terminate/3` and
`code_change/4`, with state/data result aliases and a negative mismatch test;
both callbacks execute through the ordinary lifted module (`84d4b30b`, 62
focused object tests).

The Tier-3 inferred FSM path now derives nullary event heads in `Std.Fsm` and
isolates the generated unit's explicit imports while retaining enclosing
declarations (`370a0c54`). Payload-bearing event views and richer transition
contract derivation remain open under the same soundness policy as actor
messages.

#### Phase 4d — `app`

**STATUS: LANDED — structured `syntax family` surface (2026-07-15); see "Structured
application status" in the `OPEN GATE` section. The 2026-07-13 transparent-rule expansion
described below was the first replacement, since refined into the family surface.**
The public `app` syntax now expands to
an ordinary lifted `Application` module with checked `start/2` and `stop/1`
callbacks, and the generic Unix/AtomVM packaging path is exercised. In
addition to the bootstrap form, the standard-library macro accepts an
explicit `state <Type>` clause and emits a module-local `State` alias shared
by application start and stop; ordinary elaboration rejects mismatched start
results. Root supervisor startup is now transparent: the `root` form emits an
ordinary `start/2` callback through `beam_ops start_supervisor`, with a compiler
regression proving the generated callback is available through the common
lift/emission path (`66302bb2`, `7b421759`). Supervisor
intensity, period, and shutdown timeout values now use `Nat`, so negative
values cannot pass ordinary elaboration while retaining erased BEAM integer
representation (`136bb396`). A phase form now
emits an ordinary `start_phase/3` callback with a delayed, single-expression
body reparsed under application callback context (`7b13fe7d`). Payload
preservation, multiple phase declarations, and effectful lifecycle-body
context remain required. Supervisor child startup now also has a checked
`child_with_args/6` path whose MFA arguments are `List(Atom)`
(`12f483b8`). Delayed callback bodies now resolve recursively through nested
AST nodes, phase callbacks guard on their declared phase, and app root payloads
flow through a polymorphic startup wrapper (`77bee942`). Multiple phase
declarations and effect sequencing remain required. The latest phase floor
defines an ordinary source-level `PhaseResult = Effect(Atom)` alias, promotes
pure values in effectful conditional, literal-match, and nested branch
positions, and lets an annotated `let pid: Pid(Atom) = beam_ops self` check its
RHS against `Effect(Pid(Atom))` while binding the payload (`769f2077`). The
focused transparent-object suite is 41 passing tests and
`mix compile --warnings-as-errors` is clean; the focused transparent-object
suite is now 44 passing tests and the algebra and lifted-module suites pass 16
and 15 tests respectively. A `phases` form now supports multiple transparent
phase/result pairs through ordinary Cure recursion and pattern matching, with
unmatched phases returning `:ok` (`1c079498`). **The direct `Effect(T)`
case-motive gap is now CLOSED in the kernel (`6a7bf46f`) and the `PhaseResult`
alias is REMOVED (`1eef8b33`)** — the app phase callback's `match` body now
checks against an inline `returns Effect(Atom)`. See "RESOLVED GATE" below.

Define `app` in `lib/std/app.cure`. Emit `Application` lifecycle callbacks,
optional phases, ordinary startup/shutdown bodies, and checked supervision
results.

For every sub-phase:

1. preserve existing syntax and compatibility behavior;
2. add structural expansion tests proving transparent output;
3. add negative callback/algebra tests;
4. add generic-unix runtime tests;
5. add nested `beam_ops` callback tests;
6. commit before the next sub-phase.

Suggested commits:

- `feat(std): replace supervisor container compiler with transparent macro`
- `feat(std): replace actor container compiler with transparent macro`
- `feat(std): replace fsm container compiler with transparent macro`
- `feat(std): replace application container compiler with transparent macro`

### Phase 5 — Remove bespoke OTP compiler paths and OTP knowledge

**STATUS: IN PROGRESS (2026-07-13; sub-phase 5a — reusable `syntax family` surface and
the beginner-friendly `Std.Syntax` builder/hygiene/diagnostic slices — landing through
2026-07-15, see the dated status blocks in the `OPEN GATE` section).** The active compiler no longer dispatches
through `ContainerMacro`, the legacy OTP raw-body parser and `__otp_container`
marker path are gone, and the closed `OtpMacro` behavior registry has been
deleted. Remaining work is auditing all generic tooling and application
resource documentation, migrating legacy examples and documentation tests,
and proving that no OTP-specific compiler case remains while the standard
library owns the vocabulary and lowering. `DepGraph` now discovers generic
`lift_module` units and no longer classifies `:actor`, `:fsm`, `:supervisor`,
or `:app` as compiler module kinds. `actor` and `fsm` are also no longer
lexer keywords; they use the same generic identifier macro dispatch as every
user-defined vocabulary. The in-repo OTP examples have been migrated from the
removed transition/handler parser to ordinary transparent macro bodies with
explicit `Cure.*` module names. Colony, Forge, Turnstile, Moneta, and Motif now
compile with typed callback bodies; their Elixir facades use standard casts,
statem calls, and `:sys.get_state/1` rather than retired generated helpers.
Moneta's host facade performs an explicit map-to-Cure-tuple conversion at its
boundary while its Cure implementation remains ordinary functions.
Project application discovery and LSP tooling now consume lifted-module
metadata and generic AST nodes rather than retired OTP container shapes, and
the LSP no longer synthesizes FSM transition or lifecycle symbols
(`00943ad4`, 26 LSP tests and 11 project tests pass).

Only after Phase 4 parity is proven:

1. delete `__otp_container` and its parser fallback;
2. delete the compiler dispatch branch for container markers;
3. delete `ContainerMacro` OTP semantics and the four bespoke object classes;
4. delete source-string compilation and direct code-server loading from the
   former actor/fsm/sup/app paths;
5. retain only generic quoted-module collection and the common BEAM writer;
6. update tests so they exercise the standard-library macros and common path;
7. remove compiler-owned OTP behavior maps, callback contracts, behavior-name
   translation, OTP-specific module validation, and any other OTP vocabulary
   from the generic compiler; define those vocabularies and their lowering in
   Cure language code, macros, and checked algebra/foreign primitives. The
   standard library and user-defined macros must be able to define an
   actor-like abstraction without compiler changes;
8. search for forbidden remnants and justify every remaining generic match.

The compiler printer and algebra formatter have now dropped their unreachable
legacy `actor`/`fsm`/`app`/`supervisor`/`child_spec` rendering branches. The
totality corpus tracks only parser-constructed generic nodes, and focused
printer, precedence, `with`, and corpus round-trip verification passes.
The compiler lexer also no longer recognizes `--event-->` or carries FSM
transition state; transition-shaped text is ordinary punctuation and identifier
tokens, leaving any higher-level transition vocabulary to Cure macros.
The compiler diagnostics module also no longer formats the retired application,
release, or FSM-verifier error families; those are project/runtime concerns and
must not remain compiler-owned vocabulary. Parser comments and helper names now
describe generic macro dispatch and lifted-module collection. The retired
behavior-verifier stage catalogs and stale OTP-specific compiler comments were
removed in `f191d8b6`. Project and LSP tooling that pattern-matched the old
application/FSM shapes was genericized in `00943ad4`; the remaining Phase 5
audit is to migrate stale documentation/examples/tests and complete the
forbidden-remnant search. The stale compiler diagnostics and genericized
compiler comments/formatter/parser surface were cleaned in
`87b2669c` and `6633b27d`; ASCII/Mermaid documentation now consumes
only the generic lifted-module metadata contract, with the draw CLI accepting
`lifted|all`, in `8f5af31b`; the story outline no longer walks retired
actor/FSM/supervisor/application container nodes (`fca7fd18`, `f6c1f340`).
The user-facing application, FSM, supervision, and language-spec guides now
describe the transparent `app`, `fsm`, `sup`, and `actor` macros, checked
`beam_ops`, and lifted modules; the tutorial follows the same callback floor
(`0984209a`, 31 documentation tests). Current example READMEs, the FSM guide,
glossary, and replay reference now use the transparent macro/algebra surface
(`217bacc5`, 23 documentation tests plus the glossary telescope check). Dated
changelog and site-post material remains historical release data and is excluded
from the present-tense forbidden-remnant gate; stale host harnesses in older
example projects remain an explicit migration surface, not current proofs.
The Colony and Forge example READMEs and compile tasks now describe lifted
module emission and no longer advertise source-string compiler loading
(`b4bf53cb`). Their Elixir facades/tests and the Motif facade have now been
migrated to the transparent callback ABI; duplicate unnamed actor starts have
a compiler regression test.
The current forbidden-remnant audit confirms that the active compiler path is
clean: no `__otp_container`, `ContainerMacro`, `OtpMacro`, `Code.compile_string`,
or direct code-server loading remains in compiler/elaborator modules. The
non-historical example references to retired `Cure.FSM.*`, `Cure.Actor.Runtime`,
old `get_state/1` helpers, and eager source-string/container compilation have
been removed from the migrated surfaces. Historical documentation and ordinary
Elixir `@impl` annotations remain unrelated to compiler OTP knowledge.

**Macro-only stdlib runtime surface (2026-07-19).** The final parallel
convenience tails in `Std.Actor`, `Std.Fsm`, `Std.Supervisor`, and `Std.App`
have been removed. Those tails called `Cure.Actor.Builtins`,
`Cure.FSM.Builtins`, `Cure.Sup.Builtins`, and `Cure.App.Builtins` and exposed a
second runtime architecture beside the transparent macros. The four modules now
own only source-defined macro derivation, checked helper data/functions, and
ordinary calls into `Std.Otp`; each generated lifted module carries its own
`start_link`/application callback surface. A dedicated forbidden-remnant test
requires the macro and `Std.Otp` fragments and rejects restoration of any
`.Builtins` bridge in these active stdlib modules.

Gate: no public OTP macro or compiler path can bypass parse, recursive
expansion, elaboration, validation, and common emission, and compiling a new
user-defined behavior/macro must not require adding an OTP-specific compiler
case.

Suggested commit:
`refactor(compiler): remove bespoke OTP object compilation after macro parity`

### Phase 6 — End-to-end verification and remaining macro program work

1. Build the generic-unix AtomVM from
   `/Users/ch/Develop/esp32-beam/AtomVM`.
2. Package generated Cure modules with the required estdlib beams.
3. Run generated supervisor/application and all four macro runtime proofs.
   The generic-unix AtomVM package proof now includes a generated actor child
   under the generated supervisor and a transition-table FSM, with the typed
   FSM starter invoked using its initial state (`3cc076b9`, 1 test passed after
   a clean AtomVM rebuild). The AtomVM proof remains 1 passing after the latest
   source changes. The source-level four-macro callback floors, indexed
   reducer/view/flow bundle, and embedded SP6 builders are implemented and
   covered. The direct `Effect(T)` motive gap is **CLOSED** (`6a7bf46f` +
   `1eef8b33`); **automatic message-code derivation remains the one open gap**
   and is now a funded work programme, not a tracked excuse — see "RESOLVED
   GATE" and "OPEN GATE" below.
4. Run skeptical review to two clean passes.
5. Run `mix compile --warnings-as-errors`, the full `mix test` gate, Antigen
   verification, and formatting checks. Current results: warnings-as-errors
   clean; full gate `4060 passed` (3 doctests, 4057 tests), `1 skipped`, 128
   expected immune responses; Antigen-only gate `556 passed`, 141 expected
   immune responses, with `318/318` shape coverage.
6. Confirm the worktree is clean and update the live state with exact counts.

Gate: no replacement, merge conflict, legacy regression, missing new test,
runtime failure, or implementation gap remains. Only then may the DONE
criterion be marked complete.

Suggested commit:
`test: verify transparent OTP macros across Unix and AtomVM end to end`

### Standing rules for every phase

- ~~TCB delta is zero; do not modify `lib/cure/core/*`.~~ **SUPERSEDED 2026-07-14
  by operator authorization** (see "RESOLVED GATE" below). This rule is what
  deadlocked the run: the `Effect(T)` motive gap was a genuine kernel
  completeness bug, so "zero TCB delta" and "no workarounds" could not both
  hold, and the autopilot papered the conflict over with typealiases rather
  than surfacing it. A kernel change is now permitted **when it is a
  completeness fix that aligns with Idris/Agda/Lean**, and it carries the full
  TCB bar: red-green, an Antigen antibody proving termination and no new
  equations, the full Antigen suite, and the full test suite. It is NOT a
  licence for convenience changes to `lib/cure/core/*`.
- Run commands from the worktree root, never the parent clone.
- Run one `mix` suite at a time.
- Use explicit pathspecs for staging and preserve unrelated user changes.
- Revert Antigen seed/corpus banking noise before commits.
- Commit every phase or sub-phase with a highly descriptive message.
- Do not return control or declare completion while a gate is open.

## CRITICAL CONTINUATION DIRECTIVE — 2026-07-13

ABSOLUTELY CRITICAL: Continue this autopilot without returning control to the
user until every phase in `## ORDERED TRANSPARENT BEAM PLAN` is genuinely
complete and verified end to end. The plan includes the required merge order:
`kernel-parity-batch` into `idris-parity`, then `idris-parity` into
`core-let-binder`. Do not merge directly into `core-let-binder`, restore deleted
bespoke container classes, or declare DONE while any replacement, merge
conflict, failing legacy test, missing new test, runtime proof, or listed
implementation gap remains.

This directive applies for the entirety of the session and every context
compaction. Commit every implementation phase with a highly descriptive commit
message and keep the worktree clean between phases.

## RESOLVED GATE — direct `Effect(T)` case motives (2026-07-14)

**Operator authorized the kernel fix and the removal of the workaround.** Both
landed. This gate is CLOSED.

**The bug.** `check_motive_wf` sorts a motive body with `infer_type_value_sort`,
which had clauses for `{:vtype}`, the neutrals, the primitives, `{:vdata}` and
`{:vpi}` — but none for `{:veffect_type, _}`. A `case`/`match` whose result type
was a direct `Effect(T)` fell to the catch-all and came back a spurious
`:bad_motive`. `infer/2`'s own formation rule (`Effect : Type l -> Type l`) types
the identical TERM without complaint; only the value-side sorter was missing the
arm. A false negative, never unsoundness.

**Why it hid for so long.** A `typealias EventResult = Effect(Atom)` makes the
motive body an `{:nglobal}` neutral, which the typealias clause (`3516c843`)
already admitted. So the aliases *worked* — they just moved the type behind a
name the kernel happened to accept. 19 of them accumulated across
`lib/std/{actor,fsm,app}.cure`, one wherever a `delayed raw` callback body (i.e.
a body that could be a `match`) landed. The tell: `supervisor.cure` never needed
one, because its callbacks have fixed tuple-literal bodies and so never built a
motive at an effect goal.

**Fix** (`6a7bf46f`, K-layer/TCB): one clause, mirroring the formation rule —
`Effect(t)` sorts at `t`'s own level. It recurses on the sub-VALUE rather than
reifying, for the same reason the `{:vpi}` clause does: `Quote.reify` collapses
`{:vdata, name, args}` -> `{:data, name, args, []}` and loses the param/index
split, so reify+re-infer would turn an indexed payload like `Effect(SNat s)` into
a false `:arg_arity` -> `:bad_motive`.

TCB bar discharged: red-green (2 of 3 unit pins red before, all green after);
Antigen antibody through the real kernel with an accept pin, a reject pin (an
`Effect` head over a VALUE global is still refused — the accept set is enlarged
but BOUNDED), a termination pin (nested `Effect(Effect(T))`, structural descent),
and a no-new-equations pin (`Effect` stays congruence-only: not convertible with
its payload nor with a differently-payloaded sibling); full Antigen suite;
coverage floor re-recorded (kernel total 437 -> 438).

**Cleanup** (`1eef8b33`): all 20 alias lines deleted; every callback declares its
`Effect(...)` contract inline. `State`/`Message`/`Event` aliases are untouched —
those bind a macro type parameter to a name shared across callbacks, which is a
real abstraction. Transparent-object suite 68 passed; AtomVM proof 1 passed; full
suite 4067 passed, 1 skipped, 318/318 Antigen coverage.

**Lesson for the next run.** The deadlock was self-inflicted: "TCB delta is zero"
+ "no workarounds" + "never declare DONE with an open gap" is unsatisfiable when
the gap IS a kernel bug. The autopilot resolved the conflict by papering over it
and recording the paper as a "compatibility bridge". When two standing rules
contradict, STOP and surface the contradiction — do not pick the one that lets
you keep moving.

## OPEN GATE — automatic message-code derivation

The remaining derivation gap is now narrowed. Operator directive (2026-07-14):
**build source-language reflection/derivation. Do not work around it.**

The nullary-constructor path is landed in the source macros: `actor` and `fsm`
inspect their reflected match arms, synthesize one shared nominal message/event
declaration, and emit direct callback code in an isolated lifted unit. Tests now
also prove that the generated `ActorMessage` crosses the lifted-unit boundary
into an enclosing caller's `Pid(ActorMessage)` and `beam_ops tell` call. The
computed-result path now shares the parser's compile-time hygiene protocol:
explicit generated markers are freshened while reflected use-site syntax is
left untouched. Typed payload derivation is now landed for explicit constructor
views; the remaining work is multi-channel `handle_call` reply typing, plus
retirement of the standalone proof exemption once the derived transparent
operation templates are provable without a use-site context.

**Goal.** Today an `actor` must be handed an explicit `messages <Type>` clause
(and an `fsm` an `events <Type>`). The std macro should DERIVE the message type
from the handler clauses, so `beam_ops self`/`send`/`call` can mint a `Pid(m)`
carrying the callback's message code instead of leaving `m` undetermined.

**Reconnaissance already done — do not redo it:**

- **Tier-3 reflection is ALREADY BUILT**, not future work. Of the 6 slices in
  `docs/superpowers/specs/tooling/2026-07-12-tier3-computed-by-execution-design.md`,
  slices 1, 2, 3, 5, 6 are landed and slice 4 is partial. `computed by` parses;
  `Std.Syntax` is a real ADT with a reflection bridge (`macro_syntax.ex`);
  compile-time execution runs inside-out, cycle-detecting and budgeted
  (`macro_expand.ex`); `check … else fail` works; typed derived records (`a.name`,
  the operator's steer) are live and tested. Tier-2 (`becomes`) is verbatim hole
  substitution — which is exactly WHY `messages <Type>` must be hand-written
  today: the template cannot look inside `<cast_body>`.
- **`Std.Otp.MessageCode`** (`otp.cure:65`, `Empty | Shape(Atom, Int, MessageCode)`)
  is VESTIGIAL — referenced by nothing but its own unit test. Do not confuse it
  with the `m` in `Pid(m)`, which is an ordinary erased type index. Deriving "the
  message code" means synthesising a TYPE, not building a `MessageCode` value.
- **`contextual`** is consumed in exactly one place (`macro_fuzz.ex`): it exempts
  a rule from the SP3 generative self-proof. It has zero effect on parsing,
  expansion or elaboration. `beam_ops self` is `contextual` because the proof
  checks expansions standalone in infer mode with an empty context, so its
  `{m: Type}` implicit has nothing to solve against. It is the visible scar of
  the missing callback context, and derivation is what removes it.

**THE STRUCTURAL BLOCKER — do this first.** Tier-3 expansion only runs inside
FUNCTION BODIES. A `{:computed_use}` in declaration position is silently dropped
by `Program.declarations/1`, and `LiftModule.collect` runs on the PARSED AST
(`lib/cure/compiler.ex:298`) — before elaboration — so a `lift module` produced by
a Tier-3 elab would never reach codegen. But `actor` IS a declaration that expands
to a lift module. So step zero is: make Tier-3 a declaration-position pass and
move `LiftModule.collect` behind it, reordering parse -> collect -> elaborate into
parse -> expand -> collect. Generic and OTP-agnostic (so it respects the "no OTP
knowledge in the compiler" constraint), and the riskiest change in the programme.

**Slices.**

- **L0.1** Declaration-position computed expansion; move `LiftModule.collect`
  after it. (The blocker. Must be first.)
- **L0.2** Reflect the expansion context into the elab input. `expansion_context`
  (`%{behaviour, callback, arity, parameter_names, return_annotation}`) is ALREADY
  threaded through parse and `MacroExpand` — it just never reaches the Cure elab,
  because `execute/4` builds `input_cores` from the input node only. ~30 lines.
  **Do this BEFORE L0.1**: it is the cheapest high-value probe, it directly kills
  `contextual` on `beam_ops self`, and it tells us whether the context payload is
  even sufficient (`parameter_names` + `return_annotation` may not be — the state
  and message type names are probably also needed).
- **L0.3** Type repeated groups (`...`) as `List(Syntax)`. Needed for
  `on_message <pat> <body> ...`.
- **L0.4** (optional) the `quote`/`$( )` surface — slice 4. Without it the elab
  builds `Syntax` by hand: verbose, not blocking.
- **L1** A `Std.Syntax` analysis + construction library in pure Cure: walk a
  handler body's match arms, extract each arm's pattern head (tag + arity), dedupe,
  and BUILD the AST for a `type ActorMsg = ...` declaration + `typealias Message =
  ActorMsg`. This is where the derivation lives, and it satisfies "no OTP map in
  the compiler" by construction.
- **L2** Convert `actor`/`fsm` from Tier-2 `becomes lift module` to Tier-3
  `computed by derive_actor`. Then drop `contextual` from the `beam_ops` rules.

**L0.1 status (2026-07-14).** Declaration-position expansion is now generic and
landed before lifted-module collection. `Program.expand_declaration_uses/1`
first checks the ordinary macro implementation environment, then expands only
computed uses in declaration position; function bodies remain deferred to the
ordinary declaration elaborator so callback expansion context is preserved.
The compiler invokes this pass after parse/migration and before
`LiftModule.collect`. Lifted modules inherit enclosing declarations, imports,
macro-generated computed-input records, and ordinary functions, with local
template names still winning. End-to-end coverage proves a computed use can
produce a runnable `lift module`; a companion test proves function-body
computed uses remain unconsumed by the declaration pass. (`7edd6847` plus the
follow-up declaration-expansion phase.)

**L0.3 status (2026-07-14).** Repeated Tier-3 holes now carry explicit
`syntax_repeated_fields` metadata. Their generated input records declare
`List(Syntax)` fields, and `MacroSyntax.to_core_record/4` encodes the captured
values as an actual Cure list of reflected syntax values. Ordinary fields and
the reserved context field retain their previous encoding. Coverage includes
parser metadata, compile-time pattern matching over a repeated field, and
runtime execution of the resulting function.

**Computed-result hygiene status (2026-07-15).** `Std.Syntax.fresh` is the
source-level marker for generated binders and references. `MacroExpand` now
threads a deterministic fresh counter through recursive expansion and invokes
the parser's existing marker walker on each computed result before ordinary
elaboration. Computed-result freshening rewrites only explicit `fresh(...)`
markers, because reflected use-site syntax is interleaved with generated AST
and must remain outside the generated binding scope. Tier-2 templates retain
their existing marker-plus-plain-reference behavior because hole substitution
occurs after template freshening. Tests pin both the direct protocol boundary
and a compiled computed macro that returns `{caller_value, generated_value}`
without capture. Quoted syntax remains a hygiene boundary.

**Payload derivation status (2026-07-15).** The source reflection vocabulary now
recognizes constructor patterns with explicit typed payload binders, such as
`Ping(value: Int)`, and constructs matching parameterized enum variants. The
elaborator desugars those annotations to ordinary constructor binders and
checks them definitionally against the constructor telescope, so this is a
language-level typed pattern feature rather than an actor-specific trust path.
`actor` and `fsm` now derive and execute typed payload messages/events; untyped
payload patterns remain rejected because their code set is not closed. The
remaining derivation work is multi-channel `handle_call` reply typing and any
additional payload forms that cannot be represented by an explicit type view.

**Typed callback context status (2026-07-15).** The generic staged callback
context now carries parameter type syntax and the declared return type syntax,
in addition to callback identity, arity, and parameter names. This is
compile-time `Syntax` metadata available to any computed macro; it is not an
OTP compiler branch and is not emitted into runtime code. The remaining
context work is source-level consumption by the derived operation builders,
including the reply-channel derivation that will retire the remaining proof
exemption.

**Derived call-channel floor status (2026-07-15).** The generic macro parser now
supports delimiter-aware parsed holes (`<body: Code until call>`), so a macro
can parse one indented code expression before a following grammar literal
without capturing the literal as part of the body or falling back to raw
tokens. Computed-rule dispatch also tries all rules for a keyword before
falling back to an older transparent rule. `actor` consumes this vocabulary
to derive an `ActorRequest` enum and a typed `handle_call` result from an
optional `call` arm. The initial sound floor accepts any non-empty number of
request-pattern arms whose replies agree as the reflected `state`, an
integer/float/atom/bool literal, or a tuple; unsupported expressions and
inconsistent reply categories fail at macro elaboration and never widen to
`Any`. Reflected variables carry canonical atom metadata so this check is
source-defined and does not reconstruct names in the compiler. Richer
expression inference and the one-shot typed reply capability required by the
full BEAM algebra remain open; this floor is not completion of §9.4.

**Structured actor call-channel status (2026-07-15).** The source-defined
`ActorDefinition` family now accepts an optional `on_call Cases` section in
addition to `state` and `on_cast`. The expander normalizes both family case
blocks into the reflected pattern algebra, reuses the existing request/reply
derivation, and emits the direct typed `ActorRequest` callback path. A compiled
runtime test proves `gen_server.call` against the structured actor; unsupported
reply expressions and inconsistent reply categories continue to reject through
the ordinary macro diagnostic path. Full BEAM reply capability derivation and
additional lifecycle sections remain open.

**Structured actor info-channel status (2026-07-15).** `ActorDefinition` now
also accepts an optional `on_info Cases` section. The source expander selects a
transparent default `{:noreply, state}` handler when it is absent and routes
present cases through the same checked handler normalization used by casts and
calls. A compiled integration test proves the generated `handle_info` callback
updates state from a reflected family case; no compiler-side lifecycle rule was
added.

**Structured actor lifecycle status (2026-07-15).** `ActorDefinition` now
accepts optional `terminate Code` and `code_change Code` sections. The source
expander emits those bodies directly and supplies the ordinary `:ok` and
`{:ok, state}` defaults when they are absent. Runtime assertions cover both
overrides. It now also accepts optional `initial Expression` and `init Code`
sections: `initial` derives a nullary `start_link` whose callback returns the
captured state expression, while `init` supplies the callback body directly;
the default remains `start_link(initial)`. The shared syntax builder exposes a
safe `unit_literal` marker and the lifted-module path lowers it recursively
before elaboration. Runtime assertions cover all three initialization modes,
and the complete actor computed suite is green at 19 tests.

**Hardest sub-problem** (not the reflection, not even the reorder): the derived
message type is a NEW NOMINAL DECLARATION that must exist before the lifted module
referencing it is elaborated, and must be the SAME nominal type external `send`
sites check against. One expansion must return two things into two scopes. The
representation supports it (`MacroReflection.lift/1` already takes a list), but the
splice site (`macro_expand.ex:74`) and `LiftModule.request_ast/1` both assume a
single node. Secondary: `handle_call` needs TWO derived indices (request `q` and
reply `r`), and the reply type comes from arm BODIES, not patterns.

**Shared macro definitions (2026-07-14).** Reflection provides a typed view of
one macro invocation; it is not itself a container-level inheritance or
definition-sharing mechanism. Common callback construction, state plumbing,
behaviour declarations, and syntax normalization therefore belong in ordinary
Cure functions over `Std.Syntax`. The `actor`, `fsm`, `sup`, and `app` macros
will remain thin source-level adapters that normalize their inputs and call
those shared builders. A builder may return a syntax block containing shared
declarations and specialized callbacks, allowing definitions to be reused
lexically across macro expansions without adding a compiler-owned OTP object
model. A local macro remains useful for strictly textual repetition, but it is
not a substitute for the typed `Std.Syntax` analysis/construction layer needed
to derive message types and validate handler shapes.

**Reusable macro surface blocker (2026-07-15).** The existing standard-library
containers still repeat the same `syntax actor`/`syntax fsm`/`syntax sup`/`syntax
app` grammar prefixes and lifted callback declarations for every optional
lifecycle variation. This is not an acceptable authoring model for the final
language: a user-defined actor-like abstraction cannot copy a private standard
template and remain maintainable, and moving the repetition into an Elixir
helper would violate the source-defined vocabulary requirement.

This is now an explicit ordered sub-phase (5a), before further container parity.
The canonical surface vocabulary is:

```cure
syntax family GenServerDefinition
  state Type
  optional messages Type
  optional initial Expression
  optional init Code
  optional on_call Cases
  optional on_cast Cases
  optional on_info Cases
  optional terminate Code
  optional code_change Code
end

macro actor <name: ModuleName>
  accepts GenServerDefinition
  expands with derive_actor
end
```

The family declaration owns only the reusable body shape. The macro declaration
owns the leading syntax and expansion function. Internally `accepts` may lower
to the existing computed-rule machinery, but authors should not need to write
`Code until dedent` or `contextual computed by` for ordinary structured macros.
Generated fields must retain category metadata, source ranges, cardinality,
section order, and provenance; the reflected runtime value may remain ordinary
`Syntax`.

1. Factor common callback/import/alias/lifecycle construction into ordinary
   Cure functions over `Std.Syntax`, returning transparent declaration bundles.
2. Add generic source-level grammar rule-family composition with named slots,
   optional clauses, and override bundles. Preserve grammar diagnostics,
   lexical imports, hygiene, recursive inside-out expansion, computed rules, and
   declaration bundles.
3. Rewrite the four standard macros to use those builders and prove that a
   user-defined family can reuse the same generic machinery without any
   compiler-owned OTP case or runtime dispatcher.

The implementation must not be a string-substitution pass or a hidden runtime
container. Its output must still be ordinary parsed Cure declarations and
direct checked BEAM operations. Coverage must include nested family composition,
override precedence, duplicate/ambiguous grammar rules, generated-name hygiene,
and a byte/Core-path comparison against an equivalent handwritten expansion.

**Beginner-friendliness priority (2026-07-15).** Fold the following into the
5a implementation rather than treating them as unrelated polish:

- decoded primitive captures and explicit `ExpressionSyntax`/
  `PatternSyntax`/`TypeSyntax`/`CodeSyntax` wrappers;
- direct expander parameters with generated records retained as an advanced
  fallback;
- safe syntax templates with distinct syntax splicing, literal lifting,
  declaration-list splicing, and intentional identifier construction;
- default definition-site hygiene plus explicit caller/fresh/private/exported
  identifier operations;
- named-argument typed declaration builders under `Std.Syntax`, with raw node
  construction moved to a visibly advanced `Std.Syntax.Raw` boundary;
- ordinary record access for family fields, `List(T)` repeated captures,
  unordered sections by default, and declarative empty-block cardinality;
- `MacroResult`/`Result` convenience conversion, source provenance, and
  expansion-aware diagnostics.

The following remain explicitly parked as later work: inline expansion shorthand,
implicit block capture, aliases and convenience accessors, editor completion and
hover, formatter and macro inspection commands, grouped/plural spellings,
canonical ordering and normalization hooks, user-defined syntax categories and
syntax pattern matching, dedicated `derive`/`typed macro` forms, phase controls,
and public export-policy syntax. These must layer on the same safe family,
hygiene, diagnostic, and direct-emission contracts.

**Structured family lowering status (2026-07-15).** The first 5a slice now
parses `syntax family` declarations with typed fields and cardinality, accepts
structured macro headers with leading captures, and lowers
`accepts Family`/`expands with expander` to the existing generic computed-macro
protocol. Family bodies are parsed as unordered named sections using ordinary
Cure expression and type parsing; `Cases` is represented by a generic case
block, not an OTP-specific node. Generated family and invocation records are
ordinary declarations, nested family values are reflected into Core, and the
full path is covered by a compiled user-defined family expansion.

This slice intentionally leaves the generated-record calling convention as
the advanced fallback. Direct expander parameters, primitive literal decoding,
syntax-template interpolation, typed declaration builders, and the safe/raw
API split remain ordered follow-up slices from the beginner-friendliness list;
none may be implemented by introducing compiler-owned domain knowledge.

**Direct expander arguments status (2026-07-15).** Structured family rules now
offer the expander ordinary captured arguments as a first execution candidate,
while preserving the generated invocation record and generic `Syntax` fallbacks
for compatibility. Nested family records omit the reserved expansion-context
field, and generated type names preserve their source capitalization. Partial
or undecodable candidate applications fall through to the next valid calling
convention rather than being mistaken for a successful expansion.

**Shape-specific syntax aliases status (2026-07-15).** Generated family fields
now use readable aliases such as `TypeSyntax`, `ExpressionSyntax`,
`ModuleNameSyntax`, `CodeSyntax`, and `CasesSyntax`, all transparently backed by
the checked generic `Syntax` value. This improves expander signatures without
creating runtime wrappers or a second parser representation; `Syntax` remains
the explicit low-level escape hatch.

**Primitive literal capture status (2026-07-15).** Primitive-shaped captures
(`Int`, `Float`, `Atom`, and `Bool`) are now validated as literal syntax at the
macro call site and passed to expanders as their ordinary Cure Core values. The
same shape metadata is threaded through generated family records, nested family
records, repeated fields, and direct expander arguments. Non-literal expressions
are rejected before expansion, while non-primitive captures continue to preserve
hygienic syntax values. This is compile-time representation selection only: it
adds no runtime macro protocol or OTP-specific compiler knowledge.
Direct captured arguments are attempted first; generated family records and the
generic reflected `Syntax` value remain compatibility fallbacks. Repeated and
nested primitive fields are encoded as their ordinary `List(T)` or `T` Core
values, respectively.

`Std.Syntax` now also exposes explicit `int_literal`, `float_literal`,
`bool_literal`, `string_literal`, and `atom_literal` builders for the reverse
direction. These are ordinary syntax constructors with explicit literal
subtypes; they do not interpret arbitrary strings as identifiers.

**Explicit macro result status (2026-07-15).** Source-defined expanders may now
return `MacroResult` using `expand`, `reject`, or `reject_all`. `Expanded(Syntax)`
and `Rejected(List(Diagnostic))` are compile-time wrappers decoded at the same
Core boundary as direct `Syntax`; rejected diagnostics remain ordinary reflected
syntax values. Legacy direct-`Syntax` results and `Syntax.Failure` remain valid
compatibility paths, and no result wrapper survives into generated runtime code.
The decoder also accepts `Std.Result`'s `Ok(Syntax)` and `Error(Diagnostic)` forms
as a convenience, without making `Result` part of the macro runtime protocol.

**Beginner-surface triage status (2026-07-15).** The foundation slices selected
for immediate implementation are semantic literal captures and explicit literal
lifting, direct-first structured expander arguments, ordinary family records and
repeated lists, and explicit `MacroResult`/`Std.Result` outcomes. The remaining
required foundation slices are typed syntax templates with distinct splicing and
lifting, definition-site hygiene with explicit name-intent operations, named
typed declaration builders, source provenance, expansion-aware diagnostics, and
the safe `Std.Syntax` versus advanced `Std.Syntax.Raw` boundary. Editor tooling,
inline shorthand, aliases, grouping/plural spellings, custom syntax categories,
syntax-pattern matching, and phase/export conveniences remain parked as later
work; none is a prerequisite for transparent compiled expansion.
The safe/raw boundary has begun additively: `Std.Syntax.Raw` now exposes
`unsafe_node`, `unsafe_leaf`, and `unsafe_raw` for deliberately unchecked
construction. Existing helpers remain source-compatible during the migration;
future typed templates and declaration builders must use the safe namespace and
leave raw construction visibly opt-in.

**Optional family-field status (2026-07-15).** Structured family fields with
`optional` cardinality now lower to ordinary `Std.Option.Option(T)` fields.
Absent sections are encoded as `None()`, present sections as `Some(value)`,
including through nested family records and both direct and generated expander
calling conventions. This removes the previous `nil` placeholder, which was
not a value of the declared syntax field type and prevented expanders from
using ordinary Option pattern matching. Repeated fields remain ordinary
`List(T)` values, and required fields still produce a compile-time missing-field
diagnostic.

Repeated family fields now include both `repeated` and `one_or_more`: each is
represented as an ordinary `List(T)` in the generated record, while a missing
`one_or_more` field is rejected with the same source-located missing-section
diagnostic used for required fields. This keeps cardinality semantics in the
declarative family grammar instead of requiring expander-side list decoding.

**Computed candidate rejection status (2026-07-15).** Direct, generated-record,
and generic `Syntax` calling conventions may be tried in sequence when a
candidate is incompatible with an expander signature. Once a candidate has
successfully normalized to an intentional `Failure`, `Rejected` diagnostic, or
invalid generated expansion, that result is terminal and is no longer replaced
by a later candidate's type error. This preserves source-defined macro
diagnostics and prevents a generic fallback from masking them with an
unrelated `foreign_ctor` or `unknown_global` error.

**Reusable family composition status (2026-07-15).** `syntax family` declarations
now support generic `includes OtherFamily` composition. Included fields are
flattened into the accepted family's ordinary generated record, preserving each
field's category and cardinality, while the parser remains unordered and the
expander receives normal record/Option/List values. Composition is validated at
the family boundary: unknown includes, inherited duplicate fields, and cycles
are source diagnostics rather than late expander failures. This is language-level
grammar reuse; it adds no OTP vocabulary, parser-side string substitution, or
runtime dispatch. Positive end-to-end coverage proves a user-defined service
family reuses a common state field, and parser coverage pins all three rejection
classes.

**Generated input identity status (2026-07-15).** The structured lowering now
names its advanced fallback record from the accepted family (`FamilyNameInputSyntax`)
rather than from the public macro keyword. The parser also preserves the
family-specific metadata when materializing a computed use, and only consumes
an indented body whose first section is declared by the family. Keyword-led or
undeclared-section bodies therefore fall through to legacy syntax rules. This
keeps a structured and a legacy rule with the same public keyword disjoint
without an OTP-specific compiler exception, while preserving ordinary legacy
fallback; the full 68-test transparent-container suite pins this behavior.

**Structured actor status (2026-07-15).** `Std.Actor` now declares an
`ActorDefinition` family with required `state` and `on_cast` sections, an
optional explicit `messages Type` override, and a source-defined `actor`
expander. The expander uses the existing transparent syntax reflection and
declaration builders to derive `ActorMessage` by default, or reuse the
caller-supplied nominal message type, and emits an ordinary lifted GenServer
module. Optional `initial Expression` and `init Code` are source-defined as
well, with the default, expression-initialized, and effectful callback paths
all producing direct compiled code. A compiled integration test covers these
paths alongside the legacy actor forms; reply-channel derivation and the
remaining callback-context gate stay ordered follow-up work.

**Structured FSM status (2026-07-15).** `Std.Fsm` now declares an
`FsmDefinition` family with required `state` and `events` sections plus an
optional `event_type Type` override. Its source-defined expander normalizes case
bodies into the checked callback shape, derives `FsmEvent` by default, or
reuses the caller-supplied nominal event type, and emits an ordinary lifted
GenStatem module. A compiled integration test covers both event-type paths,
initialization, event construction, and dispatch while the legacy FSM grammar
remains the fallback path.

**Structured supervisor status (2026-07-15).** `Std.Supervisor` now declares
a `SupervisorDefinition` family with a typed `children` section. Its
source-defined expander emits a lifted supervisor with a concrete
`List(ChildSpec)` initialization contract and the standard closed restart
strategy. Empty-child initialization and recursive expansion of nested
`child_spec` syntax are covered end to end, and legacy `sup` forms remain
available through grammar fallback.

**Structured application status (2026-07-15).** `Std.App` now declares an
`ApplicationDefinition` family with a typed `ModuleName` root section. Its
source-defined expander emits the ordinary application callbacks and delegates
root startup to `Std.Otp` through the generated code. Stop and phase callbacks
are covered by a compiled integration test; richer phase and body forms remain
legacy-compatible follow-up extensions of the same family surface. The generic
Unix AtomVM package proof now also compiles and starts all four structured
surfaces alongside their legacy counterparts.

**Typed declaration builder status (2026-07-15).** `Std.Syntax` now exposes
record-backed specifications and builders for parameters, linear parameters,
functions, aliases, lifted modules, and match arms. Macro authors can construct
these declarations through named record fields and typed builder functions;
generic positional node constructors remain compatibility and advanced
facilities. The builders produce the same ordinary reflected syntax
representation and add no compiler-owned declaration vocabulary. Semantic
validation remains in the ordinary Cure elaborator, while malformed reflected
representations are covered by the final expansion validation boundary.

**Source provenance status (2026-07-15).** Syntax reflection now carries source
line and column values through dedicated `source_line` and `source_col` mirror
attributes, reconstructing ordinary parser metadata on the way back out. This
keeps source coordinates distinct from semantic syntax attributes and gives
later expansion-aware diagnostics a stable location channel without adding a
runtime provenance object or changing generated code.

**Explicit name-intent status (2026-07-15).** `Std.Syntax` now exposes
`caller_identifier`, `private_identifier`, and `exported_identifier` alongside
the existing `fresh` primitive. These constructors preserve intent in the
reflected syntax value, and a reflection-boundary test proves caller capture is
consumed into an ordinary use-site variable before elaboration. Automatic freshening of ordinary
generated binders is still pending the scope-aware hygiene pass; `variable/1`
therefore remains compatibility behavior until generated binders and references
can be renamed as one lexical unit.

**Author-diagnostic formatting status (2026-07-15).** Structured `Rejected`
results and legacy `Failure` results now retain a dedicated macro-rejection
category through the outer code-generation error formatter. The compiler still
keeps the authored diagnostic payload opaque to the runtime, but users receive
the macro name, diagnostic count or failure name, and expansion source location
instead of an unclassified tuple dump.

**Raw expansion validation status (2026-07-15).** Raw construction is now
explicitly separated from executable expansion. Before a computed result is
converted back to parser AST, `MacroSyntax.validate_expansion/1` rejects raw and
quoted reflection forms when they appear as executable expansion nodes, along
with malformed syntax representations, malformed attributes, and malformed
syntax literals. Reflection-only values nested in syntax metadata remain valid;
they are part of the quoted `Syntax` data model and must survive a reflected
payload round trip without being mistaken for generated code. Legacy `Failure`
values remain available for the existing author-diagnostic protocol. The
compiler wraps invalid results with the macro's provenance and formats them
through the outer `:codegen_error` boundary, so advanced unchecked construction
cannot degrade into an `inspect/1`-only diagnostic or a host exception. Semantic
validation of known Cure declaration shapes remains the responsibility of the
typed builders and ordinary elaborator.

**Two design forks, with defaults (operator standing directive: align with real
languages; discuss in prose, don't ask).**

1. **Derivation soundness.** "The message type is exactly the set of patterns the
   handler matches" is only sound if the handler is exhaustive and its arms are
   unambiguous. A `_` catch-all, a variable-only arm, or a guard makes the derived
   type open or wrong. **Default: REJECT un-derivable handlers with a real
   diagnostic** (`check … else fail` already exists for this) rather than guessing.
   The derivation never has to be clever to be correct.
2. **Does `messages <Type>` survive?** **Default: KEEP it as an explicit override
   that skips derivation.** This is the Haskell/Idris posture — inference by
   default, annotation always permitted — and it keeps every existing program
   compiling.

**Template-hygiene characterized-hole status (2026-07-16).** Both SP5.3
correctness holes in the `becomes`-template freshening path are now closed with
red-green fixtures (`test/cure/compiler/macro_hygiene_test.exs`), parser-only,
TCB delta zero. (a) A `<fresh e>` binder that shares a hole's name no longer
swallows the use-site argument: freshening leaves a plain variable untouched
when its name is also a hole, so the hole's material still substitutes
(`7db30556`). (b) A use-site name that spoofs the predictable gensym namespace
(`` `g$0` `` passed as a hole) can no longer be captured by a `<fresh g>`
binder: `mint_gensym` collects every name appearing in the hole values and
advances the counter past any collision, so a fresh binder is always distinct
from injected caller material (`006a4652`). Full compiler suite green (822).
This closes the *correctness* core of the SP5.3 gate. The larger ergonomic
piece — automatic definition-site freshening of ALL ordinary generated binders
in a Tier-2 `becomes` template via a scope-aware set-of-scopes walk, keeping a
`<capture Name>` escape hatch — is now **LANDED (SP5.3, 2026-07-16:
`b6942c01`/`8d93fe39`/`d2ccf817`)** via `scoped_freshen/5` in the parser (frames
for let/block, match-arm+guard, lambda, single-clause fn-def params, comprehension
reverse-scope; map-shaped family-signature binders untouched; TCB delta zero).
Note this is the **Tier-2 template** path only. The **Tier-3 computed** path's
`Std.Syntax.variable/1` deliberately stays explicit-marker (`fresh(...)`) — per
the "Computed-result hygiene status" block, reflected use-site syntax is
interleaved with generated AST, so a computed result CANNOT be blanket-freshened
without renaming caller references; explicit markers are correct there by design,
not a pending gap.

**`contextual` retirement — empirical blocker analysis (2026-07-16).** Direct
probing (replicating `MacroFuzz.check_expression_expansion`: elaborate the
expansion in `Context.empty`) establishes the ground truth, correcting an earlier
belief that slice L0.2's context threading would retire `contextual` in ~30 lines:

- `beam_ops self` → `Std.Otp.self()` elaborated standalone fails with
  `{:unsolved_metavariables, :"Std.Otp#self"}`. `self : {m: Type} -> Effect(Pid(m))`
  has an erased result-position index `m` with nothing to constrain it — the
  *use* is genuinely context-dependent (like `[] : List a` / `read` with no
  expected type), even though the *definition* is well-typed.
- Wrapping the expansion in an **unannotated** definition body
  (`fn probe() = Std.Otp.self()`) **still fails** the same way: Cure does NOT
  infer a polymorphic signature from an unannotated body (Idris/Agda behave the
  same). Only an explicit return type naming the index
  (`fn probe({m: Type}) -> Effect(Pid(m)) = Std.Otp.self()`) type-checks. So no
  untrusted term-wrapping trick makes the empty-context proof pass — per the
  elaborator-HARD-STOP principle, the simple paths are ruled out.
- L0.2's `callback_context` reflection is delivered to **Tier-3 computed** elabs
  only (`MacroExpand`), so it never reaches the **Tier-2 `becomes`** `beam_ops`
  rules whose proof actually fails. The two were conflated.

**Consequence.** `contextual` (defer the SP3 self-proof) is the *correct* posture
for a genuinely context-dependent expansion — you cannot prove it standalone
without inventing an expected type. Retiring it soundly requires the proof to
elaborate such a rule under a **declared expected type** that binds the residual
result index. Two options, both real design slices (NOT tail-of-fire edits):
(A) generalize residual result-position erased-index metavars in the proof
harness (needs the elaborator to hand back the partial term + residual-metavar
relevance so the proof can prove "well-typed for all instantiations"); or
(B) a per-rule / per-context expected-type declaration the proof checks against.

**Recommendation REVISED to (B) after reading source (2026-07-16).** The two
`{:unsolved_metavariables, name}` producers — `finish_global_app`
(`elaborator.ex:7500`) and `finish_ctor_app` (`:6727`) — carry ONLY the callee
name; the residual args (`chosen`, which is in scope at the failure site and
whose telescope positions/erasure ARE known there) are discarded. So option (A)
is *not* the lower-cost path: it requires enriching a soundness-critical error
contract across ≥2 producers to surface which metavars are unsolved and their
erasure, THEN adding a generalization step that has no definition boundary to
attach to in the proof's bare-expression (infer-mode) elaboration. Option (B) is
strictly more bounded: the proof already has synthetic-frame machinery —
`check_block_expansion` (`macro_fuzz.ex:477`) wraps declaration expansions in a
`{:container, …, "MacroExpansionProof", declarations}` and checks them via
`Program.check_ast/1`. Extending that so a `contextual` *expression*-rule declares
a proof frame (a signature binding the residual index, e.g.
`fn __proof({m: Type}) -> Effect(Pid(m)) = <expansion>`) and is checked the same
way reuses a proven path and needs no elaborator error-contract change. It also
matches probe case 2 exactly (an explicit `-> Effect(Pid(m))` annotation makes
elaboration succeed). Cost: new macro-rule surface to carry the proof frame, plus
routing contextual expression-rules through the synthetic-def check instead of
exempting them. Still its own plan + red-green; NOT a tail-of-fire edit.

**Priority note.** This is *optional polish*, not a soundness hole: `contextual`
rules are still type-checked at their REAL use sites whenever the stdlib and the
`examples/**` corpus elaborate (PrinterTotality gate + full suite). What
`contextual` skips is only the *generative, use-site-free* self-proof — whose
value for a genuinely context-dependent rule is inherently limited.

**Derivation-programme status re-grounded against source (2026-07-16).** The
message-type **derivation** programme — which older notes (and the
`macro-message-code-derivation-programme` memory) framed as "the last open gate,
structural blocker do-this-first" — has in fact LANDED and is green. Verified this
fire: (1) declaration-position Tier-3 expansion is real —
`Program.expand_declaration_uses/1` (`program.ex:356`) expands decl-position
`{:computed_use}` nodes, and it runs at `compiler.ex:96` BEFORE `codegen` →
`LiftModule.collect` (`:300`); the "make Tier-3 a declaration pass and move
`collect` behind it" reorder is done. (2) `actor.cure` derives the message type
and reply contract from handler clauses — `derive_actor`/`derive_reply_contract`/
`derive_pattern_heads`, driven by the Tier-3 rule
`actor <name> state <state_type> derive <cast_body: Code until call> (call …)?
computed by derive_actor` (`actor.cure:75`). (3) `mix test
test/cure/compiler/actor_computed_test.exs
test/cure/compiler/declaration_macro_expansion_test.exs` = **36 passed, 0
failed** — the two-scope nominal-type + lifted-module derivation works end-to-end.

So the residual non-optional macro work is NOT derivation. Per the CURRENT
POSITION pointer it is: the safe-vs-`Std.Syntax.Raw` split, multi-channel
`handle_call` reply typing, and Phase 6 (end-to-end / AtomVM). The `contextual`
retirement (option B) is *optional* polish layered on the now-landed derivation —
note the derive rules (`actor.cure:75` etc.) still carry `contextual`, and the
sound way to drop it there is the same option-(B) synthetic-proof-frame. Until a
planned slice takes it, `contextual` stays and is honest.

**Structured-only OTP and constrained-capture status (2026-07-19).** The
unreleased positional `actor`/`fsm`/`sup`/`app` compatibility rules and their
orphaned emitters are removed (`84b83d30`), along with the generic parser
ambiguity heuristic they required. Characterization fixtures whose only subject
was that unreleased grammar were retired; structured-family, live OTP, and
generic-Unix AtomVM gates remain. Structured matching now pins zero-progress and
missing-required-field rejection (`7dac09b3`). `Expression` is a supported proof
domain (`10fde963`). Rule and family-field obligations parse, print, preserve
order, validate capture ownership, and resolve through the ordinary coherence
table at the real caller-side inferred type (`0cc167ae`, `e192bd7a`).
Obligation-bearing rules defer definition-site fuzzing because evidence is
necessarily contextual, while positive and negative use-site tests prove
resolution and `no_instance` rejection. `Std.Supervisor` consumes the generic
facility through `child Module id Expression where BeamEncode(identity)` and
emits direct `encoded_child(module, to_beam(identity))` code; the placeholder-ID
mutation workaround is gone (`8a5eaa66`). The structured computed-use printer
now renders family sections, so migration round-trips the new surface
(`06fc990a`). The final structured AtomVM test passes (`6cb53670`). Full `mix
test`: 4,961 tests, 3 failures, all three caused solely by the intentionally
empty `examples/` directory (`examples/hello.cure` absent), matching the known
workspace baseline.

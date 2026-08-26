# Cure Macro Facility — Master Specification Digest

**Date:** 2026-07-21

**Scope.** This document condenses the 45 specs in `docs/superpowers/specs/macros/` into one
reference that can replace reading them individually. It covers: the core macro facility (the ONE
compiler frontend feature — container, meta-grammar, power tiers, hygiene, staging, reflection,
zero-TCB soundness, Racket parity, OTP container ownership); the self-proving-macro and
composition extensions; the OTP/BEAM macro programme (transparent algebra → the authoritative
reflective design → actor consolidation → constrained expansions → the parked type-aware tier);
the beginner-embedded-surfaces product programme with its infrastructure (error explainers,
`check`, `units`, toolchain, `blocks`) and its full catalog of domain-DSL child specs; and the
100-idea backlog. Where a later spec supersedes an earlier one, only the final design is kept and
the supersession is noted in one line. An appendix lists every source file.

---

## 1. Core macro facility (2026-07-08-macro-facility-design.md)

**Operator decision (locked):** Cure gets exactly ONE compiler frontend feature — a general macro
facility. No per-DSL compiler treatment, ever. Design goal: "beginner-friendly at the floor,
Racket-complete at the ceiling."

### 1.1 The `macro` container

A `macro Name … end` block holds: `syntax` rules (surface grammar as examples-with-holes),
`literal` rules (literal-token rewrites, e.g. `500ms`), an expansion member (`becomes` template or
`computed by f` elab), and `explain` clauses (registered domain-vocabulary diagnostics). Example
shape: `macro Every` with `syntax every <d: Duration> do <body: Block> end` expanding to a
generated timer `fsm`.

### 1.2 Meta-grammar: examples with holes

- Three metasymbols only: `<name: Kind>` (typed hole), `...` (repetition — ALWAYS zero-or-more),
  `( … )?` (optional group). Alternation = write separate `syntax` clauses.
- `is Category` on a rule creates/extends a syntactic category; categories are namespaced by
  macro and may be declared **open** (extensible by other macros).
- Hole kinds: `Name`, `Code`, `Block`, `Type`, `Pattern`, `Expression`, plus raw-until-delimiter
  holes for bootstrap cases. Holes may carry refinement types (`<n: {i: Int | i > 0}>`).
- Default error machinery: progress-ordered furthest-parse selection plus a context trace — "the
  rule is the documentation."
- Honest cost recorded: rules beginning with `<` stress the lexer; a severable `$name:Kind`
  fallback notation exists if needed.
- Quoted ASTs are **derived typed ASTs per category**, not a universal `Syntax` blob; `quote` and
  `$( … )` splices are typed against the category.

### 1.3 Power tiers (renumbered 2026-07-08; older sibling specs use OLD numbers — map old→new:
1→3, 2→2, 3→1, 4→4)

| Tier | Capability |
|---|---|
| 1 | `literal` rules (token rewrites) |
| 2 | `becomes` hygienic templates |
| 3 | `computed by` — total compile-time Cure elaboration functions |
| 4 | Tier 3 + reflection API |
| 5 | module rules + raw holes |

Tier-4 reflection API (closed): `resolve`, `constructors`, `infer`, `expand`, `lift`. **No
metavariable access** (`fresh_meta` etc.); extending the API requires amending the facility spec —
no other route.

Do not confuse with the separate Lean-style *consolidation* tiers from the actor spec (§5.4):
Tier 0 raw escape hatch, 1 declarative shorthand, 2 procedural expander, 3 typed MetaM analogue.

### 1.4 Hygiene, termination, purity (invariants)

- Hygienic by default; `<fresh Name>` mints fresh names; `<capture>` is the marked capture escape.
- Recursive `becomes` requires a decreasing-input check; `computed by` elabs must be
  size-change-total. **Compilation provably terminates.**
- Elabs are pure: no ambient effects, deterministic builds.

### 1.5 Staging and scoping

- Two-pass: a declares-signature pass, then elaboration (macros can be used before textual
  definition within the pass discipline).
- Macro syntax is **import-scoped**; keyword conflicts error at the use site; categories are
  namespaced; open categories allow cross-macro extension.

### 1.6 Zero-TCB soundness argument (load-bearing, repeated across all children)

Macro output is re-elaborated and kernel-checked exactly like handwritten code. A buggy macro can
produce a *rejected* or *confusing* program, never an *unsound* one. No macro machinery enters the
kernel or TCB.

### 1.7 Racket-parity audit (§13)

Already equivalent: hygiene, syntax-parse-class error discipline, phase separation (sidestepped by
the two-pass design), "the type system is the bus." Five gaps closed in-spec: module macros
(§13.1), raw holes bootstrapped via `parse` (§13.2), open categories (§13.3), `expand` and `lift`
members (§13.4–5). **Exceeds Racket** (§13.6): guaranteed-terminating expansion and type-directed
expansion. Deliberately unmatched (§13.7): arbitrary compile-time IO, unbounded computation.

### 1.8 §14 — Full OTP container ownership

Goal: the bespoke compilers for `fsm`/`actor`/`sup`/`app` become ordinary macros.

- Audit found: fsm has a pure-forms path; four containers eagerly used
  `Code.compile_string` + load (forbidden going forward).
- Raw attribute/export emission **REJECTED** in favour of a closed vocabulary:
  `OTPBehaviour = GenStatem | GenServer | Supervisor | Application` plus per-behaviour callback
  ADTs (`GenStatemCallback`, …).
- `lift module` produces a pure `QuotedModule` value; `ModuleName = Named(Text) | Fresh(Text)`.
  The orchestrator loads modules once — macros never load code.
- Lexer obstacle: `fsm`/`actor`/`proto`/`impl` are hard keywords (block full replacement until
  demoted); `sup`/`app` soft. Gate 1b = `sup` under a fresh name proving behaviour + callback +
  lift-module; Gate 1c (full replacement) gated on lexer demotion; Gate 2 = `reducer` compiles as
  a library. `proto`/`impl` need neither primitive, only the lexer.

### 1.9 Open-decisions ledger and non-goals

Ledger items 1–17; notable: #15 shared-load-path migration RETRACTED; #16 verifier-logic
migration (~900 lines) blocks full sup/app/fsm ownership; #17 lift-module × two-pass interaction.
Non-goals: no compile-time IO, no binary macro distribution, no unbounded expansion, no
proof-producing macros/tactics.

---

## 2. Self-proving macros (2026-07-11) and Racket syntax-parse ports (2026-07-12)

**Status: approved direction**, extends the base facility. Settled operator decisions
(2026-07-12): `Diagnosis` is a derived + author-extensible sum (`fail C(args)` adds points);
exhaustiveness is lenient (one `describe` may cover many points) but a missing point is the
compile error `missing_diagnosis`; generative proof = **FULL Antigen-budget expansion fuzz on
every macro compile** (cache by definition only); `region delimited by { }` optional/later;
per-rule worked `example … expands …` required (exact-Core or type-only, per-rule choice);
sequencing AFTER the base facility.

- Three-layer safety: parse layer closed/exhaustive-by-type; expansion layer proved by generation
  + intent pins; type layer keeps the never-raw fallback.
- Three new compile errors: undescribed failure point, generatable ill-typed expansion, unpinned
  rule. Type-directed generation is the one new engine cost; statistical coverage is the honest
  limit.
- Slice order: Diagnosis → examples → generative fuzz → region.

**Racket syntax-parse comparison (grounded against Racket sources).** PORT: failure-set +
maximal-by-progress failure selection; the `(message, context-frames, at-stx, within-stx)` report
shape; a `current-failure-handler`-style seam; expectation dedup; report-rendering params.
STRICTLY STRONGER than Racket: required exhaustive descriptions, first-class typed semantic
failures, generative expansion proof (impossible in untyped Racket — the headline divergence),
required examples, total terminating expansion. Constraint: SP1 must thread progress
instrumentation from the start.

---

## 3. Macro composition (2026-07-08-macro-composition-design.md)

Stacked DSLs. **Closure property:** seam obligations are machine-authored on both sides →
concrete indices → discharge by computation; generality is recovered by declaration
(quantification by enumeration).

- `provides` / `requires` theorem signatures on macros; facts arrive as *proved by construction*,
  *proved by <name>* (library Core term), or *certificate*.
- **Trust rule (load-bearing):** only proved-by-construction and proved-(certificate) facts may
  participate in typing; tested-rung facts are advisory only and never type.
- Parameterized categories — e.g. `$payload:Packet.FieldDecl(max_size: $transport.mtu)` —
  dependent types *between* languages.
- Seam discharge protocol: computation first, then fact resolution, then a composition error.
  Bilingual seam explainers (E270–E279). Explicit adapter forms are mandatory; silent coercion is
  banned. Ledger items 1–8; non-goals recorded.

---

## 4. OTP/BEAM macro programme

Supersession chain: the 07-13 transparent-algebra spec is consumed and extended by the
**07-14 reflective spec, which is self-declared "the authoritative design for the remaining macro
work."** 07-16 (actor consolidation) and the two 07-19 specs build on it.

### 4.1 Transparent BEAM algebra (2026-07-13) — implementation contract

- Checked BEAM algebra = a stdlib layer over a sealed, honest `Std.Otp.Raw`; `Effect(T)` stays
  inert (no EffectM).
- Macro output is syntax / closed compile-time values — never Elixir strings, raw Erlang forms, or
  loaded modules. Forbidden expansion products (§4.2): `__otp_container`, `Code.compile_string`,
  raw forms, code-server mutation. Verification includes proving
  `rg "__otp_container|ContainerMacro|Code.compile_string|load_binary"` comes up empty.
- **Recursive inside-out fixed-point expansion is a HARD semantic requirement.** Cycle detection
  mandatory (stack-scoped); production budget default = infinite.
- Four macros live in `lib/std/{actor,fsm,supervisor,app}.cure`, auto-preluded; replacement must
  be generic (no new `Cure.Compiler.*Macro`).
- Message codes: `handles`/`subset`/`union` are total computations — no subtyping judgment, no
  silent `Any` fallback.
- Context-introducing outer macros use declared **delayed callback slots** (§5.5).
- Closed behaviour vocabulary + callback arities; QuotedModule validation checklist;
  single-writer multi-module emission; `beam_ops` closed vocabulary (raw ops out of scope).
- Gaps ledger 1–13. (Gap #13, Effect(T) case-motive `:bad_motive`, was later CLOSED by kernel fix
  `6a7bf46f` — outside this folder.)

### 4.2 Compile-time reflective BEAM macros (2026-07-14) — AUTHORITATIVE

Mandatory dependency: the structured-compiler-diagnostics spec.

**Invariants (§2):** compile-time only — no runtime `Syntax` value, interpreter, dispatcher,
EffectM, `__otp_container`, or second runtime object layer; normal compilation after expansion;
user-definable vocabulary (the compiler owns generic mechanisms only); no avoidable workarounds.

**Research position (§4):** of the two camps — semantic/staging (Kovács, NbE) vs typed-syntactic /
modal (Idris elaborator reflection, DeLaM, Mœbius, Lean) — Cure is **typed-syntactic; Idris
elaborator reflection is the primary model**, not semantic staging.

Key designs:

- **Atom-equality normalization (§5):** extend the existing `struct_eq` reduction fold with a
  `{:vatom,_}` clause mirroring the numeric clause. Full TCB bar; 7 required proof cases.
- **Qualified names (§6):** `:"Std.List#map"` resolves in staged elaboration via generic
  resolution.
- **`contextual` (§7):** a macro-RULE flag exempting a rule from standalone expansion-soundness
  proof (recorded `deferred` by MacroFuzz); retirement depends on derivation (step 12).
- **Declaration bundles (§8):** nominal message types shared across use sites, not per-use-site
  unions.
- **Derivation (§9):** message/event codes derived from `on_message`/transition clauses; soundness
  policy REJECTS catch-alls, unguardable patterns, and overlapping clauses. Reply = one-shot
  typed channel: a `Pid(Reply(T))` field (§9.4). **v1 scope = send-conformance over nominal
  constructor sets**; typestate, multiplicity, and junk-freedom are explicitly out of scope
  (caveat: BEAM's ordered mailbox vs unordered mailbox-type theory).
- **Syntax families (§10.1):** `syntax family GenServerDefinition` with `state Type`,
  `optional`/`repeated`/`one_or_more` fields, `accepts` / `expands with`, productions like
  `syntax <from: Name> --<event: Name>--> <to: Name>`, `includes` (rejects conflicts). Built-in
  categories: Name, ModuleName, Type, Pattern, Expression, Statement, Code, Cases, Parameters,
  Fields, Declarations, ModuleBody, Token, Syntax. §10.2 splits build-now vs maybe-later features.

**§11 — NORMATIVE contract for the complete OTP macro family.** Shared architecture pipeline;
`BeamEncode`/`BeamDecode` representation boundary (validate inbound at the edge before typed
construction; raw stays visible).

- **Actor (§11.2):** a typed mailbox fold — state lives in the receive-loop accumulator, no
  ETS/wrapper process. Preferred surface: `state` / `initial` / `on_message` /
  `on_call X returns T`. Derived `Message`, `Request`, and dependent `ReplyOf` (**dependent
  replies MANDATORY**). Generated API: `start`/`send`/`stop`, named query adapters via generic
  identifier transformation, opt-in observers. Completion gates listed.
- **FSM (§11.3):** a verified constrained actor. Graph syntax `Red --Timer--> Green`, wildcard
  `*`, payload events, `when`/`update`/`perform`, hard `Event!` / soft `Event?`. A 12-item
  source-defined verifier. Forbidden legacy: `on_transition`, `%[:ok,...]`,
  `%Cure.FSM.State{}`, hidden `Cure.FSM.` prefixes.
- **Supervisor (§11.4):** closed policy vocabulary — `OneForOne|OneForAll|RestForOne`,
  `Permanent|Transient|Temporary`, `BrutalKill|Infinity|After`; 9 verifier checks; no mandatory
  registry.
- **Application (§11.5):** typed nominal phases + dependencies; must agree with `Cure.toml`.
- §11.6 cross-container composition proof program; §11.7 mandatory deletions.

§12 gives implementation order (steps 1–14); §13 a verification matrix.

### 4.3 Actor macro consolidation (2026-07-16) — design approved, implementation pending

Three backends — Gen A (16 positional `becomes` templates), Gen B (`derive` → `derive_actor`),
Gen C (family → `derive_actor_family`) — fold into one quasiquote-templated expander via
`emit_actor_parts`/`emit_actor_call_parts`. `expands with` = `computed by` + a generated typed
record (lowered by `MacroFamily.computed_rule/2`). Verified constraint: **`quote` holds exactly
one form** (single fn/expr; module blocks fail).

Steps: 1a fold → 1b templatize → 1c optional whole-module quote → 1d body passthrough → 1e terse
shorthand. **1e CORRECTION (2026-07-16, resolves open decision 1):** 15 of 16 Gen A forms take
raw callback *expressions* (not `Cases`) — these are a **permanent Tier-0 escape hatch**;
mechanism = unified family with a raw-body branch; the raw fold is guarded by
behavioral-equivalence suites (byte-identical only for derive/call + 6 quote-port goldens);
Raw01–Raw16 goldens re-freezable. Stage 2 replays the fold for fsm/sup/app; Stage 3 = deferred
Tier-3 typed layer (removes the `infer_reply_type` literal-sniffing hack behind an isolated
seam). Constraints: no `lib/cure/core/*` changes; author in `lib/std/`, never `priv/std/`.

### 4.4 Constrained macro expansions (2026-07-19) — approved, implementation pending

Problem: captures cannot state typeclass obligations, so the hidden dictionary leaks as
`:too_few_arguments`; plus `{:unsupported_hole_type, "Expression"}` and optional-only families
accepting empty prefixes.

- Surface: `Expression` capture kind; `where BeamEncode(capture)` obligations (conceptually
  `type_of`); complete-family matching with explicit `accepts Definition or empty`.
- Two-stage checking: use-site resolution, then generated-unit reification via a hygienic adapter
  in the lifted module, e.g.
  `fn __encode_child_id(id: ChildIdentity) -> BeamTerm where BeamEncode(ChildIdentity) = to_beam(id)`.
- Failures surface at the capture; **`:too_few_arguments` must never be user-visible.**
- Proof system: Expression witnesses (`0:Int`, `false:Bool`, `:witness:Atom`, generated ctors);
  constraint-aware fresh `Witness` ADT `deriving Interface` (no BeamEncode special-case);
  mandatory negative proof (`no_instance`).
- Preferred standard surfaces: actor messages `deriving BeamEncode`; FSM `Keep`/`Next`/`Stop`
  `FsmAction` ctors (no raw `:keep_state_and_data`); sup `child Counter id CounterWorker()`;
  app phases as an ADT. 11 ordered phases with acceptance gates.

### 4.5 Type-aware macro tier (2026-07-19) — approved design, **PARKED** (token budget)

Branch `core-let-binder`. **Route B chosen** (general MetaM-analogue tier) over Route A
(optics-only bespoke expander; Route A remains the fallback). Today Tier-3 runs pre-elaboration
(`declarations.ex:582` expands before context; `macro_expand.ex:222` `execute_with_env` uses
`Context.empty(env)`).

Design: (1) a `computed_use` clause **inside** `elaborate_expr_typed`; delete the body pre-pass
(declaration-producing macros stay pre-pass); (2) typed reflection baseline (a) — operand types
threaded as companion `Std.Syntax` data; an `inferType`/`whnf` callback interface (b) is
deferred; (3) re-establish cycle detection — the active stack must thread through the elaboration
context (**R1, highest risk**); freshening and `Relevance.check` unchanged. Zero TCB. 4 phases;
the optic client (postfix `expr[i]`, `<~`) is a follow-on. Effort 1.5–3 weeks.

---

## 5. Beginner-embedded-surfaces programme (2026-07-08-beginner-embedded-surfaces-design.md)

**Status: product-direction design, not scheduled.** Parent of all §6 catalog specs. Thesis:
embedded is the ideal hidden-dependent-types domain — concrete literal indices discharge by
computation. Motto: "Users declare facts; the compiler manufactures types; errors speak the
user's vocabulary."

**Four hiding principles (LAW for every child spec):**
1. Indices come from declarations, never annotations.
2. Correct-by-construction beats proved-correct (ill-formed programs are inexpressible).
3. Obligations discharge by computation or not at all (no surfaced goals, no solver, no proof
   terms).
4. `unsafe` is the pressure valve — explicit, greppable, reported.

Other parent content: §4 error-explainer architecture (see 6.1); §5 the facility origin sketch —
its `$name:Kind` / `expand ~>` notation is **superseded by facility spec §2**; §5.5 the reducer
worked example (moved to the reducer spec); §7 de-specialization ("libraries are languages"; one
declaration serves both ends of the wire); §7.5 `check` (see 6.2); §8 priorities (toolchain #1,
error-explainer #2, board #3, driver #4); §9 open decisions 1–18; §10 non-goals — **no
proof-authoring surface for beginners, ever**; no AVR target. Error-code authority: child spec
wins over this doc.

### 5.1 Error-explainer subsystem (infrastructure, not a macro; priority #2)

Three commitments: **attribution** (provenance `{macro, span, decl_path, expansion}` as term
metadata), **translation** (registered pattern-matched explainers on a fixed 4-part template:
what you wrote → why the domain forbids it → what to write instead → optional reference), and the
**never-raw guarantee** (a raw kernel error reaching a macro user is a defect by definition).

- **TCB discipline (non-negotiable):** provenance is diagnostic metadata, never semantics — the
  kernel never reads it; erasure/conversion are provenance-blind. TCB delta: zero.
- Dispatch: innermost provenance wins; outer layers may `wrap` (one line of context — recommended
  over replacement, which reintroduces the attribution gap).
- Vocabulary rule ENFORCED by a build-failing lint: type-theory terms (unify, metavariable, Pi,
  refinement, GADT, kernel, …) banned from explainer text; per-macro whitelistable.
- **E-code registry (adopted):** E001–E099 core; per-macro blocks E100–E299 (e.g. E110–E114
  driver, E120–E129 config/secret, E130–E139 fleet, E210–E219 dive, E245–E249 crossword,
  E270–E279 composition seams, E290–E299 crochet). Community macros use namespaced codes
  (`pkg/E3`) — bare E-space is first-party curated. Checked registry file; duplicates fail the
  build.
- Context queries: read-only pure functions over artifacts the macro deposited at elaboration
  time; no re-elaboration during formatting.
- Fallback: provenance + no match → honest raw term framed "this is a bug in the macro — please
  report it" (never-raw is really never-*unowned*); no provenance → existing core pipeline.
- Golden corpus (byte-for-byte): E102, E110, E115, E118, E120, E13x, E14x. Non-goals: no
  AI-generated messages; no core-diagnostic restyling.

### 5.2 `check` / `prop` — property testing productized (Antigen's engine)

- Prop bodies are Bool-valued (decidable — makes elevation constructive and verdicts honest).
- **Three-rung ladder** (fixed report vocabulary): (1) `proved by construction — <fact>; 0 runs`;
  (2) `proved (certificate — <fragment>, N steps kernel-checked)`; (3) `tested (N runs)`.
  Elevation is monotone, best-effort, never blocks a build; failure silently demotes a rung.
- Generator derivation is total over the declarable surface; **refinements narrow, never filter**
  (no generate-then-discard); shrinking stays inside refinements.
- **Certificate elevation:** SMTCoq-style — an untrusted reconstructor translates solver
  certificates into ordinary Core proof terms the kernel checks. **TCB delta: zero.** A trusted
  in-TCB certificate checker is **REJECTED** (locked, consistent with the SMT trust boundary).
  Honest boundary: arithmetic/finite fragment only; inductive properties stay `tested` or are
  proved once at library level — never by the user. CI caches the reconstructed Core term.
- `templates for` — a fourth macro section; sibling macros ship prop templates with dual
  provenance. Temporal props (`always`/`eventually` over generated finite sequences) = bounded
  model checking without saying so.
- Z3 model enumeration permitted only as a *generation* strategy. Default 200 runs, one printed
  seed. "No proof-authoring surface, ever. No trusted solver — locked, not open."

### 5.3 `units` — the smallest macro, consumed by everything (Tier-1 literal rules, old "tier 3")

- **DECIDED scope: additive units only** — same-unit add/sub/compare, scalar multiply, explicit
  named conversions. NO dimensional algebra (revisit trigger ledgered): additive units catch the
  real bug class (quantity confusion) at low type-level cost.
- v1 inventory: Duration (`us/ms/s`, one µs-backed Int carrier), Frequency (`hz/khz`), Percent
  (`pct`, 0..100 refinement), Baud, Voltage (`mv/v`, scaled at elaboration), Celsius (no literal
  suffix in v1), `Raw12` ADC counts (`{n | 0 <= n < 4096}`; `raw.millivolts(vref)` with explicit
  vref is the only way out).
- **Zero runtime cost** (say it loudly): rides landed Nat→Int erasure; `sleep(500ms)` compiles to
  the same BEAM code as `sleep(500)`. Refinement failures fire AT the literal (`120pct`).
  Explainers E115/E116/E117. Non-goals: no unit inference (the unit is written at the literal),
  no SI completeness.
- (Partially landed outside this folder: `Std.Units` literal units `89c9ea72`, unmerged.)

### 5.4 Toolchain ergonomics (not a macro; priority #1 — "the fifteen-minute path")

Under 15 minutes from `curl | sh` to a blinking LED with no Erlang installed. Decisions:
`cure.toml` manifest (TOML, not a macro; code is the source of truth for the board — "anything
the elaborator needs lives in code; anything only the build needs lives in cure.toml");
burrito-style self-contained binary (makes OTP 26–28 pinning enforceable — OTP-29 beams boot-loop
on AtomVM 0.6.x); **board images** with the local AtomVM patch set BAKED IN (process-dict/Enum
exavmlib helpers, `ets:whereis/1`, network-driver IDF guard, enlarged Elixir boot partition),
SHA-256 checksummed, cached; flash composition from the boarddef ("no user ever types a flash
offset"); host sim (virtual GPIO/UART/I2C/SPI, driver mocks, fleet loss/latency/partition
injection, `--seed` determinism); REPL host-side always, device `:push` with reflash fallback;
LSP for free from the macro registry; formatter with no config knobs. **Generated `start/0`
rule:** hand-written `start/0` in a module with containers is a COMPILE ERROR (move code into
`on_start`) — no silent merge. Fidelity boundary stated honestly: sim proves logic/concurrency/
protocol, never timing/electrical/RF; hardware verification stays observable-output-based.

### 5.5 `blocks` — the meta-macro (grammar-as-data dividend #3, after LSP and docs)

Any macro's declarative grammar exports as a Blockly-style visual surface with zero per-macro
work: productions → blocks, typed non-terminals → typed sockets ("socket compatibility IS the
non-terminal type" — mismatches never snap in), `Many(K)` → growable lists. Optional presentation
annex (color/icon/tooltip only — "can change nothing structural"). Blocks and text are the same
typed quoted AST — no second representation, bidirectional live round-trip, file on disk stays
ordinary `.cure` text through all four progressive-disclosure stages. `check`: every
constructable arrangement parses (proved by construction); round-trip stability via Antigen
generators over the meta-grammar. Non-goals: no new visual semantics, no block-only macros.

---

## 6. Domain-DSL catalog (children of §5; all "zero compiler special-casing"; hiding principles
are law; all status "design" unless noted)

Shared invariants: obligations over declared literals discharge by pure computation ("proved by
construction; 0 runs"); errors speak domain vocabulary, never type theory; erasure ships zero
type tax to the device; each spec ends with an open-decisions ledger and non-goals.

### 6.1 Hardware foundation

- **`board`** (priority #3, the foundation): `board :name` brings a typed pin namespace
  (`pin.gpioN : Pin(Board, n)` via landed Bounded/Fin), pre-wired bus handles, and the flash
  manifest; capabilities are refinements over a delta-reducible per-board table (input-only
  gpio34–39 → E102 "with zero special-casing"); strapping pins warn, never error; pins erase to
  plain ints (same NIF call as hand-written `@extern`); `boarddef` author surface is Tier-1
  declarative data checked at *its* build; flash manifest never reaches the type system. Future:
  claimed pins become linear under the grade wave (interim: elaboration-time claim registry).
- **`driver`** (priority #4, the ecosystem play): declare a peripheral from its datasheet —
  `reg`/`field`/`mode governed_by`/`init`. Register direction enforced; bit-windows
  non-overlapping; undeclared bits reserved and unwritable by construction; field values
  refinement-bounded. Handle = one GADT with attachment + mode axes; `Type.on(bus)` is the sole
  attached constructor, so read-before-init is unrepresentable; mode index erases. Writing the
  governing field IS the typestate transition — "checked, not asserted." Sleeper feature: a
  **derived device simulator** ("derived, never hand-written — it cannot drift"), wired by
  `cure run --sim`. Timing-critical bit-bang does NOT fit (future cost/WCET axis or NIFs).
- **`tasks` (`every`/`on`)** — Tier-2 templates onto the ESP32-proven `fsm` container (the
  parent-§5.1 `Every` sketch is canonical). `on <edge>(<pin>) debounce <dur>` subscribes to GPIO
  interrupt messages; debounce is a timestamp guard, no extra process. All task fsms supervised
  under one generated `sup` ("the blink survives the button handler's bug"). Totality = the
  watchdog story: non-terminating handlers do not compile (E150). `within 5ms` parses but is
  reserved for the WCET grade axis — produces "not yet checked," never silence. Honesty: handlers
  are not ISRs (AtomVM delivers messages); v1 lints long-blocking effects in `on` bodies.
- **`units`** — see §5.3.

### 6.2 Communication stack

- **`packet` / `codec`**: binary wire layouts with length-indexed fields (`payload :
  Bytes(length)` via landed Vector; parser cannot overrun by construction; zero-copy
  sub-binaries — "the safe parser is also the fast one"). Decisions: `u8/u16(be)/…` scalars with
  mandatory endianness (no host-endian fallback; `u16le` REJECTED); fields reference earlier
  fields only; checksum coverage by field NAME (inserting a field can't desync the CRC);
  derived fields (`length`/`magic`/`crc`) never user-supplied — a lying length field is
  unrepresentable; round-trip `parse(encode(f)) == Ok(f)` proved once centrally, inherited free.
  `codec` = same field grammar for JSON/CBOR/MessagePack; `crc` REJECTED in codec ("integrity is
  the transport's job"); a codec backs the type's Json instance so they never disagree.
- **`parse`**: PEG grammars compiling to plain total typed Cure functions — provably terminating
  text parsers (no ReDoS: "regex engines market backtracking limits; Cure markets a theorem");
  retires the `Std.Regex` dead-end on AtomVM. Left recursion and empty-body repetition rejected
  at elaboration *with the rewrite shown*; then the ordinary size-change checker suffices.
  Captures positionally typed against constructors. v1 UTF-8-byte-based. Tier-1 (`syntax` +
  `elab` over quoted rules). **Release placement 2026-07-17: parked for Cure 0.35** under the
  native-parser-diagnostics/self-hosting design (outside the 0.34 rewrite) — the only catalog
  spec with a later status change. Non-goal: no public combinator library ("the grammar surface
  IS the API").
- **`protocol`**: session types (Honda/Yoshida) with endpoint projection; surface restricted so
  ill-projectable protocols are inexpressible (`choose role` names the decider; loops are
  labeled, `continue` tail-only → sessions are finite-state, so `serve` compiles onto `fsm`).
  Two APIs per role: affine typestate handles (GADT state index; first consumer of the affine
  grade rung; "affine, not linear" — dead handles droppable) and the beginner `serve` container
  (coverage-checked clauses). **Tag elision**: deterministic steps carry NO wire discriminator;
  only `choose` points carry a `Bounded(branches)` tag. Session open carries the declaration
  hash. `timeout` is declared in the protocol. `secret` fields refuse unencrypted transports.
- **`fleet`**: choreographic programming / endpoint projection (Choral, HasChor, MPST) — one
  `hub` block of Flow logic over declared nodes compiles into per-node images; no hub at runtime.
  Purity is why the hub illusion is sound: control flow reified as dataflow (a choreographic `if`
  is a Bool signal = knowledge of choice); pure derivations replicate for free. "The illusion is
  checked, not faked." Projection residue (stateful combinator feeding sinks on multiple nodes)
  → E13x offering `at <node>` ownership, commutative `merge` (CRDT; only merge-blessed
  combinators project silently — "no solver heuristics deciding distribution semantics"), or
  `at quorum(…)`. Partial failure "impossible to ignore rather than impossible to have":
  unhandled `NodeLost` is a compile error. Node identity `Fin(k)`; no distributed Erlang on
  AtomVM — channels are generated `packet` layouts + `protocol` sessions (espnow/udp/mqtt).
  Cross-node timestamp comparison flagged.

### 6.3 State-machine family

- **`reducer`** (operator-designed surface — "it is fixed"; Tier 4, joins the facility dogfood
  gate): an fsm whose payload TYPE depends on state (per-state `over` schemas → state-indexed
  GADT model as a dependent pair `%[s: State, Model(s)]`), typed `emits`/`rejects` streams, and
  a `body` lowering onto Flow as `Signal.scan`. Multiple edges per (state, message) resolved by
  `when` guards; guard double-duty (runtime dispatch AND refinement-context discharge, e.g.
  `retries + 1 : Bounded(3)` from `when retries < 2`); singleton rule (`motor: Stopped` ~>
  refinement, zero bytes); mandatory final catch-all makes the scan total; forced state tag
  erased → runtime model is just live payload fields. Static checks: undeclared/unhandled edges,
  init conformance. No rejects declared → `rejection : Event(Never)`.
- **`workflow` / `bot`** (host-side reducer specializations): workflow = reducer + persistence +
  durable wall-clock timers + human approval points. Event sourcing by construction — emissions
  ARE the event log; state = fold of history ("replay/audit/read-model are the same one-line
  fold, not a subsystem"); "you cannot refund an unpaid order" is structural (payment_ref only
  exists in `Paid`'s schema). Durable timers: due-time row written in the step's transaction;
  at-least-once, idempotent by construction. `await approval` is sugar — "the event log IS the
  inbox." `bot`: one conversation = one actor; `ask(text) expecting T` re-prompts with the
  refinement's explainer rendered for the end user; garbage never crashes, never silently drops.
- **`web-trio` (`api`/`view`/`form`)** — host-BEAM only in v1 (AtomVM has no `:inets`, a proven
  dead-end). `api`: "the parse IS the validation" — an unvalidated value has no type to be
  passed as; refinement failure is a 400 before user code; per-request supervision (crashed
  handler = clean 500, never a crashed server); typed client + OpenAPI export. `view`: builder,
  NOT string templates; typed `Msg` events; **impossible UI states unrepresentable** (`from
  Loaded with (payload)` — the spinner cannot render beside the error banner: "the flagship demo
  sentence for the whole trio"); LiveView-style diff over websocket; text always escaped. `form`:
  step ordering is typestate; ONE declaration yields both client hints and the authoritative
  server check — the browser-allows-what-the-server-rejects bug cannot exist.
- **`agenttools`** (`tool`/`agent`): the effect system as the sandbox — an agent physically
  cannot call outside its declared tool manifest (the call doesn't type-check). One declaration,
  two artifacts (model-facing schema + checked implementation — cannot drift). Two enforcement
  layers always distinguished: static (effect rows) and runtime (model output parsed against
  schemas; violations are typed refusals, never executed). Honesty (verbatim docs requirement):
  "reduces injection to declared blast radius; does not eliminate it." IFC: secrets cannot flow
  into prompts without audited `declassify`. Audit by construction: the loop is a reducer;
  replay deterministic given recorded model responses. "No autonomous self-modification — a
  designed impossibility, not a policy."
- **`schema`**: typed versioned storage; columns as refinements (checked on write, assumed on
  read); `Id(T)`/`Ref(T)` phantom keys erase to ints; typed pipe queries (raw SQL requires
  `unsafe`). Centerpiece: **totality-checked migrations** — size-change total ("cannot hang a
  device mid-flash-rewrite"), type-correct against BOTH schemas including refinements, no silent
  data loss (unmapped field = compile error), chain-complete to every deployed version.
  **Rollback deliberately NOT a checked construct** (reverse migrations are lossy; "pretending
  otherwise is a lie") — forward-only + backup snapshot. §4b doubles as OTA device-state
  migration: `persistent in nvs` reducers register in the version chain; shape change without
  `migrate from` fails the BUILD, not the fleet. Backends ets/dets/sqlite/nvs (no Registry, no
  persistent_term, ever); one actor per store — serializable per store, "that is the whole
  story." NVS budget report computed from refinements.
- **`config` / `secret`**: `config` = Tier-1 data — `env("…")` read at BUILD time, refinements
  validated against resolved values ("never a runtime nil on the device"). `secret` = Tier-2
  sugar instantiating the two-point lattice `Public ⊑ Secret` over the Final-Core security grade
  axis; sticky label; `declassify(value, reason:)` is the SOLE downward coercion (reason
  mandatory, audited); "the label is on the TYPE, not the provenance"; sink clearance rule owned
  here (§3.5), consumed by protocol and fleet. Until kernel IFC lands: carried-not-checked +
  elaborator flow lint. Redacting wrapper covers inspect paths, NOT raw VM dumps (ledgered
  honestly, "the hardest part"). v1 = the one keyword; "one word is a product; a lattice
  declaration is a seminar."
- **`cli` / `job`**: typed CLI declarations (parser/help/completion from one declaration; `run`
  receives a refined record — "no re-checking, ever"; one rule, one message: the runtime parser
  reuses the compile-time explainer) and scheduled supervised jobs on `sup` (crash → restart →
  retry → dead-letter: "there is no path on which a failure evaporates"); `ExistingPath` is a
  validated newtype, not a static refinement (parse-don't-validate); compile-time-validated cron
  via a `parse` grammar; flags > env > config. The `cure` CLI should eventually self-host on it.

### 6.4 Flow/causality family ("one theorem, new audiences")

The Safe-FRP causality/decoupledness index is reused verbatim by four audiences:

- **`synth`**: modular patch graphs; "a feedback loop without a delay element is rejected" is
  *literally the same causality index* — a feedback edge is legal iff the loop passes a
  decoupled (memory-bearing) node. Ports typed by kind (Audio/Control/Gate) AND rate; explicit
  `a2k(window:)`/`k2a(slew:)` converters; one cable per input, mixing explicit. Honesty: "the
  BEAM does control-rate work superbly and does not do per-sample audio DSP" — SuperCollider
  over OSC; the on-device crossover that works today is CV/gate output. Units throughout
  (`up(7st)`, not `+ 7`).
- **`gates`**: digital logic — combinational loops rejected by the causality index ("real
  hardware would oscillate"; a flip-flop IS the delay that makes feedback legal). `implements`
  discharged by exhaustive enumeration, honest bound 16 inputs. Killer feature: generated ESP32
  GPIO bench harness verifies real 74xx chips against the compile-time truth table ("your
  homework is checked against physics") — the concrete pilot for check §10.8 on-device runs.
  Electrical-level checks in v1 (5V LS output into a 3.3V pin fails before flashing); one driver
  per wire ("that's a short circuit"); K-map minimization is a teaching artifact, never a
  rewrite.
- **`backtest`** (`strategy`/`backtest`): look-ahead bias is a causality violation — "a decision
  at bar t may read bars ≤ t"; `shift(-1)` and whole-period normalization are "inexpressible,
  not detected" ("backtesting is the fourth audience for one theorem"). A backtest without a
  declared cost model does not run; same-bar fills require the mandatory greppable `optimistic`
  marker printed in the report header; walk-forward splits are a type boundary (train/test
  leakage doesn't type-check); overfitting gets "only an honest lint." Report carries data hash,
  costs, fills, seed, toolchain version — "a result that cannot state its inputs is an
  anecdote."
- **`sim` / `pattern`** (+ the games decision): `sim` = agent-based modeling with exact
  reproducibility via lockstep rounds — snapshot world, agents compute `(self, nbhd, rng)`-pure
  next states (live reads inexpressible = error S014), deterministic conflict order (`Fin(n)`
  identity tiebreak), per-agent PRNG streams from one root seed. `pattern` = live-coded music
  (Tidal/Sonic-Pi): mini-notation via the `parse` macro (dogfood); hot-swap at cycle boundaries
  is the HARD dependency ("the music never stops — the demo that ends arguments about hot code
  push"); polymeter warns, not errors; NO in-BEAM synthesis — OSC out (the proven Sonic Pi
  split). **Games get NO macro**: reducer+view+on already IS the game loop; "a `game` keyword
  would be branding, not machinery" — tutorials + a tiny `terminal_view` library instead.

### 6.5 Safety-critical planning (shared: monotone-safety law — config may only TIGHTEN a
refinement, never loosen; loosening requires `unsafe`)

- **`dive`**: NDL/ascent/MOD/reserve as refinements — "the refinement IS the physiology"; "the
  purest case of indices-are-literals ⇒ everything discharges by computation." v1 = declared
  agency constant tables ("proved by lookup"), no live algorithm; pressure groups thread purely
  through table lookups. No default agency blessed. §8 safety honesty unhedged: planning aid
  only; "do not build a real-time dive computer with this — explicitly" (permanent); multi-gas
  deco "probably a permanent non-goal."
- **`flightplan`**: W&B as a 2D declared-polygon refinement checked at takeoff AND landing (the
  landing check "is the one that gets skipped" by pilots — the compiler has the fuel-burn
  numbers, so it always runs); legal fuel floors (day 30min/night 45min, "no way to select 'no
  reserve'"); runway factor ≥1.5, raise-only; POH-table extrapolation is a compile error ("the
  POH doesn't know either"); no bare numbers (heaviest `units` consumer). Print-first kneeboard
  artifacts. Not a certified EFB; no live data in v1.
- **`checklist`**: aviation challenge-and-response procedures as typestate; four static
  disciplines: goto coverage, procedure reachability, **no dead ends** ("you cannot write a
  checklist that strands the crew"), and state provenance (`check 10deg` needs a prior `set
  10deg` — "the check no paper process has ever had"). `memory` sections length-refined (≤6).
  Three surfaces from one declaration: printed cards (primary — "paper is primary in cockpits"),
  ESP32/e-paper device with schema-persisted resume, voice (ledgered). Sensed and manual
  completion advance the same state index. Not certified avionics; no POH auto-extraction (the
  exact silent-error surface this exists to eliminate).
- **`reef`** (operator flagship, backlog #99): Shuttle-grade multi-sensor redundancy no industry
  controller has — sensor quorums (`vote k of n`, median vote, `agree within` bands, sticky
  suspect, abstention for stale/uncalibrated/out-of-range), typed dissimilarity requirements,
  and **compile-time common-mode fault-domain analysis** (the crown jewel: fault-domain vector
  `{node, bus, power_rail, mount, kind, excitation}`; single-fault survivability checked by pure
  arithmetic). Control loops read ONLY voted quantities (trusting one sensor is inexpressible);
  interlocks are the sole single-channel path, safe-direction only, latching. Quorum ladder
  Full→Degraded→Lost — a Lost quantity has NO value ("the type system simply withdraws the
  number"); degradation handling coverage-checked. `profile :shop` changes what the compiler
  *demands* (quantitative level, dissimilar drop witnesses, retro-veto). Last defense stays
  mechanical and dumb. Appendix A: salinity-sensor market survey with recommended quorums.

### 6.6 Craft and games of form

- **`knit`**: the stitch algebra — every operation has a (consumes, produces) arity; central
  refinement: row consumed == previous row produced (`Row(before: Nat) -> {after | …}`); repeat
  divisibility; every declared size instantiated and checked ("adding a size IS requesting its
  proof"); shaping sections summed against schematics (drift "inexpressible to ship"); chart ↔
  written round-trip both directions. Errors "in stitches and rows, never in types."
- **`knit-vertical-scope`** (companion product doc): personas — tech editors are "the
  load-bearing persona" and economic wedge ("machine tech-edited, all sizes verified"); `— 84
  sts` callouts are checked assertions in published syntax; markers are tracked state (`sm`
  before any `pm` is a compile error); repetition speaks knitter English (`rep rnds 1 and 2`,
  `to` ranges, bare `times` REJECTED as ambiguous; `until 168 sts` verifies reachability);
  measurement repeats stay knitter-authoritative; Fair Isle float refinements promoted to a
  worked example; roadmap v1 tech-editor → v1.5 colorwork → v2 companion device/import.
- **`crochet`**: deliberately a SEPARATE macro from knit (knit's state is one `Nat`; crochet's
  is a position vector — `Vec(Position, n) -> Vec(Position, m)`, "a *better* fit for the
  dependent kernel"); knit is the degenerate case. Form-aware circle law: flat rate is
  stitch-height dependent (sc +6 / hdc +8 / dc +12 / tr +16); sphere needs mirrored decreases;
  spiral vs joined declared; E290–E299.
- **`fold`**: origami — Maekawa (`|M − V| == 2`) and Kawasaki (alternating angles / composed
  reflections = identity, exact over rationals — "no solver, no epsilon, no tolerance knob")
  checked at every interior vertex. Honesty boundary: local flat-foldability only; global layer
  ordering is NP-hard → lint-grade `attested`, never `proved` ("no rung between them to blur");
  every artifact stamped. Fold sequences are typestate; score vs cut lines are different types
  ("a machine cannot be told to cut a fold line").
- **`crossword`**: "the poster child for the locked SMT trust boundary as a product" — an
  untrusted solver fills; a short, total, boring checked verifier is the guarantee ("a better
  solver finds *nicer* fills, never *more correct* ones"). Slots derived from the grid, never
  declared; symmetry/min-length/no-unchecked-squares by computation. Uniqueness honesty: minis
  ≤7×7 `proved` by exhaustive enumeration; full grids `lint (solver-attested)` — "rungs never
  inflate, and a solver failure demotes, never lies."
- **`cad`** (`model`): typed CSG (Cadova/OpenSCAD lineage). Headline: **no result builders** —
  geometry IS a value; Cadova's builder protocol collapses to one `computed by union` fold and
  `buildOptional`/`buildEither`/`buildArray` are "deleted entirely." Dimensionality is a real
  erasing index `Shape(d)`, `extruded : Shape(2) -> Shape(3)` the sole introduction. All lengths
  `Length` (bare number = E280); wall-thinner-than-nozzle is a compile error when literal
  (flagship beyond-Cadova payoff); manifoldness inherited from the kernel "rather than proved —
  and says so." Host-side only; E280–E289.
- **`gates`** — see §6.4. **`a11y`** — a *rule pack*, not a syntax macro: WCAG's checkable core
  (contrast as arithmetic over hex literals; 44×44 touch targets; heading monotonicity as a
  fold; focus-graph totality; alt/label coverage — "absence is never silent") on by default at AA
  for every `view`/`form`/`display`, violations are ERRORS ("a rule that can be ignored is a rule
  that will be"); `unsafe a11y off` surfaces in reports. Normative honesty ceiling: never
  marketed as "accessibility solved"; e-paper/OLED support is "a genuinely novel application."

---

## 7. Macro-ideas backlog (macro-ideas-backlog.md)

100 unspecced ideas in two same-day batches of 50, each a name + pitch + invisible-machinery hook
(legend: R refinements · T typestate · U units · C coverage/totality · F flow/causality · E
effects/IFC · K check templates · P projection/purity). **Promoted to full specs (2026-07-08):**
#17 knit, #26 blocks, #33 synth, #35 dive, #37 checklist, #49 agenttools, #52 flightplan, #61
fold, #65 crossword, #78 a11y, #93 backtest, #95 gates, and #99 reef **promoted to flagship
(operator favourite)**. The other 87 span physical computing (wiring, power, display, motion,
pid), fabrication (gcode, modbus, canbus, keymap, behavior), home (home, alarm, energy, climate,
grow), food/craft (brew, quilt, kiln, railway, chem), science/lab (table, plot, stats, labproto,
notebook), teaching (turtle, lesson, automata, roll), games/stories (scene, dialogue, quest,
cards), music/stage (score, choreo), safety hobbies (ham, rocketry, drone), ops (netpolicy,
deploy, backup, alert), office/money (ledger, pricing, rota, recur, budget, split, fire,
contract), AI (prompt, evals, dataset, voice), vehicles/sky (sail, astro, ecu, solar, ev),
body/health (train, dose, meal), puzzles/worlds (conlang, srs, console, rom, mud, escape,
tournament), civic (vote, moderation, conf, transit, map), media/writing (subtitle, edit,
podcast, timelapse, darkroom, book, screen, cite, feed, wiki, genealogy), and animals/water
(flock). Recurring close, verbatim-faithful: "users declare domain facts; the compiler
manufactures types; errors speak the domain's vocabulary; every guarantee is marketed as the
disaster it prevents." All library work, zero compiler changes.

---

## 8. Source specs appendix

All files in `docs/superpowers/specs/macros/`, one line each:

- `2026-07-08-macro-facility-design.md` — THE base spec: container, meta-grammar, tiers 1–5,
  hygiene/termination, staging, reflection API, zero-TCB, Racket audit, §14 OTP ownership.
- `2026-07-08-beginner-embedded-surfaces-design.md` — parent product programme: hiding
  principles, DSL catalog, priorities, non-goals; origin sketch of the facility (superseded §2).
- `2026-07-08-macro-composition-design.md` — stacked DSLs: provides/requires theorem signatures,
  trust rule, parameterized categories, seam protocol.
- `2026-07-11-self-proving-macros-design.md` — Diagnosis sums, exhaustive `explain`, Antigen
  expansion fuzz per compile, required worked examples.
- `2026-07-12-racket-syntax-parse-comparison.md` — grounded port list (progress-ordered failure
  selection, report shape) + strictly-stronger claims.
- `2026-07-13-transparent-beam-algebra-otp-macros-design.md` — OTP-forms-as-macros contract:
  sealed Raw, forbidden products, fixed-point expansion (superseded/extended by 07-14).
- `2026-07-14-compile-time-reflective-beam-macros-design.md` — AUTHORITATIVE remaining-work
  design: typed-syntactic reflection, atom normalization, syntax families, normative §11
  actor/fsm/sup/app contract.
- `2026-07-16-actor-macro-consolidation-design.md` — three actor backends fold to one quasiquote
  expander; 1e Tier-0 raw escape-hatch correction; Lean tier table.
- `2026-07-19-constrained-macro-expansions-design.md` — `Expression` captures with `where`
  typeclass obligations, hygienic adapters, witness proofs.
- `2026-07-19-type-aware-macro-tier-design.md` — PARKED Route-B MetaM tier: `computed_use`
  inside `elaborate_expr_typed`, typed reflection, cycle-detection risk R1.
- `2026-07-08-a11y-macro-design.md` — WCAG rule pack: contrast/targets/focus/coverage as
  refinements; honesty ceiling.
- `2026-07-08-agenttools-macro-design.md` — tool/agent manifests; effects as the sandbox;
  injection honesty; audit-by-reducer.
- `2026-07-08-backtest-macro-design.md` — look-ahead bias as causality violation; mandatory cost
  models; honest overfitting lint.
- `2026-07-08-blocks-macro-design.md` — meta-macro: any grammar becomes a typed-socket visual
  block surface; lossless round-trip.
- `2026-07-08-board-macro-design.md` — typed pin namespace + boarddef + flash manifest; the
  hardware foundation.
- `2026-07-08-cad-macro-design.md` — typed CSG modeling; no result builders; dimensionality as
  erasing index; printability refinements.
- `2026-07-08-check-macro-design.md` — property testing: three-rung ladder, certificate
  elevation (zero TCB), macro-shipped templates.
- `2026-07-08-checklist-macro-design.md` — procedures as typestate: coverage, no dead ends,
  state provenance, memory-item limits.
- `2026-07-08-cli-job-macro-design.md` — typed CLI parsing + supervised scheduled jobs;
  one-rule-one-message; dead letters.
- `2026-07-08-config-secret-macro-design.md` — build-time config refinements + `secret` IFC
  label with audited `declassify`.
- `2026-07-08-crochet-macro-design.md` — position-vector stitch state; form-aware circle law;
  separate from knit by design.
- `2026-07-08-crossword-macro-design.md` — untrusted solver / checked verifier; honest
  uniqueness rungs; grid discipline by computation.
- `2026-07-08-dive-macro-design.md` — dive-table physiology as refinements; monotone safety;
  permanent no-dive-computer warning.
- `2026-07-08-driver-macro-design.md` — datasheet-declared peripherals: register/field/typestate
  discipline + derived simulator.
- `2026-07-08-error-explainer-design.md` — provenance, explainer registry, E-code blocks,
  never-raw guarantee, banned-word lint.
- `2026-07-08-fleet-macro-design.md` — choreographic hub illusion via endpoint projection;
  residue diagnostics; NodeLost as compile obligation.
- `2026-07-08-flightplan-macro-design.md` — W&B envelope, fuel floors, runway factors as
  compile-time refinements; print-first.
- `2026-07-08-fold-macro-design.md` — Maekawa/Kawasaki flat-foldability by exact computation;
  local-vs-global honesty; typestate sequences.
- `2026-07-08-gates-macro-design.md` — logic circuits: causality-index loop rejection,
  exhaustive equivalence, real-chip GPIO bench.
- `2026-07-08-knit-macro-design.md` — stitch algebra: row balance, divisibility, per-size
  proofs, shaping conformance.
- `2026-07-08-knit-vertical-scope.md` — knit product vertical: personas (tech editor wedge),
  knitter-English repetition, marker state.
- `2026-07-08-packet-codec-macro-design.md` — cannot-overrun binary layouts + JSON/CBOR
  contracts; central round-trip theorem.
- `2026-07-08-parse-macro-design.md` — total PEG parsers (no ReDoS); regex-dead-end
  replacement; PARKED for 0.35 (2026-07-17 note).
- `2026-07-08-protocol-macro-design.md` — session-typed conversations: affine handles, `serve`,
  tag elision, declaration-hash handshake.
- `2026-07-08-reducer-macro-design.md` — state-dependent-payload fsm with typed
  emissions, lowering to `Signal.scan`; Tier-4 dogfood.
- `2026-07-08-reef-macro-design.md` — flagship: sensor quorums, dissimilarity, compile-time
  common-mode fault analysis.
- `2026-07-08-schema-macro-design.md` — typed versioned storage; totality-checked migrations;
  OTA device-state migration; forward-only.
- `2026-07-08-sim-pattern-macro-design.md` — deterministic lockstep agent sims + live-coded
  music; games-get-no-macro decision.
- `2026-07-08-synth-macro-design.md` — modular synth patches; causality dividend; rate/kind
  port typing; CV out on device.
- `2026-07-08-tasks-macro-design.md` — `every`/`on` Tier-2 templates onto fsm; totality as the
  watchdog story; supervised by default.
- `2026-07-08-toolchain-ergonomics-design.md` — fifteen-minute path: cure.toml, burrito binary,
  baked board images, host sim, REPL, LSP.
- `2026-07-08-units-macro-design.md` — additive-only literal units erasing to ints; `Raw12`;
  the macro everything else consumes.
- `2026-07-08-web-trio-macro-design.md` — api/view/form: parse-is-validation, impossible UI
  states, typestate forms; host-only v1.
- `2026-07-08-workflow-bot-macro-design.md` — event-sourced workflows (durable timers,
  approvals) + per-conversation bot actors.
- `macro-ideas-backlog.md` — 100 unspecced ideas with hooks; 13 promoted (reef as flagship).

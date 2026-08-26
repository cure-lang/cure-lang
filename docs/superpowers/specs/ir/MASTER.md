# Cure IR Specification Family — Condensed Master

**Date:** 2026-07-21

**Scope.** This document condenses the entire `specs/ir/` family: the multiple-IR compilation
architecture (Surface → Elaborated Core → Value/Computation IR → Handler/Continuation IR → Flow IR →
Concurrency/Capability IR → targets), the Lean-verified middle-end and its trust boundary, the
`cure-core-0.1` JSON interchange contract, Flow machine semantics with ownership-preserving
suspension, the Lean/Core Erlang proof boundary, and the LowCure restricted ownership-aware profile
for C/Rust/Wasm/ESP32. It can replace reading the individual specs; the originals remain
authoritative for implementation detail.

**Authority hierarchy** (from README): (1) multiple-irs owns the IR sequence; (2)
lean-verified-middle-end owns the Lean boundary/validation/proofs; (3) cure-core-json-schema +
`cure-core-0.1.schema.json` own the serialized input contract; (4) cure-flow-machine-semantics owns
Flow transitions and suspension; (5) lean-core-erlang-proof-boundary owns the verified target
boundary; (6) lowcure-restricted-ir owns the restricted target profile. The 2026-07-14
backend-decoupling spec is **parked historical context**, superseded by the 2026-07-21 pipeline
(motivation only; does not override). Normative companions live in `../effects/`
(`cure-computation-effect-typing`, `dependent-effects-and-stackless-flow-design`).

---

## 1. The IR pipeline (locked architecture)

Cure does NOT lower source AST directly to Erlang abstract forms. Decision:

```text
Surface AST → Elaborated Core → Typed Value/Computation IR
  → Handler/Continuation IR → Defunctionalized Flow IR
  → Concurrency/Capability IR
       ├→ Core Erlang        (BEAM/OTP; this branch is BEFORE LowCure)
       └→ LowCure IR → C11/C89 | Rust | CFlat/Wasm | C/ESP32 scheduler ABI
```

Not every function traverses every arrow: pure straight-line code may stop at Value/Computation IR
and lower directly; anything that can suspend, cross a handler boundary, enter a scheduler, or cross
a process boundary MUST pass through Flow IR. Concurrency/Capability IR is required for
topology/deployment checking but may be erased after its checks.

**Central invariant (non-negotiable):** every IR preserves the semantics and static obligations of
the preceding IR; an IR may erase information only when the preceding phase has discharged the
proofs/checks that depended on it. Core Erlang and C are *targets*, not Cure's semantic IR — neither
can represent dependent proofs, effect rows, latent effects, continuation ownership, or deployment
constraints.

**Literature rationale:** value/computation split with type dependencies restricted to value terms
(arXiv:2601.14846); Flow IR = CPS + defunctionalization with frame constructors derived from *typed
continuation sites*, never one untyped universal record (arXiv:2111.10413); typed handler
obligations incl. pre/postconditions and continuation-use policy (arXiv:2302.01265); single-shot
continuations as a practical low-level design point (WasmFX, arXiv:2308.08347); frame-stack and
concurrent-actor Core Erlang semantics as target references (arXiv:2308.12403, arXiv:2311.10482);
direct-style source over a small core (Frank, arXiv:1611.09259) — but suspended computations are
NOT source-level values (unsafe inside Cure's dependent kernel).

### 1.1 Per-IR responsibilities

- **Surface AST** — spans, user syntax, macros, patterns, dependent terms. Never a backend input;
  macros expand before semantic IR; macro machinery must not survive into runtime IR.
- **Elaborated Core** — identifiers resolved; generated terms carry source-origin metadata; macros
  absent as runtime constructs; dependent terms explicit for kernel checking; every effectful form
  classified primitive/abstract/higher-order/suspension/actor/rejected. Last IR allowed to contain
  the full dependent language and source handler syntax.
- **Typed Value IR** — pure, normalized-by-construction value language (vars, ctors, literals, pure
  primitives, closures over computations, dependent pairs, proof terms). A closure is a value only
  when capture and body types are checked; effectful bodies never evaluate during kernel conversion.
  Erased later: runtime-irrelevant proofs, definitional-equality witnesses, source-only annotations.
- **Typed Computation IR** — fine-grain CBV: `return | let | apply | pure_op | perform | case |
  raise | handle | suspend | spawn | send | receive`. Judgment `Γ ⊢c c : A ! ρ [ι]` — `ρ` a
  qualitative effect row, `ι` an optional indexed/refinement summary (protocol state, cost,
  resources, deployment facts); `ι` never substitutes for `ρ`. Effect categories: `Primitive`
  (sealed runtime), `Abstract` (user-declared), `HigherOrder` (receives/stores a computation),
  `Suspend` (sealed transfer to scheduler), `Actor`, `Foreign` (declared FFI). Sealed effects
  cannot be removed by an ordinary user handler; handling removes an abstract effect only when the
  typing rule proves all clauses + return path account for it. Initial dependent sequencing is
  conservative: a continuation's effect/index summary may not depend directly on the result of an
  effectful computation (refinement substitution can discharge where sound).
- **Handler/Continuation IR** — makes explicit: handled operations, return/operation clauses,
  deep/shallow/scoped/sealed mode, answer-type transitions, state/resource protocols, continuation
  captures, use policy (`one_shot | affine | unrestricted`). Last IR where a continuation may be a
  higher-order function. **First implementation: `one_shot` only** (or statically safe affine) — a
  continuation must be consumed, aborted, or transferred to an owning scheduler; dropping without a
  checked cleanup path is an error for resource-bearing effects. `handle` lowers to direct code
  when no suspension escapes locally; otherwise it is a Flow boundary.
- **Flow IR** — §2. **Concurrency/Capability IR** — §3.

### 1.2 Erasure policy

Spans → IDs in Flow, debug metadata in target. Dependent types/proofs → erased after checks unless
a runtime witness is needed. Qualitative rows → attached to transitions, erased after deployment
closure check. Indexed/refinement facts → erased or compiled to witnesses after answer/protocol
checks. Continuation functions → allowed through Handler IR, **forbidden in Flow IR**. Frame
ownership → latent, then checked, then explicit token/state in Flow, then runtime/linear ABI. Macro
syntax/interpreters → compile time only, absent from every runtime IR and target. No phase may infer
"pure" from the absence of a runtime call in emitted code: purity is a typed property established
before lowering; sealed effects stay accounted for even when the target instruction is a primitive.

### 1.3 Lowering contracts

(1) Core → Value/Computation IR: preserve typing, spans, effect declarations, dependent
substitution; reject unresolved handlers, unclassified foreign calls, effectful terms in
kernel-value positions. (2) Computation → Handler/Continuation IR: handler scope, answer-type
changes, captures, use policy explicit; a handler removes only effects it is typed to handle;
deep/shallow never inferred from backend convenience. (3) Handler/Continuation → Flow IR:
semantics-preserving CPS/defunctionalization; per continuation shape a state constructor + capture
layout + proof/test artifact that state-with-frame ≈ source continuation; pure fast path only when
nothing escapes or can suspend across the boundary. (4) Flow → Concurrency/Capability IR: preserve
latent effects of callbacks/children/supervisors/mailbox handlers; explicit protocol +
serialization/ownership decision per cross-process transition; deployment effect closure computed
before target selection. (5) Concurrency/Capability → Core Erlang or C: preserve observable
concurrency actions, failure behavior, mailbox-ordering assumptions, flow transitions.

Non-goals of the architecture spec: surface keywords, concrete row syntax, exact Core Erlang
constructor API, C scheduler ABI, full dependent answer-type modification (downstream designs).

---

## 2. Flow IR and machine semantics

Flow IR is the typed, first-order, defunctionalized representation of suspended control, generated
from typed continuation sites by CPS + defunctionalization; used on BEAM paths crossing
suspension/actor boundaries and for stackless C/ESP32. It is NOT an opaque `Effect(A)` value, not a
syntax interpreter, and does not force pure computations to allocate frames.

**Syntax.** A program is a set of per-function flow machines (not one global machine). `State =
{id, captures, result, effects, step}`; `Step ::= Return(v) | Call(fn, args, success, failure?) |
Perform(op, args, success, failure?, ControlMode) | Branch(v, (Pattern × StateId)*) |
ConcurrencyAction(action, next) | Abort(failure)`; `ControlMode ::= LocalHandler |
ExternalScheduler`. Target states receive results in statically identified result slots; captures
have fixed type and layout.

**Invariants (all binding):** (1) typed transitions — exactly the fields the target state requires;
(2) explicit suspension — operation, captures, owner, resume state all named; (3) single ownership —
a one-shot frame has exactly one legal consume/abort/transfer transition; (4) no hidden effects —
anything that can suspend/allocate/send/receive/spawn/fail/FFI is in the row and the transition;
(5) bounded frame shape — statically known layout; dynamic collections are explicit heap/scheduler
values; (6) pure fast path permitted for non-suspending code; (7) handler scope — handler env
captured only when observable; sealed runtime handlers cannot be forged as user data; (8) debug
identity — states/transitions retain source-origin IDs.

**Machine.** `Config ::= Running(state, frame) | Suspended(op, payload, resumption, owner) |
Returned(v) | Failed(f)`; `Frame = {state, fields, ownership token, handler?}`; scheduler state is
separate (`ready` queue, `blocked : Map<Owner, Resumption>`, capabilities); relation `⟨config,
scheduler⟩ → ⟨config', scheduler'⟩`. `Perform(..., ExternalScheduler)` produces `Suspended` and
inserts the resumption into `blocked[owner]`; not runnable until the owner supplies a result, which
creates exactly one continuation transition `Running(success, extend(frame, v))`; failure uses the
`failure` state if present, else `Failed`. `LocalHandler` operations are handled inside the local
transition — no scheduler suspension exposed; handler resolution occurs before any external
`Suspended` config is created. The scheduler protocol is target-specific but must implement this
abstract relation.

**Ownership.** Frame lifecycle `Available → Consumed | Aborted | Transferred(owner)`; no transition
from Consumed/Aborted; a transferred frame is consumed only by its new owner; resource-bearing
frames need an explicit cleanup transition on abort/completion. Lean should encode ownership
intrinsically in transitions where practical, keeping a dynamic debug-build check until intrinsic.

**Defunctionalization contract.** For every source continuation `k`, lowering yields state `s` +
capture env `f` with `sourceResume(k, v) ≈ flowRun(s, extend(f, v))`, preserving returned values,
failures, performed effects, and ownership outcomes. Direct compilation of a continuation site is
legal only if it does not escape, cannot suspend across the local boundary, and has no resource
cleanup obligation.

**Fast paths.** May skip Flow allocation: pure returns; pure calls with non-escaping continuations;
local handlers with no suspension-capable op; compatible tail calls. Must use explicit Flow state:
scheduler suspension; stored/higher-order callbacks; actor/process boundary crossings;
resource-bearing continuations; continuations surviving the host call; operations whose
*implementation may suspend* even if one backend is currently synchronous.

**Concurrency extension.** `Process = {id, flow config, mailbox, links, monitors, trapExit}`; the
relation covers local steps, message arrival, sends, spawns, exits, links, monitors. Local Flow
semantics must not assume a scheduling order; observable equivalence via traces/weak bisimulation.

**Targets.** BEAM: non-escaping states → direct Core Erlang calls; escaping states → explicit
dispatch functions + frame records; generated programs are compiled behavior, never a runtime IR
interpreter. C/ESP32: each scheduler step returns a bounded record `Done(v) | Next(stateId, fields)
| Perform(op, payload, owner) | Fail(e)`; suspension returns to the outer loop; no suspended path
relies on native stack unwinding or unbounded recursion.

**Theorem obligations (first fragment):** capture layouts match states; transitions type-correct;
defunctionalization simulates continuation invocation; one-shot ownership preserved; fast paths
agree with the Flow path; scheduler execution preserves op/result/failure traces; concurrency
extension preserves selected observable message traces.

## 3. Concurrency/Capability IR

Separates local continuation execution from process topology, lifecycle, and capabilities. Contains
NO compiler-owned `actor`/`fsm`/`sup`/`app` — those are expanded by Cure macros before this
boundary. Entities: `process_definition` (state schema, entry flow, mailbox schema, handlers,
links/monitors, supervision policy), `deployment` (processes, instances, scheduler ownership,
foreign capabilities, required effect closure, platform restrictions), actions
`spawn | send | receive | link | monitor | exit | yield`. A process body is a Flow machine plus an
explicit mailbox boundary. Callbacks and child bodies carry **latent computation rows — spawning
does not erase them**; the deployment checker closes effects over all reachable bodies, callbacks,
supervisors, and foreign primitives. AtomVM consumes the BEAM output path; AtomVM restrictions are
target capability checks here or in the backend, never a weakening of source effect types.

---

## 4. Lean-verified middle-end

**Decision.** A Lean-implemented, Lean-checked middle-end sits between the existing front end and
the backends: canonical Cure Core over JSON → Lean validation → typed IRs → verified Core Erlang AST
(and later the LowCure path). Lean chosen over Idris/Agda: dependent types + efficient native
compiler + mature proving ecosystem + practical JSON/process integration (Idris stays a
language-design comparison; Agda a literate-metatheory tool). This is a **verified middle-end, not a
verified compiler**: parsing, macros, name resolution, and elaboration stay outside the proof
boundary until moved into Cure/Lean or certificate-emitting.

**Trust profile (initial).** Trusted, unverified: source parser/macros/elaborator. Checked by Lean
kernel: JSON validation, IR transformations + proofs, Core Erlang AST well-formedness. Trusted
external: OTP Core Erlang compiler, BEAM/AtomVM runtimes, Lean kernel + runtime, JSON
transport/process launcher, foreign primitives. For `cure-core-0.1` the proof begins at a
structurally and simply-typed validated term; Cure's dependent kernel remains a *separate* trust
assumption. **A Lean proof success must never be advertised as proof that the original source
elaborated correctly** until the front-end boundary is checked; docs/diagnostics must report trust
categories separately. Trust-reduction ladder: (1) Lean validates Core independently → (2) host
emits typed Core certificates → (3) Core elaboration in Cure/Lean → (4) macros + name resolution
into the checked pipeline → (5) bootstrapped Cure compiler checked by the same boundary. Non-goals
(first version): parse all Cure in Lean; prove the existing front end; formalize all Erlang/OTP;
prove OTP's Core-Erlang→BEAM compiler; multi-shot continuations; effectful terms in dependent
indices; JSON as permanent inter-pass representation; direct BEAM bytecode.

**Interfaces.** Standalone Lean package (`cure-verified/`) exposing `validate : JSON → Result
ValidatedCore Diagnostic` and `compile : ValidatedCore → Result (CoreErlang × Certificate)
Diagnostic`; CLI over files/stdio; internal passes on Lean values, never JSON. The host compiler
invokes the Lean executable as a separate process and must not reimplement its transformations in
parallel; golden fixtures at every phase boundary; FFI embedding only after the schema stabilizes.

**Representation strategy (fixed):** raw decoded syntax → extrinsic validator producing a checked
derivation → validated Core paired with derivation → intrinsically constrained Flow transitions
where ownership matters; lowering APIs cannot consume raw syntax. Rows: `{labels : Finset
EffectLabel, tail : Option EffectVar}` with checked union/inclusion/subtraction/closure; sealed
effects cannot be removed by ordinary row subtraction. `ComputationType = result × row × optional
index` keeps qualitative rows separate from indexed summaries. Ownership `oneShot | affine |
unrestricted`; first compiler accepts only oneShot / statically safe affine — double resume
unrepresentable where possible, dynamically diagnosable otherwise.

**Proof obligations (minimum):** validation soundness (bindings, types, rows, no runtime macros, no
unclassified foreign ops); type preservation per lowering; effect preservation (no effect performed
outside the source row; none disappears without a checked handler/capability discharge);
defunctionalization correctness; ownership preservation; concurrency preservation of observable
send/receive/spawn/exit/link/monitor/supervision; Core Erlang correctness `⟦source⟧ ≈ ⟦generated⟧`
(contextual/trace/simulation sequentially; stated weak bisimulation concurrently). Semantics must
represent **divergence and blocking**: finite traces for completed/failed runs, coinductive traces
for divergence and schedulers — big-step termination results are insufficient.

**Optimization policy:** only transformations with a preservation theorem or checked invariant.
Semantic lowerings are theorem-producing; optional optimizations use **translation validation** (an
optimizer proposes; a small Lean checker proves or the unoptimized term is kept). Allowed: pure
constant folding, dead pure bindings, row normalization, proved handler-clause pruning,
continuation-site specialization, frame liveness/shrinking, state merging when types/rows/
ownership/observables agree, tail-transition elimination, direct-call lowering, capability pruning.
Forbidden initially: effectful normalization in the dependent kernel; removing sealed effects
because a call "looks primitive"; continuation duplication; state merging across differing
ownership/effect obligations; opaque runtime `Effect(A)` containers; runtime macro interpretation;
whole-program CPS as the only path.

**Staged plan + gates:** S0 freeze `cure-core-0.1` (gate: malformed/unsupported JSON rejected
deterministically) → S1 validation + pure slice (gate: Lean output matches reference evaluator,
accepted by OTP) → S2 primitive effects (gate: no primitive effect removable by untyped
transformation) → S3 Handler/Continuation IR (gate: no double resume, no uncleaned drop) → S4 Flow
IR (gate: checked transition preservation on a suspension example) → S5 actors/deployment (gate:
observable message/failure traces preserved) → S6 C/ESP32 (gate: no unbounded native stack for
suspension) → S7 bootstrap (gate: bootstrapped compiler observationally equivalent on the corpus).
The first milestone is the small proof-producing pipeline, not "bootstrap the compiler"; Cure must
not become the sole implementation of semantic passes until its kernel can verify the metatheory.

## 5. Canonical Core JSON (`cure-core-0.1`)

Normative process boundary between front end and Lean middle-end: canonical post-elaboration Core,
not source syntax; a boundary/debug format, never the permanent internal representation. **The
decoder rejects malformed, unknown, unresolved, or unsupported input; no JSON field is trusted
because it carries a type/row/certificate claim — Lean reconstructs or checks everything.** Metadata
never alters kernel reduction or runtime behavior.

- **Envelope:** `{schema, module, imports, data, effects, definitions, concurrency, capabilities,
  metadata}`; required: `schema`, `module`, `definitions`. Unknown top-level fields rejected in
  strict mode. Serialization deterministic (ordered arrays, canonical keys, no map-order semantics).
- **Identifiers:** globals `Module.Name/arity`; locals de Bruijn; source names/spans are metadata
  (`origin` objects) and never determine binding. Duplicates, invalid indices/arities, and
  undeclared globals are rejected.
- **Types:** unit/bool/int/named/pair/sum/function(with row)/computation. Dependent nodes
  (`dependent-function`, `dependent-pair`, `refinement`) exist in the schema even though the first
  Lean fragment rejects them — unsupported nodes yield a versioned diagnostic, never silent erasure.
- **Effects:** nominal, globally qualified labels with three separate axes — `category`
  (primitive|abstract|higher-order|suspend|concurrency|foreign), `handling` (open|sealed), `control`
  (ordinary|suspending); row tail is null or an explicit row variable. Sealed labels cannot be
  removed by an ordinary user handler.
- **Values vs computations:** structurally distinguished. `perform`/`suspend` are computations,
  never values; a stored computation needs an explicitly typed computation-layer wrapper retaining
  its latent row; computations may not occur in kernel proof positions.
- **Concurrency declarations:** generic process operations, message schemas, callbacks with latent
  computation types, capability requirements only; `actor`/`fsm`/`sup`/`app` already macro-expanded;
  checked for effect closure; no implicit capability grants.
- **Validation:** `decode : Bytes → Result RawCore Diagnostic`; `validate : RawCore → Result
  ValidatedCore Diagnostic`; total decoding (structured error, never a partial term). Diagnostics
  carry phase, stable code (e.g. `CURE_CONTINUATION_DOUBLE_USE`), message, origin IDs, related
  spans; resource limits bound size/depth/lengths. Protocol: version negotiation, deterministic
  output, `--check-only`, `--dump-ir <phase>`, `--emit-core-erlang`, `--emit-certificate`.
- **Versioning:** breaking = major bump; additive = minor + explicit decoder support; schema version
  recorded in artifacts. Required fixtures: pure identity/arith; let/case; recursion; one primitive
  effect; one suspension; invalid de Bruijn; invalid row; unclassified foreign op; callback with
  latent effect; unsupported dependent computation. `cure-core-0.1.schema.json` is a structural
  prefilter; Lean stays authoritative for binding/type/effect/semantic validation.

## 6. Lean / Core Erlang proof boundary

Target = a **versioned Core Erlang subset**, not the unstable OTP `cerl` API and not BEAM bytecode.
Lean defines a Cure-owned Core Erlang AST (module, function, variable, literal, tuple, let, letrec,
call, apply, case, receive, send, spawn, exit, primitive call), pinned to a recorded OTP/Core
Erlang version per release; a constructor is not supported merely because a `cerl` helper accepts
it. Only checked terms are exposed (`WellFormedCore : CoreTerm → Prop`): scoping, arity/call
compatibility, recursion bindings, branch validity, literal/ctor shapes, process primitive
signatures, absence of macro/interpreter nodes and opaque unlowered computation containers.
`Lowered : CureCore → CoreErlang → Prop`; `compile` returns target + `WellFormedCore` proof +
`Lowered` certificate; proofs may be erased from the emitted file, but compilation succeeds only
after Lean checked them. Semantic reference: ported from the Rocq Core Erlang formalisation
(harp-project) in stages — values/expressions/envs; sequential evaluation for the emitted subset;
frame-stack semantics; process/mailbox semantics; trace/bisimulation — with recorded correspondence
notes, no equivalence claims outside the ported subset, unsupported primitives failing closed.

**Preservation theorems:** pure evaluation correspondence (literals, lets, functions, calls, cases,
tuples, recursion); result-and-trace equivalence for computations (primitive ops, suspension,
failure, actor actions); Flow lowering composed as `Cure computation ≈ Flow machine ≈ Core Erlang
dispatch`, the middle theorem covering frame ownership and cleanup, not just values; actors via
stated weak bisimulation / observable traces — sequential determinism does NOT imply actor
equivalence (scheduling and mailbox arrival are observable).

**Backend adapter** (outside the semantic AST): serializes only `WellFormedCore` terms to a
recorded OTP version; rejects unsupported constructors; runs OTP acceptance tests; preserves debug
origin metadata; must not add semantics, expand macros, interpret IR, or introduce opaque OTP
containers. The initial printer is trusted but gated by deterministic parse-back (`Lean AST →
printer → OTP parser → normalized structural comparison`, with printer/parser-version/normalization
recorded per artifact; parse success alone proves nothing; future: proven `parse(print t) = t`).
Regression gate per supported construct: JSON fixture + Lean result/trace + generated Core Erlang
fixture + OTP output + proof or explicitly documented unproved relation; unsupported constructs
fail closed with stable diagnostics. Direct BEAM bytecode emission is a separate target and must
not weaken this boundary.

## 7. LowCure restricted IR

LowCure is a restricted, ownership-aware **target profile** of Cure — not a second surface language,
not a replacement for Computation/Flow IR. Programs that cannot meet its restrictions remain valid
Cure (BEAM path); they are just not LowCure programs. The BEAM path branches before LowCure. The MCU
pipeline narrows further: Computation IR → Flow IR → **pure Flow/Request IR** → LowCure →
C/Rust/ESP32; state is an explicit named state-machine continuation, never an algebraic resumption
or a native stack to unwind.

**Precedent:** KaRaMeL/Low* (local clone `/Users/ch/Develop/algebraic-effects/karamel` @
`0a39f5a2`): a restricted profile belongs *after* high-level type/data/control transformations, and
separate C*/C/CFlat-Wasm target layers are valuable. But KaRaMeL's Low* invariant is informal (deep
guarantees live in F*); LowCure instead makes ownership/continuation obligations explicit and
checked before the backend.

**Legality profile** — a `LowCureProgram` = typed Flow/Concurrency program + proof/certificate of:
(1) *first-order control* — no higher-order continuations, dynamic handler interpreters, or macro
machinery; recursion via named calls/loops; suspension is an explicit transition to the scheduler
ABI; function pointers only with explicit signature/capture/ownership; arbitrary closure envs are
not LowCure values; (2) *monomorphic target data* — abbreviations expanded, generics specialized,
tuple/product layouts explicit, pattern matching compiled to tags/switches/branches, recursive data
via explicit indirection + declared storage policy, every layout with a known size/alignment
formula or explicit dynamic representation, layout never depending on unresolved type variables or
proofs; (3) *explicit storage classes* (checked static properties, not runtime tags) —
`Stack(frame) | Region(region) | OwnedHeap | SharedRuntime | Foreign(capability) | Static`;
(4) *closed residual effects* — only declared target capabilities (`Foreign |
Scheduler(yield/resume) | Concurrency(send/receive/spawn/exit) | Failure`), which belong to the
surrounding program/scheduler/capability layers, not to pure Flow transitions; `Suspend` lowers to
a transition record/scheduler call, never stack unwinding.

**Flow purity (ALL target profiles — a semantic property of the Flow model, not ESP32-specific):** a
Flow is a signal-graph computation, `FlowState × Signal<Input> → Pure(Signal<Output>* × NextState)`;
it never directly performs foreign, device, scheduler, mailbox, filesystem, or clock effects. The
only Flow-level bridge is **`Signal.Remote`** — a typed VM-to-VM message edge whose schema,
destination capability, ownership, and failure behavior are checked; not an escape hatch, and it
grants the receiver no authority to perform the sender's effects.

**MCU effect boundary:** Flow states construct typed *requests* (`ReadSensor | WriteGPIO |
StartTimer | SendMessage | …`) as pure data — `FlowState × Input → Pure(State × Request*)`; the
outer `program` layer or a declared capability owner interprets them and feeds typed responses/
failures back as ordinary state transitions with fixed frame layouts — an effect boundary, not a
hidden `World` token. Capabilities (GPIO, timers, storage, messaging) are explicit and owned by
interpreting code. The Cure `Effect` monad remains valid here for sequencing/failure/cleanup/
interpretation but needs no runtime monad objects — `bind` lowers to direct control flow or an
explicit scheduler state machine. The `program` macro is compile-time syntax generating the request
dispatcher; it must not introduce a runtime interpreter, opaque effect container, or dynamic
dispatch.

**Ownership.** Two separate axes that must NOT be collapsed into one "linear" flag: `usage:
unrestricted|affine|linear` and `ownership: shared|unique|borrowed`. Static capabilities `Own<T> |
Borrow<'r,T> | BorrowMut<'r,T> | Shared<T>` — no runtime wrappers required. Checker rejects:
use-after-move; two live unique owners; borrows stored beyond their region or sent across
processes; stack-owned references escaping; non-`Send` owned values in messages; dropped linear
cleanup obligations; duplicated one-shot frames. Operations declare ownership behavior (`borrow |
consume | return-own | transfer | share`); failure is part of the contract — a failed transfer
preserves the source owner or yields an explicit recovery/poisoned state, never silent loss.
Continuations: general LowCure = one-shot/affine only (multi-shot cloning excluded — conflicts with
unique resources and stack allocation); MCU profile = **no continuation value at all** — only
defunctionalized named states with static capture layouts, retainable by the scheduler but never
duplicated, inspected as functions, or resumed through dynamic handlers. Intentional ladder:
general Cure has algebraic handlers/resumptions → LowCure keeps only first-order state transitions
→ MCU has pure Flows with externally interpreted requests.

**IR shape.** Statement/control-oriented ownership-aware machine IR: `LowProgram = {types(layouts),
regions, functions, capabilities}`; functions have `Place` parameters/locals and blocks with
`Statement ::= let | move | copy | borrow | load | store | construct | drop | call | primitive` and
`Terminator ::= return | jump | branch | switch | suspend(op, places, ResumeState) | send | receive
| spawn | fail`. RValues do not hide allocation or effectful computation.

**Lowering.** Flow states → blocks/functions with explicit frame layouts; Karamel-style data
lowering (specialize → enum/struct/union layout → tag/switch/field ops; checker proves layout
agreement; infinitely sized by-value types rejected); expression-to-statement conversion fixes
evaluation order; storage resolution via ownership + escape analysis — stack only when size is
statically bounded, nothing escapes the frame, and cleanup precedes frame exit (rejected if later
Flow transitions can retain the value); handlers resolved before LowCure; MCU request/response
lowering makes pending-request states explicit with fixed layouts — request payloads may transfer
owned `Send` values but never borrows, stack addresses, or unresolved computations.

**Target profiles:** `LowCure-C` (C11/C89), `LowCure-Rust`, `LowCure-Wasm` (fixed locals, linear
memory, CFlat-like), `LowCure-ESP32` (pure Flow transitions; closed declared request/response
vocabulary; effect interpretation only in the program/capability layer; bounded pending-request and
scheduler state; no general handlers/resumptions/cloning; explicit failure/cleanup per request; no
implicit allocation in dispatch). Semantic legality checks are shared; layout/ABI/widths/alignment/
FFI are per-profile parameters. **Rust output is a validation backend only — passing the Rust
borrow checker is not the Cure ownership proof; Cure's derivation is authoritative.** Preservation
obligations (Lean): LowCure typing + closed residual effects; usage/ownership preservation;
borrow-region non-escape; one-shot frame preservation; layout/size/alignment correctness; no hidden
allocation or stack escape; evaluation-order preservation; failure/cleanup preservation; capability
closure; Flow-transition purity on every profile; MCU request/response protocol preservation;
semantic correspondence with C/Rust/Wasm execution (optional layout/register optimizations via
translation validation).

**Rejected by the first profile:** unrestricted higher-order closures; open rows at target
boundaries; unresolved abstract handlers; multi-shot resumptions; unbounded recursive by-value
data; unknown-size stack values; stack references escaping via messages/callbacks; unannotated
foreign allocation/ownership; implicit GC; runtime IR interpretation; runtime macro expansion. MCU
additionally rejects: direct effectful ops in Flow states; rows open at the Flow/Request boundary;
request payloads with borrows/stack refs/unresolved computations; unbounded pending requests; any
runtime algebraic-handler or general-continuation implementation. Sequencing: implement LowCure
after the general Computation/Flow typing boundaries exist, but design its legality checker and
storage model before C/Rust lowering begins.

## 8. Parked: backend decoupling (2026-07-14)

STATUS: PARKED. Superseded as pipeline design by the 2026-07-21 family, but its doctrine survives:
(a) the macro work (`actor`/`fsm`/`sup`/`app` importable) decoupled **syntax, not semantics** —
real decoupling needs an abstract process/mailbox/supervisor effect interface with BEAM as one
lawful implementation (generalizing sealed `Std.Otp.Raw`); (b) **the Gleam caveat** — a non-BEAM
process target means shipping a per-target scheduler/runtime (gleam/otp is BEAM-only; Lumen died
reimplementing BEAM semantics), and guarantees differ per target: a mailbox-bound proof under
`BEAMMailboxModel` is invalid under a JS event loop — **never transport a BEAM-modelled guarantee
to another target without re-deriving it under that target's named model** (evidential-systems §130
generalized); (c) **NON-NEGOTIABLE** — multi-backend must be invisible to the kernel/TCB; it is
TCB-cheap only while it lives below the erased-core narrow waist, and turns dangerous only if a
backend concern leaks up into typing; (d) its defended sequencing (effect interface → waist IR
retargeting the existing BEAM path → value-only second target → per-target process runtimes) shaped
the 2026-07-21 staged plans; (e) open question raised: should `fsm` use a more restricted "driven
transition" interface than `actor` — a ladder `fsm ⊂ actor ⊂ raw` where lower rungs port to more
targets with stronger portable guarantees? The LowCure pure-Flow/Request model is effectively that
answer taking shape.

---

## Source specs

- `README.md` — authority hierarchy across the family; marks the 2026-07-14 spec as parked.
- `2026-07-21-multiple-irs-architecture-design.md` — the IR sequence, per-IR responsibilities,
  erasure policy, lowering contracts, verification gates, literature rationale (§1–3 here).
- `2026-07-21-lean-verified-middle-end-design.md` — Lean middle-end decision, trust boundary +
  reduction ladder, interfaces, representation strategy, proofs, optimization policy, stages (§4).
- `2026-07-21-cure-core-json-schema.md` — normative `cure-core-0.1` boundary: envelope, binding,
  type/effect/value/computation nodes, validation contract, versioning, fixtures (§5).
- `cure-core-0.1.schema.json` — machine-readable structural prefilter (Lean stays authoritative).
- `2026-07-21-cure-flow-machine-semantics.md` — Flow syntax, machine configs, transition relation,
  ownership lifecycle, defunctionalization contract, fast paths, targets, theorems (§2).
- `2026-07-21-lean-core-erlang-proof-boundary.md` — Lean-owned Core Erlang subset AST,
  well-formedness, `Lowered` relation, Rocq port order, theorems, printer gate, trust claims (§6).
- `2026-07-21-lowcure-restricted-ir-design.md` — LowCure legality profile, ownership/storage, Flow
  purity + `Signal.Remote`, MCU request/response boundary, target profiles, rejections (§7).
- `2026-07-14-backend-decoupling-cureir-design.md` — parked precursor: narrow-waist thesis, Gleam
  caveat, kernel-invisibility non-negotiable, interface-ladder question (§8).

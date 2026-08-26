# BEAM / OTP Integration — Master Spec

**Date:** 2026-07-21

**Scope.** Condenses the `specs/beam/` family into one reference: the
kernel-checked typed process algebra over a sealed raw FFI base; the linear
session-channel and resource design that supersedes the original "rung 3"
plan; the `Std.Otp` conformance repairs; the boundary representation
typeclasses; the actor and FSM surfaces on the shared `ActorBehavior`
substrate; and the independent `cure port` tool. Where a later spec
supersedes an earlier one, only the final design is kept, noted in one line.

---

## 1. Typed process algebra — the foundation

**Locked decision (operator, 2026-07-09):** the BEAM process/OTP model is
exposed as a **typed algebra** — dependent, indexed operation signatures making
incorrect BEAM use a compile error — not a thin layer of asserted `@extern`s.
The typed algebra is the **only sanctioned surface**; the raw base is sealed.

### 1.1 Layers and trust boundary

User and macro-emitted code call `Std.Otp` (checked Cure: `Pid(m)`,
send/call/cast, codes, subset/union), which is the **only** importer of the
sealed `Std.Otp.Raw` (`unsafe`: the ONLY trust boundary — `@extern`s at
honest, most-permissive BEAM types: raw_send, raw_call, …) over stock
`erlang:`/`gen_server:`/`gen_statem:` BIFs plus the inert `Effect(T)` former.

- The kernel checks the algebra is consistent and used correctly; the only
  asserted facts are the raw base's signatures.
- `Any` is the foreign-boundary type: the typed layer only *injects into* it
  (total embed), never projects out unchecked — not a top type.
- A genuine raw need is met by the user's *own* explicit, greppable `@extern`;
  device FFI (`gpio`/`uart`) is ordinary user `@extern`, outside the algebra.

### 1.2 Message types as codes

The index `m` in `Pid(m)` is a **code**: ordinary data describing the set of
tagged messages (tag + payload field type-codes) a process accepts.
- `TypeCode` covers the **first-order** fragment only — exactly what BEAM
  message copying already imposes. A decoder `El : MsgType -> Type` gives
  the message type users see; code and type cannot drift.
- **Codes are derived, never hand-written** — projected from the message ADTs
  / handler clauses (the same source the macro compiles into `handle_*`).
- `handles`/`subset`/`union` are total functions; inclusion is a Bool-valued
  **computation** checked by normalisation — **no `<:` judgment anywhere**
  (locked: no subtyping, Agda/Lean/Idris-aligned).
- Codes are **0-quantity (erased)**: at runtime a pid is a bare `RawPid`;
  emitted code is `erlang:send(Pid, {:deposit, 100})` — zero ESP32 footprint,
  enforced by the erasure check and the `codes_erased` release validator.

### 1.3 The typed floor

- `send(p: Pid(m), msg: El(m)) -> Effect(Unit)` — wrong tag *and* wrong
  payload are both compile errors.
- Dependent call/reply: `reply_of : CallCode -> Atom -> TypeCode` is a pure
  lookup (not a GADT/type family); `call` returns `Effect(El(reply_of(...)))`.
- Behaviour conformance is structural: `start_link` yields a handle whose
  channels are the behaviour's declared codes; disagreeing callbacks fail.
- Subsumption by computation: `narrow_pid : Pid(wide) -> {subset(narrow,
  wide)} -> Pid(narrow)`, runtime-identity, discharged by normalisation for
  concrete codes. Ergonomic enhancement, not a soundness requirement.
- `self` inside a behaviour has the ambient code; outside, `self_raw :
  Effect(Pid(empty))` (encoding still a ledgered ergonomics fork).

### 1.4 Rollout rungs and status

- **Rung 1 — externs** (landed): macros rebuild `actor`/`fsm`/`sup`/`app` as
  `lift module` behaviours over effect-typed externs; pids raw.
- **Rung 2 — sealed typed + codes floor** (largely landed; see §3, §5):
  `Std.Otp` over sealed `Std.Otp.Raw`; derived codes; `Pid(m)`, dependent
  call/reply, conformance, computed subsumption; seal validators on.
- **Rung 3 — indexed `Effect(pre, post, T)`**: **DELETED — superseded** by §2.
  The parameterized monad only simulated missing linearity; with `{0,1,ω}`
  planned, concurrency is elaborator + stdlib work, **zero kernel change**.

Release validators (trusted, at the emission gate): `otp_raw_sealed`,
`no_widening_narrow` (pinned as the §3 regression table), `unsafe_confined`,
`codes_erased` (extended to protocol states, quantities, budgets). Honest
limits: the raw mailbox is dynamically typed (the algebra governs typed
channels, not the mailbox — Akka-Typed-style opt-in boundary); foreign-
boundary trust is irreducible; inject/narrow wrappers are the seam. Open
ledger: `self`-outside-behaviour encoding, bespoke-codes-vs-`schema`, deep
maps/pids-in-messages payloads, `handle_info` system-message coverage, typed
registry (name→code association — see §3 `whereis`), `unsafe` tag surface.

## 2. Checked concurrency — linear session channels (supersedes rung 3)

**Status:** approved direction; prerequisite step 1 (Core `:let` binder) LANDED.
**Core principle:** BEAM processes are not Cure's concurrency semantics. Cure
has a checked semantics — session-typed channels and linear capabilities —
that *lowers to* BEAM processes under a narrow, explicit backend contract.
`Effect(T)` stays **inert** (that was never the defect; the uninformative
index was) and is the substrate, not the thing to escape.

### 2.1 Types

```
Protocol ::= Send(MsgShape, Protocol) | Recv(MsgShape, Deadline, Protocol)
           | Offer(Deadline, List(%[MsgShape, Protocol]))   -- external choice
           | Select(List(%[MsgShape, Protocol]))            -- internal choice
           | Done
Deadline ::= Forever | Within(Duration)
```

- Only the two **blocking** formers (`Recv`, `Offer`) carry a `Deadline`; the
  deadline lives in the *protocol*, never in an argument list.
- `Chan : Protocol -> Type` is an ordinary indexed family. Operations return
  the **next-state channel inside the result** (`send : (1 c :
  Chan(Send(m,next))) -> El(m) -> Effect(Chan(next))`; `offer` returns a sum
  whose constructors carry the typed continuation channel) — this removes
  the need for a dependent/indexed bind. `call` is sugar for send-then-recv
  over `Send(q, Recv(r, d, next))`, deadline-polymorphic (the *reactor*
  rejects `Forever`; NB `gen_server:call/2` silently defaults to 5000 ms).
- **Duality by computation:** `dual : Protocol -> Protocol` total function;
  `spawn`/`connect` mint pairs at `p`/`dual(p)`; discharged by normalisation.
- **Two levels of reference:** `Pid(m)` = *address* (ω, copyable, storable —
  the rung-2 floor); `Chan(p)` = *conversation* (linear, confined to Cure —
  not a first-order value, hence not a legal payload). Addresses survive
  supervisor restarts; conversations don't.
- Constrained payloads are **Σ-types, not refinements** (refinement types
  were removed 2026-07-09 and are not queued to return).
- Polymorphic protocols allowed; **codes are always ground** (derived after
  instantiation). Same `(tag, arity)` with two field types is rejected.
  Dependent protocols (`Depends`) ledgered for v1.1.

### 2.2 Quantities {0,1,ω} — E-layer, kernel quantity-blind

- Extend `relevance.ex`'s two-point lattice to `{0,1,ω}` in the **E layer**
  (as Idris keeps `LinearCheck` outside its core). `0` = proofs/indices/codes,
  `1` = channels/resource capabilities/task handles, `ω` = default. Rejects:
  use-twice, use-zero, capture in non-one-shot closure, storage in ω
  container, escape without transfer. **The error is reuse of a consumed
  handle, never operation count** — implement use-counting, not "one op per
  channel". Errors name the protocol state.
- **Linear, not affine** (overturns the protocol-macro spec's affine choice):
  affine drop of an endpoint is exactly the peer-left-blocked leak; error
  paths use elaborator-inserted `cancel`. Affine is reserved for **ownership
  transfer** (a `Task` handed to a supervisor).
- **Hard prerequisite — LANDED:** Cure's substituting `let` would duplicate/
  discard linear values below the check. Fixed by a Core `:let` binder with ζ
  (`a84c454` kernel, `d2054e2` elaborator; Idris/Lean-aligned, pre-approved
  TCB change); `Context` now stores its NbE environment (`extend_def/3`). No
  `RigCount` yet — `{0,1,ω}` must later land uniformly on def params, ctor
  fields, and binders. Surface substitution survives only at exactly-one-use
  (else ascription); the elaborator can no longer duplicate/discard a rhs.
- One-shot closures and linear containers (`LinList`, `await_any`,
  `cancel_all`) are the acknowledged stdlib cost; they buy pools/racing/
  dynamic topologies.

### 2.3 Surface syntax

`protocol` declarations (states, `recv M(T) [reply R within d] -> S`, `done`);
`process` blocks — servers are receive loops (missing clause for a legal
message = totality error), clients are straight-line statements:

```cure
process main() -> Int =
  acct = spawn Account.serve(0)   # acct : Account@Open
  send acct, Deposit(100)
  b = call acct, Balance()
  send acct, Close()              # acct : Account@Closed, discharged
  b
```

The elaborator threads the handle through each statement (each is a plain
non-dependent `Effect` bind rebinding the handle at its new state); inserts
terminal `close` at scope end and `cancel` for live linear binders at
`raise`/`try` boundaries; the block's final type must be `Effect(R)`.

**Locked syntax rule: arrows *describe* the protocol; statements *drive* it.**
An arrowised send/receive surface (`acct <- Msg`) was rejected: infix invites
nesting which typestate forbids; receive is an n-way offer, not binary; `->`
would collide; `<-` reads backwards to half the audience; pipes/arrows = pure
dataflow vs statements = effects. `send`/`call` stay distinct keywords
(`call` blocks; `send` does not). Consequence: the Melquiades `<-|`/`✉`
operator is retired or retyped statement-position-only returning the
next-state channel (E044–E046 subsumed by the protocol check).

Containers separate by kind: **`fsm` reduces** (the handle's type *is* the
machine state — but only while the handle is linear; an ω-shared fsm degrades
to the flat floor, state recovery becoming a runtime query returning `Σ s.
Chan(M@s)`); **`actor` is a process**; **`sup` owns addresses, not
conversations** (restart kills the session, not the address; children are the
affine case); **`app`** owns the root supervisor capability linearly.

### 2.4 Failure model — let it crash, typed (EGV)

- Failure is an **exit, not a value**: a dead peer unwinds the caller
  (monitor `DOWN` → exit), like `gen_server:call`.
- Unwinding cancels the ledger: elaborator-inserted `cancel` notifies peers
  (`PeerCancelled`); theorem: no unwind strands a peer or leaks a session.
- Recovery is scoped `try … rescue PeerDown(_) -> …`.
- `Task(a)` states type structured spawn/await; detached spawn transfers the
  affine task to a supervisor; unjoined+untransferred = linearity error.
- Timeout expiry raises exactly where `PeerDown` raises — one failure shape.

### 2.5 Resources — peripherals are linear capabilities, not processes

On C3-class chips one scheduler thread runs the port handlers — wrapping I²C
in a process buys nothing. Per the reactive-bible layer rule, peripherals are
`resource`s owned by the Program layer; only genuinely-async drivers (Wi-Fi,
sockets) become processes. AtomVM drivers enforce this dynamically already;
linear capabilities move it to compile time.

- `resource` types carry protocol states and `@blocking(budget:)` per op;
  constructors **consume** pin capabilities (`I2c.new(1 sda: Gpio(p1), …)`)
  so pin-mux corruption is a type error — the strongest peripheral-safety
  property in the design. Long operations spread across ticks as protocol
  states (DS18B20 `convert : Idle → Converting`, `poll → Pending | Done`).
- **Timing as checked arithmetic:** (1) Σ blocking budgets reachable in a
  reactor drain phase < tick period; (2) max single budget < 16 / Σ declared
  interrupt rates (the shared ISR queue is 16 deep and drops silently).
  Budgets are trusted declarations about foreign IDF code. A reachable
  `Forever` receive, or `Within(d)` > tick period, is a compile error inside
  a reactor; legal outside one.
- GPIO interrupt honesty: `Rising`/`Falling` distinct sources; `both`
  advanced-only; level triggers only under `unsafe`; the event type promises
  **soundness, not completeness** (queue overflow drops edges silently).

### 2.6 Backend contract (trusted lowering)

Protocol fidelity alone is not the contract — memory and scheduling
invariants are obligations too.

- **Wire format:** session messages are `{'$cure', SessionRef, Seq?, Tag?,
  Payload…}`. `SessionRef` = fresh `make_ref()` — provenance, **not**
  security; per-boot only, sessions never persist across restart. `Seq` only
  for delegation-permitting protocols (v1: never); `Tag` elided when the
  state admits exactly one message. Resources are local: no token.
- **Receive lowering — never scan (when we own the mailbox):** AtomVM has no
  receive-marker optimisation; head-take with a **mandatory catch-all
  quarantine clause** in every emitted receive (O(1) + foreign decode + junk
  hygiene, by construction). O(1) holds **only for mailbox-owning
  (`raw`-lowered) processes**; a `gen_server`-lowered `call` goes through
  `gen:call`'s selective receive (O(N), N normally zero — `handle_info` drains).
- **Foreign boundary:** valid live SessionRef → trusted; matches a declared
  `accepts` contract (flat `(tag, arity) → shapes`; runtime injections like
  `{gpio_interrupt, P}`/`{'DOWN', …}` are just another foreign peer) →
  decoded at the door; otherwise **drop and count**.
- **Failure obligations:** every spawn is monitored; **cancellation terms are
  preallocated at session creation** (building them on an exhausted heap hits
  `AVM_ABORT()`; reasons constrained to atoms). **Delegation
  (channel-in-message) is excluded from v1** — a lowering gap: BEAM ordering
  is per sender-receiver pair only; lifting needs an explicit
  drain-and-handoff protocol + mandatory `Seq`. Ledgered.
- **No effect-interpreting emit:** lowering is a syntax-directed walk over the
  bind-chain spine, never an evaluator over effect trees.
- **Behaviour lowering decision:** `gen_server` is the **default** (interop,
  `sys` introspection, `handle_info` *is* the quarantine clause,
  `gen_server:call`'s exit-on-peer-death *is* the EGV failure model, no
  defensive wildcards on typed clauses); a **`raw` loop lowering is available
  per-container** for hot-path mailbox-owning processes. Both are
  supervisable — "a bare loop cannot be supervised" was **retracted**
  (`proc_lib`/`sys` buy reports/introspection, not supervisability).
- Retired by this lowering: `Std.Actor.notify/1` + implicit `:caller`,
  `Std.Fsm.state/1` returning a bare Atom, the ETS-backed actor runtime,
  defensive wildcard clauses, string-based FSM/Actor codegen.

### 2.7 AtomVM obligations (patches we own)

1. **I²C: a lowering choice, not a patch** — use the `i2c_resource` NIF
   collection, passing the declared budget as `send_timeout_ms` (override
   the 500 ms default). **SPI: patch required** — no timeout parameter
   exists; until patched an SPI budget is a declaration only.
2. Optional: expose event-queue overflow counters.
3. **Guard the NULL in `mailbox_send`** — on allocation failure AtomVM
   dereferences NULL and crashes the whole VM; patch to raise catchable
   `out_of_memory` in the sender. Until patched, every guarantee is
   conditional on the sender's malloc succeeding.

### 2.8 Overturned decisions (recorded so they are not relitigated)

(1) Rung-3 indexed bind — deleted (rungs 0–2 stand). (2) "Indices, not
linear types" — reversed; its teardown citation was wrong. (3) Affine
protocol handles — now linear + inserted `cancel`. (4) Per-op `Result`
failure — replaced by EGV exit + scoped `rescue`. (5) Melquiades `<-|`
typing — retired/retyped (§2.3). (6) The brief's kernel-responsibility list —
rejected; net kernel delta zero. (7) Refinement types assumed by the brief —
do not exist; Σ-types instead. (8) The brief's backend contract — necessary
but insufficient (memory/scheduling safety added). (9) The brief's `Effect`
migration plan — vacuous; preemption, not migration. (10) The brief's
task/join algebra — ill-formed (agreement is a post-condition; decide
equality on values). (11) "A bare loop cannot be supervised" — retracted.

**Non-negotiable invariants (checklist).** Safe Cure code cannot: spawn or
send unchecked; receive unchecked as protocol traffic; duplicate/reuse a
consumed channel or resource; silently drop an obligation; smuggle a session
through a message; bypass checking via macros (output re-elaborated); hide
behaviour in an effect the type doesn't name; write a pin owned by a bus;
assume ordering BEAM doesn't give; assume interrupt completeness.

**Honest limits.** Raw mailbox stays dynamic (quarantine is best-effort);
`accepts`/budgets are trusted declarations; `send` is not memory-safe on
stock AtomVM until the NULL patch; the token is provenance; liveness is not
proven (deadlock lint is an out-of-TCB advisory, same trust shape as the Z3
lint); O(1) receive and static fsm typestate are conditional; function
colouring exists (a pure `fn` cannot send).

## 3. `Std.Otp` conformance fixes (2026-07-14)

**Status:** approved; zero TCB delta. Repairs the typed layer where it claimed
things the BEAM does not deliver (from the executed conformance audit).

- **`@erases(<class>)`** — item-level decorator declaring an opaque FFI
  carrier's runtime shape (`:pid`, `:reference`, plus the scalar classes),
  each mapping to one total Erlang guard; makes `RawPid(...) | :undefined` a
  discriminable union. Not a safety proof — an assertion by the sealed raw
  base's author; compile error on non-opaque types.
- **`whereis` (F-2c + amendment 7.2):** raw op returns `Effect(BarePid |
  :undefined)`, `BarePid = RawPid(NoMessage, NoMessage, Plain)` (`NoMessage`
  uninhabited); typed `whereis : Atom -> Effect(Option(BarePid))`. A union
  member must be **ground**, and the `m` claim was the F-1 lie (nothing
  associates a name with a message type until code derivation lands). The
  result may be linked/monitored/supervised but **cannot be sent to** — the
  correct statement of what the BEAM registry gives.
- **`Pid` vs `GenServer` (F-2a):** separated by an erased phantom index.
  Amendment 7.1: kinded type parameters do not exist in Cure — `PidKind` is
  encoded as **phantom tags at kind `Type`** (`opaque type Plain` / `Server`;
  `RawPid(m, r, k)`). `call`/`cast`/`stop` are `Server`-only (also fixes
  F-2b); `tell`/`link`/`monitor`/`exit`/… are kind-polymorphic; `spawn`/
  `self` produce `Plain`. Zero runtime cost. (Partly superseded by §5's
  three-index `ServerPid`.)
- **Honest raw results (F-4):** ten ops stop lying `Effect(Unit)` —
  `raw_send → Effect(m)`, link/exit/register family → `Effect(Bool)`,
  cast/stop → `Effect(Atom)`, `raw_cancel_timer → Effect(Int | Bool)`; typed
  wrappers discard the raw result; typed `cancel_timer : Effect(Option(Int))`.
  Prerequisite (7.3): an `@extern` may return `Effect(<union>)` (both check
  sites strip one `Effect` layer; unions in real structures stay rejected).
  7.4: union elimination has no catch-all — one exhaustive arm per member.
- **`ExitReason` (F-3):** typed layer narrows `exit`'s reason to `Normal |
  Kill | Because(Atom)`; raw stays permissive; still no claim the target dies.
- **Reference split (F-5):** distinct `opaque type MonitorRef` / `TimerRef`
  (both `@erases(:reference)`); `demonitor` gains a `flush` variant so a
  stale `DOWN` cannot outlive it; docstrings promise only pairwise
  sender→target ordering and no delivery guarantee. Platform hazards
  documented at the ops: AtomVM's `send_after` ref is **not cancellable**
  (retargeting at `start_timer/3` is a typed change, deferred); `call` is
  partial (timeout/death **exits the caller** — partial, not unsound).
- **Deferred as one bundle:** F-1 (code derivation grounding the pid index),
  honest `start_link` return, `try_call` over a runtime shim, `send_after`
  retargeting. Regression pin: a test asserting every `Std.Otp.Raw` op's
  declared return type against the audited table (practical `no_widening_narrow`).

## 4. Typed BEAM representation (2026-07-19)

**Status:** implementing. Foreign boundary crossing goes through two ordinary
typeclasses: `BeamEncode(t)` (`to_beam : t -> BeamTerm`, total) and
`BeamDecode(t)` (`from_beam : BeamTerm -> Result(t, BeamDecodeError)`,
fallible). `BeamTerm` is opaque; **no API may use a polymorphic cast from
`BeamTerm` as a successful decoder**.

- Representation is an ABI commitment, so derivation is explicit (`deriving
  BeamEncode`); a hand-written `implementation` is the override. `BeamDecode`
  is not derived until the generated decoder validates every tag, arity,
  guard, and recursive field.
- **Macro staging rule:** typeclass dictionaries resolve in the final lifted
  module's environment, so a typed OTP macro emits a local concrete adapter
  (`fn encode_child_id(id: ChildId) -> BeamTerm = to_beam(id)`) rather than
  calling a constrained helper during isolated expansion-proof checking.
- OTP surface: actor messages/requests, FSM states/events/actions, supervisor
  strategies/policies/child identities, and application phases are all typed
  values; encoding happens only at the boundary. Raw forms remain under
  visibly raw names. Verification per migration: rejection without the
  instance; derived + override tests; recursive macro coverage; live OTP
  runtime test; AtomVM generic-unix where the facility exists.

## 5. Typed actors over the checked algebra (2026-07-19)

**Status:** authoritative; phases 2–3 in progress. An actor is an **effectful
mailbox fold** whose accumulator is an immutable Cure value — OTP owns the
receive loop, scheduling, and tail recursion; Cure owns the message/request
algebras and checks every transition. State is the argument retained by the
suspended loop — no host registry, no mutable actor object.

- `actor` MUST expand through the source-defined `Std.ActorBehavior` substrate
  to ordinary Cure declarations calling checked `Std.Otp`. Emitted runtime code
  MUST NOT contain syntax values, macro dispatchers, callback interpreters,
  process-dictionary state, or a mandatory registry.
- **Three protocol indices** — `ServerPid(message, request, reply)`; the
  dependent form replaces `reply` with `ReplyOf : request -> Type`.
  `GenServer(q, r)` survives only as the alias `ServerPid(q, q, r)`; actor
  generation MUST use the three-index form (supersedes §3's two-index split).
  Handles are phantom indices over the native PID, erasing without a wrapper.
- Surface: `actor Name` with `state`/`initial`, `on_message` (async fold),
  `on_call` (typed queries), plus lifecycle `on_start`/`on_info`/`on_stop`/
  `on_failure`. Constructors are nominal values, not Atom tags; raw
  `handle_cast`/`handle_call` remain visible escape hatches only.
- Generated API: nominal `Message`/`Request`/`ReplyOf`/`Handle` + `start`,
  `start_with`, `send`, `stop`, and named query adapters via `call_dep`. **No
  universal `get_state`** — state is encapsulated unless a query is declared
  (FSMs deliberately derive snapshot queries). Startup is honest: the algebra
  MUST NOT assert `{:ok, pid} | {:error, r}` is always a pid.
- Notification requires an explicit typed observer capability (`actor Worker
  notifying WorkerNotice`); hidden untyped `caller`, process-dictionary
  registration, and ambient `notify` are forbidden. Not restored: global
  `Cure.Actor.Runtime`, mandatory ETS registry, automatic `Cure.Actor.`
  prefixes, `%Cure.Actor.State{}`.
- Status: nominal protocols, validated `start`, typed `send`/`stop`,
  uniform-reply `request`, and explicit `reply ReplyOf` families with
  per-branch checking are landed with live BEAM tests. Open: deriving
  `ReplyOf` from annotated clauses; full exhaustiveness diagnostics; generic
  publication of lifted-module declarations to same-compilation clients
  (currently `bad_projection` — must be fixed in the generic transparent
  module pipeline, **not** with actor-aware resolution).

## 6. Typed FSMs as constrained actors (2026-07-19)

**Status:** authoritative; phase 1–2 foundation implemented —
`Std.ActorBehavior` owns the one transparent behavior-module emission
boundary; `Std.Actor` and `Std.Fsm` both target its strategies; neither
invokes `lift_module_isolated` independently.

**Decision:** an FSM is a constrained actor: authored graph → source-defined
grammar records → derived nominal `State`/`Event` + total transition reducer →
verified actor behavior → recursively expanded ordinary Cure → direct OTP
code. No runtime FSM interpreter, transition-table interpreter, or opaque
container may be emitted. The compiler MUST NOT recognize FSM/actor/OTP
vocabulary specially — only generic syntax families, reflection, and
elaboration (the same machinery `knit` requires; no FSM-specific parser
extension may be needed for `knit`).

- Surface: `fsm Name with Data`; edges `Red --Timer--> Green`; wildcard `*`
  (explicit edges win; fully-shadowed wildcards diagnosed); `initial` /
  repeatable `terminal`; typed event payloads (`--Coin(source: CoinSource)-->`,
  every appearance of a constructor agreeing on arity/types/relevance/order);
  `when` guards (ambiguity rejected unless proven disjoint — never silent
  source-order choice); pure `update` (ordinary record-update checked against
  `Data`); effectful `perform` (through the checked algebra, lowered direct);
  lifecycle hooks (`on_start`, `on_stop`, `on_enter/on_exit State`,
  `on_failure`, `on_timer`); `timer 500ms`; hard `Event!` (auto-fires, sole
  unconditional outgoing) and soft `Event?` (may fail without `on_failure`).
  State/event names are PascalCase constructors, never Atom literals.
- Derived: `type State`, `type Event`, visible `rec MachineState{state,
  data}`, a closed internal `MachineMessage` protocol that must not widen the
  public event type to `Atom`/`BeamTerm`, and a typed public API
  (`start_link`, `send(pid, Coin(Token()))`, `get_state`, `get_data`,
  `snapshot`, `stop`). No hidden `Cure.FSM.` module prefix.
- Fifteen required compile-time checks (ordinary total Cure over reflected
  records): closed state/event catalogues, payload consistency,
  initial/terminal validity, reachability, deadlock freedom, duplicate edges,
  guard ambiguity, wildcard precedence, hard-event validity, update/hook/
  notification typing, total reducer. Warnings are insufficient for
  unsound/ambiguous selection. Diagnostics use authored constructor names
  with expansion provenance, never lowered atoms.
- Non-goals: legacy `on_transition` syntax, raw Atom event APIs,
  `%Cure.FSM.State{caller, meta, payload}`, dynamic transition tables,
  runtime graph verification, arbitrary guard-disjointness proof,
  distribution/persistence. History/registry/health are opt-in layers that
  leave no residue when disabled.

## 7. `cure port` — interactive BEAM-to-dependent porting (independent tool)

**Status:** approved design, pre-plan. Not part of the actor/FSM runtime
contract. **Core insight: lift the BEAM, not the source** — Elixir, Erlang,
and Gleam all lower to Core Erlang (~20 node types), so a near-total shape
catalog with a hard `unsupported_shape` surface (fail-closed, coverage
measured like Antigen's manifest) sees exactly what the computation is.

- Pipeline: Reader (per-language Core Erlang adapters) → Shapes → Fitter
  (Cure AST + obligations) → Hammer (auto-discharge via a banked proof
  library, candidates checked by the Lean oracle/kernel) → Prover (interactive
  REPL; journaled, resumable) → Emitter (Cure source + report; postulates
  routed into the trust ledger). Phases: 0 end-to-end value surface,
  non-interactive; 1 Hammer; 2 interactive prover; 3 dependent-refinement
  pass (`Vector`/`Fin` proposals) + source-type enrichment (Gleam types,
  `-spec`, `@spec`). Obligation taxonomy: totality, coverage, termination,
  refinement invariants, partiality reshaping (`throw`/`error` →
  `Option`/`Result` or postulate).
- **`Std.Port.*` proof library**, transliterated from Lean/Agda/Coq/Isabelle
  stdlibs and validated via the differential oracle: Nat arithmetic +
  well-founded `<`; List algebra (the workhorse); Vec/Fin; Order/sorting;
  Bool reflection; Eq (injectivity, disjointness, DecEq); Wf termination
  certificates; Absurd/⊥-elim; Map laws; Option/Result monad laws; Bits
  (stretch). Banking priority: List, Nat, Wf, Eq, Order, Absurd, Bool, rest.
- Give-up tiers: auto → interactive → postulate (a visible trust-ledger axiom;
  an incomplete port never blocks). Primary acceptance: differential BEAM↔port
  behavioural equivalence on generated inputs. Out of scope: porting BEAM
  concurrency semantics beyond a faithful `Std.Otp.Raw` wrapper; re-deriving
  Gleam's type system.

---

## Source specs

- `2026-07-09-typed-beam-process-algebra-design.md` — foundational typed algebra: sealed raw base, codes, typed floor, rungs (rung 3 superseded).
- `2026-07-10-checked-beam-concurrency-design.md` — governing correction: linear session channels, {0,1,ω}, deadlines, EGV failure, resources, backend contract, AtomVM patches, eleven overturned decisions.
- `2026-07-13-cure-port-interactive-design.md` — independent `cure port` tool: Core Erlang lifting, shape catalog, obligations, `Std.Port.*` proof library, interactive prover.
- `2026-07-14-otp-conformance-fixes-design.md` — conformance repairs: `@erases`, honest `whereis`, Pid/GenServer split, honest result types, `ExitReason`, ref split, four planning amendments.
- `2026-07-19-typed-beam-representation-design.md` — `BeamEncode`/`BeamDecode` boundary typeclasses, derivation/coherence, macro staging rule.
- `2026-07-19-typed-actor-behavior-design.md` — actors as effectful mailbox folds over `ActorBehavior`; three-index `ServerPid`; generated APIs.
- `2026-07-19-typed-fsm-as-constrained-actor-design.md` — FSM lowering as a constrained actor: graph surface, derived types, fifteen checks, phases.
- `README.md` — the family index and supersession pointers.

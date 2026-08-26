# Typed Actors over the Checked OTP Algebra

**Status:** Authoritative

**Date:** 2026-07-19

**Applies to:** `Std.ActorBehavior`, `Std.Actor`, the checked `Std.Otp`
process algebra, generated actor APIs, and actor capabilities reused by FSMs.

**Parent specifications:**

- `2026-07-14-compile-time-reflective-beam-macros-design.md`
- `2026-07-19-typed-beam-representation-design.md`
- `2026-07-19-typed-fsm-as-constrained-actor-design.md`

## 1. Decision

An actor is an effectful mailbox fold whose accumulator is an immutable Cure
value:

```text
loop(state)
  receive message
  next <- handle(message, state)
  loop(next)
```

OTP owns the receive loop, scheduling, suspension, and tail recursion. Cure
owns the message/request algebras and checks every state transition. State is
not stored in a host registry or mutable actor object; it is the current
argument retained by the suspended OTP loop.

`actor` MUST expand through the source-defined `Std.ActorBehavior` substrate to
ordinary Cure declarations which call the checked `Std.Otp` algebra. Generated
runtime code MUST NOT contain syntax values, a macro dispatcher, a callback
interpreter, a process-dictionary state container, or a mandatory registry.

## 2. Protocol indices

A server PID has three independent protocol indices:

```cure
ServerPid(message, request, reply)
```

- `message` is accepted asynchronously by `cast`/typed delivery;
- `request` is accepted synchronously by `call`; and
- `reply` is the synchronous result type.

The dependent form replaces `reply` with `ReplyOf : request -> Type`.

The old `GenServer(q, r)` spelling MAY remain as the compatibility alias
`ServerPid(q, q, r)`, but actor generation MUST use the honest three-index
form. Conflating messages and requests is not sound merely because both travel
to the same BEAM PID.

All handles are opaque phantom indices over the native PID and erase without a
wrapper. `tell`, `cast`, `call`, `call_dep`, `stop`, links, monitors, exits, and
timers remain operations of `Std.Otp`; actor-generated functions are nominal,
domain-specific adapters, not another runtime layer.

## 3. Preferred actor surface

```cure
rec CounterState
  count: Int

actor Counter
  state CounterState
  initial CounterState{count: 0}

  on_message
    Increment() -> CounterState{state | count: state.count + 1}
    Add(amount: Int) -> CounterState{state | count: state.count + amount}

  on_call
    Value() -> state.count
```

The exact source-family factoring may evolve, but the public vocabulary MUST
describe domain behavior rather than raw OTP tuples. `on_message` is the
ergonomic name for asynchronous mailbox folds. `on_call` declares typed
queries. Raw `handle_cast`/`handle_call` remain explicit escape hatches and do
not define the preferred surface.

Message and request constructors are nominal values, not Atom tags:

```cure
type Message = Increment | Add(Int)
type Request = Value

fn ReplyOf(request: Request) -> Type = match request
  Value() -> Int
```

Constructor payload binders use ordinary typed parameter syntax. Repeated
constructors MUST agree on arity, type, relevance, and order.

## 4. Generated declarations and API

Each actor derives, as applicable:

```cure
type Message = ...
type Request = ...
fn ReplyOf(request: Request) -> Type = ...
typealias Handle = DepActorServer(Message, Request, ReplyOf)
```

and a direct API:

```cure
fn start() -> Effect(Handle)
fn start_with(initial: State) -> Effect(Handle)
fn send(actor: Handle, message: Message) -> Effect(Unit)
fn stop(actor: Handle, reason: ExitReason) -> Effect(Unit)
```

Declared queries generate named wrappers, for example:

```cure
fn value(actor: Handle) -> Effect(Int) =
  Std.Otp.call_dep(actor, Value())
```

There is no universal generated `get_state`. Internal state is encapsulated
unless the declaration explicitly exposes a query. FSMs deliberately derive
state/data/snapshot queries because observability is part of their specified
abstraction.

Startup is partial in the same operational sense as links and synchronous
calls: the process may fail to start and no successful handle is returned.
The checked algebra MUST model the actual start outcome honestly. It MUST NOT
assert that OTP's raw `{:ok, pid} | {:error, reason}` tuple is always a PID.
An explicitly partial `start!` or a typed `StartResult(Handle)` are acceptable;
the final spelling must preserve the handle indices on success.

## 5. Lifecycle and capabilities

The structured lifecycle is:

- `on_start`: computes or validates initial state inside the process;
- `on_message`: performs the asynchronous mailbox fold;
- `on_call`: answers declared typed requests and may explicitly update state;
- `on_info`: handles explicitly declared system/external message codes;
- `on_stop`: observes a typed `ExitReason`; and
- `on_failure`: handles declared recoverable domain failures.

Links, monitors, timers, names, and exits are checked `Std.Otp` capabilities,
not hidden actor services. An actor declaration may request generated adapters
for them, but the implementation remains the ordinary algebra.

Notification requires an explicit typed observer capability:

```cure
actor Worker notifying WorkerNotice
```

The observer is supplied at startup and stored only when requested. A hidden
untyped `caller`, process-dictionary registration, and ambient `notify` are
forbidden in the preferred architecture.

## 6. Optional operational layers

Naming, discovery, actor listings, history, health checks, and introspection
are opt-in source-defined layers. They may use typed `Std.Otp.Name` values or
explicit state fields when selected. The following historical machinery is
not restored:

- a global `Cure.Actor.Runtime` GenServer;
- a mandatory ETS actor registry;
- automatic `Cure.Actor.` module prefixes;
- `%Cure.Actor.State{caller, payload, meta}`; or
- process-dictionary state/observer lookup.

## 7. ActorBehavior responsibilities

`Std.ActorBehavior` owns reusable compile-time generation for:

1. direct behavior-module construction;
2. typed startup and handle construction;
3. asynchronous delivery callbacks;
4. dependent request/reply callbacks;
5. stop and lifecycle callbacks; and
6. optional observer/timer/monitor capabilities.

`Std.Actor` owns actor grammar, constructor derivation, handler exhaustiveness,
and the generated nominal API. `Std.Fsm` owns graph derivation and verification,
then supplies its reducer and protocols to the same behavior substrate.

The compiler recognizes none of this vocabulary. It supplies only generic
syntax families, recursive expansion, reflection, diagnostics, and ordinary
elaboration.

## 8. Ordered implementation phases

Each phase receives a focused commit and green focused tests.

### Phase 1: honest server handle

- Separate asynchronous message and synchronous request indices in `Std.Otp`.
- Preserve compatibility aliases where sound.
- Add typed cast/call/call-dep/start/stop proofs and negative conformance tests.

### Phase 2: generated actor API

- Derive nominal `Message`, `Request`, `ReplyOf`, and `Handle` declarations.
- Generate typed start, send, stop, and declared query adapters.
- Prove no raw module Atom is required by ordinary callers.

**Implementation status (2026-07-19): in progress.** Structured actors now
derive nominal `Message`, `Request`, and `Handle` protocols and emit direct
validated `start`, typed `send`, and typed `stop` functions. Uniform-reply
actors additionally emit a typed `request` adapter. Live BEAM tests prove two
sequential messages update the suspended immutable state before a synchronous
request observes it, and a negative elaboration test rejects an `Int` sent to
an `Inc` mailbox. The remaining Phase-2 work is the preferred dependent query
surface (`ReplyOf` plus named adapters) and generic publication of declarations
from a lifted module to same-compilation Cure clients; the latter currently
reports `bad_projection` after the lifted module is intentionally stripped from
the host AST. It must be solved in the generic transparent module pipeline, not
with actor-aware resolution.

### Phase 3: modern message/query grammar

- Add payload-bearing `on_message` and `on_call` productions.
- Check constructor consistency, handler exhaustiveness, and binder scope.
- Remove syntax-level reply-type guessing from the preferred path.

**Implementation status (2026-07-19): in progress.** `on_message` is now the
preferred asynchronous fold section and derives nominal constructors with
ordinary typed payload binders. The reflected constructor checker supplies
arity/type consistency, and ordinary elaboration checks payload binder scope.
A live actor test sends `Add(Int)`, updates two fields of an immutable record,
observes the suspended accumulator, and resets it through a nullary message.
`on_cast` remains a compatibility spelling and raw callback sections remain
explicit escape hatches. Actors may now select an explicit source-defined
`reply ReplyOf` family: generation then uses `DepActorServer`, checks each
`on_call` branch against `ReplyOf(request)`, and exposes request-indexed calls.
A positive live test exercises distinct reply types from one PID and a negative
test rejects returning the `Ping` reply from the `Count` branch. Deriving
`ReplyOf` and named query adapters directly from annotated clauses, plus the
full handler-exhaustiveness diagnostic, remain open.

### Phase 4: lifecycle and failures

- Add typed `on_start`, `on_stop`, `on_info`, and `on_failure` sections.
- Prove mailbox-fold state preservation and lifecycle ordering.

### Phase 5: optional capabilities

- Add explicit typed observer support.
- Add opt-in names, timers, links, monitors, and introspection adapters.
- Prove absent capabilities leave no runtime fields or calls behind.

### Phase 6: cleanup and shared FSM gate

- Retain raw callbacks only as visibly raw escape hatches.
- Remove preferred-surface Atom/BeamTerm/callback-tuple leakage.
- Resume FSM event payloads using the completed actor handle and lifecycle.
- Run full ExUnit, Antigen, Unix BEAM, and supported AtomVM gates.

## 9. Required tests

- sequential messages observe immutable state evolution;
- payload-bearing messages update multiple state fields;
- message/request types are distinct and cannot be crossed;
- multiple request constructors return their own dependent reply types;
- undeclared state inspection is unavailable;
- declared queries return typed values;
- typed startup success and failure behavior;
- lifecycle ordering and stop reasons;
- explicit observer delivery and absence when not requested;
- link, monitor, timer, and failure paths;
- source-defined user actor-like macro targeting `ActorBehavior`;
- emitted BEAM contains no syntax interpreter, registry, or opaque actor state;
- full Unix runtime behavior; and
- supported AtomVM behavior.

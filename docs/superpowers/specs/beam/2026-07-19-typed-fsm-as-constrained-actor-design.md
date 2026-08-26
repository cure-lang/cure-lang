# Typed FSMs as Constrained Actors

**Status:** Authoritative; phases 1–2 foundation implemented

**Date:** 2026-07-19

**Applies to:** `Std.Fsm`, `Std.Actor`, source-defined grammar productions,
typed events, transition verification, lifecycle behavior, generated process
APIs, and direct OTP lowering.

**Parent specifications:**

- `2026-07-14-compile-time-reflective-beam-macros-design.md`
- `2026-07-19-constrained-macro-expansions-design.md`
- `2026-07-19-typed-beam-representation-design.md`

## 1. Decision

An FSM is a constrained actor. The `fsm` macro MUST derive and verify a finite
state/event algebra and then expand through the same source-defined actor
behavior substrate used by `actor`.

The required compilation path is:

```text
authored FSM graph
  -> source-defined grammar records
  -> derived State, Event, and transition reducer
  -> verified actor behavior
  -> recursively expanded ordinary Cure declarations
  -> elaborated, kernel-checked, erased, and directly emitted OTP code
```

This is compile-time composition. Generated runtime code MUST NOT contain an
FSM syntax interpreter, transition-table interpreter, macro dispatcher, opaque
OTP container, or actor object wrapper introduced solely by expansion.

`fsm` MAY emit a generated `actor` use directly. If the public actor grammar is
not a stable internal target, `fsm` and `actor` MUST instead share a reusable
source-defined `ActorBehavior` family. The compiler MUST NOT recognize FSM,
actor, OTP callback, lifecycle, transition, or event vocabulary specially.

## 2. Goals

The design MUST provide:

1. a concise transition-graph surface;
2. nominal derived `State` and `Event` types;
3. typed event payloads and edge-local payload binders;
4. typed user data with ordinary record update syntax;
5. wildcard transitions, guards, initial states, and terminal states;
6. effectful actions, typed notifications, lifecycle hooks, timers, and failure
   handling without raw callback tuples;
7. compile-time reachability, deadlock, ambiguity, and event-consistency checks;
8. a typed generated process API;
9. one actor/process lifecycle architecture shared with `actor`; and
10. transparent direct BEAM code after recursive expansion.

The design MUST NOT preserve unreleased callback-mode compatibility merely for
its own sake. There is no requirement to retain `on_transition`, lowercase Atom
event labels, `%[:ok, ...]` callback tuples, `%Cure.FSM.State{}` or any legacy
host-side runtime container.

## 3. Core surface

### 3.1 Basic graph

```cure
fsm TrafficLight with TrafficData
  Red --Timer--> Green
  Green --Timer--> Yellow
  Yellow --Timer--> Red
  * --Emergency--> Red
```

State and event names are constructor names, not Atom literals. The macro
catalogues every non-wildcard source and target into a closed nominal `State`
type, and every event label into a closed nominal `Event` type:

```cure
type State = Red | Green | Yellow
type Event = Timer | Emergency
```

Duplicate appearances denote the same constructor. A constructor name MUST be
PascalCase. Lowercase labels MUST be rejected with a diagnostic suggesting the
capitalized constructor spelling.

### 3.2 Data

`with DataType` declares the user-visible machine data type:

```cure
rec TurnstileData
  coins: Int
  passages: Int
  enabled: Bool

fsm Turnstile with TurnstileData
  Locked --Coin--> Unlocked
    update TurnstileData{
      data
      | coins: data.coins + 1,
      enabled: true
    }
```

Within an edge body, `data` has exactly the declared data type. `update` is an
ordinary Cure expression checked against that same type. An edge without an
`update` preserves `data`.

All ordinary record-update layouts are valid, including:

```cure
Data{data | count: data.count + 1}
```

```cure
Data{
  data
  |
  count: data.count + 1
}
```

```cure
Data{
  data
  | count: data.count + 1,
  active: true
}
```

### 3.3 Typed event payloads

An event may declare typed payload binders in the graph:

```cure
fsm Turnstile with TurnstileData
  Locked --Coin(source: CoinSource)--> Unlocked
    update TurnstileData{
      data
      | coins: data.coins + 1,
      last_source: source
    }

  Unlocked --Push--> Locked
```

The derived event type is:

```cure
type Event = Coin(CoinSource) | Push
```

Every appearance of an event constructor MUST agree on payload arity, binder
types, relevance, and order. Binder names MAY differ between edges; their types
and positions determine constructor compatibility. Inconsistent declarations
are a compile-time error naming both source locations.

Payload binders are scoped over `when`, `update`, and `perform` sections of
their edge only.

### 3.4 Initial and terminal states

The first non-wildcard source state is the default initial state. Authors SHOULD
write an explicit initial state when row reordering must not change behavior:

```cure
fsm Pipeline with PipelineData
  initial Idle
  terminal Finished

  Idle --Start--> Ready
  Ready --Done--> Finished
```

`initial` names exactly one derived state. `terminal` is repeatable or accepts a
closed state collection. An unknown initial or terminal state is an error.
Terminal states may omit outgoing edges; non-terminal states may not.

### 3.5 Wildcards

`*` matches every derived source state:

```cure
* --Emergency--> Safe
```

Wildcard expansion occurs after the complete state catalogue is known. An
explicit edge for the same source state and event takes precedence. A wildcard
that can never apply MUST produce a shadowing diagnostic.

Wildcard rows do not contribute a state constructor and cannot determine the
default initial state.

### 3.6 Guards and updates

```cure
fsm Counter with CounterData
  Counting --Tick--> Counting
    when data.remaining > 0
    update CounterData{data | remaining: data.remaining - 1}

  Counting --Tick--> Done
    when data.remaining == 0
```

`when` is an ordinary Bool expression. Multiple edges with the same source and
event are permitted only when their guard set is accepted by the ambiguity
policy in §7. Compile-time evaluation SHOULD prove disjointness for decidable
closed guards. Otherwise the macro MUST reject ambiguity rather than silently
choose source order, unless an explicit ordered form is added by a later spec.

`update` remains pure. It computes the next data value but does not perform
foreign operations.

### 3.7 Effects and notifications

Effectful work is visibly separate from the pure update:

```cure
Unlocked --Push--> Locked
  update TurnstileData{data | passages: data.passages + 1}
  perform
    notify(PassageRecorded(data.passages + 1))
```

`perform` is checked through the ordinary effect and BEAM algebra. It MUST lower
to direct operations. It MUST NOT construct an effect-command syntax tree for a
runtime interpreter.

Notification messages are typed constructors. A machine that emits notices
declares or derives a notification code and carries an optional typed observer
capability. A permanently present untyped `caller` field is not part of every
machine's hidden runtime state.

### 3.8 Lifecycle and failure hooks

Lifecycle behavior uses structured sections:

```cure
fsm Pipeline with PipelineData
  initial Idle
  terminal Finished

  on_start
    perform notify(Started())

  on_enter Finished
    perform notify(Completed(data.result))

  on_stop reason
    perform release(data.resource, reason)

  on_failure event reason
    perform report_failure(event, reason)

  Idle --Start--> Ready
  Ready --Done(result: Result)--> Finished
    update PipelineData{data | result: result}
```

Hooks receive typed values. They MUST NOT expose raw OTP callback argument
tuples, state atoms, or an implementation-owned map/struct.

The initial hook set is `on_start`, `on_stop`, `on_enter State`, `on_exit
State`, `on_failure`, and `on_timer`. Additional hooks require a specification
update rather than an untyped `Code` catch-all.

### 3.9 Timers and hard/soft events

```cure
fsm Poller with PollData
  timer 500ms
  terminal Finished

  Idle --Start--> Setup
  Setup --Init!--> Ready
  Ready --Poll?--> Ready
  Ready --Done--> Finished
```

A hard event (`Event!`) fires automatically after entering a source state and
MUST be the sole unconditional outgoing event from that state. A soft event
(`Event?`) may fail without invoking `on_failure`; failure preserves state and
data. The suffix is transition policy and does not create a different public
event constructor name.

Timer duration parsing uses the generic literal/macro facility. Timer delivery
is expressed as a typed generated event or typed `on_timer` hook and lowers to
the selected actor behavior's direct timer support.

## 4. Source-defined grammar

The standard-library grammar is conceptually:

```cure
syntax family EventDefinition
  syntax <event: Name>(<payload: Parameters>)

syntax family TransitionDefinition
  syntax <from: StatePattern> --<event: EventDefinition>--> <to: Name>
  optional when Expression
  optional update Expression
  optional perform Code

syntax family FsmDefinition
  optional initial Name
  repeated terminal Name
  optional timer Duration
  optional notify_transitions Type
  repeated on_start LifecycleClause
  repeated on_stop LifecycleClause
  repeated on_enter StateLifecycleClause
  repeated on_exit StateLifecycleClause
  repeated on_failure FailureClause
  repeated on_timer LifecycleClause
  one_or_more transitions TransitionDefinition
```

The exact factoring may use included families and multiple productions. It MUST
remain Cure source. `StatePattern`, `Duration`, and other reusable categories
must be generic or source-defined categories, not branches named `fsm` in the
compiler.

Indented production bodies, punctuation adjacency (`--Event-->`), cardinality,
printing, source provenance, and typed nested records are generic macro-family
facilities shared with domain languages such as `knit`.

## 5. Derived declarations

For each machine the macro derives at least:

```cure
type State = ...
type Event = ...

rec MachineState
  state: State
  data: Data
```

`MachineState` is semantically necessary runtime state, not an opaque container.
Its complete definition is generated as ordinary Cure and is visible to normal
elaboration and inspection.

When administrative process messages are required, the actor contract derives
a closed internal protocol such as:

```cure
type MachineMessage =
  | Deliver(Event)
  | GetState(Pid(Reply(State)))
  | GetData(Pid(Reply(Data)))
  | Stop(ExitReason)
```

The exact reply-channel representation follows the actor specification. It
must be typed and one-shot where supported. Administrative messages MUST NOT
widen the public event type to `Atom` or `BeamTerm`.

Generated declarations are nominal and shared by the lifted module and callers.
Equivalent anonymous unions reconstructed at separate use sites are forbidden.

## 6. FSM-to-actor expansion

The FSM expander produces a total transition reducer plus an actor behavior.
Conceptually:

```cure
fn transition(
  state: State,
  event: Event,
  data: Data
) -> TransitionResult(State, Data, Notice) = ...
```

The reducer contains direct nested matches over derived constructors. Each
successful edge returns its declared target and checked updated data. Guard
failure continues transition selection. No match returns a typed failure or a
soft no-op according to declared policy.

The generated actor behavior:

- initializes `MachineState(initial, data)`;
- receives `Deliver(event)`;
- invokes the reducer;
- executes checked effects and notifications;
- commits the next `MachineState`;
- serves typed state/data queries;
- runs lifecycle hooks; and
- lowers timers and stop behavior through the shared actor substrate.

`actor` owns process startup, typed message delivery, calls/replies, links,
monitors, supervision integration, lifecycle scheduling, and direct OTP callback
generation. `fsm` owns graph syntax, derivation, transition semantics, and graph
verification.

If `gen_statem` behavior is selected, the shared `ActorBehavior` substrate may
emit `gen_statem` callbacks directly. If the public `actor` macro currently
targets `gen_server`, this specification does not permit hiding an FSM runtime
interpreter behind it. The shared substrate must express the required direct
callback behavior, or the FSM expansion must choose a direct source-defined
actor behavior strategy.

After recursive expansion, no `fsm`, `actor`, `ActorBehavior`, `Syntax`, or
macro-dispatch value remains at runtime.

## 7. Compile-time verification

Verification is an ordinary total Cure computation over reflected grammar
records. It reports structured source diagnostics before runtime code emission.

The required checks are:

1. **Closed state catalogue:** every source/target is a valid constructor.
2. **Closed event catalogue:** every event is a valid constructor.
3. **Payload consistency:** repeated event declarations agree exactly.
4. **Initial-state validity:** the selected state exists and is non-wildcard.
5. **Terminal-state validity:** every declared terminal exists.
6. **Reachability:** every declared state is reachable from the initial state,
   accounting for wildcards and satisfiable guards.
7. **Deadlock freedom:** every reachable non-terminal state has an applicable
   outgoing transition or declared timer/hard-event behavior.
8. **Duplicate transitions:** identical unguarded source/event edges are errors.
9. **Guard ambiguity:** overlapping guarded edges are rejected unless proven
   disjoint.
10. **Wildcard precedence:** explicit edges win; fully shadowed wildcards are
    diagnosed.
11. **Hard-event validity:** hard events are sole unconditional outgoing edges.
12. **Update preservation:** every update checks as `Data`.
13. **Hook typing:** lifecycle and failure hooks satisfy their declared types.
14. **Notification typing:** emitted notices belong to the declared notice code.
15. **Total reducer:** the generated reducer covers every accepted state/event
    combination or explicitly returns a typed rejection policy.

Warnings are insufficient for unsound or ambiguous transition selection.
Reachability may initially be a warning only if the language's warning policy
requires it, but the verifier API must distinguish warning from error explicitly.

The compiler supplies only generic compile-time evaluation, reflection, and
diagnostic transport. It MUST NOT contain `Cure.FSM.Verifier`-style knowledge of
states, events, terminals, hard events, or wildcard precedence.

## 8. Generated public API

Each FSM exposes a typed API conceptually equivalent to:

```cure
fn start_link(data: Data) -> Effect(FsmPid(Event, State, Data))
fn send(pid: FsmPid(Event, State, Data), event: Event) -> Effect(Unit)
fn get_state(pid: FsmPid(Event, State, Data)) -> Effect(State)
fn get_data(pid: FsmPid(Event, State, Data)) -> Effect(Data)
fn snapshot(pid: FsmPid(Event, State, Data)) -> Effect(FsmSnapshot(State, Data))
fn stop(pid: FsmPid(Event, State, Data), reason: ExitReason) -> Effect(Unit)
```

An event with a payload is sent as its constructor:

```cure
send(pid, Coin(Token()))
```

There is no preferred `send_with(pid, :coin, arbitrary_payload)` path. An
explicit raw/foreign escape hatch may transport a BEAM term, but it is not part
of the derived typed API and does not weaken its contract.

The generated module name is the authored module name. The macro MUST NOT add a
hidden `Cure.FSM.` prefix unless that prefix is explicitly present in source.

## 9. Optional operational layers

History, registry lookup, health checks, dashboards, and automatic transition
telemetry are useful but are not intrinsic FSM semantics. They MUST be optional
source-defined actor behaviors or instrumentation families.

Enabling history may generate typed entries:

```cure
rec TransitionEntry
  from: State
  event: Event
  to: State
  data: Data
```

Operational layers may retain runtime values because the user requested those
features. They must not force history, caller, metadata, registry, or health
state into every FSM.

## 10. Diagnostics

Diagnostics use authored constructor names and graph vocabulary, never lowered
atoms or OTP callback names. Required examples include:

```text
error: event Coin has inconsistent payload types
  first declared here as CoinSource
  later declared here as Token
```

```text
error: state Blocked is unreachable from initial state Locked
```

```text
error: non-terminal state Ready has no outgoing transition
```

```text
error: Tick from Counting has two transitions whose guards may overlap
```

```text
error: update on Locked --Coin--> Unlocked returns Int, expected TurnstileData
```

Generated-code errors retain expansion provenance and point to the originating
edge or lifecycle section.

## 11. Implementation phases

Implement in this order. Each phase requires a focused commit and green focused
tests before the next phase.

**Implementation status (2026-07-19):** `Std.ActorBehavior` now owns the one
transparent behavior-module emission boundary. `Std.Actor` targets its
`actor_module`/`actor_module_raw` strategies and `Std.Fsm` targets its
`state_machine_module` strategy. Thus both surfaces recursively produce direct
OTP callback modules through the same source-defined compile-time substrate;
neither surface invokes `lift_module_isolated` independently. Existing derived
actor behavior and the typed FSM graph—including default-preserving,
single-field, multi-field, and multiline record updates—pass live Unix BEAM
tests. This establishes the phase 1 substrate and phase 2 lowering foundation;
the richer shared lifecycle/API work remains incremental work in the phases
below rather than a reason to reintroduce a standalone FSM shell.

### Phase 1: shared actor behavior substrate

- Specify the reusable source-defined `ActorBehavior` family.
- Factor process startup, delivery, lifecycle, stop, and direct callback
  generation out of public `actor` templates.
- Prove both `actor` and a user-defined actor-like macro can target it.
- Prove no runtime interpreter or opaque container is emitted.

### Phase 2: FSM lowers through actor behavior

- Replace the standalone FSM process shell with generated actor behavior.
- Preserve the existing `State --Event--> State`, `with Data`, and `update`
  surface.
- Prove direct runtime transitions and record updates on Unix BEAM and AtomVM.

### Phase 3: typed event payloads

- Extend the source-defined event production with typed parameters.
- Derive one nominal payload-bearing `Event` type.
- Add payload consistency and binder-scope diagnostics.
- Generate typed send APIs and negative send-conformance tests.

### Phase 4: graph policy

- Add explicit `initial`, repeatable `terminal`, and wildcard rows.
- Implement source-defined reachability and deadlock checks.
- Add duplicate, shadowing, and unknown-state diagnostics.

### Phase 5: guards and total selection

- Add edge `when` sections.
- Define and implement ambiguity rejection.
- Prove guard and update expressions see typed payload/data binders.
- Prove generated selection is total and source-order independent where the
  graph is declared unambiguous.

### Phase 6: effects and notifications

- Add `perform` through the checked BEAM algebra.
- Add typed observer capabilities and notice codes.
- Add optional transition notifications without hidden caller/meta fields.

### Phase 7: lifecycle, failure, and timers

- Add the typed lifecycle sections in §3.8.
- Add `timer`, hard events, and soft events.
- Prove hook ordering, failure routing, timer behavior, and hard-event validity.

### Phase 8: optional operations

- Implement history, registry, and health as opt-in source-defined layers.
- Prove disabled layers leave no runtime fields or calls behind.

### Phase 9: cleanup and final gates

- Remove any remaining legacy callback vocabulary and documentation.
- Remove bespoke host-side FSM verifier/runtime paths from the preferred build.
- Verify generated code contains no syntax values, macro dispatch, transition
  interpreter, or opaque FSM/actor container.
- Run the complete ExUnit, Antigen, Unix runtime, and AtomVM gates.
- Update the macro autopilot ledger and public FSM documentation.

## 12. Required tests

At minimum, the completed implementation includes:

- basic state/event derivation;
- duplicate catalogue entries deduplicated nominally;
- payload-less and payload-bearing events;
- inconsistent payload rejection;
- data preservation without `update`;
- single-field and multi-field record updates in every supported layout;
- update wrong-type rejection;
- explicit and default initial state;
- terminal-state acceptance and deadlock rejection;
- wildcard expansion and explicit precedence;
- unreachable-state diagnostics;
- duplicate and ambiguous guarded transition rejection;
- hard- and soft-event behavior;
- typed notification delivery;
- lifecycle ordering and failure hooks;
- generated typed send/state/data APIs;
- actor/FSM shared-substrate architecture guard;
- macro recursive-expansion and hygiene tests;
- absence of forbidden runtime machinery in emitted BEAM;
- live Unix BEAM behavior; and
- live AtomVM behavior for the supported subset.

## 13. Relationship to `knit`

This specification does not define the knitting algebra. It deliberately uses
the same generic nested-production machinery that `knit` requires: punctuation
productions, repeated typed records, indented child sections, domain-specific
verification in Cure, and direct generated declarations. No FSM-specific parser
extension introduced by this work may be required to implement `knit`.

## 14. Non-goals

The first complete implementation does not require:

- preservation of unreleased `on_transition` syntax;
- raw Atom event APIs as the preferred interface;
- a permanent `%Cure.FSM.State{caller, meta, payload}` wrapper;
- dynamic loading of transition tables;
- runtime graph verification;
- automatic proof of arbitrary guard disjointness;
- distributed FSM replication or persistence; or
- a compiler-owned FSM object model.

These exclusions do not prohibit explicit foreign escape hatches. Escape
hatches remain visibly raw and do not weaken the typed derived path.

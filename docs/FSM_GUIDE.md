# FSM Programming Guide

`fsm` is an auto-preluded standard-library macro. It expands to an ordinary
`lift module` with a checked `gen_statem` callback surface; the compiler does
not contain a separate FSM parser or object class. Everything below is
verified against `lib/std/fsm.cure` and against real `cure check`/`cure
run`/`cure test` invocations, not just the macro's declared grammar.

`Std.Fsm` declares two `fsm` macros over one shared callback floor:

- **The transition graph surface** (`fsm Name with Data`) -- a graph of
  `From --Event--> To` rows, verified at compile time and compiled to a total
  `decide/3`. This is the preferred surface for anything shaped like a state
  machine, and the one that derives a full typed `send`/`start` API.
- **The structured event-body surface** (`fsm Name` with `state`/`events`) -- a
  lower-level shape that maps event patterns directly to callback results (or,
  in its typed form, to `FsmAction` values). Use it when you want to write a
  `gen_statem` callback body by hand, or need the enclosing module to see the
  state/event type names.

Both require `use Std.Fsm`. A bare module name is relative to its lexical
owner; a dotted name is absolute within the Cure source namespace. Source
never needs to spell the emitter-owned `Cure.` prefix.

## Defining An FSM

The transition graph is the preferred surface:

```cure
use Std.Fsm

fsm Turnstile with Int
  Locked --Coin--> Unlocked
    update data + 1
  Unlocked --Push--> Locked
  Unlocked --Coin--> Unlocked
    update data + 1
  Locked --Push--> Locked
```

`with Int` declares the machine's data type -- any Cure type works here,
including a record or a `Tuple(...)`, not just a primitive. The macro catalogs
every endpoint into a nominal `State` type (`Locked | Unlocked`) and every
label into a nominal `Event` type (`Coin | Push`). Without an explicit
`initial` row (below), the source state of the first written edge is the
initial state; a wildcard row's source (`*`) is never eligible for this.

An edge preserves `data` unless it has an indented `update` expression. The
expression is checked as the declared data type and may refer to `data`; the
target state is already fixed by the edge and is not repeated in callback
tuples.

Record data uses Cure's ordinary typed record-update syntax. Fields not named
after the bar are preserved:

```cure
use Std.Fsm

rec TurnstileData
  coins: Int
  pushes: Int
  enabled: Bool

fsm Turnstile with TurnstileData
  Locked --Coin--> Unlocked
    update TurnstileData{
      data
      | coins: data.coins + 1,
      enabled: true
    }
  Unlocked --Push--> Locked
    update TurnstileData{data | pushes: data.pushes + 1}
  Unlocked --Coin--> Unlocked
    update TurnstileData{data | coins: data.coins + 1}
  Locked --Push--> Locked
```

The `|` may instead occupy its own line before the first field; both layouts
parse as the same typed record update, and either may update more than one
field at once.

## Event Payloads

An edge may declare typed payload binders directly on the event label:

```cure
use Std.Fsm

fsm PayloadFsm with Int
  Locked --Coin(amount: Int)--> Unlocked
    update data + amount
  Unlocked --Reset--> Locked
    update 0
```

The derived `Event` type becomes `Coin(Int) | Reset`. `amount` is in scope
only inside that edge's `when` and `update` expressions; the binder's *name*
may differ between edges for the same event, but every edge for a given event
must agree exactly on payload arity, order, and types. A conflicting
redeclaration (e.g. `Coin(amount: Int)` on one edge and `Coin(source: String)`
on another) is a compile error (`:fsm_inconsistent_event_payload`).

Send a payload-bearing event by passing its constructor to `send/2`:

```text
Machine.send(handle, Coin(5))
```

At runtime, a nullary event compiles to a bare atom of its exact spelling
(`Reset` erases to `:Reset`), and a payload-bearing event compiles to a tagged
tuple with the payload fields in declared order (`Coin(5)` erases to
`{:Coin, 5}`). This is what an external caller (Elixir, or `:gen_statem.cast`
from a shell) must send to trigger that edge directly, and it is exactly what
`:sys.get_state/1` returns for a nullary state (a bare atom like `:Locked`).

## Guards

An edge may restrict when it applies with an indented `when` expression:

```cure
use Std.Fsm

fsm GuardedFsm with Int
  Locked --Add(amount: Int)--> Unlocked
    when amount > 0
    update data + amount
  Unlocked --Reset--> Locked
```

`when` is an ordinary `Bool` expression, checked with the edge's payload
binders and `data` in scope. If the guard is not satisfied and no other row
matches the same state/event pair, the machine falls through to the table's
default fallback: `data` is preserved and the state does not change (a
guard-rejected event is therefore indistinguishable, at the state-machine
level, from an event the graph has no row for at all).

## Initial And Terminal States

Write `initial` to fix the starting state independent of row order, and
`terminal` (repeatable, one state per line) to declare states that are
allowed to have no outgoing edges:

```cure
use Std.Fsm

fsm GraphPolicyFsm with Int
  initial Green
  terminal Red

  Green --Emergency--> Yellow
    update data + 1
  Yellow --Reset--> Green
  Yellow --Stop--> Red
```

Every non-terminal state must have at least one outgoing edge (an explicit row
or an applicable wildcard); a non-terminal state with none is rejected as
deadlocked, and every catalogued state must be reachable from the initial
state.

## Wildcard Transitions

`*` in place of a source state matches every catalogued state that has no more
specific edge for the same event. An explicit `From --Event--> To` row always
takes precedence over a `* --Event--> To` row for the same source and event:

```cure
use Std.Fsm

fsm GraphPolicyFsm with Int
  initial Green
  terminal Red

  * --Emergency--> Red
    update 99
  Green --Emergency--> Yellow
    update data + 1
  Yellow --Reset--> Green
```

Here `Green` still routes `Emergency` to `Yellow` (the explicit row wins), while
`Yellow` falls through to the wildcard and moves to `Red`. A wildcard row does
not itself add a state to the catalogue and cannot supply the default initial
state.

## Compile-Time Validation

The table is checked while the macro expands, before any code is generated.
Every violation below is a compile error, never a runtime failure:

- `fsm_requires_transition` -- the table has no rows.
- `fsm_requires_initial_state` -- no row and no explicit `initial` supplies a
  starting state.
- `fsm_unknown_initial_state` -- an explicit `initial` names a state absent
  from the graph.
- `fsm_unknown_terminal_state` -- a `terminal` names a state absent from the
  graph.
- `fsm_duplicate_transition` -- the same (source, event) pair is declared by
  more than one *unguarded* row (two `when`-guarded rows for the same pair are
  allowed; the table does not currently prove their guards are disjoint).
- `fsm_unreachable_state` -- a catalogued state cannot be reached from the
  initial state.
- `fsm_deadlocked_state` -- a non-terminal state has no applicable outgoing
  edge.
- `fsm_inconsistent_event_payload` -- the same event label declares
  incompatible payload shapes on different rows.

These checks run every time the `fsm` macro expands -- including under `cure
run` and, in a single-file project, under `cure check`. See "Known toolchain
limitations" below for where `cure check` currently does *not* reliably reach
them in a multi-file project.

## Generated API

Given `fsm Machine with Data`, the expansion emits (inside `Machine`):

- `State`, `Event` -- nominal enums catalogued from the graph.
- `TransitionInfo` -- `Explicit(Atom, Atom, Atom)` or `Wildcard(Atom, Atom)`,
  one constructor per row, so tooling and tests can inspect the compiled graph
  as ordinary data.
- `Data` -- alias for the declared data type.
- `Handle` -- alias for `Std.Otp.FsmPid(Event, State, Data)`.
- `transitions() -> List(TransitionInfo)` -- every row `decide/3` was compiled
  from, explicit rows before wildcard rows.
- `responds?(state: State, event: Event) -> Bool` -- whether the graph has a
  row for that state/event shape. Guards are deliberately not evaluated, since
  they may depend on data the caller doesn't have.
- `decide(event: Event, state: State, data: Data) -> FsmAction(State, Data)` --
  the pure transition function: `Next(to, data)` for a matched row, `Keep(data)`
  otherwise. This function has no process behind it and is safe to call from
  ordinary test code to walk a sequence of events without spawning anything.
- `callback_mode`, `init`, `handle_event` -- the raw `gen_statem` callbacks that
  lower `decide/3`'s result via `Std.Fsm.action_to_beam/1`.
- `start_link(initial: Data) -> Effect(Tuple)` -- for a supervisor child spec.
- `start(initial: Data) -> Effect(Std.Otp.StartResult(Handle))` -- a typed
  handle for direct use.
- `send(machine: Handle, event: Event) -> Effect(Unit)` -- deliver an event to
  a running machine.

## Runtime

The generated module is an ordinary BEAM module implementing the standard
`gen_statem` behavior. It exports both entry points a `gen_statem` needs:
`start_link/1` for a supervisor, and `start/1` for a typed handle. Events go
through `send/2`, and the event constructors are the ones derived from the
table.

```cure
mod TrafficLight
  use Std.Fsm
  use Std.Otp

  fsm Machine with Int
    Red    --Timer--> Green
    Green  --Timer--> Yellow
    Yellow --Timer--> Red

  fn boot() -> Effect(Tuple) = Machine.start_link(0)

  fn start() -> Effect(StartResult(Machine.Handle)) = Machine.start(0)
```

`start/1` returns a `Std.Otp.StartResult(Handle)`, so the failure cases are in
the type rather than in a tuple you have to remember to check. There is no FSM
registry or process-inspection layer: a running machine is reached through its
handle, like any other OTP process.

Because every `Std.Otp` operation is effect-typed, calling `start`/`send` (or
any other `Effect(_)`-returning function) requires the *calling* function to
itself be declared `-> Effect(...)` -- bind the call with `let`, don't inline
it as a bare expression, and prefer an exhaustive `match` over `StartResult`
(`Started`/`StartFailed`/`StartIgnored`/`InvalidStartResult`) to a wildcard arm
when branches mix effectful and pure results.

## The Structured Event-Body Surface

`Std.Fsm` also accepts a second, lower-level shape, built from `state`, an
optional `states`/`initial`/`event_type`, and `events`. Where the transition
graph describes edges, this surface describes what each event *does*, as an
ordinary `match` over `event` (and, in its typed form, over `state` and
`data` too).

### Untyped Form

```cure
use Std.Fsm

fsm Ticker
  state Int
  events
    Tick -> :keep_state_and_data
```

Despite the keyword, `state Int` here names the type carried as `gen_statem`'s
*data* argument, not a state enum. Without `states`, the machine has exactly
one implicit `gen_statem` state (`:initial`), and each arm of `events` returns
a raw `gen_statem` action term directly (`:keep_state_and_data`, or any other
`Effect(Atom)` result your handler computes). Event constructors used in
`events` are catalogued into an `Event` enum owned by the generated machine
(e.g. `Ticker.Event`), not bound beside it -- so two sibling modules that each
declare an `fsm` never collide on the name.

This form only emits `callback_mode/0`, `init/1`, `handle_event/4`, and
`start_link/1` -- there is no generated `send`/`start` typed API. Drive it with
raw `:gen_statem` calls or `Std.Otp` directly. Treat it as an escape hatch for
a `gen_statem` callback body you would rather write as a Cure `match`, not as
the primary FSM surface.

### Typed Form

Adding `states`, `initial`, and (usually) `event_type` turns `events` into a
total function from `(event, state, data)` to a checked `FsmAction`:

```cure
use Std.Fsm

type CounterState = Idle | Counting
type CounterEvent = Start | Bump

fsm Counter
  state Int
  states CounterState
  initial Idle
  event_type CounterEvent
  events
    Start -> Next(Counting(), data)
    Bump  -> Keep(data + 1)
```

`state Int` still names the *data* type (aliased inside the machine as
`Data`); `states` names the real state enum (aliased as `StateName`);
`initial` fixes the starting state; `event_type` supplies the `Event` type
instead of deriving one from the patterns in `events`. Naming `states` and
`event_type` explicitly is how the *enclosing* module gets a name it can use
-- a derived `Event` lives only inside the generated machine, out of reach of
the caller. `states` requires `initial`.

Event bodies return `FsmAction` values here, so transitions lower through the
same `decide`/`action_to_beam` path as the transition graph surface. As with
the untyped form, only `start_link/1` is generated -- there is no `send`/`start`
helper, so drive the machine with raw `:gen_statem` calls or `Std.Otp`.

Prefer the transition graph surface for anything with more than one or two
states: it derives the full typed `send`/`start` API, verifies the graph at
compile time, and reads as the graph it compiles.

## FsmAction

Both surfaces resolve to the same checked callback result:

```cure
use Std.ExitReason

type FsmAction(state, data) = Keep(data) | Next(state, data) | Stop(ExitReason, data)
```

- `Keep(data)` keeps the current state, replacing `data`.
- `Next(state, data)` moves to `state` with the new `data`.
- `Stop(reason, data)` stops the machine (`reason: Std.ExitReason`).

`Std.Fsm.action_to_beam/1` is the single place these lower to the `gen_statem`
tuple vocabulary (`:keep_state`, `:next_state`, `:stop`); nothing else in the
generated module constructs those tuples by hand. The transition graph surface
only ever produces `Next` (a matched row) or `Keep` (its unmatched fallback);
reaching `Stop` requires the structured typed surface, where an `events` arm
may return it explicitly.

`Std.Fsm` also exports `keep/1`, `next/2`, and `stop/2` as ordinary function
wrappers around the three constructors, for callers that would rather not
name the ADT directly.

## Compatibility Helpers

`Std.Fsm` also carries a small atom-labelled `Transition`/`dispatch` algebra
(`Transition(state, event) = Row(state, event, state)`, `AtomTransition`,
`transition/3`, `first_state/1`, `first_state_or/2`, `dispatch/5`,
`dispatch_atom/4`) and a `transition <from> <event> <to> becomes
Std.Fsm.transition(from, event, to)` syntax rule. These exist solely as a
compatibility target for `cure migrate` upgrading pre-graph-surface FSM code;
new code should use the transition graph or structured surfaces above instead
of authoring `Transition` rows by hand.

## Transparency

The expansion is ordinary Cure syntax. It contains no `__otp_container`
marker, raw-source compilation, or direct code-server load. Generated modules
are collected and emitted by the same generic lifted-module path as any
user-defined macro (`Std.ActorBehavior.state_machine_module`, shared with
`actor`, `sup`, and `app`).

The transition grammar and event/state derivation are language-level macro
work. Another package can define the same kind of declarative algebra without
changing the compiler.

## Known Toolchain Limitations

The points below were confirmed by hand against a current build of the
compiler (declaring minimal reproductions and running `cure check`/`cure
compile`/`cure test`/`cure run` directly, including against the officially
scaffolded `cure new --fsm` template). They are toolchain behavior, not `fsm`
grammar or semantics, and are recorded here so they don't have to be
rediscovered by every project that hits them.

- **A macro-generated submodule cannot be called from *project-mode* code.**
  Compiling a whole project (`cure compile <dir>`, and therefore `cure test`)
  fails with an internal `missing_module` resolution error as soon as any
  module -- same file or a different one -- calls another module's
  `fsm`-generated API (`.start`, `.send`, even the pure `.decide`). Declaring
  the macro on its own, without calling its generated API from elsewhere in a
  directory-mode build, compiles fine; the nested generated submodule is
  simply never referenced. The one currently reliable way to exercise a
  generated `fsm`'s own API end to end is `cure run <single-file>`, or driving
  it from a *different* language entirely (an Elixir project compiling the
  `.cure` file with `Cure.Compiler.compile_file/2` and calling the result by
  its raw BEAM atom, the way `examples/cure_turnstile` and
  `examples/cure_moneta` do -- that path never goes through the project-mode
  resolver at all).
- **`cure check` does not currently validate an `fsm` declaration reliably.**
  Even a trivial two-state, two-edge graph (as produced by `cure new --fsm`)
  fails `cure check` with a generic macro-expansion-rejected diagnostic,
  independent of whether a `Cure.toml` is in scope. The graph verification
  logic itself is not the problem -- it runs, and correctly rejects an
  actually-broken graph (e.g. a missing `terminal`) -- but `cure run` on a
  single file that both declares the `fsm` and has a `main/0` is the reliable
  way to see that result today; `cure check` is not.
- **A macro's generated constructors are not independently namespaced from
  the rest of their enclosing module.** Unlike a plain nested `mod`, if a
  module both declares `fsm Escrow with Data` (whose graph derives a `State`
  constructor `FundsReserved`, say) *and* its own top-level `type EscrowState
  = ... | FundsReserved | ...` for some other purpose, expansion fails with a
  duplicate-constructor error. Keep a hand-written mirror of an `fsm`'s
  state/event ADTs (if you need one, e.g. because of the limitation above) in
  its own module.

None of this affects the `fsm` macro's own compile-time graph verification
(§ "Compile-Time Validation"), which runs correctly wherever expansion runs at
all -- it affects only *which* command reliably shows you the result, and
whether the generated runtime API is reachable from other project-mode Cure
code. See `examples/cure_exchange/cure/README.md` for a worked-through example
of designing a project around these constraints, and
`examples/cure_exchange/elixir/README.md` for the unaffected Elixir-hosted
path.

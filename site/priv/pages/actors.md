%{
  title: "Actors",
  description: "Typed supervision trees with first-class actor and sup containers, the Melquiades send operator (<-|), links, monitors, and exit signals.",
  order: 5
}
---

> **0.34 update:** `actor` and `sup` are standard-library macros living in
> `Std.Actor` and `Std.Supervisor`, not privileged compiler container nodes.
> Neither is ambient -- a unit that declares one must `use` the module it
> comes from. They expand to ordinary lifted modules, callbacks, and the
> checked `Std.Otp` algebra. The dependent kernel checks message indices and
> linear reply capabilities before erasure; no raw-source or direct
> code-server escape path is involved. The sections below retain the
> established runtime vocabulary and pre-0.34 history.

Cure 0.25.0 turns the language into a first-class environment for writing OTP-style supervision trees. The four pieces that land together are:

1. The **Melquiades Operator** `<-|` (unicode alias `✉`) for sending a message to a pid.
2. `actor` containers that compile to loaded `GenServer` modules with exhaustiveness-checked message handlers.
3. `sup` containers that compile to verified `Supervisor` behaviour modules with compile-time structural checks.
4. Stdlib modules `Std.Actor`, `Std.Process`, `Std.Supervisor` that define the `actor`/`sup` macros and the checked concurrency algebra they expand into.

Together they let you declare a production-grade supervision tree without ever dropping into Elixir or Erlang.

## The Melquiades Operator

`pid <-| message` sends `message` to `pid` as a checked, fire-and-forget effect. The ASCII spelling and its unicode alias are interchangeable:

```text
pid <-| :hello
pid ✉  :hello
```

Both spellings are ordinary operator sugar over `Std.Otp.tell`, which checks `message`'s type against `pid`'s declared inbox and sends with the raw BEAM primitive underneath: non-blocking, never raises for a dead receiver, and evaluates to `Effect(Unit)` rather than to the sent message.

The operator is **non-associative** and binds one notch below `|>` so pipelines feed into it naturally:

```text
request
|> encode()
|> worker_pid <-| _
```

The last line is equivalent to `worker_pid <-| encode(request)`.

### Why "Melquiades"?

Named after the ghost-mailman of *One Hundred Years of Solitude*, who keeps delivering letters even after his own death. The arrow points into the inbox on the left: `pid <-| message` reads "the pid gets this message".

### Keyword form

`send target, msg` is a synonymous statement form retained for backward compatibility and for `Std.Fsm` clients. It desugars to the same `{:send, …}` MetaAST node as `<-|`, so round-trip printing preserves the author's chosen spelling through a `:melquiades_form` meta key (`:ascii`, `:unicode`, or `:keyword`).

## Actors

An `actor` creates a lifted `gen_server` module. `state` is the only required
clause; `initial`, `messages`, `init`, `on_start`, `on_message`, `on_cast`,
`on_call` queries, `on_info`, `handle_cast`, `handle_info`, `terminate`,
`on_stop`, `code_change`, and `body` are all optional, and the shape you
supply chooses how the module is derived.

The structured surface derives a message type from capitalised `on_message`
constructors, and each clause returns the actor's new state directly:

```cure
use Std.Actor

actor Counter
  state Int
  initial 0
  on_message
    Inc -> state + 1
    Dec -> state - 1
  on_call Get() returns Int
    reply state
```

- `on_call <Request>(<params>) returns <Type>` declares a synchronous query:
  `reply <expr>` is what the caller receives, and an optional `update <expr>`
  is the state the actor keeps afterward.
- A request name is a constructor of the generated `Request` family, so it
  must be capitalised; the caller-facing adapter is its downcased form --
  `Get()` gives `get/1`, `Bump(step: Int)` gives `bump/2`.
- The raw form (`handle_cast` / `handle_info`) splices a full `gen_server`
  callback result verbatim, which is what lets value-equality dispatch and
  `pickup`/`else` appear where the structured surface cannot express them:

```cure
use Std.Actor

actor Worker
  state Int
  initial 0
  messages Atom
  handle_cast
    pickup
      message == :inc -> %[:noreply, state + 1]
      message == :reset -> %[:noreply, 0]
      else -> %[:noreply, state]
```

`actor` names its lifted module the way `mod` does: `actor Counter` at top
level is owned by the implicit `Main`, so sibling code refers to it as
`Counter`; nested inside `mod Gate` it becomes `Cure.Gate.Counter`, still
written as `Counter` from inside `Gate`. The generated module exports the
normal `gen_server` callbacks plus a checked `start(initial)`,
`start_link(initial)`, `send(handle, message)`, `stop(handle)`, and one
function per named query:

```text
fn boot() = Counter.start()
fn bump(pid: Counter.Handle) -> Effect(Unit) = Counter.send(pid, Inc())
fn halt(pid: Counter.Handle) -> Effect(Unit) = Counter.stop(pid)
```

`start/N` returns `Effect(StartResult(Handle))` --
`Started(handle) | StartFailed | StartIgnored | InvalidStartResult`, from
`Std.Otp` -- and `start_link/N` returns the raw OTP startup tuple for use
under a supervisor.

### Typed process handles

The concurrency algebra behind `actor`/`sup` is `Std.Otp`'s typed process
family: `Pid(m)` is a plain process that only accepts messages of type `m`;
`GenServer(q, r)` is a synchronous server keyed on request `q` and reply `r`;
`ActorServer(m, q, r)` covers an actor with both a message type and a query
surface. All three are phantom-typed views over one opaque, erased raw pid,
so sending a message of the wrong type is a compile error, not a runtime one.

## Supervisors

A `sup` container declares a supervisor module. `children` is not optional --
a supervisor needs at least one child:

```cure
use Std.Supervisor

sup Root
  children
    worker Counter as counter
```

Each child names its kind (`worker` or `supervisor`), the module that
implements it, and the identity it is known by inside the tree. The tree's
own policy is three optional clauses, and `restart`/`shutdown` are optional
per child:

```cure
use Std.Supervisor

sup Tree
  strategy OneForOne()
  intensity 5
  period more(9)
  children
    worker Counter as counter
      restart Permanent()
      shutdown Timeout(5000)
    supervisor Subtree as subtree
      restart Transient()
```

- `strategy` is one of `OneForOne()`, `OneForAll()`, `RestForOne()`;
  it defaults to `OneForOne()`.
- `intensity` is an ordinary `Nat` literal; it defaults to `3`.
- `period` takes a `Positive` (`One() | More(Nat)` -- `more(9)` is `10`,
  `one()` is `1`), so a zero or negative period is unrepresentable; it
  defaults to `more(4)` (`5`).
- `restart` is one of `Permanent()`, `Transient()`, `Temporary()`;
  `shutdown` is `Brutal()` or `Timeout(ms)`.

Two children may not share an identity: `sup` rejects that at expansion time
rather than deferring it to the supervisor's own start-up.

### Child specs by hand

The macro's `children` clause is the ordinary way to build a tree, but the
underlying vocabulary is public in `Std.Supervisor`: `child/2`,
`child_with_typed_args/7`, `child_with_raw_args/6`, the `permanent`/
`transient`/`temporary`/`brutal_shutdown`/`shutdown_after`/`worker`/
`supervisor` constructors, and the closed `Restart` / `Shutdown` /
`ChildType` / `Strategy` types, for building a `ChildSpec` outside the macro.

## Runtime

Starting and stopping a tree is done through the module the macro generated,
not through `Std.Supervisor` itself -- that module holds the vocabulary,
while the generated one holds the running tree:

```cure
mod Driver
  use Std.Supervisor
  use Std.Otp
  use Std.ExitReason

  sup Tree
    strategy OneForOne()
    children
      worker Counter as counter

  fn boot() -> Effect(Tuple) = Tree.start_link()

  fn typed() -> Effect(StartResult(Tree.Handle)) = Tree.start()

  fn halt(tree: Tree.Handle) -> Effect(Unit) =
    Tree.stop(tree, Normal())
```

`start_link/0` is the raw OTP startup tuple; `start/0` narrows it to
`StartResult(Handle)`, where `Handle` is the tree's own alias for a
supervisor handle. Both route through `Std.Otp.start_supervisor` /
`start_typed_supervisor` -- the same checked effect path the generated `app`
module's `start/2` uses (see [Applications](/applications)).

## Links, monitors, and exit signals

`Std.Process` is a compatibility facade over a slice of `Std.Otp`'s typed
process algebra, keeping the familiar signal-operation names while returning
the same indexed handles and `Effect` results:

```text
mod MyApp.Pool
  use Std.Process

  fn watch(target: RawPid(m, r, k)) -> Effect(MonitorRef) = monitor(Process(), target)
```

The full surface: `self/0`, `link/1`, `unlink/1`, `monitor/2` (returns a
`MonitorRef`; the first argument is the closed `MonitorKind`), `demonitor/1`,
`is_alive/1`. Their process/reply-type parameters are implicit, so call sites
read as above. `Std.Otp` itself additionally has `exit/2` for sending an exit
signal built from `Std.ExitReason` (`Normal() | Kill() | Shutdown() |
Because(atom)`); the current stdlib has no `trap_exit` wrapper.

## Error codes

The codes below were introduced with the pre-0.34 `actor`/`sup` container
implementation. They describe checks the 0.34 macro-based rewrite still
performs in spirit, but the numbered codes themselves are no longer part
of the diagnostic registry, so `cure explain <code>` cannot resolve them
today; violations now surface through the general dependent-checking
diagnostics instead.

- **E045 Untyped Send** -- `<-|` on a bare `Pid` in strict mode.
- **E046 Inbox Mismatch** -- message not a subtype of the receiver's inbox ADT.
- **E047 Supervisor Unknown Child** -- child resolves to no compiled module.
- **E048 Supervisor Cycle** -- supervisor references itself transitively.
- **E049 Actor Handler Non-Exhaustive** -- `on_message` misses an inbox variant.
- **E050 Invalid Supervisor Strategy** -- unknown strategy, restart, or shutdown value.

## Full example

`examples/cure_colony/` ships with the release and exercises the whole
surface: two transparent actors (`Worker`, `Echo`) and a supervisor tree
wiring them under the default `:one_for_one` strategy.

```cure
# cure_src/worker.cure
use Std.Actor

actor Worker
  state Int
  initial 0
  messages Atom
  handle_cast
    pickup
      message == :inc -> %[:noreply, state + 1]
      message == :reset -> %[:noreply, 0]
      else -> %[:noreply, state]
```

```cure
# cure_src/echo.cure
use Std.Actor

actor Echo
  state Atom
  initial :nil
  messages Atom
  handle_cast %[:noreply, message]
```

```cure
# cure_src/colony.cure
use Std.Supervisor

sup Colony
  children
    worker Worker as worker_a
    worker Worker as worker_b
    worker Echo as echo
```

See the on-disk reference [`docs/SUPERVISION.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/SUPERVISION.md) for the full prose companion to this page.

## See also

With Cure 0.26.0 the `app` container wraps an entire supervision tree into a first-class OTP application, and `cure release` packages it as a bootable BEAM release. Read the [Applications](/applications) page for the tour, or go straight to the on-disk reference [`docs/APP.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/APP.md). The canonical end-to-end example is [`examples/cure_forge/`](https://github.com/cure-lang/cure-lang/blob/main/examples/cure_forge): an `app CureForge` container, a `sup Forge.Root` tree, four cooperating actors, and a start-phase-driven cache warm-up.

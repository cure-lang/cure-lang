%{
  title: "Actors & Supervision",
  description: "Type-safe concurrency on the BEAM: phantom-typed process handles, compile-time exhaustiveness checking, the Melquiades send operator (<-|), and declarative supervision trees.",
  category: :concurrency,
  category_title: "OTP & Concurrency",
  order: 1
}
---

Cure brings **dependent type safety** to the BEAM actor model. It bridges battle-tested Erlang/OTP fault tolerance with compile-time message safety, eliminating runtime inbox mismatches, untyped message drops, and dynamic supervision bugs.

## Why Concurrency in Cure?

- **Phantom-Typed Handles (`Pid[M]`)**: Process handles carry phantom types representing their inbox message family (`M`). Sending an invalid message type to an actor is caught at compile time.
- **Exhaustive Message Handlers**: The `actor` macro enforces pattern-matching exhaustiveness over your inbox algebraic data type (ADT).
- **The Melquiades Operator (`<-|` / `✉`)**: A first-class, pipeline-friendly send operator that desugars into checked, non-blocking BEAM effects.
- **Declarative Supervision (`sup`)**: Construct OTP supervision trees with compile-time child identity uniqueness, verified restart strategies, and zero boilerplate.
- **Native OTP Compatibility**: Cure actors lower directly onto `gen_server` and supervisors lower onto `supervisor`, maintaining 100% interoperability with the BEAM ecosystem.

## The Melquiades Operator (`<-|` / `✉`)

`pid <-| message` sends `message` to `pid` as a type-checked, non-blocking effect. You can use the ASCII spelling (`<-|`) or the Unicode symbol (`✉`):

```cure
pid <-| :hello
pid ✉  :hello
```

Both spellings desugar to `Std.Otp.tell`, which validates `message` against `pid`'s declared inbox type. The call is non-blocking, evaluates to `Effect(Unit)`, and never raises if the recipient has terminated.

### Pipeline Integration

The operator binds just below the pipe operator (`|>`), allowing transformed data to feed directly into an actor:

```cure
request
|> encode()
|> worker_pid <-| _
```

The last line is equivalent to `worker_pid <-| encode(request)`.

### Origin of "Melquiades"

Named after the ghost-mailman in *One Hundred Years of Solitude*, who continues delivering messages beyond lifetime boundaries. The arrow points into the receiver's inbox on the left: `pid <-| message` reads "the pid receives this message".

## Defining Actors (`actor`)

The `actor` macro (from `Std.Actor`) generates a type-checked `gen_server` module.

### Structured Actor Surface

The structured surface declares the actor's state, initial value, message handlers, and synchronous queries:

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

- **`on_message`**: Pattern-matches over incoming messages. Each clause returns the actor's updated state directly. The compiler enforces that all constructors of the message family are handled.
- **`on_call Request(params) returns Type`**: Declares a synchronous query. The `reply <expr>` statement provides the return value to the caller, while an optional `update <expr>` sets the new internal state.
- **Auto-generated API**: For `Counter`, the macro exports:
  - `start(initial)` — returns `Effect(StartResult(Handle))`
  - `start_link(initial)` — returns raw OTP startup tuple for supervisors
  - `send(handle, message)` — asynchronous message send
  - `get(handle)` — synchronous caller adapter for `on_call Get()`

### Raw Callback Surface (`handle_cast` / `handle_info`)

For advanced use cases requiring custom OTP return tuples, value-based pattern matching, or fallback clauses, use `handle_cast` or `handle_info`:

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

## Phantom-Typed Process Handles

The type system tracks process capabilities through phantom types defined in `Std.Otp`:

- `Pid(M)`: A process that only accepts messages of type `M`.
- `GenServer(Q, R)`: A synchronous server keyed on request `Q` and reply `R`.
- `ActorServer(M, Q, R)`: An actor supporting both asynchronous messages (`M`) and synchronous queries (`Q` / `R`).

Because these types are erased at runtime into raw BEAM pids, you get zero-cost compile-time type safety.

## Declarative Supervisors (`sup`)

Supervisors manage actor lifecycles and ensure fault tolerance. The `sup` macro (from `Std.Supervisor`) defines a supervisor module:

```cure
use Std.Supervisor

sup RootTree
  strategy OneForOne()
  intensity 5
  period more(9)

  children
    worker Counter as counter
      restart Permanent()
      shutdown Timeout(5000)
    supervisor SubTree as subtree
      restart Transient()
```

### Configuration & Guarantees
- **Restart Strategies**: `OneForOne()`, `OneForAll()`, `RestForOne()`.
- **Restart Policies**: `Permanent()`, `Transient()`, `Temporary()`.
- **Shutdown Policies**: `Brutal()` or `Timeout(ms)`.
- **Compile-Time Identity Uniqueness**: Duplicate child names are rejected at compile time before starting the VM.

## Links, Monitors, and Process Operations

`Std.Process` provides type-safe process operations wrapping BEAM primitives:

```cure
use Std.Process

fn watch(target: RawPid(m, r, k)) -> Effect(MonitorRef) =
  monitor(Process(), target)
```

Core primitives include:
- `self()` — Fetch current process handle.
- `link(pid)` / `unlink(pid)` — Establish or break process links.
- `monitor(kind, target)` / `demonitor(ref)` — Monitor process termination.
- `is_alive(pid)` — Check if a process is alive.

## Complete End-to-End Example

Here is a complete, self-contained example with two workers supervised under a `Root` tree:

```cure
use Std.Actor
use Std.Supervisor

actor Worker
  state Int
  initial 0
  on_message
    Inc -> state + 1
    Reset -> 0

sup AppTree
  strategy OneForOne()
  children
    worker Worker as worker_a
    worker Worker as worker_b
```

Starting and managing the tree:

```cure
mod Main
  use Std.Supervisor
  use Std.Otp

  fn boot() -> Effect(StartResult(AppTree.Handle)) =
    AppTree.start()
```

## See Also

- [Finite State Machines](/finite-state-machines): Verified state transitions backed by `gen_statem`.
- [Applications & Releases](/applications): Wrap supervision trees into OTP applications and build bootable BEAM releases with `cure release`.

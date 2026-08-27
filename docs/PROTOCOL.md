# Protocols (Session Types)

v0.27.0 introduces `protocol` -- a session-typed binary protocol
between actors. A protocol declaration describes, step by step, the
messages that flow between a finite set of roles; the compiler then
projects the declaration onto each role and verifies that the
actor implementing that role respects the projected FSM.

## Minimal example

```text
protocol Ping.Pong with Client, Server
  Client -> Server: Ping
  Server -> Client: Pong(Int)
  end
```

## DSL

- **Header**: `protocol <DottedName> with <Role1>, <Role2>[, ...]`.
  At least two roles are required.
- **Message step**: `<Role> -> <Role>: <Tag>` or
  `<Role> -> <Role>: <Tag>(<TypeList>)`. `<TypeList>` is a
  comma-separated list of Cure type expressions.
- **`loop`**: terminates the body and declares the whole preceding
  sequence as a loop.
- **`end`**: explicitly terminates the protocol.
- Comments (`# ...`) run to end-of-line.

## API

`Cure.Protocol` is the top-level module:

```elixir
{:ok, script} = Cure.Protocol.parse(dsl)
:ok           = Cure.Protocol.verify(script)

transitions   = Cure.Protocol.project(script, "Client")
model         = Cure.Protocol.participant_trace(script, "Client")
```

`parse_and_verify/1` fuses the two halves into a single call:

```elixir
{:ok, script} = Cure.Protocol.parse_and_verify(dsl)
```

## Projection

`Cure.Protocol.Script.project/2` produces an FSM-style transition
list from a role's perspective. Each state is labelled `S<index>`;
each event carries a `send `, `recv `, or `idle ` prefix followed
by the underlying message tag. The returned list is directly
compatible with `Cure.Temporal.Checker.from_fsm/2` so you can
layer LTL properties on top of the projected protocol.

## Verification and error codes

`Cure.Protocol.Verifier.verify/1` runs three structural checks:

1. Every declared role appears in the body.
2. Every role used in the body is declared.
3. Every state in a role's projection is reachable from the
   initial state.

Failures surface as `{:protocol_violation, message, meta}` tuples
with `code: "PROTO001"` in their meta keyword list. This code is
private to the protocol DSL: it is not registered in
`Cure.Diagnostic.Registry` and is never formatted by
`Cure.Compiler.Errors`, since `Cure.Protocol.Verifier` runs outside
the `.cure` compiler pipeline.

## PROTO001 -- Protocol Violation

Canonical examples:

- **Dead role** (declared but never used). Appears as
  `role X never appears in the protocol body`.
- **Stranger role** (used in a step but not declared). Appears as
  `role X referenced in protocol body but not declared in the with list`.
- **Unreachable state** (should only arise from malformed input).

## Integration with actors

Actors opt into a role via a future `@protocol` decorator
(v0.28). Today, projection + the temporal checker give you the
same verification story from Elixir test code -- see
`examples/cure_atelier/test/cure_atelier_test.exs` for a worked
example.

## See also

- [`docs/TEMPORAL.md`](TEMPORAL.md) -- LTL checker that consumes
  projected models.
- [`docs/SUPERVISION.md`](SUPERVISION.md) -- the actor surface
  protocols attach to.

# Temporal Properties

v0.27.0 introduces `Cure.Temporal`: a Linear Temporal Logic formula
ADT, a small DSL parser, and a bounded model checker that runs
properties over an FSM's transition graph.

## DSL

```text
always eventually Open
never Dead
always (Locked -> eventually Unlocked)
Locked until Unlocked
```

Operators, from lowest to highest precedence:

- `;` or newline -- property separator inside a multi-property script.
- `->` -- implication, right-associative.
- `or`, `and`, `until`.
- `always`, `eventually`, `never`, `next`, `!`.
- Atoms (any `[A-Za-z_][A-Za-z0-9_.]*` identifier).
- Parentheses for grouping.

`tt` and `true` are the tautological formula; `ff` and `false` are
the contradiction.

## API

```elixir
# Parse one formula:
{:ok, f} = Cure.Temporal.Parser.parse_one("always eventually Open")

# Parse a multi-property script:
{:ok, fs} = Cure.Temporal.Parser.parse("always Open; never Dead")

# Build a model from an FSM's transitions:
model = Cure.Temporal.Checker.from_fsm(
  [
    %{from: "Closed", to: "Open"},
    %{from: "Open",   to: "Closed"}
  ],
  "Closed"
)

# Check the formula:
Cure.Temporal.Checker.check(f, model)
```

`check/3` returns `{:ok, :holds}`, `{:violation, trace}`, or
`{:error, reason}`.

## Algorithms

- `always P` (safety): BFS over the reachable closure from the
  initial state; fails on the first violating state, with the BFS
  trail as a counterexample.
- `eventually P` (liveness): forward BFS for any reachable state
  satisfying `P`; fails when the frontier is exhausted.
- `next P`: universal next -- `P` must hold in every direct
  successor.
- `P until Q`: forward BFS along edges where `P` holds, succeeding
  when any reachable state satisfies `Q`.

## Bounds

The default search bound is `length(states) * 8`. Override via
the `:bound` option on `check/3`. Liveness checks that exceed the
bound return `{:error, :bound_exceeded}`; safety checks are sound
over the full reachable set regardless of bound.

## Error codes

`Cure.Temporal.Checker` does not raise catalog diagnostics (the `E059`
and `E062` codes planned in the v0.27.0 changelog were never wired into
the diagnostic registry). `check/3` instead returns plain result tuples:
`{:violation, trace}` with a concrete counterexample trace, `{:error,
{:unknown_atoms, unknown}}` when a formula references a state absent from
the model, and `{:error, :bound_exceeded}` when a liveness or `until`
search exceeds its bound.

## Integration

The checker is composable with the new `Cure.Protocol` projection:
a session-typed protocol projects onto each role as an FSM-style
transition list, which the temporal checker consumes unchanged.
See `examples/cure_atelier/test/cure_atelier_test.exs` for an
end-to-end exercise.

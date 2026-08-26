# SP3 Slice D: Shrunk Expansion Counterexamples

## Goal

Reduce a generated macro input while preserving the same ill-typed expansion
failure, then include the minimized Core filler in the proof diagnostic.

## Scope

- Represent a generated filler as an Antigen typed-term challenge.
- Use `Antigen.Shrink.minimize/3` with a predicate that reassembles and
  rechecks the same macro rule.
- Preserve both the original generated input and the shrunk witness in the
  `expansion_ill_typed` details.

## Invariants

- Shrinking is bounded and deterministic.
- Candidate acceptance always reruns the real parser expansion and dependent
  elaborator; a smaller but different failure is not accepted.
- No corpus banking and no trusted Core changes.

## Verification

- The deliberately ill-typed proof fixture reports a shrunk filler no larger
  than the original generated filler.
- Valid proof fixtures remain green.


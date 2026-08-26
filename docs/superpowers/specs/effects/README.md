# Effects specification family

## Canonical specifications

- [`2026-07-21-cure-computation-effect-typing.md`](2026-07-21-cure-computation-effect-typing.md)
  is the normative computation/value separation, effect-row, handler, latent
  effect, and dependent-kernel boundary specification.
- [`2026-07-21-dependent-effects-and-stackless-flow-design.md`](2026-07-21-dependent-effects-and-stackless-flow-design.md)
  is the companion design rationale and backend policy for dependent effects,
  monadic composition, stackless Flow, BEAM, and MCU execution.

The two 2026-07-21 documents are complementary: the former owns typing rules;
the latter owns the language/runtime architecture and research conclusions.
They must be updated together when a decision crosses both boundaries.

## Historical decision records

- `2026-07-09-effect-type-former-design.md` records the earlier inert
  `Effect(T)` pathway and is superseded by the computation IR and effect-row
  model for new design work.
- `2026-07-07-sound-effect-discipline-design.md` records the earlier surface
  `!`-only repair and remains useful for migration history.
- `2026-07-09-effects-as-data-design.md` records the rejected free-monad/data
  encoding and must not be treated as the current implementation.
- `2026-07-11-effect-deferred-items.md` records the old deferred-work ledger;
  current deferrals belong in the implementation ledger of the canonical IR
  and Lean specifications.

`2026-07-09-typeclasses-elaborator-feature-design.md` belongs to the `types/`
family, not this family.

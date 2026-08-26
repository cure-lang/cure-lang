# SP3 Slice C: Expansion Proof Gate

## Goal

Run a deterministic batch of generated macro uses, expand each through the
parser, and kernel-check the resulting surface expression.

## Scope

- Add `MacroFuzz.check_expansion_proof/3` for supported syntax rules.
- Use Slice A generation and Slice B assembly, then check each expansion with
  the dependent elaborator in the supplied module environment.
- Return `{:error, {:expansion_ill_typed, details}}` with the rule keyword,
  generated input, expansion, and kernel/elaborator error.
- Return `{:error, {:unsupported_hole_type, category}}` when a rule cannot yet
  be covered; callers must treat that as a coverage gap, never as a pass.

## Invariants

- The dependent elaborator and kernel remain the only type-checking authority.
- No compile-and-load or trusted Core modifications.
- The proof budget is deterministic and configurable for tests.

## Verification

- A valid `n + 1` rule passes across a batch of generated inputs.
- A rule whose expansion combines `n` with `true` returns an ill-typed proof
  failure.
- Unsupported rule categories return a coverage-gap error.


# SP2 Type-Only Example Pins

## Goal

Complete the remaining SP2 example obligation for `example ... expands : Type`.
An exact expansion pin remains α-normalized surface equality; a type-only pin
must elaborate the expansion against the pinned type in the real module
environment.

## Scope

1. Extend `Cure.Compiler.MacroValidate` with an environment-aware example check.
   Lower the pinned type through `Cure.Elab.Declarations.lower_type/3` and
   check the expanded expression through
   `Cure.Elab.Elaborator.elaborate_expr_checked/5`.
2. Keep the existing one-argument validator API for parser/compiler tests and
   exact expansion pins; the environment-aware API handles type-only pins.
3. Add a structured `example_type_mismatch` diagnostic with the rule keyword,
   expected type, expansion, and underlying reason.
4. Wire the environment-aware check into dependent `Program` validation and
   add red/green tests for a valid type-only pin and a rejected pin.

## Invariants

- No changes under `lib/cure/core/*`.
- The module environment is the one produced by declaration elaboration, so
  imported names and generated macro input records remain visible.
- Type-only pins do not compare surface AST shape; exact pins retain their
  existing α-normalized comparison.

## Verification

- Focused compiler and elaboration macro tests.
- `mix compile --warnings-as-errors`.
- Full `mix test` after the slice.


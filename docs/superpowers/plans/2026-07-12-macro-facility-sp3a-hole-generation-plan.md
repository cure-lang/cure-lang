# SP3 Slice A: Typed Hole Generation

## Goal

Expose the existing Antigen type-directed Core generator to macro proof code
through an explicit grammar-category bridge.

## Scope

- Add a small `Cure.Compiler.MacroFuzz` module that maps supported macro hole
  categories to certified Antigen v1 Core goals and returns a reusable `Gen`.
- Support only categories whose generated terms are covered by the v1 menu in
  this slice (`Nat`, `Bd`, and `Vec`); unsupported categories return
  `{:error, {:unsupported_hole_type, category}}`.
- Sampled terms must be checked against the mapped goal with the existing Core
  kernel before the API returns them.

## Invariants

- This is untrusted compiler/Antigen glue; no `lib/cure/core/*` changes.
- Unsupported coverage is reported, never replaced with a term of another
  type.
- The generator remains the existing `Antigen.Generators.Term.gen_term/2`.

## Verification

- Unit tests sample multiple deterministic terms for each supported category
  and kernel-check them.
- Unit test verifies unsupported categories are reported.
- `mix compile --warnings-as-errors` and the focused macro/Antigen test suites.


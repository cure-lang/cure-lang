# SP4 Tier 4 Reflection API

## Goal

Provide the minimal advisory reflection surface required by reducer/flow/view
style macro elaborators.

## Scope

- `resolve/2`: return a definition or type-family signature from a real Core
  environment.
- `constructors/2`: enumerate constructor signatures for a family.
- `infer/2`: elaborate a quoted surface expression and return its reified Core
  type, with all errors preserved.
- `expand/2`: run deferred computed expansion through `MacroExpand`; ordinary
  quoted ASTs pass through unchanged.
- `lift/1`: return declarations in append-only order without mutating the input
  environment.

## Invariants

- Every result is advisory and must still cross ordinary elaboration/kernel
  checks before becoming program state.
- No environment mutation, unification hooks, metavariable access, or Core
  changes.
- Unknown names and malformed requests return structured errors.

## Verification

- Resolve a real function and enumerate a real ADT's constructors.
- Infer a quoted expression in a real module environment.
- Expand a quoted AST and verify lift preserves append-only order and does not
  mutate its input.


# Plan: Validate Computed Macro Examples

**Date:** 2026-07-12  
**Scope:** SP2 computed-rule example execution, before compile-pipeline wiring

## Goal

Run `example ... expands ...` pins attached to `computed by` rules through the
existing compile-time macro executor and compare the resulting surface AST with
the pinned AST. Ordinary syntax-rule example validation remains unchanged.

## Phase 1: Environment-aware validation

- Add `MacroValidate.check_computed_examples/2`.
- Select only `:computed` rules and only `{:expansion, expected}` examples.
- Use `Parser.expand_example/2` to build the deferred computed use, then
  `MacroExpand.expand/2` with the caller-provided `Cure.Core.Env`.
- Compare successful expansions with the existing alpha-normalization helper.
- Return structured mismatch data and structured execution failures; do not
  raise or silently treat a deferred node as a successful expansion.

## Phase 2: Focused coverage

- Add a green computed example using a typed `Std.Syntax` record input.
- Add a wrong-pin mismatch test.
- Add an execution-failure test and compiler error rendering coverage.
- Run the focused compiler/elaborator tests and `mix compile --warnings-as-errors`.

## Constraints

- No changes under `lib/cure/core/*`.
- Do not wire these checks into `Program` in this phase; that is the next phase.
- Commit the implementation and tests as one phase with the ghost author.

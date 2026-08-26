# Plan: Wire Macro Self-Proving Checks Into Compilation

**Date:** 2026-07-12  
**Scope:** enforce M1/M3 and computed example checks in `Program`

## Phase 1: AST-level validation pass

- Add `MacroValidate.check_program/2` to collect every parsed `macro_def` and
  run, in order, exhaustive diagnosis, rule pinning, syntax expansion pins,
  and computed expansion pins.
- Return the first structured validation error unchanged so existing compiler
  error formatting remains the single presentation layer.
- Invoke the pass in `Program.check_ast_elixir_core/1` after declaration/body
  elaboration has populated the module environment and before totality
  certification.

## Phase 2: Compile-pipeline coverage

- Add green and red `Program.elaborate/1` tests proving missing diagnosis,
  unpinned rules, mismatched pins, and computed example execution are enforced.
- Update existing macro elaboration fixtures with minimal valid obligations so
  unrelated parser and soundness tests continue to exercise their original
  behavior under the now-enforced contract.
- Run the focused macro suites and the compile warning gate.

## Constraints

- No changes under `lib/cure/core/*`.
- Preserve the existing two-pass environment construction and ordinary macro
  expansion/kernel-checking behavior.
- Commit the implementation, wiring tests, and fixture updates as one phase
  with the ghost author.

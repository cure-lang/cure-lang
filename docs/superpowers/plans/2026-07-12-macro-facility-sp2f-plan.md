# SP2 Tier-3 Slice 3 — Compile-Time `computed by` Execution

> Stage 2 implementation plan. This slice turns the already-parsed Tier-3
> `computed by` rule into a real compile-time expansion. It is deliberately
> limited to the generic `Std.Syntax` value from slice 2; typed per-rule
> derived records, `check … else fail`, example execution, and compile-pipeline
> validation remain later SP2 slices.

## Goal

Given:

```cure
macro Mk
  syntax mk computed by build_it
```

the parser emits a deferred `{:computed_use, meta, [elab_ref, input]}` at `mk`
use-sites. The dependent elaboration path then:

1. reflects the matched input into a Core value of `Std.Syntax`;
2. elaborates `build_it` to a Core function;
3. kernel-infers and normalizes its application to the quoted input;
4. reflects the resulting `Std.Syntax` value back to surface AST; and
5. sends the spliced AST through the existing elaborator and kernel unchanged.

TCB delta remains zero: no `lib/cure/core/*` changes, and the normalizer is
only called, never modified.

## Grounded decisions

- Parser state gets `computed_macros: %{keyword => [rule]}` beside the existing
  syntax and literal maps. Harvest remains two-phase and local-only.
- A computed use has the shape
  `{:computed_use, [keyword:, line:, col:], [elab_ast, input_ast]}`. The input
  is a synthetic `{:macro_input, [keyword: keyword], bindings}` node, where
  `bindings` preserves rule-segment order. This is an ordinary generic
  `Std.Syntax` node and gives an elab a stable input even for a zero-hole rule.
- `Cure.Compiler.MacroSyntax` owns the mirror-repr ↔ Core conversion. Lists are
  encoded with `Nil`/`Cons`; strings are `List(Char)` values using bounded char
  literals; `Syntax`/`SynLit` constructors use the names in `Std.Syntax`.
- `Cure.Elab.MacroExpand` is untrusted frontend orchestration. It uses
  `Elaborator.elaborate_expr_typed/4`, `Kernel.infer/2`, and
  `Normalise.nf/3`, then calls `MacroSyntax.from_core/1`.
- Function bodies containing a computed use are elaborated after bodies without
  computed uses. All signatures are already registered, so this preserves
  forward references while ensuring a referenced total elab has a checked and
  certified body before normalization. A computed-body cycle is rejected by the
  expansion fuel guard rather than looping.
- Expansion has a finite fuel limit (32 nested computed expansions). Exhaustion,
  a non-function elab, an ill-typed application, or an invalid reflected result
  returns a structured `{:computed_macro_error, details}` error.

## Files and phases

### Phase 1 — parser deferral

- Modify `lib/cure/compiler/parser.ex`.
- Add computed-rule harvest/state seeding and dispatch.
- Reuse `match_segments/4`; successful computed matches emit the deferred node
  without running the elab. Mismatch diagnostics retain the SP1 error-floor
  shape.
- Tests: extend `test/cure/compiler/macro_computed_test.exs` with zero-hole,
  one-hole, and mismatch/deferred-AST assertions.
- Commit immediately after the focused parser tests and compiler warnings pass.

### Phase 2 — Core reflection bridge

- Modify `lib/cure/compiler/macro_syntax.ex` with public `to_core/1` and
  `from_core/1` over the existing mirror representation.
- Add direct bridge tests for every `Std.Syntax` constructor family, list/string
  encoding, and a round-trip through normalized constructor values.
- Commit immediately after the focused bridge tests and warnings pass.

### Phase 3 — elaborator-side execution and hook

- Create `lib/cure/elab/macro_expand.ex` with recursive AST walking, application
  checking, normalization, reflection back to AST, and fuel/error handling.
- Modify `lib/cure/elab/declarations.ex` to expand a function body before the
  ordinary body elaboration.
- Modify `lib/cure/elab/program.ex` to run plain function bodies before bodies
  containing deferred computed uses.
- Add friendly `Cure.Compiler.Errors.format_error/2` coverage for the structured
  execution error.
- Tests: add `test/cure/elab/macro_computed_execution_test.exs` covering a
  constant `Syntax` result, a hole-bearing input received by the elab, a bad
  result rejection, and recursion-fuel rejection. The end-to-end accept case
  must pass `Program.elaborate/1` and the hand-written equivalent must agree.
- Commit immediately after focused tests and `mix compile --warnings-as-errors`.

### Phase 4 — regression gate

- Run `mix test test/cure/compiler/ test/cure/elab/ test/cure/stdlib/`.
- Run the full `mix test` once, from the worktree root, and confirm no antigen
  seeds/corpus files changed.
- Commit only any required test/documentation correction as a separate,
  explicitly described phase; do not fold unrelated cleanup into this slice.

## Non-goals

- No typed derived per-rule record (`a.name`) yet.
- No `quote`/`$()` surface syntax yet.
- No `check … else fail`, computed-rule example checking, or MacroValidate wiring.
- No imported macro scoping, automatic hygiene, SP3 fuzzing, or classic pipeline
  support.

## Acceptance gate

- A computed macro parses to a deferred node and does not execute during either
  parser harvest or authoritative parse.
- A `Syntax -> Syntax` Cure elab executes at compile time through elaboration +
  normalization and its output is re-elaborated/kernel-checked.
- Invalid computed output fails compilation with a structured error, never a
  host exception or an unchecked AST.
- `mix compile --warnings-as-errors` and the full test suite are green.
- `git diff --name-only` contains no `lib/cure/core/*` changes.

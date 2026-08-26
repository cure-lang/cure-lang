# SP2 Tier-3 Typed Rule Records

> Stage 2 plan. This slice adds the typed elab-facing record promised by the
> Tier-3 execution design. It builds on the completed generic `Std.Syntax`
> bridge and `computed by` execution slice.

## Goal

For a rule such as:

```cure
syntax mk <x: Code> computed by build_it
```

derive a record `MkSyntax` with an `x: Syntax` field. The author can write:

```cure
fn build_it(a: MkSyntax) -> Syntax = a.x
```

The record is a normal Cure record, so projection is type-checked by the
existing elaborator and kernel. A misspelled field is rejected before the
computed macro executes.

## Grounded decisions

- The derived type name is `Capitalize(rule.keyword) <> "Syntax"`; this is
  deterministic and avoids coupling the type name to the macro container name.
- Fields are the rule's typed holes in segment order. Duplicate hole names are
  represented once, matching the existing substitution map semantics.
- Every field has type `Syntax` in this first typed-record slice. Category-indexed
  `Syntax(Category)` is deferred until the type-level reflection API supports it.
- `Program.declarations/1` expands `{:macro_def, ...}` into synthetic ordinary
  `:struct` declarations for computed rules. Existing record header, constructor,
  projection, duplicate-name, and import machinery remains authoritative.
- Deferred use metadata carries `syntax_type` and ordered `fields`. The execution
  pass constructs the derived record constructor with reflected `Std.Syntax` values
  as its fields. The elab's declared parameter type therefore matches the value
  passed at normalization time.
- A computed rule with no holes still derives a zero-field record. This keeps the
  elab ABI uniform and makes the rule type explicit.
- The generic `{:macro_input, ...}` node remains only parser metadata for the
  mirror bridge; it is never passed as the elab argument after this slice.

## Phases

### Phase 1 — derive metadata and declarations

- Annotate parsed computed rules with `syntax_type` and ordered `syntax_fields`.
- Emit those fields in the deferred-use metadata.
- Add synthetic record declarations to the dependent declaration flattener.
- Tests cover parsed metadata, generated family/field presence, and no regression
  for Tier-1/2 rules.
- Commit after focused parser/elab tests.

### Phase 2 — construct typed record inputs

- Add `MacroSyntax.to_core_record/2` over the existing mirror representation.
- Change `MacroExpand` to construct the derived record rather than a generic
  `Std.Syntax` node; retain the generic-node fallback for legacy hand-built ASTs
  without `syntax_type` metadata.
- Add a direct bridge test for empty and one-field derived records.
- Commit after focused tests and warnings-as-errors compilation.

### Phase 3 — typed projection gate

- Add an end-to-end program where `build_it(a: MkSyntax) -> Syntax = a.x` returns
  the reflected hole and the enclosing `mk n` function elaborates successfully.
- Add a negative test where `a.missing` returns the existing
  `{:unknown_field, :MkSyntax, "missing"}` error.
- Commit after the focused parser/compiler/elab regression.

### Phase 4 — full regression and state

- Run `mix test test/cure/compiler/ test/cure/elab/ test/cure/stdlib/`.
- Run full `mix test` once from the worktree root and verify no Antigen banking
  noise remains.
- Update the autopilot state and commit that record separately.

## Non-goals

- No category-indexed `Syntax(Category)` types yet.
- No `...` repeated-hole group records yet.
- No `quote`/`$()` surface syntax, `check … else fail`, example execution, or
  MacroValidate wiring.
- No imported macro scoping or classic pipeline support.

## Acceptance gate

- `a.x` is accepted only when `x` is a derived field on the rule record.
- A misspelled field fails through ordinary record projection diagnostics.
- The valid typed elab expands and kernel-checks end-to-end.
- Full suite green and no `lib/cure/core/*` changes.

# SP2 Tier-3 `check` / `fail` Slice

**Date:** 2026-07-12

## Scope

Add the author-extensible semantic failure half of self-proving macros without
changing the trusted Core implementation:

1. Parse macro-local `fail Name(args)` declarations and retain their source
   argument declarations in the `{:macro_def, ...}` rule stream.
2. Extend `MacroValidate`'s derived diagnosis points so every declared failure
   constructor must be covered by an `explain` clause.
3. Add a `Std.Syntax` failure carrier for compile-time elabs. A lowered
   `check condition else fail Name(args)` returns that carrier when the guard is
   false; `MacroExpand` converts it into the existing structured computed-macro
   error path.
4. Keep ordinary function behavior unchanged: the new forms are only accepted
   in the computed-elab surface and the generated failure value is still an
   ordinary `Std.Syntax` value checked by the kernel.

## Non-goals

- MacroValidate wiring into every compile remains a later SP2 slice.
- `quote` / `$()` sugar, category-indexed field types, and generative proof are
  not part of this slice.
- No changes under `lib/cure/core/*`.

## Phase commits

- Phase 1: parser `fail` declarations + structural diagnosis coverage.
- Phase 2: `Std.Syntax` failure carrier + `check`/`fail` lowering and decode.
- Phase 3: focused end-to-end tests and full verification.

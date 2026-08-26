# Constructor Qualification & `exposing` Imports — Design

**Status:** PARKED design (approved direction, not scheduled for implementation)
**Branch:** authored on `core-let-binder`; implement on its own branch later
**Date:** 2026-07-19

## Why this is parked

This captures an approved design so it is not re-derived later. It is **not**
being built now. The motivating change — the `Dyn → Dynamic` rename that dropped
the `D` prefix from the constructors (`Atom`/`Int`/`Float`/`Str`/`List`/`Tuple`/
`Map`/`Entry`) — has already landed. Those bare names are collision-prone with
the primitive types they wrap, and the `D` prefix used to be the disambiguator.
This feature is the principled replacement for that prefix: hide such
constructors behind a qualifier by default, and let an importer opt them back
into bare scope with an `exposing(...)` modifier.

Until this lands, `Std.Dynamic`'s constructors remain exposed unqualified (the
current behaviour); positional resolution keeps the stdlib compiling, so nothing
is broken in the interim.

## Goal

Let a module declare that its constructors are **qualified-by-default**: callers
reach them as `Dynamic.Atom(x)` (type-qualified) rather than bare `Atom(x)`,
unless the importing `use` opts in with an `exposing(...)` modifier.

```
use Std.Dynamic                       # constructors qualified: Dynamic.Int(3)
use Std.Dynamic exposing(*)           # every constructor bare: Int(3)
use Std.Dynamic exposing(Dynamic.*)   # every ctor of type Dynamic bare: Int(3)
use Std.Dynamic exposing(Int, Str)    # only these two bare; rest still qualified
```

Smart constructors and other module functions (`of_int`, `tag`, `entries`, …)
are unaffected — they come in unqualified as they do today. This feature governs
**data constructors only**.

## Decisions (settled)

1. **Opt-in at the defining module, NOT a global default.** A language-wide
   "constructors are qualified-by-default" flip would break every ADT in the
   stdlib and every test (`Some`/`None`/`Cons`/`Nil`/`Ok`/`Err`/…) until each
   import added `exposing(*)`. Instead a module (or a single type) *declares*
   that its constructors are qualified-by-default. `Std.Dynamic` opts in; every
   other module is unchanged. Migration cost is confined to `Std.Dynamic`'s own
   call sites.

   Surface for the opt-in (pick during implementation; both are additive):
   - a module attribute, e.g. `@qualified_constructors` on `mod Std.Dynamic`, or
   - a per-type marker, e.g. `type Dynamic qualified = Atom(Atom) | …`.

   The per-type marker is finer-grained and preferred if cheap; the module
   attribute is the fallback.

2. **Type-qualified, not module-qualified.** The qualifier is the constructor's
   **type name**: `Dynamic.Atom`, `Optic.Lens`. The type owns the constructor,
   it reads naturally, and it composes with the existing qualified-*type* path
   (`Resolution.resolve_qualified/3`, which already resolves `Std.Nat.Nat`).
   Module-qualification would force the full `Std.Dynamic.Atom` or an `as` alias.
   (In the `Std.Dynamic` case the module short-name and type name coincide as
   `Dynamic`; the rule is nonetheless "type name".)

3. **`exposing(...)` surface with globs.** Three forms:
   - `exposing(*)` — every qualified-by-default constructor of the module bare.
   - `exposing(TypeName.*)` — every constructor of that one type bare.
   - `exposing(Name, Name, …)` — those named constructors bare; rest qualified.

   This reuses the dormant `:exposing` filter concept the elaborator author
   already reserved (`program.ex:1457`: "a filter on WHICH of a module's names
   come in unqualified").

## What has to be built

- **Parser.** New `exposing(...)` modifier on `use` (alongside the existing
  `.{…}` selective form and `as` alias), producing an `:exposing` entry on the
  import meta with the glob/name list. New grammar for a **qualified constructor
  reference** `TypeName.Ctor` in BOTH expression and pattern position — Cure has
  no qualified-constructor syntax today. Plus the defining-module opt-in surface
  from Decision 1.

- **Elaborator.** Extend qualified resolution to constructors (today
  `resolve_qualified` handles types and owner-qualified globals, not ctors).
  Record a per-module/per-type "qualified-by-default" flag in the module
  interface. Gate bare-constructor injection at import on the `:exposing` filter:
  a qualified-by-default module contributes its constructors to the bare
  namespace only for names the filter admits; the rest are reachable solely as
  `TypeName.Ctor`. Pattern-match compilation must resolve the qualified spelling
  to the same constructor identity as the bare one (they are the same ctor, two
  spellings) — no runtime tag change.

- **Migration.** Update `Std.Dynamic`'s own consumers (`Std.Optic` case affines,
  the run-tests) to either `exposing(*)` or the qualified spelling. Small and
  local, because the opt-in is Dynamic-only.

- **Zero TCB.** This is surface resolution and import filtering; the kernel never
  sees a difference — a qualified constructor elaborates to the identical Core
  constructor as its bare spelling. Outside the trust boundary.

## Testing strategy (when built)

- `use Std.Dynamic` (no modifier): a module referencing bare `Int(3)` fails to
  resolve; `Dynamic.Int(3)` resolves. Both expression and `match` pattern.
- `exposing(*)`, `exposing(Dynamic.*)`, `exposing(Int, Str)`: each admits exactly
  the intended bare names and no others.
- Runtime identity: `Dynamic.Int(3)` and (under `exposing`) `Int(3)` compile to
  the same tag `{:Int, 3}` — the qualification is purely a source-level scope
  distinction.
- Regression: every other module's bare constructors (`Some`/`None`/`Cons`/…)
  keep working with no import change — proof the default is opt-in, not global.

## Out of scope

- Qualified references for **functions/values** (only constructors here).
- Module-qualified (`Std.Dynamic.Atom`) constructor syntax — type-qualified only.
- Any global flip of the constructor-exposure default.

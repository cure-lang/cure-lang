# `@group` decorator placement — above `mod`, not inside it

**Status:** Approved (design), ready for planning.
**Date:** 2026-07-10
**Batch:** Std hygiene (1 of 2; precedes `2026-07-10-primitive-type-declarations-design`).

## Problem

`@group(:core)` currently sits as the *first statement inside* the `mod` body:

```cure
mod Std.Binary
  ## docs …
  use Std.Bounded
  @group(:core)          # <-- inside the body
  ...
```

This is a holdover from when grouping was the magic identifier `__group__`, a
statement that necessarily lived among the module's statements. Now that it is a
real decorator, its in-body position is *misleading*: a decorator annotates
**the item that follows it**, so a reader parses `@group(:core)` as "the next
declaration is grouped," when what it actually annotates is **the module
itself** (`Cure.Stdlib.Preload.module_groups/0` is keyed by module atom, not by
any inner declaration).

The fix is to place `@group` **above** the `mod` declaration, the position where
a decorator unambiguously annotates what follows:

```cure
@group(:core)
mod Std.Binary
  ## docs …
  use Std.Bounded
  ...
```

## Why this is more than moving text

`@group` is in the parser's `@module_level_decorators` allow-list
(`parser.ex:71`). When the parser encounters it, it **short-circuits to a
standalone `{:decorator, …}` node** (`parser.ex:4914`) *before* inspecting what
follows, and never attaches it to anything. `parse_at_attach/4` knows how to
attach a decorator to a following `fn` / `rec` / `type` (`parser.ex:4927-4948`)
but has **no clause for `mod`**. So a `@group` written above `mod` today becomes
a floating node *outside* the module, orphaned from it.

Two consumers read the group, and they must keep working after the move:

1. **Compile-time source scan** — `@std_module_groups` (`preload.ex:110`) uses
   the line-anchored, multiline regex `@group_regex` (`preload.ex:104`,
   `~r/^\s*@group\(\s*:([a-z_][a-z0-9_]*)\s*\)/m`). This is **position-agnostic**:
   it matches `@group(:x)` on *any* line, so it already works whether the
   decorator is inside or above `mod`. **No change required** — but the design
   pins a test that confirms it.
2. **BEAM-attribute path** — packaged releases with no `lib/std/` source read the
   group from each module's `-group([:g])` BEAM attribute
   (`preload.ex:422-428`). That attribute is emitted by the **classic codegen**
   from a module-level decorator. If the parser attaches the pre-`mod` `@group`
   to the module container, codegen must read it from the container meta so the
   attribute is still emitted.

## Design

### 1. Parser — attach a pre-`mod` `@group` to the module; reject it elsewhere

`@group` is the only entry in `@module_level_decorators` today, so its handling
can be made position-strict. When the parser encounters `@group`, check whether
the next token opens a module (`mod` / `module` keyword):

- **Followed by `mod`** — parse the module and attach the decorator to the module
  container's `:decorator` meta (reusing `attach_decorator/3`'s generic container
  clause, the same path `@builtin(:key) type Name` uses at
  `parser.ex:4945-4948`). Result AST for `@group(:core)\nmod Std.Binary … end`: a
  single `{:container, container_type: :module, …}` node carrying the group in its
  meta (the plan verifies the exact meta key against `attach_decorator/3`), **not**
  a floating sibling decorator.
- **Anywhere else** (in-body, or before a non-`mod` item) — a **hard error** with
  a clear message ("place `@group` above the `mod` declaration"). The legacy
  standalone-node path for `@group` is removed. This is the hard cutover: the
  misleading in-body form no longer parses at all, so no reader can be bamboozled
  by it again.

### 2. Classic codegen — emit `-group` from the module container meta

Wherever the classic pipeline currently emits the `-group([:g])` module
attribute from an in-body `@group` decorator node, additionally (or instead)
read it from the module container's attached decorator meta, so the attribute is
emitted for the above-`mod` form. This touches `lib/cure/compiler/codegen.ex` —
which is legitimate here: module grouping is a **classic-pipeline / Preload
runtime** concern, not a dependent-kernel one. This is explicitly *not* a
dependent-pipeline change.

### 3. Migration — move `@group(:core)` above `mod` in all 13 std files

The modules carrying `@group(:core)` today:

`functor, bool, ord, equatable, bounded, equivalent, core, decision, sigma,
binary, nat, proof, show` (files under `lib/std/`).

Each moves its `@group(:core)` line from the body to immediately above its `mod`
line. No other edits. Because the in-body form is a hard parse error after §1,
this migration is **mandatory and atomic with the parser change** — the suite
does not compile until every in-tree `@group` (stdlib and any test fixtures) is
above its `mod`. Any non-stdlib usage the full suite surfaces is migrated in the
same change.

### 4. Hard cutover — the in-body form no longer parses

There is no back-compat path. Per §1 an in-body `@group` is a parse error, so the
misleading placement cannot recur. The canonical and *only* accepted form is
above `mod`.

## Testing

- **Parser** — `@group(:core)\nmod M … end` parses to a single module container
  whose meta carries the group; the floating-sibling shape is gone. An in-body
  `@group` (or one before a non-`mod` item) is a **parse error** with the
  placement message.
- **Association** — `Preload.module_groups()` returns `:core` for every migrated
  module (regex path), and `group_from_beam/2` returns `:core` for a compiled
  module (BEAM-attribute path) — proving both consumers survive the move.
- **Migration guard** — every file under `lib/std/` that contains `@group(`
  has it on a line *above* its `mod` line (a structural rehearsal check over the
  sources), so no file silently keeps the legacy placement.
- **Full suite + stdlib preload** green (the preload machinery is exercised
  throughout the suite via `setup_all` preload).

## Out of scope

- Any change to the dependent elaborator / kernel.
- An automated codemod for the in-body form — migration is the manual, one-time
  move of 13 lines (the in-body form is a hard error, so there is nothing to
  deprecate).
- Grouping semantics themselves (what `:core` means, prelude membership) — that
  is the sibling primitive-types spec's concern.

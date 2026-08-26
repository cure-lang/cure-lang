# Overloading & Argument Labels — Design

**Status:** approved design, deferred implementation (build after the current
stdlib-graduation batch). Author gate: design approved 2026-07-10.

**Goal:** Let several functions share a name, disambiguated at the call site by
**argument type** (Idris2-style type-directed resolution) and by optional
**argument labels** (Swift-style), so the stdlib no longer needs unique-name
workarounds (e.g. `Std.Char.code_point` renamed to dodge `Std.String.to_int`)
and user APIs can carry self-documenting call sites.

**Non-goal:** any change to the trusted kernel (`lib/cure/core/*`). Labels and
overload sets are a **surface + elaborator** concern only; both erase before
Core. This is a P (parser) + E (elaborator/resolution) feature with **zero TCB
risk**.

---

## 1. Motivation

The dependent pipeline resolves globals by **bare name**. Two modules that
export the same name collide: `Cure.Elab.Resolution` re-keys the shadowed import
to a qualified atom `:"Mod#Name"` and a bare reference either resolves uniquely
or raises `{:ambiguous_name, atom, mods}`. That forced a rename in the stdlib —
`Std.Char.to_int(Char) -> Int` collided with `Std.String.to_int(String) -> Int`
(string parse), so the Char coercion was renamed to `code_point`. That is a
workaround, not a fix: the two functions have **different argument types** and a
type-directed resolver should keep both under the name `to_int` and pick the
right one per call site.

Separately, functions that differ only by *role* rather than type —
`move(to: Point)` vs `move(from: Point)` — cannot be told apart by argument type
at all. Swift solves this with argument **labels** that are part of the
function's identity. Cure adopts the same idea, with one deliberate divergence:
labels are **optional by default** (readability, not ceremony), becoming
mandatory only when they are load-bearing.

## 2. Real-language alignment

- **Type-directed overload resolution** — Idris2. When a name is ambiguous,
  Idris2 elaborates each candidate against the expected/argument types and keeps
  the one that checks. This is the mechanism we port, and the piece we
  oracle-probe against `idris2 --check`.
- **Argument labels (external vs internal name)** — Swift / OCaml labelled args.
  Labels are a surface ergonomic that erases; they never reach the core theory,
  so aligning them with Swift (rather than one of the dependent-3) is sound —
  the operator's Agda/Lean/Idris alignment law binds TCB changes, and this is
  not one.

## 3. The parameter model

Every parameter has up to two names:

- **Internal name** — the binder the function **body** refers to.
- **External label** — the name the **caller** writes.

Three declaration forms:

| Declaration            | Caller writes            | Label status                     |
|------------------------|--------------------------|----------------------------------|
| `fn f(x: T)`           | `f(5)` **or** `f(x: 5)`  | optional (single name = both)    |
| `fn f(to dest: T)`     | `f(to: 5)` **only**      | **mandatory** (label ≠ internal) |
| `fn f(_ x: T)`         | `f(5)` **only**          | forbidden (`_` suppresses)       |

The `_`-suppressed form is included for completeness/parity with Swift but is
**Phase 3 / optional** — since single-name labels are already optional, it earns
its place only if a function wants to *forbid* a label. Not on the critical
path.

### Why "mandatory under shadowing" falls out of scoping

When the external label differs from the internal name (`fn f(to dest: T)`), the
internal name `dest` is **private to the body** — it is not in scope at the call
site. The only name a caller can use is the external label `to`. So the label
*must* be mandatory there; it is not an arbitrary rule but a consequence of the
internal name being unavailable to callers.

## 4. Call-site resolution

Resolution is **elaborate-and-prune** (Idris2 model), keyed by
`(name, arity, argument types, written labels)`:

1. Gather all candidates in scope with the given `name` and `arity` (the
   overload set). A qualified reference `Mod.f` restricts the set to one module
   — the ultimate escape hatch, always available.
2. Filter by **written labels**: a candidate survives only if every written
   label names one of its parameters at the matching position, and every
   parameter whose label is *mandatory* (two-name form) has its label written.
3. Filter by **argument type**: a candidate survives only if each argument's
   inferred type unifies with the corresponding parameter type.
4. Decide:
   - exactly one survivor → resolve to it;
   - zero survivors → `{:no_matching_overload, name, arg_types}`;
   - more than one survivor → `{:ambiguous_overload, name, candidates}`, and the
     diagnostic tells the user that a **label** (or a qualified `Mod.f`) will
     break the tie.

Labels are therefore **optional for readability, mandatory only when
load-bearing** — i.e. when omitting them would leave step 4 with >1 survivor.
This single rule subsumes the "mandatory under shadowing" case (a two-name form
already forces its label in step 2) *and* the "two overloads, same types,
different labels" case (`move(to:)` vs `move(from:)`, which only the label can
separate).

### Ordering

**Superseded on 2026-07-21.** The proof-language ergonomics design upgrades
labels into reorderable named arguments. Positional arguments must form a
prefix and fill the leftmost present parameters; after the first named argument,
every argument is named and those names may appear in any order. Elaboration
aligns them to the chosen declaration's telescope before dependent solving and
Core construction. This section records the original v1 constraint only; the
July 21 design is authoritative.

## 5. Surface syntax

Declaration — Swift spelling, `label internal`:

```cure
fn move(to dest: Point, from src: Point) -> Path = ...
fn to_int(c: Char) -> Int = code_point(c)   # single name, label optional
```

Call site — `label: value`:

```cure
move(to: p1, from: p0)     # labels mandatory (two-name form)
to_int('A')                # label omitted (optional)
to_int(c: 'A')             # label written (self-doc), same call
```

### Parser: the happy coincidence

`f(x: 1, y: 2)` **already parses** in Cure — it is the record-construction
field-pair form (`Point(x: 1, y: 2)` →
`{:function_call, [name: "Point", record: true, ...], field_pairs}`). Labelled
function arguments are the **same surface shape**. The elaborator routes on
whether the head resolves to a record type or a function: record type → record
construction; function → labelled call. So this adds little new parser surface;
the two-name **declaration** form (`label internal:`) is the main new parse, and
it mirrors the existing named-function-type-argument handling already present in
`parse_type_atom` (parser.ex ~3335, "unnamed args unchanged").

## 6. Erasure & where it lives

- **Erasure:** labels and overload sets are resolved away during elaboration.
  The emitted Core (and the BEAM call) is **positional** — the kernel never sees
  a label, an overload set, or an external/internal name split. No
  `lib/cure/core/*` change; no Antigen antibody needed (nothing in the trusted
  boundary moves).
- **Home:** `lib/cure/elab/resolution.ex` — today it treats a same-name
  collision as an error to escape via qualification. This feature flips that
  philosophy: **a collision is an overload set to resolve by signature**, with
  qualified `Mod.f` retained as the escape hatch. The declaration-side changes
  (two-name binder, per-parameter label metadata) live in the parser and in
  `lib/cure/elab/declarations.ex` where parameters are lowered to binders; the
  call-site pruning lives where application heads are resolved
  (`declarations.ex` global-app path, alongside the existing
  `resolve_bare_shadowed`).

## 7. Pinned decisions

1. **SUPERSEDED:** declaration-order-only labels were the v1 rule; the July 21
   named-argument design permits reordering after a positional prefix.
2. **Elaborate-and-prune resolution** keyed by `(name, arity, arg types,
   labels)`, Idris2-style; qualified `Mod.f` is the always-available escape
   hatch.
3. **Labels optional by default**, mandatory only when load-bearing (two-name
   form, or omission leaves the overload set ambiguous).
4. **Zero TCB change** — labels erase; nothing enters `lib/cure/core/*`.
5. **`_`-suppressed labels are deferred** (Phase 3, optional).

## 8. Out of scope

- Return-type-directed overloading beyond what falls out of the existing
  bidirectional `expected`-type threading (we do not add a dedicated
  return-type dispatch pass in this feature).
- ~~Reordering labelled arguments.~~ Superseded and brought into scope by the
  July 21 proof-language ergonomics design.
- Labels on constructor fields beyond the record-construction syntax that
  already exists.

## 9. Phasing (build order, each its own red-green batch)

**Phase 1 — type-directed resolution (carries the parity weight).**
Turn a same-name collision into an overload set; resolve at the call site by
`(name, arity, argument types)`. No label surface yet. Unblocks the stdlib
collisions directly. First regression test: `Std.Char.to_int(Char)` and
`Std.String.to_int(String)` coexist under the name `to_int`, each resolving by
argument type. Oracle probe: an Idris2 program with two same-named,
type-disambiguated functions vs the Cure transliteration (`cure-porting`).

**Phase 2 — argument labels (Swift ergonomics).**
Add the two-name declaration form (`label internal:`) and call-site labels
(`f(label: v)`), reusing the record field-pair parse. Extend resolution's
pruning with the label filter and the mandatory-label rule. Regression:
`move(to:)` vs `move(from:)` disambiguated by label alone.

**Phase 3 — `_`-suppressed labels (optional).**
Only if a concrete need to *forbid* a label appears.

## 10. Interaction with the current stdlib workaround

Once Phase 1 lands, `Std.Char.code_point` **may** revert to `to_int` (coexisting
with `Std.String.to_int` by type). `code_point` is, however, the more accurate
name (it *is* the Unicode code point; Lean calls the analog `Char.val`), so the
revert is optional — the point of Phase 1 is that the rename is **no longer
forced**, not that it must be undone.

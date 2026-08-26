# Record Field-Lens Deriving — Design

**Status:** approved design (autopilot Sub-project 1 of the optic-path programme)
**Branch:** `core-let-binder` (accumulating optic stack — Std.Dynamic, case affines, laws)
**Date:** 2026-07-19

## Goal

Make a well-behaved `Lens` available for **every field of every record**, derived
automatically, with **no tag on the record** and **no bespoke compiler
machinery**. After this lands, a caller can focus and update any record field
through the existing `Std.Optic` eliminators:

```
set(compose(User_address, Address_city), "Paris", u)   # deep update, no handwritten lens
view(User_name, u)                                     # read
over(User_age, fn(n) -> n + 1, u)                      # modify
```

plus reach a **list element** through a partial (affine) index optic:

```
preview(compose(User_scores, ix(0)), u)                # Option — may miss
set(compose(User_scores, ix(0)), 100, u)               # no-op if out of range
```

This is the function-call substrate. The prettier operator surface (`<~`,
`.`-composition) and the projection/bracket sugar (`u.scores[0] <~ v`) are
**explicitly out of scope** here and specified separately later (they depend,
respectively, on the operator/overload branches and on a future type-aware macro
tier). See "Deferred" below.

## Why this needs no new compiler machinery

`Std.Optic` already ships `lens/4`, `compose`, and the `view`/`set`/`over`/
`preview`/`to_list_of` eliminators, all law-checked. A field lens is nothing more
than a specific `lens/4` application:

```
# field `f : F` of record `R` becomes:
lens(fn(r) -> r.f, fn(v) -> fn(r) -> R{r | f: v})
```

Both halves are ordinary, already-supported surface: `r.f` is field projection
and `R{r | f: v}` is functional record update (see `test/oracle/record/
rc04_update.cure`). So "deriving a lens" is **purely syntactic code generation**
— templating that expression per field from the record's declared shape. It
needs the field name and the record name, both present in the `rec` AST, and it
needs **no type information**, because the generated code type-checks afterward
through the normal kernel like any handwritten `lens/4` call. The derivation
therefore rides the existing **decl-position Tier-3 macro** path (the model is
the landed message-code derivation programme, which runs before
`LiftModule.collect`), and stays entirely **outside the TCB**.

## Surface

### Derived field lenses

For each `rec R` with fields `f1: T1, …, fn: Tn`, the deriver emits one
module-scoped lens value per field, named **`R_f`** (the record's exact spelling,
an underscore, the field name):

```
rec User
  name: String
  age: Int
  address: Address
  scores: List(Int)

# derived, automatically, as if the module had written:
#   fn User_name    = lens(fn(r) -> r.name,    fn(v) -> fn(r) -> User{r | name: v})
#   fn User_age     = lens(fn(r) -> r.age,     fn(v) -> fn(r) -> User{r | age: v})
#   fn User_address = lens(fn(r) -> r.address, fn(v) -> fn(r) -> User{r | address: v})
#   fn User_scores  = lens(fn(r) -> r.scores,  fn(v) -> fn(r) -> User{r | scores: v})
```

`R_f` is collision-free by construction: record names are unique within a module
and field names are unique within a record. **Collision policy:** if a
user-defined binding of the exact name `R_f` already exists in the module, the
deriver does **not** silently overwrite it — it reports a
`{:field_lens_name_clash, R, f}` error at derivation time. (A user who wants a
custom lens for that field names it something else, or the clash is a real bug.)

**Eager vs. use-site derivation.** Because this phase has no path syntax to
trigger on, derivation is **eager**: every `rec` in every elaborated module gets
its field lenses. They are ordinary functions, tree-shaken at emit by
`reachable_def_names`, so an unused `R_f` costs nothing in the output. The future
type-aware macro tier (deferred) can make derivation lazy/use-site-driven; this
phase does not need that and does not attempt it.

### List index affine — `ix`

A new primitive in `Std.Optic`:

```
fn ix({a: Type}, i: Int) -> Optic(List(a), a, AffineKind)
```

built directly on the existing `affine/…` constructor with two new `Std.List`
partials as the partial getter and putter:

```
fn ix(i) = affine(fn(xs) -> Std.List.at(xs, i),
                  fn(v) -> fn(xs) -> Std.List.set_at(xs, i, v))
```

`ix(i)` is an **affine**, not a lens, and deliberately so: a bare `List` carries
no length, so indexing genuinely may miss. `preview(ix(i), xs)` is `Some(elem)`
in range and `None` out of range; `set`/`over` replace in place when the index
exists and are a **no-op** otherwise (the affine miss-is-a-no-op law). Totality
is available by *choosing a different container* — `Vector(a, n)` with a
`Bounded(n)` index is a total lens (`Std.Vector.lookup`/`set` already exist); the
container is the totality declaration. This phase adds the `List` (affine) form
only; a `Vector` index **lens** wrapper is a natural follow-on but not required
here.

### New `Std.List` primitives

```
fn at({t: Type}, list: List(t), idx: Int) -> Option(t)
  # Some(element) when 0 <= idx < length; None otherwise. Structural recursion.

fn set_at({t: Type}, list: List(t), idx: Int, value: t) -> List(t)
  # Replace the element at idx when in range; return the list unchanged otherwise.
```

Both are total, plain structural recursion, no TCB. They complement the existing
`nth(list, idx, default)` (total-by-default) rather than replacing it.

### List traversal — `each` (highest implementation risk; may be split out)

```
fn each({a: Type}) -> Optic(List(a), a, TraversalKind)
```

A traversal focusing every element: `to_list_of(each(), xs)` returns all
elements, and `over(each(), f, xs)` maps `f` across them. This reuses the
count-indexed `TravRep` (`Sigma(n, Sigma(Vector(a, n), Vector(a, n) -> s))`) and
the landed traversal machinery (`compose_trav`, `Std.Vector.take`/`drop`,
`to_list_of`). Building a traversal over an *unindexed* list requires gathering
the list into a `Vector(a, len)` and providing the length-preserving rebuild;
this is the one piece here that touches the harder count-indexed rebuild, so it
is scheduled **last** and **may be deferred to its own follow-on** if it resists
— the field-lens deriving and `ix` are the committed core of this run and do not
depend on `each`.

## Testing strategy

Concrete run-tests in the codebase's established style (deterministic sample
tables compiled and loaded via `Emit.compile_and_load`, mirroring
`test/cure/stdlib/optic_laws_test.exs` and `optic_dynamic_run_test.exs`). No
generative property tests (StreamData is Antigen-internal here).

1. **Deriving unit tests** (`record_field_lens_test.exs`):
   - A `rec` with several fields derives one `R_f` lens per field; each obeys the
     three **lens laws** (get-put, put-get, put-put) over a sample table.
   - **Deep composition:** `compose(R_a, A_b)` reads and writes a nested field;
     law-checked.
   - **Name-clash policy:** a module defining both `rec User{…name…}` and a
     user `fn User_name` fails elaboration with `{:field_lens_name_clash, …}`.
   - **Tree-shaking:** an unused derived lens does not appear in the emitted
     module (assert against `reachable_def_names`).
2. **`ix` affine tests** (`list_index_affine_test.exs`):
   - `preview(ix(i), xs)` hits in range, misses out of range and on `[]`.
   - `set`/`over` through `ix(i)` replace in range, no-op out of range — i.e. the
     **affine laws** (set-preview, preview-set, set-set, miss-is-no-op) over a
     sample table.
   - `compose(R_listfield, ix(i))` — deep affine through a derived lens.
3. **`Std.List.at`/`set_at` unit tests** — in range, out of range (both ends),
   empty list, negative index.
4. **`each` traversal tests** (if built) — identity (`over(each(), id) == id`)
   and composition (`over(each(), g) ∘ over(each(), f) == over(each(), g ∘ f)`),
   matching the existing traversal-law test shape.
5. **Regression firewall:** `Std.Optic` and `Std.List` stay in the
   `DependentElaborationParityTest` `@green` scan; the existing
   `optic_laws_test.exs` continues to pass unchanged.

Every task is red-first: write the failing law/behavior test, watch it fail for
the right reason, implement minimally, green, commit.

## Files touched

- `lib/std/list.cure` — add `at/3`, `set_at/4`.
- `lib/std/optic.cure` — add `ix/2` (and `each/1` if built).
- Compiler decl-macro path (the Tier-3 derivation hook that runs before
  `LiftModule.collect`) — add the per-`rec` field-lens emission. Exact module and
  function are pinned in the implementation plan; the derivation is additive and
  outside the TCB.
- `test/cure/stdlib/record_field_lens_test.exs`, `list_index_affine_test.exs`,
  and `Std.List` unit tests — new.

## Deferred (each its own later spec — do NOT build here)

1. **Operator sugar** — `<~` (set/over, dispatched by overloading on the RHS) and
   a `.`/`%` compose operator, as user-defined operators. Gated on merging
   `feature/precedence-operator-overloading` + the type-directed overload branch
   into this line.
2. **Projection/bracket sugar** — `u.scores[0] <~ v`, `xs[]`, `v[Ctor]`. Requires
   a **type-aware macro tier** (a Lean-`MetaM`-analogue) that can read
   intermediate field types during expansion and reinterpret projection position
   as an optic. Its output stays kernel-checked, so the tier remains outside the
   TCB. This is the motivated, standalone initiative the whole programme builds
   toward; this run is its concrete use case, not its implementation.
3. **Grade-decorator refactor** — `@linear cap: T` replacing `cap :linear T`.
   Independent, surface-only, no dependency on any of the above; can run anytime.
4. **`Vector` index lens** and **prism sugar for `Option`** (`_Some`) — natural
   companions to `ix`, small, but not required for this run's core.

## Terminology guard

The word **affine** appears in two unrelated senses in Cure and the spec keeps
them distinct: the optic **`AffineKind`** (a focus that may be absent — what `ix`
and prisms produce) versus the QTT **`:affine` grade** (a binder used at most
once — a multiplicity on the arrow). They share a name only by historical
accident; nothing in this design connects them.

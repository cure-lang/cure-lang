# Std.Optic — a well-typed optics library (design)

**Date:** 2026-07-11
**Status:** Design approved (brainstorming). Ready for implementation planning.
**Replaces:** the deleted `Std.Access` (removed 2026-07-11, commit `28efda0`).

## 1. Motivation

`Std.Access` was a port of Elixir's `Access` behaviour: uniform read/update/pop
over nested, heterogeneous containers (maps, keyword lists, tuples, lists), plus
composable path/lens values (`key`, `at`, `elem_at`, `all`, `filter`) walked by
`get_in`/`put_in`/`update_in`/`pop_in`.

The only way it elaborated on the dependent pipeline was an opaque `Any` top type
plus `believe_me` coercions dispatching on runtime `is_map`/`is_tuple` tags — a
proliferation of unchecked casts that *bypassed* the type system instead of using
it. It was deleted for that reason.

This document designs the well-typed replacement: **`Std.Optic`**, a
lens/prism/traversal library in which the whole-type and part-type are genuinely
connected at compile time, with **zero `believe_me`**.

### What the old module solved (and we must keep)

1. **Deep update without hand-rebuilding.** Change one leaf in a nested immutable
   structure declaratively.
2. **Composable, reusable paths.** A path is a first-class value you can build,
   name, and pass around; `all`/`filter` fan out over many leaves at once.

### What changes (and why it's a feature)

Reaching into *heterogeneous, untyped* data is no longer free. Optics compose
only where leaf types line up. The primary targets become:

- **Records** (`rec`) — known fields → *total* lenses.
- **Homogeneous collections** — `List` / `Vector` / `Map(K,V)` → traversals and
  (fallible) affines.
- A standalone **`Std.Dynamic`** sum (`Dyn`, over BEAM value shapes) as the
  deliberate, typed escape hatch for genuinely mixed/dynamic data — matched, not
  `believe_me`d. Optic-agnostic; `Std.Optic` imports it (§5a).

The runtime-crashing accessors (`fetch_bang`, raise-on-miss) and the
domain-changing ones (`pop`) leave the optics surface; see §6.

## 2. Prior art (why this shape)

- **Idris 2** (`idris2-lens`): profunctor / van Laarhoven optics
  (`∀p. Strong p => p a b -> p s t`). Uniform composition and free kind
  subtyping, but leans on rank-2 polymorphism + interface resolution under a `∀`.
- **Agda**: the existential / coend encoding
  `Optic S T A B = Σ M. (S → M×A) × (M×B → T)` — the coend becomes a plain
  Σ-type, so it needs no rank-2 machinery. This is the dependently-typed-native
  form and the one we follow.
- **Lean 4**: no canonical profunctor library; native structure-update
  (`{ s with f := v }`) + concrete monomorphic lens structures.

We adopt the **Agda existential** as the foundation, realized as the
**count-indexed traversal** (§4): the residual is specialized to a value-level
`Σ(n : Nat)`, which today's kernel supports directly, and which makes rebuild
total by length-matching — a guarantee Haskell/Idris cannot state.

## 3. Kernel constraints (verified against the tree)

- The kernel is **predicative** with a fixed hierarchy `Type 0 : Type 1 : Type 2`
  (ceiling 2), cumulative (`Type i <: Type i+1`) — **not** `Type : Type`
  (`term.ex:13,83`; `kernel.ex:8-9,583-590`; `universe.ex`).
- The built-in `Sigma(a: Type, b: (a) -> Type)` fixes its witness at **`Type 0`**
  (`builtins.ex:286`). A value-level `Σ(n : Nat)` (Sigma over `Nat`) and
  length-indexed `Vector(a, n)` are both present and proven
  (`lib/std/sigma.cure`, `lib/std/vector.cure`).
- Consequence: the *pure* coend `Σ(M : Type). …` quantifies the residual over the
  **universe** and would need a `Type 1` Sigma (surface syntax + a level-1
  instance) — deliberately **out of scope** here. Universe polymorphism is
  decoupled as its own future kernel initiative, not an `Std.Optic` prerequisite.
- **Records** are `rec Name / field: Type`, constructed `Name{field: v}`, compiled
  to BEAM maps. There is **no `{r with f: v}` update syntax**, so field-lens `set`
  reconstructs via `Name{…}` (drives the deriving decision in §5).
- **Large elimination** (a value-scrutinee `match` that *returns a `Type`*, i.e.
  `OpticKind → Type`) has **no precedent** in the stdlib or tests. It is the one
  feasibility risk and is gated by an early probe (§7, task 1).

## 4. Core representation

Monomorphic (type-preserving) in v1: `Optic(k, s, a)` focuses `a`-values inside
an `s` and puts back `a`-values. Type-changing optics (`s t a b`) are a clean
later extension; the old dynamic module was effectively monomorphic anyway.

The canonical optic is the count-indexed traversal (van-Laarhoven-free
"extract foci + total rebuild"), needing only a value-level `Σ(n : Nat)`:

```
extract : s → Σ(n: Nat). Vector(a, n) × (Vector(a, n) → s)
```

Rebuild is **total**: the replacement vector's length matches the extracted
length by construction.

### Kinds as a static index (approach 2A — the committed design)

The optic kinds form an ordered lattice `LensKind < AffineKind < TraversalKind`.
The kind is a **static index** on the optic, and a type-level **representation
selector** `FocusShape : OpticKind → Type → Type → Type` (a large elimination)
chooses the rep:

```
type OpticKind = LensKind() | AffineKind() | TraversalKind()

FocusShape(LensKind,      a, s) = Tuple(a, (a) -> s)                                    # exactly 1
FocusShape(AffineKind,    a, s) = Option(Tuple(a, (a) -> s))                            # 0 or 1
FocusShape(TraversalKind, a, s) = Sigma(n: Nat, Tuple(Vector(a, n), (Vector(a, n)) -> s))  # any n

type Optic(k: OpticKind, s: Type, a: Type) = MkOptic((s) -> FocusShape(k, a, s))
```

Users never write `OpticKind`/`FocusShape` directly — three **friendly aliases**
carry the kind, and these are what appear in signatures:

```
Lens(s, a)      = Optic(LensKind, s, a)
Affine(s, a)    = Optic(AffineKind, s, a)
Traversal(s, a) = Optic(TraversalKind, s, a)
```

The index **is** the kind: `view` is total on a `Lens` *by construction*, and
`compose` computes its result kind as the lattice join. This is approach **2A**.
There is **no fallback to separate concrete types** — if the probe (§7, task 1)
shows large elimination is unavailable, *enabling* it is the plan's job (large
elimination is standard in Idris, Agda, and Lean, so this is a real-language-
aligned TCB task with the full gate — not a reason to change the design).

## 5. The optic zoo, eliminators, composition

### Kind lattice
`join : OpticKind → OpticKind → OpticKind` — the max under
`LensKind < AffineKind < TraversalKind`.

### Eliminators (each total at its kind, dispatching on the static `k`)
- `view : Lens(s, a) → (s) → a` — **Lens-only, total.** No `Option`, no
  default — the concrete win over `get_in` returning `nil`.
- `preview : {k} → Optic(k, s, a) → (s) → Option(a)` — first focus, any kind.
- `to_list_of : {k} → Optic(k, s, a) → (s) → List(a)` — all foci.
- `over : {k} → Optic(k, s, a) → (a → a) → (s) → s` — modify every focus.
- `set : {k} → Optic(k, s, a) → a → (s) → s` — `over(o, fn(_) -> v)`.

### Composition (the workhorse)
```
compose : {k1} {k2} → Optic(k1, s, a) → Optic(k2, a, x) → Optic(join(k1,k2), s, x)
```
Result kind is the lattice join (so `Lens ∘ Traversal` is a `Traversal`
automatically). Traversal∘Traversal concatenates foci with `Vector (m+n)`
arithmetic — the hardest implementation piece; Cure's `Vector` already supports
the `n+m` concat/split it needs.

### Primitive optics (the accessor replacements)
| Old `Std.Access` | New `Std.Optic` | Kind |
|---|---|---|
| `elem_at(i)` (tuple) | `_1`, `_2`, … `_i` | Lens |
| record field | derived field lens | Lens |
| `key(k)` (map) | `key(k)` | Affine |
| `at(i)` (list) | `at(i)` | Affine |
| `all()` | `each` | Traversal |
| `filter(pred)` | `filtered(pred)` | Traversal |

### Record field lenses & deriving
Because there is no `{r with f: v}` syntax, a field lens's `set` reconstructs the
whole record via `Name{…}`. Per-record **deriving** (generate one lens per field)
is the ergonomic answer; the mechanism (`@derive(:optics)` on `rec`, or a macro)
is a planning decision. Manual `lens(get, set)` construction is always available.

### Surface composition — the dot-path operator `.`
The old runtime path list `[key(:a), all(), key(:b)]` becomes a typed composition
written with **`.`**, so optic paths read like native field access:

```
key(:langs).each.key(:name)        # == compose(compose(key(:langs), each), key(:name))
```

`.` is left-associative and binds tightest (it already does, as projection), so a
path is a single primary expression. `compose(o1, o2)` remains the underlying
function; `.` is surface sugar for it.

**Disambiguation is type-directed** — identical to how Cure already resolves
`.i`/`tproj` from the left operand's type (memory: `.i` via `tproj`, type-directed
projection). At the `{:dot, left, right}` node the elaborator inspects the
inferred head type of `left`:

- `left : Tuple` / `Sigma` and `right` a numeric literal → positional projection
  (`sigma_first` / `sigma_second` / `tproj_i`), unchanged.
- `left : rec` and `right` a bare field label → record field projection, unchanged.
- `left : Optic(k1, s, x)` → **composition**: `right` must elaborate to an
  `Optic(k2, x, y)`, yielding `Optic(join(k1,k2), s, y)`.

A value has exactly one type, so the three cases never overlap — a field named
`each` on a record still projects (left is a record, not an optic). Resolution
requires the left operand's head type to be known at the dot (the same
precondition `tproj` already imposes); a fully-unresolved metavariable left is a
deferred/elaboration error, as today.

**Parser change:** the right side of `.` must accept a general optic *expression*,
not only a bare label/index — `key(:langs).key(:name)` has a *call* (`key(:name)`)
after the dot, and `.each` / `._1` have bare optic identifiers. The postfix-`.`
rule is widened to parse `left . primary` (identifier, call, or numeric index),
producing the same `{:dot, …}` node the elaborator then resolves by type.

Note the tuple lenses are named `_1`, `_2`, … (underscore), never `.1`, so they
never collide with numeric projection: `t.1` projects, `_1` is the lens value.

### 5a. The escape hatch: `Std.Dynamic` (v1)

Optics compose only where leaf types line up, so genuinely heterogeneous data
(`%{langs: [...], count: 5, active: true}` — the old dynamic-map case) needs a
representation. The honest, well-typed stand-in for `Any` is a **standalone,
optic-agnostic** module — a single homogeneous tagged sum over Cure's real BEAM
value shapes:

```
# module Std.Dynamic — knows nothing about optics
type Dyn =
    DAtom(Atom)  | DInt(Int)   | DFloat(Float)
  | DStr(String) | DList(List(Dyn))
  | DTuple(List(Dyn)) | DMap(Map(Dyn, Dyn))
```

This is a **general stdlib citizen**, usable on its own by anyone who wants a
typed `Any` (pattern-match it directly); optics is only one consumer. The
dependency is strictly one-way: `Std.Optic` **imports** `Std.Dynamic`, never the
reverse.

Everything is a `Dyn`, so `Map(Dyn, Dyn)` typechecks and optics traverse it.
Narrowing to a concrete leaf is an **affine** (case optic) provided *by
`Std.Optic`*, never a cast — one per constructor:

```
dyn_atom  : Affine(Dyn, Atom)    dyn_int   : Affine(Dyn, Int)
dyn_float : Affine(Dyn, Float)   dyn_str   : Affine(Dyn, String)
dyn_list  : Affine(Dyn, List(Dyn))  dyn_tuple : Affine(Dyn, List(Dyn))
dyn_map   : Affine(Dyn, Map(Dyn, Dyn))
```

`preview(key(k).dyn_str, doc) : Option(String)` answers "is this a string?" with
an honest runtime tag match; the affine's `set` rebuilds via the ordinary
`DStr(_)` constructor (no Prism-*review* needed). These are ordinary Affines, so
they fit the existing `Lens < Affine < Traversal` lattice with no new kind.
`DMap`'s map is homogeneous (`Dyn` values), so `key`/`each` compose straight
through.

## 6. Migration from `Std.Access`

| Old | New |
|---|---|
| `fetch(c, k)` | `preview(key(k), c)` |
| `get(c, k, default)` | `Std.Option.unwrap(preview(key(k), c), default)` |
| `fetch_bang(c, k)` (raises) | **gone** — record-field lens `view` (total) or handle `preview`'s `Option` |
| `fetch_in(c, path)` | `preview(<composed>, c)` |
| `get_in(c, path)` | `Std.Option.unwrap(preview(<composed>, c), default)` |
| `put_in(c, path, v)` | `set(<composed>, v, c)` |
| `update_in(c, path, f)` | `over(<composed>, f, c)` |
| `get_and_update_in(c, path, f)` | `over` (+ optional `get_and_set` combinator) |
| `pop`, `pop_in` | **gone** — domain change, not a focus → `Std.Map.remove` |

Two principled drops: **raise-on-miss** (`fetch_bang`/`key_bang`) — static typing
replaces "crash if absent" with "prove presence (total `view`) or handle
`Option`"; and **`pop`** — removing a key changes a map's domain, which is a
container operation (`Std.Map`), not a lens.

Headline example:
```
# old:  update_in(data, [key(:langs), all(), key(:name)], upcase)
over(key(:langs).each.key(:name), Std.String.upcase, data)
```
Type-checks only when leaves line up (`data : Map(Atom, List(Map(Atom, String)))`
or a record equivalent) — the honest cost of dropping `Any`.

## 7. Testing & oracle plan

Layer **E** (elaborator) + `lib/std/optic.cure`; escalates to **K** only if task
1 demands it. Strict red-green, differential-oracle-driven, ghost-writer commits,
explicit-pathspec staging, one build at a time.

1. **Probe: large elimination.** Minimal paired `.cure`/`.idr` for
   `FocusShape : OpticKind → Type → Type → Type` returning distinct reps per kind plus a
   consumer. `mix cure.oracle`. Cure-rejects/Idris-accepts ⇒ enable large
   elimination (TCB gate, real-language-aligned) *before* the library. De-risks
   everything; it is task 1.
2. Kind lattice + `join` (pure).
3. `OpticKind` + `FocusShape` selector + `Optic` + `MkOptic` + friendly aliases
   (`Lens`/`Affine`/`Traversal`).
4. Lens primitives (`_i`, field lenses) + `view` / `set` / `over`.
5. Affine (`key`, `at`) + `preview`.
6. Traversal (`each`, `filtered`) + `to_list_of` + the `Vector (m+n)` rebuild.
7. `compose` + `join`-computed result kind — a test per kind pair.
8. **Dot-path `.` resolution** (P + E): widen the postfix-`.` parser to accept an
   optic expression on the right; type-directed elaboration routes `Optic`-headed
   `.` to `compose`. Collision tests: `t.1`/`r.field` projection still works; a
   `rec` field named `each` still projects; chained `key(:a).each.key(:b)`
   left-associates into nested `compose`; an unresolved-left metavariable errors
   as today.
9. Field-lens deriving for `rec`.
10. **`Std.Dynamic` (`Dyn` sum) + its case affines** (`dyn_str`/`dyn_int`/… in
    `Std.Optic`, importing `Std.Dynamic`) + a heterogeneous-document parity test
    (`preview`/`set`/`over` through a mixed `DMap`, replacing an old `Any`-map
    access). `Std.Dynamic` lands as its own module with direct pattern-match
    tests independent of optics.
11. Migration-parity tests + an oracle cluster mirroring `idris2-lens`
    view/set/over/compose behavior.
12. **Optic laws** as properties: lens get-put / put-get / put-put; traversal
    identity / composition. Antigen antibody **only** if the kernel is touched in
    task 1 (then: termination + no-distinct-NF-equated + full Antigen suite).

## 8. Scope boundaries (YAGNI)

- **In:** monomorphic Lens/Affine/Traversal, the primitives in §5, the dot-path
  `.` composition surface, the five eliminators, record field-lens deriving, and
  the standalone `Std.Dynamic` escape-hatch sum with its case affines (§5a).
- **Out (v1):** type-changing optics (`s t a b`); Prism-*review* (building a sum
  from a branch — the old module never did it); the pure `Σ(M:Type)` coend and
  universe polymorphism (own initiative); `pop`/domain-changing operations.

## 9. Open questions for planning

1. **Large elimination** — available, or must the plan enable it (and at what
   layer: elaborator-only, or kernel)? Task 1 answers this and sets the risk.
2. **Deriving mechanism** for record field lenses: `@derive(:optics)` decorator
   vs macro vs manual-only for v1.

**Decided during brainstorming:**
- Composition surface is the dot-path operator `.` (type-directed, §5) — not a
  new glyph or `pathN` helper.
- The escape hatch ships in v1 as a standalone `Std.Dynamic` module (`Dyn` over
  BEAM value shapes), optic-agnostic, with case affines living in `Std.Optic`
  (§5a).

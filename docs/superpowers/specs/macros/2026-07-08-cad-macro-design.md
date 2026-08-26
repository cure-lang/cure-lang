# `cad` — Typed Solid Modeling as Code

**Date:** 2026-07-08
**Status:** design (operator-requested; sketched from a Cadova comparison).
Child of [`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
— it extends the parent's **beyond-the-MCU** reach (§7) into *fabrication*.
Built as a `macro` (see [`2026-07-08-macro-facility-design.md`](2026-07-08-macro-facility-design.md));
consumes [`units`](2026-07-08-units-macro-design.md) (`Length`). Prior art:
Cadova (`~/3DModelling/Cadova`), SwiftSCAD, OpenSCAD, CadQuery.

---

## 1. Purpose

Describe a 3D solid — for printing or fabrication — as an ordinary Cure
value: primitive shapes, transforms, and boolean combinations, composed in a
declarative block. Everything a code-CAD library gives you (versionable,
parametric, reusable models), plus two things every existing code-CAD tool
can only *approximate*: **2D-vs-3D correctness** and **unit correctness**
enforced by the type system rather than by phantom types and bare `Double`s,
and — the fabrication payoff — **statically-known printability constraints**
(minimum wall, minimum feature, sane radii) checked before a single triangle
is generated.

This is a **host-side** macro. Boolean/mesh evaluation runs a real geometry
kernel (Manifold-class) reached by `@extern` on desktop BEAM, exactly as
Cadova reaches Manifold-Swift; the output is a mesh/3MF artifact. CSG on a
$3 microcontroller is a non-goal (§9) — `cad` is Cure being *a BEAM language
where libraries are languages*, not an MCU feature.

## 2. The design decision — no result builders

The reference library (Cadova) leans on two Swift mechanisms `cad` must
*not* copy, because Cure doesn't have the problems they solve:

**Result builders go away.** Cadova's `GeometryBuilder` is a six-hook result
builder (`buildBlock`/`buildExpression`/`buildOptional`/`buildEither`/
`buildArray`/`buildFinalResult`) whose entire job is to reify a *statement*
block — including its `if`/`for`/`switch` — back into a value. Cure geometry
**is** a value and a block of geometry **is** an expression, so:

- `buildBlock` (union adjacent children) → a `<children: Shape3D>...`
  repetition hole closed by `computed by union` — the fold *is* `buildBlock`,
  but total and type-directed instead of an untyped overload set.
- `buildFinalResult` (one child → itself, else `Union`) → the tail of that
  same fold.
- `buildExpression`'s `Sequence` overload → the one piece worth keeping: the
  repetition hole must **splice a computed `List(Shape)`**, so a `for`
  comprehension can appear among literal children.
- `buildOptional` / `buildEither` / `buildArray` → **deleted entirely.**
  These exist only because Swift `if`/`for` are statements needing
  reification. In Cure they are value expressions; a comprehension yielding
  `List(Shape3D)` needs no reification. A third of the builder protocol
  vanishes with the disease it treated.

**Phantom dimensionality becomes a real index.** Cadova carries 2D-vs-3D as a
phantom `D2`/`D3` type parameter on `Geometry<D>`, paying for it with a whole
`Dimensionality` protocol and a dozen associated types — the canonical
"phantom type faking a dependent index" this initiative exists to retire.
In `cad`, dimensionality is a genuine index (§4): `Shape2D = Shape(2)`,
`Shape3D = Shape(3)`, and `extruded : Shape(2) -> Shape(3)` is a typed
transition the kernel checks. One index does what Cadova needs an entire
protocol to approximate.

So `computed by` on a repetition hole *is* the generalization of a result
builder: the same "decide how adjacent children combine" freedom, total and
elaboration-checked. Nothing else in the facility is needed.

## 3. User surface

The Cadova hex-key holder, in `cad`:

```cure
model HexKeyHolder
  ## A rack of hex-key holes cut from a rounded slab.

  let height  = 20mm
  let spacing = 8mm

  stack along x, spacing spacing
    for size in 1.5mm to 5.0mm step 0.5mm
      hexagon across size          # a computed List(Shape2D) splices in

  measuring bounds as holes, size
    stadium (size + spacing * 2)
      extruded height
      subtracting
        holes aligned centerx
          extruded height
          moved up 2mm
```

Reads top to bottom: build the holes, measure them, cut them from a slab.
Rules:

- **`model Name`** is the container — one exported solid, the fabrication
  analogue of `board`'s module. It elaborates to a value of type
  `Shape(3)` plus a `cure cad export` entry point (§4); no `start/0`, no
  boilerplate.
- **Primitive shapes** are constructors with **refined** parameters:
  `circle radius <r>`, `rectangle <w> by <h>`, `hexagon across <d>`,
  `box`, `sphere radius <r>`, `cylinder radius <r> height <h>`. Radii,
  side counts, and extents are refinement-checked at the literal (§4) — a
  zero-radius sphere fails before it exists.
- **Transforms and combinators are ordinary functions** returning a shape:
  `moved`, `rotated`, `scaled`, `extruded`, `subtracting { … }`,
  `union { … }`, `intersecting { … }`. Chained by indentation, not by a
  builder. `subtracting`/`union`/`intersecting` take a `Block` hole; nothing
  about them is special-cased.
- **All lengths are `Length`** (the units macro). A bare `20` where a
  length is meant is E280 — the units front door, reused wholesale.
- **`for … in <lo> to <hi> step <s>`** is a comprehension whose body is a
  `Shape`, producing a `List(Shape)` that splices into the enclosing
  block. No `buildArray`; ordinary value-level iteration.
- **`measuring bounds as <names> … <body>`** is a scoped feedback binding —
  it names the accumulated shape's bounding box and feeds it into the body.
  This is `becomes`-a-`let`, not builder magic (§4).

Surface idiom (shape names, `to`/`step`, `aligned centerx`) is
operator-reviewed for practitioner fidelity per the corpus's surface-idiom
rule — a CAD user reads it cold and notices nothing foreign. The exact
spelling of the modifier vocabulary is ledgered (§8.1), not load-bearing
here.

## 4. Author surface — how `cad` is defined as a macro

`cad` is library code. The load-bearing rules, in the §2 meta-grammar
notation (examples with holes):

```cure
macro Cad
  ## Solid modeling: shapes, transforms, boolean combinations.

  # primitives — refinements ride on the hole
  syntax circle radius <r: Length where r > 0mm>                   is Shape2D
  syntax hexagon across <d: Length where d > 0mm>                  is Shape2D
  syntax rectangle <w: Length> by <h: Length>                      is Shape2D
  syntax box <w: Length> by <d: Length> by <h: Length>             is Shape3D
  syntax sphere radius <r: Length where r > 0mm>                   is Shape3D
  syntax cylinder radius <r: Length> height <h: Length>            is Shape3D

  # 2D -> 3D transition, checked by the index
  syntax <s: Shape2D> extruded <h: Length where h > 0mm>
    becomes Cad.extrude(<s>, <h>)                                  is Shape3D

  # composition — the "result builder", replaced by one fold
  syntax union
    <children: Shape>...
    computed by cad_union                                          is Shape

  syntax <s: Shape> subtracting
    <cuts: Shape>...
    computed by cad_subtract

  # scoped feedback binding — becomes-a-let, no builder
  syntax measuring bounds as <box: name>
    <body: Block>
    becomes let <box> = Cad.bounds(<self>) in <body>
```

- `cad_union` receives the parsed `List(Shape)` and folds it into one shape;
  `<children: Shape>...` accepts **literal children and a spliced computed
  `List(Shape)` alike** — the one capability salvaged from Cadova's
  `buildExpression`. If the list is empty, the fold raises E281 with an
  explainer, not a parse error (the "at-least-one is an elab check" rule from
  the facility §2).
- `extruded` is the whole 2D→3D story: its rule takes `Shape2D`, yields
  `Shape3D`. A `box` piped into `extruded` fails to parse the hole — you
  cannot extrude a solid — and the default typed-hole error says exactly
  that.
- The refinements (`r > 0mm`, `sides >= 3`) are refinement-typed holes
  (facility §2), so a degenerate primitive fails **at the literal**, the same
  mechanism `units` uses for `120pct`.

## 5. Invisible machinery

- **Dimensionality is one index.** `Shape(d)` with `d ∈ {2,3}` — the landed
  `Bounded`-style native builtin. `extrude` is the sole `2 → 3` introduction;
  boolean ops demand `Shape(d)` on both sides by unification, so
  `circle …` unioned with `box …` is a domain error naming the dimensions,
  never a unifier dump. This *replaces* Cadova's `Dimensionality` protocol +
  associated-type tax with a single index, and it **erases**: at runtime a
  shape is just its kernel handle; the index is gone.
- **Lengths reuse `units`.** Every extent is a `Length` over units' mm-backed
  Int carrier; `20mm + 3mm` is ordinary same-unit arithmetic, `20mm * 2` is
  scalar-times-unit, and no bare number ever reaches a shape constructor.
  The `cad × units` seam is machine-authored (composition spec) — the user
  sees only "lengths, in mm."
- **Static wins are honestly bounded.** Three classes of property are
  compile-time and erase; the rest are backend invariants or run/check-time:
  - *Static (real dependent-type dividend):* dimensionality; unit
    consistency; **constructor-parameter refinements** (radius > 0, side
    count ≥ 3, non-negative extents); and **printability refinements when the
    dimensions are statically known** — minimum wall thickness vs. nozzle
    (`{ w: Length | w >= nozzle }`), minimum feature size, extrusion height >
    0. This last is the flagship "beyond Cadova" payoff: a slab wall thinner
    than your nozzle is a *compile error*, not a failed print.
  - *Backend invariant (free, not our check):* manifoldness /
    watertightness. A Manifold-class kernel *maintains* these by construction
    across boolean ops, so `cad` inherits them rather than proving them — and
    says so, rather than claiming a static guarantee it doesn't author.
  - *Run/check-time (honestly not static):* empty-result-after-subtraction
    when overlap isn't statically decidable; self-intersecting sweeps/twists;
    non-planar polygons from computed points. These surface as `check`
    properties (§6) and runtime diagnostics, never as false compile-time
    promises.
- **`measuring bounds` = a `let`.** `Cad.bounds(shape)` is a pure function
  from a shape to its `BoundingBox` (a record of `Length`s); the rule binds
  its result and substitutes it into the body. The "feedback" is ordinary
  data flow — the accumulated shape is in scope, its bounds are a function of
  it, the body is an expression over both.
- **Environment threading is the one genuinely open piece.** Cadova threads
  an implicit `EnvironmentValues` (facet count / segmentation, tolerance,
  material, corner-rounding) down the tree, SwiftUI-style. That is *not* a
  builder concern and does not evaporate. v1 position: a single `with`
  modifier that sets a reader for its sub-block
  (`with facets 64 { … }`), lowering to an explicit reader parameter thread —
  the same problem `reducer`/`flow` face. Ambient-context as a first-class
  facility feature is ledgered (§8.2), not assumed.
- **Evaluation is host-side FFI.** `Cad.union`/`extrude`/`subtract` are
  `@extern` calls into the geometry kernel (Manifold-class) on desktop BEAM;
  `model` exports 3MF/STL. The macro is the typed, checked *surface*; the
  triangle-crunching is a native port, exactly as in every code-CAD tool.

## 6. Error explainers (E280–E289)

Registered per the parent's fixed template (*what you wrote → why forbidden →
what to write instead*):

```
error[E280]: box needs a length, got a bare number
  --> holder.cure:6
   |
 6 |   box 40 by 20 by height
   |       ^^
  40 of what? Every dimension is a length: box 40mm by 20mm by height.
```

```
error[E282]: you can't extrude a solid
  --> holder.cure:11
   |
11 |   sphere radius 5mm
   |     extruded 3mm
   |     ^^^^^^^^
  extruded turns a flat shape into a solid (a circle into a cylinder).
  A sphere is already 3D. Did you mean to `scale` or `move` it?
```

```
error[E283]: this wall is thinner than your nozzle
  --> case.cure:14
   |
14 |   shell thickness 0.2mm
   |                   ^^^^^^
  Your printer profile has a 0.4mm nozzle; a 0.2mm wall won't print as a
  solid. Use at least 0.4mm (one perimeter), or 0.8mm for two.
```

E280 reuses units' E115 shape; E282 is the dimensionality index refusing the
`extruded` hole; E283 fires at the literal against the profile's nozzle
refinement. Others in the family: E281 (empty `union` block), E284
(non-positive radius/extent), E285 (`for` range with `lo >= hi`), E286
(subtraction proven to remove nothing — the whole cut misses the body,
statically decidable case only).

## 7. `check` integration (shipped templates)

- **Round-trip / determinism** — the same `model` params produce the same
  mesh hash; a pure model is reproducible, and `check` pins it.
- **Printability props** — over a `model`'s exposed parameters: no wall below
  nozzle, no unsupported overhang beyond a profile angle, bounding box within
  bed volume. Where dimensions are literals these discharge statically
  ("proved by construction — 0 runs"); where they're parametric, `check`
  generates within the refinements (the units carrier gives the generators
  for free).
- **Non-empty result** — the run/check-time half of §5: a subtraction or
  intersection that empties the model is caught by a shipped property rather
  than silently exporting a void.

## 8. Open decisions (ledger)

1. **Modifier vocabulary & surface idiom** — the exact spelling of
   transforms/combinators (`moved up 2mm` vs `translated z 2mm`;
   `aligned centerx` vs `centered on x`; `stack along x` vs `Stack(.x)`).
   Operator-reviewed for practitioner fidelity; not load-bearing for the
   architecture, so deferred to implementation with real CAD users.
2. **Environment / ambient context** (§5) — `with facets 64 { … }`
   reader-threading (v1) vs. a first-class ambient-context feature in the
   macro facility that `reducer`/`flow`/`cad` all share. The facility
   feature is the right long-term home; ship the local `with` first.
3. **Which geometry kernel, and the FFI boundary** — Manifold (Cadova's
   choice, maintains manifoldness) vs. alternatives; how a native port is
   packaged with desktop-BEAM Cure; whether host-only is acceptable or a
   pure-BEAM fallback kernel is ever wanted (probably not — §9).
4. **Printer-profile source** — where the nozzle/bed/overhang facts that
   power E283 live: a `profile` declaration in the model, a project-level
   config (the `config` macro), or slicer-file import. Leaning: a
   `profile` block that is itself a tiny macro, so the refinements have a
   typed source.
5. **2D vs 3D unification detail** — whether `Shape` (dimension-polymorphic)
   is a legal user-facing type for helpers, or dimension must always be
   concrete at a `model` boundary. Recommendation: allow polymorphic helper
   `fn`s, force concreteness at `model` export.
6. **Sweeps, lofts, revolves** — the richer 2D→3D constructors beyond
   `extrude` (twist, path-sweep, revolve). Each is another typed
   `Shape2D → Shape3D` rule; their *self-intersection* checks are run-time
   (§5), so they land after the core with their `check` props.
7. **`measuring` beyond bounds** — volume, centroid, mass (for a material) as
   further scoped feedback bindings; same `becomes`-a-`let` mechanism, more
   `Cad.*` pure measurements.

## 9. Non-goals

- **No CSG on the microcontroller** — `cad` is host-side; AtomVM/ESP32 do not
  run a geometry kernel. The parent's target-honesty rule (§1) applies: a
  macro cannot make a $3 chip a CAD workstation. (A *board* can consume a
  `cad`-exported STL as a fabrication artifact; it does not evaluate it.)
- **No claim of static manifoldness** — that is a backend invariant `cad`
  inherits, not a theorem it proves (§5). We do not counterfeit a guarantee
  the kernel authors.
- **No dimensional algebra** — lengths are additive (units' §2 decision);
  areas/volumes are named measurements (`Cad.bounds`, §8.7), not `Length *
  Length` derived dimensions.
- **No result builders** (§2) — reproducing them would import Swift's
  accidental complexity without the reason for it.
- **Not a parametric-constraint solver / not a mesh editor** — `cad`
  describes solids by construction (CSG + transforms), the OpenSCAD/Cadova
  lineage; it is not FreeCAD's sketch-constraint solver and does not edit
  imported meshes vertex-by-vertex.

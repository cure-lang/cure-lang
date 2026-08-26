# Stdlib Design Specs — Master

**Date:** 2026-07-21

Scope: condensed authority for standard-library-driven language/library designs under this folder. Current designs include **`Std.Optic`**, the clean replacement of `Std.Regex` with a dependently typed TyRE parser, and **`Std.Versioned`** for gapless, support-windowed evolution.

## Motivation and replacement mandate

`Std.Access` (Elixir-style `get_in`/`put_in`/`update_in` over heterogeneous data) only elaborated via an opaque `Any` + `believe_me` casts dispatching on runtime tags — it bypassed the type system and was deleted. `Std.Optic` is the replacement with **zero `believe_me`**: whole-type and part-type genuinely connected at compile time.

Must keep from the old module: (1) deep update without hand-rebuilding; (2) composable first-class paths with fan-out (`all`/`filter`). What changes (a feature): optics compose only where leaf types line up. Primary targets: records (total lenses), homogeneous collections (`List`/`Vector`/`Map(K,V)` → traversals/affines), and `Std.Dynamic` for genuinely mixed data — matched, never cast.

## Prior art → chosen foundation (locked)

- Idris 2 profunctor/van Laarhoven optics need rank-2 polymorphism — not adopted.
- **Agda existential/coend encoding adopted**: `Optic S T A B = Σ M. (S → M×A) × (M×B → T)`, specialized to a value-level `Σ(n : Nat)` — the **count-indexed traversal** — which today's kernel supports directly and makes rebuild total by length-matching (a guarantee Haskell/Idris cannot state).
- Lean 4: no canonical library; native record update only.

## Kernel constraints (verified)

- Kernel is predicative, hierarchy `Type 0 : Type 1 : Type 2` (ceiling 2), cumulative — not `Type : Type`. Built-in `Sigma` fixes its witness at `Type 0`.
- Consequence: the pure coend `Σ(M : Type)` would need a `Type 1` Sigma — **out of scope**; universe polymorphism is its own future kernel initiative, not an `Std.Optic` prerequisite.
- Records (`rec`) compile to BEAM maps; there is **no `{r with f: v}` update syntax**, so field-lens `set` reconstructs via `Name{…}` — this drives the deriving decision.
- **Large elimination** (value-scrutinee `match` returning a `Type`, i.e. `FocusShape : OpticKind → Type → Type → Type`) had no stdlib precedent — the one feasibility risk, gated by the plan's task 1 probe.

## Core representation (approach 2A — committed)

Monomorphic (type-preserving) in v1: `Optic(k, s, a)`. Canonical form: count-indexed traversal, `extract : s → Σ(n: Nat). Vector(a, n) × (Vector(a, n) → s)` — rebuild is **total** by construction.

Kinds form an ordered lattice `LensKind < AffineKind < TraversalKind`; the kind is a **static index** and `FocusShape` (a large elimination) selects the representation per kind:

```
FocusShape(LensKind,      a, s) = Tuple(a, (a) -> s)                       # exactly 1
FocusShape(AffineKind,    a, s) = Option(Tuple(a, (a) -> s))               # 0 or 1
FocusShape(TraversalKind, a, s) = Sigma(n: Nat, Tuple(Vector(a,n), (Vector(a,n)) -> s))
type Optic(k: OpticKind, s: Type, a: Type) = MkOptic((s) -> FocusShape(k, a, s))
```

Friendly aliases carry the kind in signatures: `Lens(s,a)` / `Affine(s,a)` / `Traversal(s,a)`. The index **is** the kind: `view` is total on a `Lens` by construction; `compose` computes its result kind as the lattice join. **No fallback to separate concrete types** — if large elimination is unavailable, enabling it is the plan's job (standard in Idris/Agda/Lean → real-language-aligned TCB task, full gate), not a reason to change the design.

## Zoo, eliminators, composition

- `join : OpticKind → OpticKind → OpticKind` — max under the lattice.
- Eliminators (each total at its kind): `view` (**Lens-only, total** — no `Option`, no default; the concrete win over `get_in`-returns-`nil`), `preview` (first focus, any kind), `to_list_of`, `over`, `set`.
- `compose : Optic(k1,s,a) → Optic(k2,a,x) → Optic(join(k1,k2), s, x)`. Traversal∘Traversal concatenates foci with `Vector (m+n)` arithmetic — hardest piece; Cure's `Vector` already supports it.
- Primitives (Access replacements): tuple lenses `_1`, `_2`, … (Lens); derived record field lenses (Lens); `key(k)` map affine; `at(i)` list affine; `each` traversal (was `all()`); `filtered(pred)` traversal.
- Record field lenses: `set` reconstructs via `Name{…}`; per-record **deriving** (one lens per field) is the ergonomic answer — mechanism (`@derive(:optics)` vs macro vs manual-only) is an open planning decision. Manual `lens(get, set)` always available.

## Dot-path composition surface (decided)

Composition is written with **`.`** (not a new glyph or `pathN` helper): `key(:langs).each.key(:name)` ≡ nested `compose`. `.` is left-associative, binds tightest; `compose` remains the underlying function. Disambiguation is **type-directed** at the `{:dot, left, right}` node, exactly like existing `.i`/`tproj`:

- left `Tuple`/`Sigma` + numeric literal → positional projection (unchanged);
- left `rec` + bare field label → record field projection (unchanged);
- left `Optic(k1,s,x)` → composition; right must elaborate to `Optic(k2,x,y)` yielding `Optic(join(k1,k2), s, y)`.

A value has one type so the cases never overlap (a record field named `each` still projects). Unresolved-metavariable left is a deferred/elaboration error, as today. Parser change: postfix-`.` widened to `left . primary` (identifier, call, or numeric index). Tuple lenses are `_1`, `_2`, … — never `.1` — so they cannot collide with numeric projection.

## `Std.Dynamic` escape hatch (v1, decided)

Standalone, **optic-agnostic** module — the honest typed `Any`: a single tagged sum over BEAM value shapes:

```
type Dyn = DAtom(Atom) | DInt(Int) | DFloat(Float) | DStr(String)
         | DList(List(Dyn)) | DTuple(List(Dyn)) | DMap(Map(Dyn, Dyn))
```

General stdlib citizen, pattern-matchable directly; dependency strictly one-way (`Std.Optic` imports `Std.Dynamic`, never the reverse). Narrowing to a leaf is an **Affine** case optic per constructor (`dyn_int`, `dyn_str`, …) provided by `Std.Optic` — never a cast; `set` rebuilds via the ordinary constructor (no Prism-review needed), fitting the existing lattice with no new kind. `DMap` is homogeneous in `Dyn`, so `key`/`each` compose straight through.

## Migration from `Std.Access`

`fetch` → `preview(key(k), _)`; `get`+default → `Option.unwrap(preview(...), default)`; `fetch_in`/`get_in` → `preview` over a composed path; `put_in` → `set`; `update_in` → `over`. Two **principled drops**: raise-on-miss (`fetch_bang`) — replaced by proving presence (total `view`) or handling `Option`; and `pop`/`pop_in` — removing a key changes the map's domain, a container operation (`Std.Map.remove`), not a lens.

## Testing / oracle plan (summary)

Layer E + `lib/std/optic.cure`; escalates to K only if the large-elimination probe demands it. Task 1 = paired `.cure`/`.idr` probe of `FocusShape` via `mix cure.oracle` — de-risks everything. Then: lattice+`join`; core types; Lens primitives; Affines; Traversals (`Vector (m+n)` rebuild); `compose` per kind pair; dot-path resolution with projection-collision tests; field-lens deriving; `Std.Dynamic` + case affines + heterogeneous-document parity; migration-parity + idris2-lens oracle cluster; optic laws as properties (get-put/put-get/put-put; traversal identity/composition). Antigen antibody only if the kernel is touched.

## Scope boundaries (YAGNI)

- **In (v1):** monomorphic Lens/Affine/Traversal, the primitives above, dot-path `.` surface, five eliminators, record field-lens deriving, standalone `Std.Dynamic` with case affines.
- **Out (v1):** type-changing optics (`s t a b`); Prism-*review*; the pure `Σ(M:Type)` coend / universe polymorphism (own initiative); `pop`/domain-changing operations.

## Open questions

1. Large elimination: available or to be enabled, and at what layer (elaborator vs kernel) — answered by task 1.
2. Field-lens deriving mechanism: `@derive(:optics)` vs macro vs manual-only for v1.

## Source specs

- `2026-08-02-stdlib-versioned-lineage-design.md` — opaque Nat-indexed release lineages, optional labels, exhaustive historical decisions, and a non-shrinking support window whose minimum requires simultaneous support for the current and previous versions.
- `2026-07-11-std-optic-design.md` — full `Std.Optic` design: motivation, prior art, kernel constraints, 2A kind-indexed representation, dot-path surface, `Std.Dynamic`, migration table, test/oracle plan.
- `2026-07-21-dependently-typed-regex-design.md` — breaking replacement of the current unindexed recursive matcher with shape-indexed TyRE, compile-time literals, Thompson NFA, evidence VM, proofs, typed extraction, properties, and ordered implementation phases.

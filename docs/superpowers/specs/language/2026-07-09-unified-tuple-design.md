# Unified Tuple — one `%[…]` over a flat BEAM tuple, dependent or not

**Date:** 2026-07-09
**Status:** design (brainstormed + representability-probed against the merged
`feature/idris-parity` compiler; implementation plan not yet written)
**Depends on:** the landed Sigma-retirement (`2026-07-09-sigma-retirement-design.md`,
`@builtin(:sigma)` inductive, `%[x,y]`→`mk_pair`, `.1`/`.2`→`element/2`).
**Supersedes in part:** `lib/std/pair.cure` (the untyped `Tuple`/`element(…)->T`
façade this replaces).

---

## 1. Purpose & positioning

`Std.Pair` predates real dependent types. Its helpers are typed against an
**undefined opaque `Tuple`** with an untyped escape hatch (`lib/std/pair.cure:26`,
`fn element(index: Int, tuple: Tuple) -> T` — `T` is a free variable used as
`Any`). Every operation (`first`/`second`/`swap`/`map_first`) is positional access
wearing a signature that asserts nothing. Now that Cure has a real dependent
kernel, that façade is the one honestly-untyped corner of the value surface.

This spec replaces it with **one surface tuple type**, `Tuple`, that:

- keeps the value syntax **`%[…]` for every arity and for both dependent and
  non-dependent tuples** — the user never picks a spelling;
- is backed by the **native flat BEAM tuple** (`{a,b,c}`, O(1) `element/i`) — no
  nesting, no boxing;
- is **honestly typed**, including genuine cross-position value dependency; and
- offers an **arity-generic API** (`get`/`map`/`to_list`/`swap`) that is available
  exactly where it is sound, gated structurally rather than by a side condition.

It adds **no new trusted-kernel surface**: the kernel only ever sees the binary
Sigma it already has.

## 2. Background: what Idris/Agda do, and Cure's fork

Neither Idris nor Agda has a native n-ary tuple. Tuples are **right-nested pairs**
(`(a,b,c)` = `(a,(b,c))`); the *one* primitive is the dependent pair (Σ / `DPair`),
and the non-dependent pair is its degenerate case (`A × B := Σ A (λ_. B)`). Arity-
generic operation lives in `HVect (Vect n Type)`. Idris keeps two visible
spellings — `,` (non-dependent) and `**` (dependent) — precisely because in
synthesis it cannot tell which packaging you want.

Cure has a primitive those languages lack: a **flat n-ary BEAM tuple** with O(1)
`element/i`. Faithfully nesting would surrender that VM primitive (extra boxing,
O(n) projection) on the exact constrained target — ESP32/AtomVM — we care about,
for zero type-theoretic gain. So we deviate from the nesting convention, using the
reference languages' own building blocks (an `HVect`-style non-dependent product, a
telescope for the dependent case, an erased inhabitation witness to gate). Per the
autonomous parity directive: faithfulness-by-nesting buys nothing here, so we don't
pay for it.

## 3. The design (locked decisions)

### 3.1 One surface `Tuple`; `%[…]` for both

- **Value syntax:** `%[a, b, c]` at every arity, for dependent and non-dependent
  tuples alike. `.1 … .n` project; `%[p1, …, pn]` patterns match.
- **Type syntax:** `Tuple(…)`, a telescope where each position may optionally bind
  a name that later positions reference — generalizing the landed `Sigma(x: T, U)`
  surface to n-ary:
  - **Non-dependent:** `Tuple(Nat, Vector(Int, n))` — bare types, no binder
    introduced by the tuple type (`n` here is an *outer* variable).
  - **Dependent:** `Tuple(m: Nat, Vector(Int, m))` — the tuple type binds `m`, and
    a later position names it.

There is no `,`-vs-`**` choice at the value site. The **mode** disambiguates
(§3.2).

### 3.2 Bidirectional mode disambiguation

- **Synthesis (no expected type) ⇒ always non-dependent.** In a flat literal,
  element *k*'s synthesized type can only mention variables already in scope, never
  a projection of the tuple being built — so the non-dependent (all-`Ext`, §3.5)
  shape is always available and is what synthesis picks. Synthesis is **never
  forced** into a dependent shape.
- **Checking against a dependent `Tuple(…)` type ⇒ dependent.** When `%[n, vec]` is
  checked against `Tuple(m: Nat, Vector(Int, m))` — a declared return, a field
  type, or an annotation — the elaborator substitutes element-1's value into
  element-2's expected type (`Vector(Int, m)[m := n]`), exactly the landed arity-2
  checked-Sigma path (`elaborator.ex` checked `%[a,b]` clause) generalized up the
  telescope.
- **Patterns and projections inherit the shape** from the scrutinee's type.

**Consequence (the one caveat, = Idris's):** a bare `let p = %[n, vec]` in
synthesis position is non-dependent; annotate the `let` (or let a downstream use
drive it) if you need it dependent. This is the price of a single value syntax, and
it is no worse than the parts Idris would force you to spell `**`.

### 3.3 Surface `Sigma` retired to internal

`Sigma` is the length-2 telescope. Once `Tuple(…)` exists, a distinct surface
`Sigma` is redundant. It is **not** a subtype of the telescope — it is the length-2
*instance*, and the non-dependent `Tuple` is the all-`Ext` *restriction*; no
subtyping is introduced. `@builtin(:sigma)` and its machinery remain as the
**internal checking target** (§3.4); `Sigma(x: T, U)` as *surface* is deprecated in
favor of `Tuple(x: T, U)` via the existing migration facility (warn-now,
error-later), never a silent break.

### 3.4 Flat representation always; the telescope is a typing scaffold

Dependency is a compile-time phenomenon and types are erased, so the runtime
representation is **flat for both dependent and non-dependent tuples**:

- **Check** a `Tuple(shape)` by unfolding `shape` to right-nested binary Sigma and
  handing *that* to the kernel — reusing the landed, proven Sigma machinery. A
  dependent position becomes a dependent Sigma; a non-dependent position becomes a
  non-dependent one.
- **Emit** a flat BEAM tuple `{a, b, c}`, and lower telescope-index *i* to
  `element(i, t)` — even though the checked type was nested. This is the landed
  arity-2 emit hook (`mk_pair`→bare 2-tuple, `.1`/`.2`→`element/2`) generalized to
  arity *n*.

The nested Sigma never reaches runtime; `Tuple(shape)` is a **shape-indexed façade
whose kernel meaning is the nested-Sigma unfolding of `shape`**. This delivers
flat-and-dependent tuples with **zero new TCB** — the kernel keeps checking only
binary Sigma.

### 3.5 The `Tele` index and structural API gating

Index `Tuple` by a telescope inductive whose dependent and non-dependent extensions
are **distinct constructors** — making "non-dependent" a structural, decidable fact
rather than a predicate over occurrence:

```cure
type Tele indices ()
  Empty : Tele
  Ext   : Type -> Tele -> Tele          # non-dependent step
  Dep   : (A: Type) -> (A -> Tele) -> Tele   # dependent step (tail under a binder)
```

`%[1,"two",3.0]` infers `Ext(Int, Ext(String, Ext(Float, Empty)))`;
`%[n, vec]` checked dependent infers `Dep(Nat, λn. Ext(Vector(Int,n), Empty))`.
The `shape` is inferred at formation (elaborate each element in the running
context; `Ext` when the fresh binder is unused, `Dep` when used — the occurrence
check erasure already performs) and is **`{0}`-erased** (never a runtime value —
§7, and confirmed by the representability probe P5).

**Gating the arity-generic API** — two cases, both clean:

- **Fixed-arity ops** (`swap`, specific projections) bake an all-`Ext` skeleton
  into their signature, so a dependent tuple is a **direct `Dep`-vs-`Ext`
  constructor clash** at unification:

  ```cure
  fn swap({A: Type}, {B: Type}, t: Tuple(Ext(A, Ext(B, Empty))))
       -> Tuple(Ext(B, Ext(A, Empty))) = %[t.2, t.1]
  ```

- **Arity-generic ops** (`map`/`to_list`/`reverse`, quantified over an unknown
  `shape`) take an **erased non-dependence witness** whose inductive is uninhabited
  at `Dep`:

  ```cure
  type NonDep indices (shape: Tele)
    NDEmpty : NonDep(Empty)
    NDExt   : NonDep(rest) -> NonDep(Ext(A, rest))
    # no clause at Dep — structurally uninhabited there

  fn reverse({shape: Tele}, {0} nd: NonDep(shape), t: Tuple(shape))
       -> Tuple(rev_tele(shape)) = …
  ```

  At a use site `shape` is a concrete `Tele`, so solving `NonDep(shape)` is a
  **decidable structural walk** (peel `Ext`s; fail at `Dep`) — not general proof
  search. Non-dependent ⇒ witness found, erased, zero runtime; dependent ⇒
  uninhabited ⇒ a clean *"no `NonDep` for this tuple; position k is dependent"*.

  **Dead-end avoided (recorded so it isn't re-attempted):** do NOT gate by indexing
  through `Tuple(embed(ts))` for `embed : List(Type) -> Tele`. `embed(?ts)` is a
  stuck neutral, not a constructor, so unifying it against `Dep(…)` strands `?ts`
  ("cannot infer `?ts`") instead of clashing — the murky error the witness avoids.

`get(i)` / projection / `match` need **no** witness — they are total on every shape.
`map_at(i, f)` wants a finer `IndepAt(shape, i)` (uninhabited only if a `Dep` sits
at or before *i*); v1 gates `map_at` on full `NonDep` and ledgers `IndepAt`.

### 3.6 The remaining fork: one type (chosen) vs two (fallback)

The design commits to **(i) one surface `Tuple`** with the shape inferred and
`Sigma`/telescope internal-only — the mechanism in §3.5 makes it achievable and the
gate is a clean inhabitation/clash rather than a side condition. If formation-time
shape inference proves too subtle in implementation, the **fallback is (ii)** two
surface types — `Tuple(ts: List(Type))` (non-dependent, full API) + `Telescope`
(dependent, escape hatch) — each with a total, obvious API. (ii) is what Idris does
by keeping `,`/`**` distinct. This fork is resolved in the implementation plan, not
re-opened in design.

## 4. Worked example (`%[n, vec]`, both readings)

```cure
type Nat = Zero | Suc(Nat)
type Vector(a: Type) indices (n: Nat)
  empty   : Vector(a, Zero)
  prepend : a -> Vector(a, n) -> Vector(a, Suc(n))
```

**Non-dependent (synthesis).** `let p = %[n, vec]` with no expected type ⇒
`shape = Ext(Nat, Ext(Vector(Int,n), Empty))` (`n` free). `p.1 : Nat`,
`p.2 : Vector(Int,n)`; `swap(p) : Tuple(Ext(Vector(Int,n), Ext(Nat, Empty)))`
= `%[vec, n]` ✓.

**Dependent (checking).**

```cure
fn demo_dep(n: Nat, vec: Vector(Int, n)) -> Tuple(m: Nat, Vector(Int, m)) =
  %[n, vec]        # checked ⇒ shape Dep(Nat, λm. Ext(Vector(Int,m), Empty));
                   # element 2 expected Vector(Int,m)[m:=n] = Vector(Int,n) ✓
```

`d.1 : Nat`, `d.2 : Vector(Int, d.1)` (dependent projection). `swap(d)` is
**rejected**: `Dep(Nat, …)` vs `swap`'s `Ext(A, Ext(B, Empty))` is a head clash —
reordering a tuple whose element-2 *type* names element-1's *value* is genuinely
ill-typed, and the type says so structurally.

**Punchline.** Both emit the identical flat value `{n, vec}`; `swap(p)` emits
`{vec, n}`. Dependent and non-dependent tuples are byte-identical at runtime; the
`Dep` shape only *withdraws the operations that would be unsound* and leaves
projection/matching fully available.

## 5. Representability — proven, not speculative

Probed against the merged compiler (`feature/idris-parity` @ merge `9a7367d`) via
`Program.elaborate` → `Emit.compile_and_load` → `apply/3` on the host BEAM. Test:
`test/cure/e2e/tuple_repr_probe_test.exs` (commit `345aa26`).

**Already works end-to-end:**

- **Dependent pair (arity-2 Sigma):** construct, project `.1`, run → `{:Suc,{:Suc,:Zero}}`.
- **A GADT indexed by inductive `Tele` *values*** (`NonDep indices (shape: Tele)`,
  `NDExt : NonDep(rest) -> NonDep(Ext(A, rest))`): builds and runs →
  `{:NDExt, :NDEmpty}`, with the `A`/`rest` indices **erased**. The witness layer's
  *construction and erasure* (§3.5) is representable today over an `Empty`/`Ext`
  telescope (the landed FRP slice already indexes `SF` by `SVDesc`/`Dec` values —
  same machinery); the `Dep`-rejection path can only be exercised once `Tele.Dep`
  parses (§6.2), but it is the ordinary "uninhabited constructor" failure, not new
  machinery.
- **Nested-Sigma projection** through annotated intermediates.

**Gaps this design must close (see §6):** flat n-ary `%[a,b,c]`; function-typed
constructor fields (`Tele.Dep`); a minor chained-projection inference fix.

**By-design constraint confirmed:** constructing a `Type`-carrying value
(`Ext(Int, …)`) is rejected (`:unknown_global`) — Types are not first-class runtime
values, so `Tele` must stay a `{0}`-erased index, never reflected. The supported
path is exactly the all-erased one the probe exercised.

## 6. What must be built

Two well-scoped compiler extensions plus one minor fix — **no kernel/TCB change**.

### 6.1 N-ary flat tuple (the foundation)

Today a non-binary `%[…]` is `:unsupported_expression` (elaborator is binary-only).
Needed:

1. **Elaboration** — clauses for `{:tuple, _, elems}` with `length ≠ 2`, in both
   checked mode (against a `Tuple(…)` / nested-Sigma-unfolded type, substituting
   earlier values into later expected types) and synthesis mode (all-`Ext` shape).
   Reuse the arity-2 checked/synth logic, folded over the telescope.
2. **Type surface** — parse and elaborate `Tuple(…)` at type position (per-position
   optional binder), generalizing `parse_sigma_type`
   (`parser.ex:parse_sigma_type`) to n-ary; lower to the `shape: Tele` index and
   its nested-Sigma unfolding.
3. **Emit** — flatten the nested-`mk_pair` chain to one BEAM tuple; lower `.i`
   (i > 2) to `element(i, t)`. Generalizes the landed arity-2 emit hooks.
4. **Projection** — `.3 … .n` (today only `.1`/`.2` lower to Sigma projections,
   `elaborator.ex:437-438`); the rest fall through to record projection.

### 6.2 Function-typed constructor fields (`Tele.Dep`)

Today `Dep : (A: Type) -> (A -> Tele) -> Tele` fails to parse at the inner `->`:
`parse_ctor_dom` (`parser.ex:3167`) accepts only a named binder `(name: T)` or a
plain `parse_type_atom`, and `parse_type_atom` (`parser.ex:3187`) parses a
parenthesized *atom* and demands `)`. Needed:

1. **Parser** — accept a parenthesized **function-type domain** in constructor
   signatures. The machinery already exists for type *parameters* (`b: (a) -> Type`
   in `Sigma`); wire it into `parse_ctor_dom`.
2. **Positivity** — accept the strictly-positive recursive occurrence in a
   function-typed field (`(A) -> Tele`), where `Tele` appears only in the codomain.
3. **Erasure/relevance** — a function-typed field carrying only erased content
   (`Tele` shapes) must erase cleanly; verify no spurious relevance report.

### 6.3 Chained projection inference (minor)

`x.2.1` in one expression fails (`projection_not_a_record`) though it works through
an annotated intermediate. Infer the inner projection's Sigma type so a second
projection fires without a `let`.

## 7. Erasure & device story

`Tele`, `NonDep`, `IndepAt`, and all shape indices are `{0}`-erased — they exist
only at check time (§5 confirms erased-index GADTs already run and drop their index
args). `run`-time tuples are flat BEAM tuples with `element/i` access. The value
surface stays pure (no `receive`/`spawn`, no `E043`, no runtime solver), so unified
tuples ship to ESP32/AtomVM unchanged. **Must-verify on host first** (per project
CLAUDE.md): the flat-emit + `element/i` path on generic-unix AtomVM before any
hardware claim — though the representability probes already exercise flat tuples on
the host BEAM.

## 8. Library surface (`Std.Tuple`)

Replaces `Std.Pair`. Sketch (full signatures fixed in the implementation plan):

```cure
mod Std.Tuple
  type Tele indices ()                 # §3.5 (needs 6.2 for Dep)
  type Tuple indices (shape: Tele)     # façade over nested Sigma (§3.4)
  type NonDep indices (shape: Tele)    # erased non-dependence witness

  fn get(i, t)            # total on any shape → element(i, t)
  fn swap(t)              # fixed-arity, all-Ext skeleton gate
  fn to_list(t)           # homogeneous + NonDep → List(a)
  fn map_uniform(nd, t, f)# NonDep + homogeneous
  fn reverse(nd, t)       # NonDep → reversed flat tuple

  # first/second retained as arity-2 aliases of get(1)/get(2) for Std.Pair source
```

`Std.Pair` is deprecated to thin aliases over `Std.Tuple` via the migration
facility, then removed after the deprecation window.

## 9. v1 scope & deferred

**v1:** `Tele`/`Tuple`/`NonDep`; n-ary flat `%[…]` (construct, `.i`, match, run);
`Tuple(…)` type surface with per-position binders; mode disambiguation; the
fixed-arity and `NonDep`-gated generic API; `Std.Pair` migration.

**Deferred (ledger):**

- **`IndepAt(shape, i)`** — finer `map_at`/single-position-update gating (v1 gates
  on full `NonDep`).
- **Fork resolution (i) vs (ii)** — decided in the implementation plan (§3.6).
- **Homogeneous-collapse & permutation ops** beyond `to_list`/`swap`/`reverse`.
- **`interface Input`-style unification** with other telescope consumers once
  typeclasses land — not on this critical path.
- **Anonymous positional dependent records** — a dependent tuple *is* one; unify
  with `dependent-records-finding` machinery later rather than duplicating.

## 10. Non-goals

- **No nested-pair runtime representation** — the whole point is the flat tuple;
  nesting is a checking scaffold only (§3.4).
- **No new trusted-kernel surface** — the kernel keeps checking binary Sigma only.
- **No `Type`-as-runtime-value reflection** — `Tele` is erased-only (§5, §7).
- **No subtyping** — `Sigma`/`Tuple` relate as instance/restriction, not sub/super
  (§3.3).
- **No general representation-selection optimizer** — the flat shape is by
  construction here, not an optimizer bet (that general `List→binary` work is the
  separate parsing-library ledger item, not this).

## 11. Relationship to other specs

- **`2026-07-09-sigma-retirement-design.md`** — provides the arity-2 target this
  generalizes: the `@builtin(:sigma)` inductive, `%[x,y]`→`mk_pair`, `.1`/`.2`→
  `element/2`, and the emit hooks. This spec re-points the arity-2 surface from a
  standalone `Sigma` to the general `Tuple` façade, keeping the ABI byte-compatible.
- **`dependent-records-finding`** — a dependent tuple is an anonymous positional
  dependent record; the GADT-ctor-from-named-domain machinery is the shared enabler
  (relevant if the fork resolves toward richer dependent shapes).
- **`stdlib-dependent-expansion`** — `Vector`/`Bounded`/`Ordering` siblings; `Std.Tuple`
  joins them as a dependently-honest collection.

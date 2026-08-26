# Dependent Type Slices

> Historical implementation plan. The classic pipeline described in this file
> has since been deleted, `Std.Equivalent` replaced the temporary
> `Std.Equal`/runtime-token surface, and all accepted programs now use the
> dependent kernel. See `docs/TYPE_SYSTEM.md`, `docs/DEPENDENT_TYPES.md`, and
> `ROADMAP-0.34.md` for current behavior.

This note lays out the dependent typing slices as they stand on this branch.
Only Slice 1 is formally specified in the current design document; later slices
below are pragmatic widening slices derived from the roadmap and from the
features explicitly called out as deferred.

## Slice 1: Kernel-Owned Indexed Families For The FRP Core

Slice 1 is the first sound dependent-typing slice. Its target is not general
Idris/Agda peerness; it is an end-to-end trusted-kernel path for the smallest
FRP fragment that forces the important machinery into existence.

Implemented capabilities:

- explicit Core terms with de Bruijn variables
- `Type` universes and cumulativity checks
- dependent `Pi` functions, lambdas, and applications
- normalization by evaluation and definitional equality
- indexed inductive family declarations
- constructor typing with computed result indices
- positivity checks for inductive families
- dependent `case` with a motive
- Sigma formation, introduction, and projections
- kernel-level equality/rewrite nodes in Core
- global definitions in the Core environment
- totality certification gating type-level unfolding
- erased/implicit arguments for dependent parameters
- elaborator-side metavariables for inferred implicit arguments
- erasure from checked Core to runtime terms
- dependent compiler route through `Cure.Compiler.compile_and_load/2`
- codegen refusal for unfilled holes
- serializable Core artifacts for future independent checking

The original Slice-1 domain example is:

```cure
type Dec = Dcoupled | Causal
type Sig = CSig | ESig
type SVDesc = SVNil | SVCons(Sig, SVDesc)

fn andd(x: Dec, y: Dec) -> Dec = x

indexed type SF(as: SVDesc, bs: SVDesc, d: Dec) where
  prim : SF(as, bs, Causal)
  seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))

fn compose({as: SVDesc}, {bs: SVDesc}, {cs: SVDesc},
           {d1: Dec}, {d2: Dec},
           l: SF(as, bs, d1), r: SF(bs, cs, d2))
  -> SF(as, cs, andd(d1, d2)) =
  seq(l, r)
```

This proves that Cure can represent a GADT-style family whose constructor
result indices encode static facts, then erase those indices before runtime.

## Slice 1 Expanded: Real Length-Indexed Vector

The Vector work expands Slice 1 from the FRP-specific `SF` example to the
canonical dependent-data example. This now lives in the stdlib as
`lib/std/nat.cure` and `lib/std/vector.cure`:

```cure
type Nat = Z | S(Nat)

indexed type Vector(a: Type, n: Nat) where
  empty : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))

fn plus(m: Nat, n: Nat) -> Nat = match m
  Z() -> n
  S(k) -> S(plus(k, n))

fn append({a: Type}, {m: Nat}, {n: Nat},
          xs: Vector(a, m), ys: Vector(a, n)) -> Vector(a, plus(m, n)) =
  match xs
    empty() -> ys
    prepend(x, rest) -> prepend(x, append(rest, ys))
```

What changed to make this real:

- `Vector` is now representable as an indexed family, not as a runtime tuple
  whose length is merely stored in a field.
- `Std.Nat` provides the separate Peano `Nat` index type and owns the total
  `plus` used by `Std.Vector.append`'s result index.
- Imported recursive type-level functions such as `Std.Nat.plus` can be
  totality-certified and unfolded during conversion.
- Global calls with erased parameters infer and insert those implicit
  arguments, so recursive calls like `append(rest, ys)` do not bind explicit
  arguments to hidden positions.
- Match motives are generalized over the scrutinee indices, so branch checking
  can see that the result type changes with the vector length.
- Branch contexts are specialized from constructor result indices, so the
  `empty` and `prepend` branches get the relevant index equalities.
- Conversion avoids looping on identical stuck recursive neutrals such as
  `plus(k, n)` versus `plus(k, n)`.
- Erasure drops implicit global-call arguments as well as implicit constructor
  arguments, so checked `append({a}, {m}, {n}, xs, ys)` emits and runs as
  runtime `append(xs, ys)`.

This is covered both through `Program.elaborate/1` and through real Cure
compilation and BEAM execution.

## Slice 2: Honest Routing And API Retirement

Slice 2 should make the trusted boundary comprehensive enough that dependent
claims cannot bypass the kernel.

Completed in this slice:

- route the supported dependent surface through Core/Elab even when a module
  has no `indexed type`: typed erased parameters, `Sigma(...)`, `%[...]`, and
  `p.1` / `p.2` projections
- prove that routing through real Cure compilation, erasure, BEAM emission, and
  execution, not only AST elaboration tests
- keep `Std.Vector` on the real dependent path with `Vector`, `empty`, and
  `prepend`
- document `Cure.Types.Reduce` as a Core-normalization compatibility facade
- soften `Std.Equal`, `Std.Proof`, and `Std.CRDT` claims so runtime tokens and
  law-shaped declarations are not described as trusted kernel proofs

Still deliberately deferred:

- public Cure `Eq(T, a, b)`, `refl`, and `rewrite` elaboration to Core
- proof containers checked by `Cure.Core.Kernel`
- retiring the legacy `Cure.Types.Pi`, `Cure.Types.Sigma`,
  `Cure.Types.Equality`, `Cure.Types.Holes`, and `Cure.Types.Dependent`
  compatibility modules

This slice is about product honesty and trust-boundary hygiene.

## Slice 3: Stronger Indexed Pattern Matching

Slice 3 should move dependent matching from the current useful fragment toward
the Agda/Idris shape.

Required capabilities:

- branch refinement by index unification beyond direct constructor aliases
- impossible-branch detection
- coverage checking under indexed-family constraints
- useful diagnostics for failed index unification
- constructor splitting for more than the current hand-shaped examples
- inaccessible or dot-pattern-like behavior, or an equivalent elaborator
  mechanism

This is the slice that decides whether indexed data stays a demo-sized feature
or becomes a practical programming tool.

## Slice 4: Constraint-Based Elaboration

Slice 4 should replace ad hoc implicit solving with an actual elaboration
constraint engine.

Required capabilities:

- metavariables with postponed constraints
- occurs checks
- blocking and resumption
- implicit insertion for constructors, globals, nested calls, and expected
  return types
- bidirectional checking that uses expected types aggressively
- unsolved-metavariable diagnostics with local context

This is needed before Cure can feel peer-like for ordinary dependent programs.

## Slice 5: Totality, Conversion, And Type-Level Computation At Scale

Slice 5 should harden the story for functions used in types.

Required capabilities:

- complete dependency closure for type-position functions
- mandatory totality certificates for every reducible global in that closure
- documented structural recursion rules
- mutual recursion support or explicit rejection
- controlled unfolding in conversion
- robust behavior for stuck neutrals under binders and substitution
- regression tests for recursive type-level programs

Minimal Vector proves the shape. This slice makes that shape dependable beyond
one recursive `Nat` function.

## Slice 6: Kernel Equality And Rewrite As A Real User Feature

Slice 6 should make equality proofs trusted-kernel artifacts rather than
runtime atoms or proof-shaped comments.

Required capabilities:

- surface `Eq(T, a, b)` elaborates to Core equality
- `refl` checks only when both endpoints are definitionally equal
- `rewrite`/transport changes goal types soundly
- congruence and symmetry are checked definitions or derived operations
- equality proofs erase only after kernel checking
- arbitrary atoms cannot inhabit arbitrary equality types

This is the slice that fixes the current `Std.Equal` and `Std.Proof` gap.

## Slice 7: Universe Hardening And Conformance

Slice 7 should make the kernel auditable and resistant to classic dependent
type failures.

Required capabilities:

- explicit universe behavior across `Pi`, `Sigma`, data, equality, and
  inductive families
- deliberate cumulativity rules
- universe-polymorphic definitions or clear rejection
- negative tests for paradox shapes and universe escape
- accepted/rejected Core conformance corpus
- accepted/rejected surface conformance corpus
- serialization round trips for every Core artifact

This is the point where an independent checker becomes realistic.

## Slice 8: Wider FRP Port

Slice 8 should return to the original Safe FRP target and widen from
sequential composition to the rest of the paper-driven constructs.

Required capabilities:

- `_++_` and `map` over descriptors
- `**`, `switch`, `dswitch`, and `loop`
- `Init` or equivalent initialized/uninitialized descriptors
- productivity checks where feedback/looping requires them
- broader use of equality/rewrite for descriptor algebra when definitional
  equality is not enough

This is where dependent typing pays off for the FRP design rather than only
for isolated examples.

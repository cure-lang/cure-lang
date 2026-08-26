# Dependent Kernel Peerness Roadmap

> Status note: this roadmap predates the 0.34 kernel convergence. Items
> describing primitive `Eq`/`refl`/`rewrite`, the classic checker, or missing
> public dependent elaboration are complete and superseded by
> `Std.Equivalent`, the single dependent pipeline, and Final-Core validation.
> Remaining research items are prospective work, not current language
> limitations.

This note summarizes the current state of the dependent typing work on this
branch, the gap to Idris/Agda-style peerness, and pragmatic milestones for
closing it.

## Current State

The branch has a promising Slice-1 trusted-kernel prototype. The implemented
direction is sound in shape: surface dependent programs are elaborated to an
explicit Core, the trusted kernel re-checks Core terms, and erasure/codegen sit
after that boundary.

The branch already contains foundations for:

- de Bruijn-indexed Core terms and contexts
- telescopes
- universes and cumulativity tests
- normalization/evaluation and conversion
- indexed family and constructor signatures
- positivity checks
- constructor typing with computed indices
- dependent `case`
- Sigma pairs — as of task #13/D2 no longer a bespoke kernel primitive: the
  dependent pair is the stdlib inductive `Std.Sigma` (family `Sigma(a, b)`,
  constructor `mk_pair`) registered `@builtin(:sigma)` and routed entirely
  through the generic indexed-family/`case` machinery; the surface `%[a, b]` /
  `.1` / `.2` behaviour and the bare-2-tuple BEAM ABI are unchanged
- equality/rewrite Core support
- totality certificates for type-level reduction
- elaborator-side metavariables for inferred erased arguments
- erasure and dependent codegen path
- Slice-1 FRP conformance tests

This is not yet Idris/Agda peer-level. It is a constrained dependent fragment
whose boundaries are still visible in both documentation and implementation.

## Current Vector Status

`test/cure/elab/vec_dependent_test.exs` and
`test/cure/compiler/dependent_vec_codegen_test.exs` establish a real
length-indexed vector family:

```cure
type Nat = Z | S(Nat)

indexed type Vector(a: Type, n: Nat) where
  empty : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

The current minimal Vector fragment passes:

- the `Vector(a, n)` family elaborates with a `Type` parameter and `Nat` index
- recursive `plus(m, n)` over `Nat` elaborates and certifies
- `append` elaborates and kernel-checks with a dependent result index
- the same program compiles through `Cure.Compiler.compile_and_load/2`, erases
  implicit indices, emits BEAM, and runs as `append/2`
- an invalid append branch is rejected through the real compiler path

```cure
fn append({a: Type}, {m: Nat}, {n: Nat},
          xs: Vector(a, m), ys: Vector(a, n)) -> Vector(a, plus(m, n)) =
  match xs
    empty() -> ys
    prepend(x, rest) -> prepend(x, append(rest, ys))
```

The important implementation changes were implicit argument insertion for
global calls with erased parameters, dependent motive generalization for
matches, branch-context specialization from constructor result indices, a
conversion shortcut for identical stuck neutrals, and erasure of implicit
arguments at global call sites.

## Why This Is Not Idris/Agda Peer-Level Yet

### Routing Is Too Narrow

The dependent pipeline is currently selected by the presence of `indexed type`.
That means other surface constructs can still claim dependent behavior without
being owned by the trusted kernel.

Kernel-owned dependent routing needs to include:

- `Pi`
- `Sigma` (now kernel-owned via the builtin inductive family, not a primitive — #13/D2)
- `Eq`
- `rewrite`
- proof containers
- indexed families
- implicit arguments
- erased arguments
- total functions used in types
- type-level definitions

No surface feature should claim dependent typing unless its artifact elaborates
to Core and is rechecked by the kernel.

### Pattern Matching Is Still Too Small

Idris/Agda peerness requires mature dependent pattern matching, not only a
minimal dependent `case`.

Required capabilities include:

- motives that genuinely vary by indices and scrutinee
- impossible-branch pruning by index unification
- coverage checking over indexed families
- constructor splitting
- inaccessible/dot patterns or an equivalent mechanism
- useful diagnostics for failed index unification

The branch has made progress here, including motive generalization work, but
the earlier Vector append failure showed the system was not yet robust.

### The Elaborator Needs To Become Serious Infrastructure

Peer systems put most complexity in elaboration, not in the tiny kernel.

Needed elaborator capabilities:

- metavariables with constraints
- occurs checks
- blocking constraints
- implicit insertion at all relevant call sites
- bidirectional checking for surface syntax
- stable name resolution and namespaces
- holes with local context and pending constraints
- clear separation between untrusted elaboration and trusted Core checking

### Definitional Equality Must Scale

Normalization/conversion must support real programs without accidental
unfolding or unsound recursion.

Needed conversion work:

- controlled global unfolding
- recursive definitions unfolded only after totality/productivity certification
- eta rules where deliberately chosen
- stuck neutrals
- constructor/case iota rules
- stable behavior under substitution and binders
- universe-aware conversion

### Totality Must Be A Gate, Not Best Effort

Any function reducible in a type must be total. Peer-level systems make this a
central invariant.

Needed totality work:

- structural recursion
- mutual recursion
- size-change or a clearly documented accepted subset
- productivity if coinductive/productive constructs are added
- explicit refusal of non-total functions in type positions

### Universe Handling Must Be Hardened

Slice-1 can avoid much of the hard universe story. A peer system cannot.

Needed universe work:

- no `Type : Type`
- robust cumulativity
- universe levels on inductive families
- universe metavariables or explicit universe parameters
- test coverage for universe escape/regression cases

### Equality And Proofs Must Stop Being Runtime Atoms

The stdlib currently contains proof-shaped APIs that are not trusted-kernel
proofs. Peer-level equality needs:

- kernel-level `Eq`
- `refl`
- eliminator/rewrite
- congruence/transport as derived or checked definitions
- proof erasure after checking
- proof containers elaborated through Core, not only shape-checked

### Legacy Fake Modules Need Retirement

The old `Cure.Types.*` dependent modules and docs still create a split-brain
system. Once Core/Elab owns the real features, the legacy modules should be
removed, quarantined, or clearly marked as obsolete compatibility code.

Targets include:

- `Cure.Types.Dependent`
- `Cure.Types.Pi`
- `Cure.Types.Sigma`
- `Cure.Types.Equality`
- `Cure.Types.Holes`
- `Cure.Types.Reduce`

## Pragmatic Milestones

### M1: Finish Minimal Vector

Goal: the length-indexed `Vector(a, n)` append test passes through
`Program.elaborate/1` and the trusted kernel.

Acceptance:

- `Vector(a, n)` elaborates as an indexed family
- `plus` over `Nat` is total enough for type-level reduction
- `append` elaborates and kernel-checks
- recursive `append(rest, ys)` receives inferred erased arguments correctly
- constructor result types are evaluated in the correct caller frame

### M2: Make Dependent Routing Comprehensive

Goal: dependent-looking surface syntax cannot bypass the trusted kernel.

Acceptance:

- modules using `Pi`, `Sigma`, `Eq`, `rewrite`, proof containers, or erased
  type-level parameters route through Core/Elab even without `indexed type`
- old checker does not silently accept kernel-dependent claims
- negative tests prove bypasses are rejected

### M3: Retire Or Quarantine Fake Dependent APIs

Goal: remove split-brain behavior between legacy dependent modules and Core.

Acceptance:

- stdlib false claims documented in `docs/STDLIB_DEPENDENT_CLAIMS_AUDIT.md`
  are either fixed or softened
- proof-shaped `Atom` equality is not presented as kernel equality
- old `Cure.Types.*` dependent modules are removed, deprecated, or isolated

### M4: Harden Indexed Pattern Matching

Goal: indexed pattern matching handles realistic GADT programs.

Acceptance:

- motives can vary by indices and scrutinee
- impossible branches are detected by unification
- missing reachable branches are coverage errors
- unreachable branches do not need bodies
- index-refinement failures report actionable diagnostics

### M5: Build A Constraint-Based Elaborator

Goal: implicit inference works beyond hand-shaped constructor/global calls.

Acceptance:

- metavariable constraints can be postponed and solved later
- occurs checks prevent cyclic solutions
- unsolved metas are reported with local context
- implicit insertion works for globals, constructors, nested calls, and returns
- bidirectional checking is used where expected types are known

### M6: Make Totality Mandatory For Type-Level Reduction

Goal: no non-total definition can affect conversion in types.

Acceptance:

- type-position dependency graph is complete
- every reducible global in that graph requires a certificate
- recursive and mutual recursive definitions are checked by a documented rule
- failures name the offending definition

### M7: Implement Real Equality And Rewrite End To End

Goal: equality proofs are Core-checked and erased only after checking.

Acceptance:

- `Eq(T, a, b)` is a kernel type
- `refl` only checks when endpoints are definitionally equal
- `rewrite`/transport changes goal types soundly
- proof containers elaborate to Core
- arbitrary atoms cannot inhabit arbitrary equality proofs

### M8: Harden Universes

Goal: universe behavior is explicit and regression-tested.

Acceptance:

- universe levels are tracked across Pi, Sigma, data, equality, and inductives
- cumulativity is deliberate
- universe-polymorphic definitions are either supported or explicitly rejected
- known paradox shapes are negative tests

### M9: Build A Conformance Corpus

Goal: prevent regressions and make the trusted boundary auditable.

Acceptance:

- accepted/rejected Core terms
- accepted/rejected surface dependent programs
- serialization round trips
- coverage failures
- positivity failures
- universe failures
- totality failures
- equality/rewrite failures
- stdlib dependent APIs checked end to end

## Near-Term Engineering Rule

The next practical bar is simple:

> If a Cure surface feature claims dependent typing, it must elaborate to Core
> and be rechecked by the trusted kernel.

Everything else should be documented as legacy, refinement-only, runtime-only,
or out of scope.

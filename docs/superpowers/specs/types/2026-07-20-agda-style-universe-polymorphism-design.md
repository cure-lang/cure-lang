# Agda-Style Predicative Universe Polymorphism for Cure

**Status:** authoritative design for replacing Cure's fixed universe ceiling

**Date:** 2026-07-20

**Applies to:** Core universes and sorting, elaboration of type declarations and
implicit arguments, inductive-family checking, standard-library polymorphism,
erasure, serialization, Antigen, and all compiler caches containing Core terms

**Does not reorder:** the macro/BEAM implementation ledger in
`2026-07-12-macro-facility-autopilot-state.md`. This specification is the
authority whenever that work or later work encounters universe representation,
sorting, or polymorphism.

## 1. Decision

Cure will replace the fixed hierarchy

```text
Type0 : Type1 : Type2
```

with an Agda-style, infinite, predicative, universe-polymorphic hierarchy:

```text
Type(l) : Type(universe_succ(l))
```

Universe levels are compile-time values of a primitive `UniverseLevel` type.
They have zero, successor, and least-upper-bound operations. Definitions may
quantify
over levels, and applications normally infer their erased level arguments.

Cure retains its existing cumulative treatment of universes. Agda makes
cumulativity optional; Cure does not. The kernel accepts `Type(a)` where
`Type(b)` is expected only after independently deciding `a <= b` in the
canonical level algebra.

There is no universe ceiling. There is no `Type : Type` rule. Quantification
over a level on which the codomain sort rigidly depends is classified by an
Agda-style `TypeLimit` hierarchy rather than collapsing the hierarchy or
inventing a finite upper bound.

This is a kernel change, not an elaborator convention. The untrusted
elaborator may generate and solve level constraints, but checked Core contains
explicit levels, no level metavariables, and no unverified universe claims.

## 2. Why the current design must be replaced

The present implementation is sound but artificially bounded:

- `Cure.Core.Universe` fixes `@ceiling 2`;
- `Core.Term` admits only integer universe levels in `0..2`;
- `Type2` has no sort because `Type3` is rejected;
- declarations search levels `0`, `1`, and `2` for the first one that works;
- `Sigma`, `Equivalent`, and other library abstractions are restricted to
  `Type0` because their definitions cannot quantify over a level;
- the Antigen universe assay treats reaching the ceiling as an expected
  rejection.

This makes library abstractions depend on an arbitrary implementation limit.
Increasing the limit merely postpones the same failure and does not permit one
definition to work uniformly at every level.

The replacement must preserve the reasons Cure rejected `Type : Type`:

- logical consistency must not depend on the totality checker;
- normalization used by conversion must remain terminating;
- a universe must never inhabit itself;
- malformed or cyclic universe constraints must fail closed.

## 3. Agda research basis

The design was derived from the local Agda checkout at
`/Users/ch/Develop/agda`, commit `7273757e5e` (2026-06-15), rather than from a
surface-language summary alone.

### 3.1 Surface model

Agda exposes:

```agda
Level
lzero : Level
lsuc  : Level -> Level
_⊔_   : Level -> Level -> Level
Set   : Level -> Sort
```

This supports definitions such as:

```agda
data List {l : Level} (A : Set l) : Set l

data _×_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b)
```

The source authority is
`doc/user-manual/language/universe-levels.lagda.rst`.

### 3.2 Canonical level representation

Agda does not carry unreduced trees of `zero`, `suc`, and `max` through its
kernel. `Agda.Syntax.Internal.Level'` represents a level as:

```text
max(constant, atom_1 + offset_1, ..., atom_n + offset_n)
```

In Agda's Haskell representation this is `Max Integer [PlusLevel]`. The
normalizer in `Agda.TypeChecking.Substitute.levelMax`:

1. flattens nested level values;
2. merges equal atoms, retaining their greatest offset;
3. sorts atoms deterministically;
4. removes a constant already subsumed by an offset lower bound.

Consequently the algebra decides the intended definitional laws directly:

```text
max(a, b)             = max(b, a)
max(a, a)             = a
max(max(a, b), c)     = max(a, max(b, c))
succ(max(a, b))       = max(succ(a), succ(b))
max(a, succ(a))       = succ(a)
max(a, 0)             = a
```

### 3.3 Sort computation

Agda separates:

- `univSort`: the sort of a universe;
- `funSort`: the sort of a non-dependent function type;
- `piSort`: the sort of a dependent function type.

Unknown sorts are represented explicitly and constraints are postponed until
their blockers are solved. The relevant implementation is
`Agda.TypeChecking.Sort` and the `univSort'`, `funSort'`, and `piSort'`
functions in `Agda.TypeChecking.Substitute`.

### 3.4 Constraint handling

Agda stores equality and ordering constraints over normalized levels. It first
tries reduction and syntactic equality, then structural level reasoning, and
otherwise postpones a constraint blocked on a metavariable. With cumulativity,
underconstrained level metas can be assigned the least upper bound of their
known lower bounds. The relevant implementations are:

- `Agda.TypeChecking.Conversion.leqLevel`;
- `Agda.TypeChecking.LevelConstraints`;
- `Agda.TypeChecking.Level.Solve`;
- `Agda.TypeChecking.Generalize`.

Cure adopts the normalized algebra and least-solution principle. It does not
adopt Agda's entire general-purpose constraint engine.

### 3.5 Why omega is necessary

The type

```agda
(l : Level) -> Set l
```

cannot inhabit any `Set n`: no finite `n` bounds all `l`. Agda classifies it in
`Setω`, followed by the non-polymorphic hierarchy
`Setω : Setω1 : Setω2 : ...`.

Cure adopts the corresponding `TypeLimit` hierarchy. Omitting it while making
`UniverseLevel` quantifiable would leave well-formed universe-polymorphic signatures
without a sort.

### 3.6 Erasure

Agda compiles level values to unit and erases sorts and function types. Its
MAlonzo primitives implement level zero, successor, and maximum as unit-valued
operations, and the Treeless translation maps internal levels to unit.

Cure already has checked grade-0 erasure, so level binders and level operations
must disappear through that existing mechanism. There must be no runtime
universe dictionary, tag, integer, or dispatch.

## 4. Scope of the adopted Agda subset

Cure adopts:

- an infinite finite-level hierarchy `Type(l)`;
- explicit, erased level parameters;
- `universe_zero`, `universe_succ`, and `universe_max`;
- canonical maximum-plus level normal forms;
- level metavariables and constraints in the elaborator;
- kernel-decided equality and ordering of closed or parametrically open levels;
- universe polymorphism for functions, aliases, inductive families,
  constructors, interfaces, implementations, and macros producing declarations;
- cumulative inclusion between universes;
- `TypeLimit(n)` for level-dependent sorts;
- complete erasure of levels.

Cure does not initially adopt:

- Agda's `Prop`, `SSet`, cubical interval universe, size universe, lock universe,
  or fibrancy lattice;
- `--type-in-type` or an equivalent escape hatch;
- `--omega-in-omega` or an equivalent escape hatch;
- universe-polymorphic limit levels;
- arbitrary user-defined rewrite rules for level equality;
- runtime reflection over levels;
- pattern matching or recursion on `UniverseLevel`;
- automatic generalization of every undeclared identifier in a signature.

`UniverseLevel` is first-class only in the restricted Agda sense: it can be bound,
passed, returned by total level expressions, and used to index `Type`, but it is
compile-time-only and has no eliminator that exposes a natural-number
representation.

## 5. Surface language

### 5.1 Primitive vocabulary

The automatically available universe vocabulary is:

```cure
UniverseLevel : Type
universe_zero : UniverseLevel
universe_succ : (l: UniverseLevel) -> UniverseLevel
universe_max  : (a: UniverseLevel) -> (b: UniverseLevel) -> UniverseLevel
```

The level-operation arguments are written explicitly at the surface, but the
Core rule in section 13 forces every `UniverseLevel` domain to grade zero. Thus
`universe_succ(l)` and `universe_max(a, b)` are ordinary readable source
expressions without
becoming runtime calls.

`universe_max` is the named primitive. A later standard-library operator may expose
Agda's `⊔` notation without changing Core.

### 5.2 Universe syntax

The accepted forms are:

```cure
Type                 # Type(universe_zero), preserving today's meaning
Type(l)              # finite universe at level l
Type0                # closed-level compatibility spelling
Type1
Type37
TypeLimit            # TypeLimit0
TypeLimit0
TypeLimit1
```

`Type(n)` is not the syntax for a closed level when `n` is an `Int`; its
argument must have type `UniverseLevel`. Closed numeric spellings use `TypeN` and are
stored as a constant in the level normal form, never expanded into `N`
successor nodes.

`Type`, `TypeN`, and `TypeLimitN` are special type syntax, not ordinary global
functions. The parser must retain source spans for the whole form and its level
argument so universe diagnostics point to the relevant expression.

### 5.3 Polymorphic examples

The target surface can express:

```cure
type List({l: UniverseLevel}, a: Type(l))
  | Nil
  | Cons(a, List(l, a))

fn id({l: UniverseLevel}, {a: Type(l)}, x: a) -> a = x

fn map(
  {la: UniverseLevel},
  {lb: UniverseLevel},
  {a: Type(la)},
  {b: Type(lb)},
  xs: List(la, a),
  f: (a) -> b,
) -> List(lb, b) = ...
```

Ordinary code remains unchanged:

```cure
fn small_id({a: Type}, x: a) -> a = x
```

This remains specifically level zero. Cure must not silently reinterpret every
existing `{a: Type}` as universe-polymorphic; doing so would change APIs and
could admit type-valued data where runtime operations only support ordinary
values.

### 5.4 Generalization policy

Declaration-site universe polymorphism is explicit in the first release: the
author writes `{l: UniverseLevel}`. Use-site universe arguments are inferred and
inserted just like other erased implicit arguments.

A later `variable` block or explicit `_`-generalization feature may add Agda's
surface convenience. It must elaborate to the same explicit grade-0 `Pi`
binders and is not part of this specification's acceptance gate.

## 6. Formal level algebra

### 6.1 Source-level grammar

```text
u, v ::= universe_zero
       | universe_succ(u)
       | universe_max(u, v)
       | alpha                 level variable
       | ?m                    elaborator-only level metavariable
       | f u1 ... un           total expression returning UniverseLevel
```

### 6.2 Canonical normal form

Checked Core uses:

```text
L ::= max(c, a1 + k1, ..., an + kn)
```

where:

- `c` and every `ki` are arbitrary-precision non-negative integers;
- every `ai` is a quoted neutral Core term checked at `UniverseLevel`;
- atoms are sorted by canonical serialized term order;
- no atom appears twice;
- for an equal atom only the greatest offset is retained;
- `c` is stored as zero when an atom offset already guarantees at least `c`;
- `max(0)` is the unique zero normal form.

The final representation must be a dedicated `Cure.Core.UniverseLevel` type. It must
not overload an integer with sentinel values and must not encode level
metavariables in `Core.Term`.

The target tuple-level shape is:

```text
{:level_nf, constant, [{atom_term, offset}]}
```

An equivalent private struct is permitted inside `Cure.Core.UniverseLevel`, but
serialized Core and public TCB boundaries use a stable tagged representation.

### 6.3 Operations

`Cure.Core.UniverseLevel` owns:

```text
zero
closed(n)
atom(term)
succ(level)
max(left, right)
normalize(level, context)
equal?(left, right, context)
leq?(left, right, context)
shift(level, amount, cutoff)
subst(level, index, replacement)
free_vars(level)
validate(level, context)
```

All constructors return canonical form. No caller may assemble an unchecked
normal form by concatenating atom lists.

### 6.4 Equality

Universe-level equality is equality of canonical normal forms after:

1. normalizing total/certified computations in each atom;
2. expanding an atom that evaluates to a known level value;
3. quoting remaining neutral atoms;
4. canonicalizing the maximum-plus representation.

Atom comparison uses ordinary Core definitional equality at `UniverseLevel`. It does
not use Elixir term equality as a substitute for conversion.

### 6.5 Ordering

`a <= b` is decided as:

```text
universe_max(a, b) == b
```

The implementation may use the equivalent component test on canonical forms:

- the constant/lower-bound component of `a` must be dominated by `b`;
- every `x + k` component of `a` must have the same atom `x` in `b` at an
  offset `j >= k`;
- unrelated atoms do not dominate each other.

There are no residual constraint assumptions in checked Core, so this decision
is complete for the admitted maximum-plus language.

## 7. Core representation

### 7.1 Sort indices

Core replaces integer levels with:

```text
sort_index ::= {:finite, level_nf}
             | {:omega, non_negative_integer}
```

The term and value forms become:

```text
Core term:
  {:level_type}
  {:level_value, level_nf}
  {:type, sort_index}

NbE value:
  {:vlevel_type}
  {:vlevel, level_nf}
  {:vtype, sort_index}
```

The existing `{:type, integer}` and `{:vtype, integer}` forms are transitional
input formats only. They map to `{:finite, UniverseLevel.closed(integer)}` during the
migration and are forbidden at the final canonical-Core boundary.

### 7.2 Binding and substitution

Universe-level variables use the existing Core de Bruijn namespace. An erased
binder `{l : UniverseLevel}` is an ordinary grade-0 `Pi` whose domain is
`{:level_type}`.

A level normal-form atom may therefore contain `{:var, k}` or a neutral
application returning `UniverseLevel`. Every generic Core traversal must descend into
level atoms. In particular:

- shift and substitution;
- free-variable and scope checks;
- occurs checks;
- relevance checks;
- totality closure and global-reference collection;
- serialization and hashing;
- pretty-printing;
- validator and malformed-input rejection;
- macro Core walkers;
- Antigen generation and shrinking.

Treating a level as an inert leaf would permit scope escape and is a soundness
bug.

### 7.3 Core contains no level metas

`?m` exists only in elaborator data structures. Before a declaration enters the
kernel:

- every level meta is assigned;
- every level expression is canonicalized;
- every atom is scope-correct;
- every explicit level term checks at `UniverseLevel`;
- no postponed universe constraint remains.

The kernel rejects, rather than solves, any serialized or directly constructed
Core term containing a meta marker.

This refines the architecture document's phrase "canonical core contains
explicit levels and solved constraints": the canonical term is fully zonked,
so the solutions are embodied by its explicit level expressions. A compiler
artifact may retain the original constraint/solution ledger for auditing and
diagnostics, but the ledger is not a set of assumptions and is never consulted
to make kernel checking succeed. The kernel recomputes every required equality
or inclusion from the explicit term.

## 8. Sorting rules

Write `U(u)` for `{:finite, u}` and `Limit(n)` for `{:omega, n}`. `omega`
remains the internal tag and mathematical name; `TypeLimit` is the
user-facing spelling.

### 8.1 Primitive rules

```text
Gamma |- UniverseLevel : Type(universe_zero)

Gamma |- universe_zero : UniverseLevel
Gamma |- u : UniverseLevel
------------------------
Gamma |- universe_succ(u) : UniverseLevel

Gamma |- u : UniverseLevel    Gamma |- v : UniverseLevel
-----------------------------------------
Gamma |- universe_max(u, v) : UniverseLevel
```

### 8.2 Universe rules

```text
Gamma |- u : UniverseLevel
---------------------------------
Gamma |- Type(u) : Type(universe_succ(u))

---------------------------------------------
Gamma |- TypeLimit(n) : TypeLimit(n + 1)
```

There is deliberately no derivation of either:

```text
Type(u)      : Type(u)
TypeLimit(n) : TypeLimit(n)
```

### 8.3 Join of non-dependent sorts

Define:

```text
join(U(a), U(b))             = U(universe_max(a, b))
join(U(_), Limit(n))         = Limit(n)
join(Limit(n), U(_))         = Limit(n)
join(Limit(m), Limit(n))     = Limit(max(m, n))
```

If the codomain sort does not mention the `Pi` binder, then:

```text
Gamma |- A : sA
Gamma, x:A |- B : sB
x not free in sB
--------------------------------
Gamma |- Pi(x:A).B : join(sA,sB)
```

`Sigma` formation, while represented by the ordinary `Sigma` inductive after
primitive retirement, follows the same level join in its universe-polymorphic
standard-library declaration.

### 8.4 Rigidly level-dependent `Pi`

After normalization, if the bound variable occurs rigidly in the finite level
of the codomain sort, no finite sort is a uniform upper bound:

```text
Gamma |- A : U(a)
Gamma, x:A |- B : U(b(x))
x occurs rigidly in b(x)
--------------------------------
Gamma |- Pi(x:A).B : Limit(0)
```

If the domain already has sort `Limit(n)`, the result is `Limit(n)`.

An occurrence under an unsolved meta is blocked in the elaborator. Checked
Core has no metas, so the kernel sees either a rigid occurrence or none.

This rule principally classifies:

```text
(l : UniverseLevel) -> Type(l) : TypeLimit
```

It is not a general impredicativity rule.

### 8.5 Cumulativity

Sort inclusion is:

```text
U(a)     <= U(b)       iff a <= b
U(a)     <= Limit(n)   always
Limit(m) <= Limit(n)   iff m <= n
Limit(_) <= U(_)       never
```

Cumulativity is identity-only. It inserts no runtime coercion and has no
reduction rule. `Kernel.check` records success only by running the inclusion
decision; the elaborator cannot assert it.

## 9. Universe-level evaluation and conversion

`Eval` evaluates `{:level_value, nf}` by evaluating its atoms in the current
environment:

- a known `{:vlevel, inner}` is flattened into the outer level;
- a neutral value of type `UniverseLevel` remains an atom;
- any non-`UniverseLevel` result is a kernel error, never a fallback atom.

`universe_succ` and `universe_max` reduce through the same primitive-reduction mechanism as
other total primitives. They must reduce only on known `vlevel` arguments and
remain neutral when blocked.

Universe-level atom reduction may delta-unfold only certified definitions, exactly like
ordinary conversion. Universe checking must not create a second evaluator or
bypass totality certification.

Because atom conversion can itself encounter types containing levels, the
mutual recursion between ordinary conversion and level conversion must share
the existing conversion fuel and active-comparison guard. Re-entering the same
atom pair at the same depth is blocked or reported as fuel exhaustion; it must
not recurse without progress.

`Conv` compares `vtype` values using sort-index equality, not cumulativity.
Cumulativity belongs to checking/subsumption; definitional equality does not
identify `Type(a)` with a strictly larger `Type(b)`.

## 10. Elaborator constraints

### 10.1 Meta representation

Universe-level metas are distinct from term metas:

```text
%LevelMeta{id, scope, origin, solution}
```

They cannot be accidentally unified with a term of `Int`, `Nat`, or an
ordinary type.

Every meta records its creation scope. Assignments undergo occurs and scope
checks before installation.

### 10.2 Constraint forms

The elaborator worklist admits only:

```text
EqualLevel(left, right, origin)
LessOrEqualLevel(left, right, origin)
EqualSort(left, right, origin)
LessOrEqualSort(left, right, origin)
HasSort(term, sort_meta, origin)
```

Constraints retain both source spans and a short reason such as
`:universe_argument`, `:pi_formation`, `:constructor_field`, or
`:declared_result_sort`.

### 10.3 Solver order

The solver repeatedly:

1. substitutes existing assignments;
2. normalizes levels;
3. discharges reflexive equality and decidable ordering;
4. assigns an isolated flex meta after occurs/scope checking;
5. decomposes sort equality by sort constructor;
6. accumulates lower bounds `li <= ?m`;
7. assigns `?m := universe_max(l1, ..., ln)` when that least solution satisfies every
   known upper bound;
8. postpones constraints blocked by another unsolved meta;
9. reports no-progress cycles with all participating origins.

The solver must not guess a large closed level and must not search successive
integers as the current declaration elaborator does.

### 10.4 Defaulting

An unconstrained use-site universe-level meta defaults to `universe_zero`. A
meta with lower bounds defaults to their canonical `universe_max`, provided all
upper bounds hold.

Defaulting occurs only at a declaration/application boundary after the
worklist has reached a fixed point. It never occurs inside the kernel.

An unsolved meta that appears in an exported type is an error unless it
corresponds to an explicit `{l : UniverseLevel}` binder. Cure does not silently turn
arbitrary metas into exported universe parameters in this phase.

### 10.5 Use-site inference

When applying a universe-polymorphic definition, the elaborator:

1. creates fresh universe-level metas for omitted grade-0 `UniverseLevel` arguments;
2. substitutes them into later parameter and result types;
3. gathers equality/order constraints while checking explicit arguments;
4. solves/defaults at the application boundary;
5. emits explicit Core applications containing canonical level values.

This is the same insertion path used by other implicit arguments; there is no
special runtime call convention.

## 11. Declarations and inductive families

### 11.1 Family result sort

`Inductive.family.level` becomes `Inductive.family.sort` and stores a
`sort_index`, not an integer.

An explicit `: Type(l)` annotation fixes the finite result sort. An omitted
result sort creates a level meta. Constructor-field constraints determine its
least solution. A constructor-less or fieldless family defaults to
`Type(universe_zero)` unless explicitly annotated otherwise.

The old loop that retries a declaration at levels `0..ceiling` must be deleted.

### 11.2 Constructor field rule

For a family `D : Type(d)`, every constructor field type `A` must itself have a
sort no greater than `Type(d)`:

```text
Gamma |- A : sA       sA <= U(d)
---------------------------------
A is admissible as a field of D
```

For example:

- if `A : Type(l)`, a field `x : A` requires `l <= d`;
- a field `T : Type(l)` stores a type itself and requires
  `universe_succ(l) <= d`.

The same rule extends to limit families using the sort inclusion relation.

### 11.3 Parameters and indices

Parameters and indices may mention level binders and may live in different
universes. Their telescopes are checked normally. The family constant's full
function type may therefore live in `TypeLimit` even when each instance of the
family returns a finite `Type(l)`.

Uniform-parameter checking, positivity, index checking, motive checking, and
coverage must compare the new sort indices through `Core.UniverseLevel` and
`Core.Sort`;
none may project or compare integer levels directly.

### 11.4 Universe-polymorphic standard families

At minimum, the following fixed-level haircuts must be removed:

```text
List       : {l : UniverseLevel} -> Type(l) -> Type(l)
Option     : {l : UniverseLevel} -> Type(l) -> Type(l)
Sigma      : {a b : UniverseLevel} ->
             (A : Type(a)) -> (A -> Type(b)) -> Type(universe_max(a,b))
Equivalent : {l : UniverseLevel} -> (A : Type(l)) -> A -> A -> Type(l)
```

`Result`, tuples, vectors, interfaces/typeclasses, and collection abstractions
must be audited and generalized where their semantics are genuinely uniform.
FFI carriers and operations whose runtime implementation supports only small
data remain explicitly at `Type`.

The migration must not generalize an API merely to make a test pass. A runtime
operation generalized over `Type(l)` must work for every admitted inhabitant or
carry a narrower constraint that says why it is safe.

## 12. `TypeLimit`

### 12.1 Purpose

`TypeLimit` exists solely to sort types whose finite level is unbounded because
it depends rigidly on a quantified `UniverseLevel`, and to close the sort hierarchy
above such types.

It is not:

- a synonym for all types as a runtime collection;
- impredicative;
- a license for `TypeLimit : TypeLimit`;
- polymorphic in another `UniverseLevel`;
- an ordinary data type that can be pattern matched.

### 12.2 No transfinite escalation beyond the declared hierarchy

Cure provides:

```text
TypeLimit0 : TypeLimit1 : TypeLimit2 : ...
```

with closed arbitrary-precision natural indices. It does not provide
`TypeLimit(l)` for `l : UniverseLevel`. This matches Agda's deliberate stopping point
and avoids requiring `Type2Omega`, `Type3Omega`, and so on.

### 12.3 Elimination and data declarations

Data families may be explicitly declared in `TypeLimitN`, but this is not a
back door to store erased levels at runtime. Constructor arguments retain their
ordinary relevance grades, and any argument of type `UniverseLevel` is grade zero.

Large elimination must continue to be governed by the existing motive and
inductive checks. This specification adds sorting capacity; it does not weaken
positivity, coverage, or relevance.

## 13. Erasure and runtime behavior

Every binder whose domain is `UniverseLevel` is forced to grade zero. An explicit
attempt to mark one present is rejected.

The relevance checker permits a level value only in:

- another level expression;
- a `Type(level)` index;
- an erased argument position;
- a type, proof, or compile-time-only declaration position.

It rejects returning a level as a runtime value, pattern matching on it,
placing it in a present constructor field, passing it to a present FFI
argument, or branching runtime behavior on it.

After erasure:

- level binders and arguments are absent;
- `universe_zero`, `universe_succ`, and `universe_max` calls are absent;
- `Type` and `TypeLimit` terms are absent;
- specialization at different levels produces byte-equivalent runtime code
  when all non-level arguments are the same;
- BEAM and AtomVM ABIs do not change.

No backend is allowed to encode a level as an integer merely because the Core
normal form contains integer offsets.

## 14. Trusted computing base

### 14.1 Trusted components

The following are trusted:

- canonical level construction and normalization;
- checking that every level atom has type `UniverseLevel`;
- level equality and ordering;
- sort joining and `piSort` classification;
- universe formation and cumulative checking;
- shifting, substitution, and scope validation inside level atoms;
- family/constructor universe checking;
- canonical serialization validation at the final Core boundary.

### 14.2 Untrusted components

The following remain untrusted conveniences:

- generation and scheduling of level constraints;
- meta assignment heuristics;
- defaulting;
- inferred implicit level insertion;
- declaration-level inference;
- pretty names for level variables;
- error rendering.

Their output is accepted only after the kernel reconstructs and checks the
explicit Core term.

### 14.3 Termination

Universe-level normalization terminates because:

- the maximum-plus canonicalizer is structurally recursive over finite input;
- flattening strictly consumes nested level nodes;
- duplicate elimination decreases or preserves the finite atom set;
- atom evaluation uses the existing fuel/totality-certified conversion path;
- there is no recursion or pattern matching eliminator for `UniverseLevel` itself.

No solver operation may call itself after making no assignment, discharging no
constraint, or reducing no blocker.

### 14.4 Resource safety

Closed levels use arbitrary-precision integers to avoid Agda's historical
machine-`Int` overflow class. Parsers and decoders must still enforce the
repository's normal input-size budgets before constructing an enormous decimal
index.

Canonicalization must deduplicate before performing quadratic atom comparison
where possible. Conversion fuel applies to atom normalization. Error rendering
must truncate huge level expressions without truncating the checked value.

## 15. Serialization, hashing, and compatibility

The Core serialization version must change. The new encoding has distinct tags
for:

- `UniverseLevel` type;
- canonical level value;
- finite sort index;
- omega sort index;
- maximum-plus atom/offset entries.

Decoding an old `{:type, n}` artifact maps it to a finite closed level only in
the compatibility decoder. Re-encoding always writes the new format.

Untrusted decoding rejects:

- negative constants or offsets;
- negative omega indices;
- duplicate or unsorted atoms;
- a nonzero constant subsumed by an atom offset;
- out-of-scope atom terms;
- atom terms that do not check at `UniverseLevel`;
- meta markers;
- unknown sort tags;
- excessively large collections before allocation.

The following hashes/versions must include the universe representation version:

- checked Core artifact hashes;
- totality certificates;
- module interface hashes;
- incremental compilation semantic hashes;
- bundled standard-library artifacts;
- macro quasiquote/Core captures;
- Antigen corpus schema and dedup keys;
- exported type/protobuf schemas.

No cache created under the fixed-ceiling representation may be reused as if it
were checked under this specification.

## 16. Diagnostics

Remove `:universe_ceiling` from newly generated diagnostics. Compatibility
decoders may still name it when explaining an obsolete artifact.

Required structured errors include:

```text
{:invalid_level_term, term, inferred_type}
{:level_occurs_check, meta, level}
{:level_scope_escape, meta, level}
{:universe_mismatch, inferred_sort, expected_sort, origin}
{:unsolved_universe, meta, constraints}
{:cyclic_universe_constraints, metas, constraints}
{:omega_not_below_finite, omega_sort, finite_sort}
{:runtime_relevant_level, binder, use_site}
{:noncanonical_level_encoding, reason}
```

Rendered messages should show both source notation and normalized form when
that distinction explains the failure. For example:

```text
Could not prove universe inclusion
  inferred: Type(universe_succ(a))
  expected: Type(a)
  normalized: max(a + 1) <= max(a)
```

## 17. Migration and compatibility rules

### 17.1 Superseded assumptions

This specification supersedes the fixed-ceiling universe decisions in:

- `2026-06-30-cure-dependent-types-frp-design.md` sections 3 and 4.3;
- `2026-07-09-sigma-retirement-design.md`'s accepted level-0 haircut;
- tests and comments describing `Type2` as the maximum universe;
- Antigen's `:family_ceiling` and `:universe_ceiling` obligations.

Those documents remain historical records for their other decisions.

It implements the direction already required by section 9 of
`2026-07-13-cure-evidential-systems-architecture.md`: zero, successor,
maximum, variables, explicit constraints, inferred surface levels, and
independent kernel checking.

### 17.2 Source compatibility

- bare `Type` continues to mean level zero;
- existing small declarations keep their semantics;
- pretty-printed `Type0`, `Type1`, and `Type2` remain accepted;
- no valid small program gains a runtime argument;
- diagnostics that asserted a ceiling must be updated, not preserved as
  misleading wording.

### 17.3 Core compatibility

During migration only, public constructors may accept integer levels and
immediately canonicalize them. This shim must be deleted once all in-repository
producers use `Core.UniverseLevel.closed/1`.

The final validator rejects integer-level Core so stale walkers or generators
cannot silently survive the migration.

## 18. Mandatory implementation sequence

Each phase is committed separately with a descriptive message. No phase may
declare completion with a documented gap or skipped gate.

### Phase U0 — characterization and inventory

1. Add red characterization tests for arbitrary closed levels, open level
   variables, `universe_max`, universe-polymorphic identity, limit sorting, and
   erasure.
2. Produce a checked inventory of every `{:type, integer}` / `{:vtype,
   integer}` producer and every walker over Core.
3. Freeze current small-program runtime output for later byte comparison.
4. Record the current Antigen universe cells that will be replaced.

Gate: characterization tests fail for the intended missing behavior; existing
suite remains green.

### Phase U1 — canonical level algebra

1. Implement `Cure.Core.UniverseLevel` with canonical construction, equality, ordering,
   substitution, shifting, validation, and printing.
2. Add algebraic property tests and malformed-form tests.
3. Add arbitrary-precision closed-level tests.

Gate: focused UniverseLevel tests and property tests green; no kernel semantics
changed.

### Phase U2 — Core representation migration

1. Add `Core.Sort` finite/limit indices and the new term/value nodes.
2. Update every Core walker fail-closed, including macro and audit walkers.
3. Version serialization and compatibility decoding.
4. Update hashing, final-boundary validation, quote/eval round trips, and
   printers.
5. Remove direct integer comparisons from Core universe paths.

Gate: Core round-trip, scope, substitution, validator, serialization, and
fail-closed walker suites green. The final boundary rejects legacy integer
levels.

### Phase U3 — trusted sorting and cumulativity

1. Implement `UniverseLevel`, `universe_zero`, `universe_succ`, and
   `universe_max` typing/reduction.
2. Implement universe formation, sort join, finite cumulativity, and limit
   cumulativity.
3. Implement dependent `piSort` and rigid dependency detection.
4. Route family, constructor, motive, alias, and global checking through sort
   indices.
5. Remove `Universe.ceiling/0`, the ceiling guard, and all retry-by-integer
   kernel logic.

Gate: focused kernel suite, subject reduction, conversion, inductive
well-formedness, and all universe antibodies green.

### Phase U4 — elaborator constraints and surface syntax

1. Parse and elaborate `UniverseLevel`, universe primitives, `Type(level)`,
   `TypeN`, and `TypeLimitN`.
2. Add scoped level metas and the universe constraint worklist.
3. Infer omitted use-site level implicits.
4. Infer omitted family result levels by least upper bound.
5. Replace declaration retry loops with constraints.
6. Add structured universe diagnostics.

Gate: parser, elaborator, declaration, implicit inference, REPL, and diagnostic
suites green, including cross-module exported universe-polymorphic APIs.

### Phase U5 — standard-library polymorphism

1. Generalize `List`, `Option`, `Result`, tuples, `Sigma`, `Equivalent`, and
   other semantically uniform families.
2. Generalize their functions, interfaces, implementations, derived code, and
   proof helpers.
3. Keep genuinely small/FFI-bound APIs explicitly small.
4. Rebuild bundled standard-library artifacts and verify interface hashes.

Gate: the same `Sigma` and `Equivalent` definitions work over ordinary values,
types, and higher-universe families without duplicate definitions or compiler
special cases.

### Phase U6 — erasure and backend proof

1. Force `UniverseLevel` binders to grade zero.
2. Reject every runtime-relevant level use.
3. Confirm backend IR contains no universe values or operations.
4. Compare frozen runtime output for existing small programs.
5. Run Unix BEAM and AtomVM-relevant compilation gates.

Gate: specialization at different universe levels emits byte-equivalent runtime
behavior modulo existing nondeterministic artifact metadata; no level symbol or
payload survives in emitted code.

### Phase U7 — Antigen and final hardening

1. Replace ceiling generators with polymorphic and adversarial level generators.
2. Add shrinking for maximum-plus levels without producing noncanonical Core.
3. Add antibodies for Type-in-Type, limit-in-limit, level occurs checks, scope
   escape, malformed serialization, false cumulativity, and missed traversal.
4. Migrate corpus schema and regenerate seeds intentionally.
5. Update historical docs/comments that claim the ceiling is current.

Sequential final gate:

1. `mix test test/cure/core/`
2. `mix test test/cure/elab/`
3. `mix test test/antigen/`
4. `mix test`
5. `mix cure.check.examples`
6. `mix cure.check.stdlib`
7. `mix test test/oracle_replay_test.exs`
8. repository clean except for the intended committed artifacts

## 19. Required verification matrix

### 19.1 Universe-level algebra

- commutativity, associativity, and idempotence of `universe_max`;
- zero neutrality;
- successor distribution over maximum;
- subsumption of `a` by `universe_succ(a)`;
- canonical duplicate removal;
- substitution followed by normalization;
- shifting under nested grade-0 binders;
- arbitrary-precision constants;
- deterministic serialization ordering.

### 19.2 Kernel positives

- `Type(a) : Type(universe_succ(a))` for an open level variable;
- `Type37 : Type38` without constructing 38 successor nodes;
- `Type(a)` accepted at `Type(universe_max(a,b))`;
- `Pi(A:Type(a)).Type(b)` sorted at the correct finite maximum when
  non-dependent;
- `(l:UniverseLevel) -> Type(l)` sorted at `TypeLimit`;
- finite sorts accepted below every `TypeLimitN`;
- limit cumulativity by closed index;
- universe-polymorphic `List`, `Sigma`, and `Equivalent`;
- use-site inference chooses levels from explicit value/type arguments;
- constructor fields determine the least admissible family level.

### 19.3 Kernel negatives

- `Type(a)` rejected at `Type(a)`;
- `TypeLimitN` rejected at itself;
- `TypeLimitN` rejected below every finite sort;
- unrelated open levels do not compare merely because both are variables;
- `a + 1 <= a` rejected;
- a non-`UniverseLevel` term rejected as a `Type` index;
- out-of-scope level atom rejected;
- noncanonical serialized level rejected;
- level meta marker rejected at Core boundary;
- constructor field whose sort exceeds the family sort rejected;
- an uncertified function in a level atom never unfolds during conversion.

### 19.4 Elaborator

- inferred erased level arguments are explicit in Core;
- named explicit level arguments work;
- ambiguous unconstrained use-site levels default to zero;
- lower bounds solve to their `universe_max`;
- incompatible upper/lower bounds report their origins;
- occurs and scope checks report stable errors;
- exported signatures contain no metas;
- cross-module imports preserve level binders and sort indices;
- aliases and typeclasses do not drop universe parameters.

### 19.5 Erasure and targets

- no level binder changes runtime arity;
- no level value appears in CureIR or backend AST;
- BEAM behavior is identical across universe instantiations;
- AtomVM compilation accepts generalized standard-library code;
- macros may construct universe-polymorphic syntax but leave no runtime macro or
  level dispatcher.

### 19.6 Antigen sensitivity

Weak-kernel mutations must be caught for at least:

- accepting `Type(a) : Type(a)`;
- treating every pair of levels as equal;
- treating every pair of levels as ordered;
- skipping atom scope validation;
- omitting level substitution under `Type`;
- accepting a limit sort below finite;
- accepting malformed/noncanonical level encodings;
- trusting an elaborator-supplied sort without reconstruction.

## 20. Non-goals

This specification does not add:

- impredicative `Prop`;
- proof irrelevance;
- cubical universes;
- higher inductive types;
- resizing axioms;
- quotient universes;
- runtime type reflection;
- user-defined universe rewrite axioms;
- heterogeneous equality beyond what universe-polymorphic `Equivalent` already
  expresses at one carrier level;
- automatic inference that a runtime FFI operation is safe at every universe;
- compatibility with intentionally inconsistent `Type : Type` programs.

## 21. Completion criteria

The universe-polymorphism work is complete only when all of the following hold:

1. No semantic universe ceiling remains in Core, elaboration, declarations,
   validation, Antigen, or documentation describing current behavior.
2. `Type : Type` and `TypeLimit : TypeLimit` remain unrepresentable as checked
   derivations.
3. A single source definition of `List`, `Sigma`, and `Equivalent` works at
   arbitrary finite levels.
4. Explicit level binders and inferred use-site level arguments work across
   module boundaries and serialized interfaces.
5. Rigid level dependency is classified in `TypeLimit`.
6. Checked Core contains explicit canonical levels and no metas.
7. The kernel independently reconstructs every universe judgment.
8. All level information is erased with no runtime ABI or behavioral cost.
9. Antigen catches weakened equality, ordering, scope, substitution, limit, and
   serialization rules.
10. Every phase gate and the sequential final gate pass, and the implementation
    is committed phase by phase as required by `AGENTS.md`.

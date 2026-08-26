# Compile-time Typeclasses — Design

**Status:** design approved (operator, 2026-07-10). Scope: migrate ALL existing
proto/impl modules. This document is the source of truth for the elaboration
strategy; the surface was locked in prior decisions (see Non-Goals §9).

**Task:** #21 (K). Prerequisite that unblocks char-literal patterns (#25),
string-literal patterns (#27), and `Std.String` (#29), all of which want value
equality through the resulting `Equatable` interface.

---

## 1. Goal

Replace Cure's **runtime `proto`/`impl` protocol dispatch** with **compile-time
typeclasses** elaborated entirely in the dependent pipeline (`lib/cure/elab/*` +
`lib/cure/core/*`). Interfaces become Core record types, implementations become
dictionary values, and instance selection is resolved by the elaborator at
compile time — statically inlined at concrete call sites, threaded as an implicit
dictionary parameter through polymorphic code. The polymorphic structural
equality primitive `struct_eq`/`struct_ne` is retired in favour of a real
`Equatable` interface.

**Success criterion:** every existing stdlib `proto`/`impl` module —
**`Equatable`, `Ord`, `Show`, `Functor`, `Access`** (verified by grep: 6, 4, 6,
2, 3 `proto`/`impl` declarations respectively) — is rewritten to
`interface`/`implementation`, elaborates through the dependent pipeline, and its
methods resolve and run correctly; `struct_eq` and the 4-way `==` dispatch are
gone; the full suite is green. **`Equivalent` and `JSON` are NOT proto/impl
modules and are out of scope** (correction found during review — both have
zero `proto`/`impl` declarations today): `Std.Equivalent` is the propositional
identity type (`@builtin(:eq)`, a GADT-indexed inductive, not a
dictionary-dispatched protocol — its own doc comment distinguishes it from
`Equatable` for exactly this reason); `Std.Json` is an ADT plus `@extern` FFI
calls with no protocol at all. Neither has anything for this design to
rewrite; see §5.

## 2. Locked surface (restated, not re-litigated)

From prior operator decisions (memory `typeclass-surface-decisions`):

- Keywords **`interface`** / **`implementation`** (Idris2 pairing),
  indentation-based blocks, **no `end`** terminator.
- **Coherence = global uniqueness + named implementations.** At most one
  anonymous instance per `(interface, head type)` globally; additional instances
  must be *named* and are selected explicitly.
- **Deriving approved**, decl-attached clause is the default form
  (`type Color = R | G | B deriving Equatable`), plus a standalone
  `derive Equatable for Color` form.

This design does NOT revisit keyword choice, block syntax, or the coherence
policy. It settles only *how these lower into Core*.

## 3. Elaboration strategy (the core of this design)

### 3.1 Interfaces are Core record types

`interface Equatable(a)` with methods `eq`, `ne` elaborates to a **dependent
record type** (the same Core machinery as `Std.Pair`/dependent records, memory
`dependent-records-finding`), parameterised by the interface variable(s):

```
Equatable : Π(a : Type). Type
Equatable(a) ≙ record { eq : a → a → Bool, ne : a → a → Bool }
```

- The interface head variable carries an **inferred kind**, determined by how it
  is used in the method signatures:
  - When the head appears **as a type** (applied to nothing) — e.g. `Equatable(a)`
    with `eq : a → a → Bool` — its kind is `Type`. The interface type former is
    `Equatable : Π(a : Type). Type`.
  - When the head appears **applied to a type** — e.g. `Functor(f)` with
    `map : (a → b) → f(a) → f(b)` — its kind is **`Type → Type`**, a genuine
    higher-kinded head. The interface type former is
    `Functor : Π(f : Type → Type). Type`, and
    `Functor(f) ≙ record { fmap : Π{a b : Type}. (a → b) → f(a) → f(b) }`.

  **`Functor` is elaborated as true HKT** (`f : Type → Type`), NOT the degenerate
  `g : Type` shape the old `proto Functor(g)` used — that shape returned the same
  opaque container `g` and could not even express that `fmap` changes the element
  type from `a` to `b`. Correcting it to real HKT is a faithful-to-Idris2
  requirement of this design, not a later extension (§8 defers only kinds *beyond*
  single-argument `Type → Type`). The head's kind is inferred by the elaborator
  from the method signatures (Idris2's rule: `f a` forces `f : Type → Type`); an
  interface whose head is used inconsistently (both `a` and `a(x)`) is a hard
  error `{:inconsistent_head_kind, iface}`.
- Method signatures with free type variables beyond the interface head (e.g.
  `fmap`'s `a`, `b`) are elaborated as **implicit-generalised** method fields:
  the record field type is a Π over those extra variables. This is ordinary
  auto-generalisation, already supported by the elaborator.
- A method whose body is defined in the interface (a *default method*, e.g.
  `Equatable`'s `ne` derived from `eq`) is stored as a **default** used when an
  implementation omits it (§3.3).

### 3.2 Implementations are dictionary values

`implementation Equatable for Int` elaborates to a **record value** (dictionary)
of type `Equatable(Int)`:

```
equatable_Int : Equatable(Int) ≙ record { eq = int_eq, ne = <default ne applied to int_eq> }
```

- The dictionary is registered in a new **coherence table** (§3.4), keyed by
  `(interface_id, head_type_id)` = `(Equatable, Int)`.
- Each method field takes its body from the implementation's method clause;
  omitted methods fall back to the interface's default method (§3.1), specialised
  to this instance.
- A **named** implementation (`implementation Equatable for Int as strictInt`)
  is registered under its name, NOT in the anonymous coherence slot, and never
  participates in automatic resolution — it is referenced explicitly.

### 3.3 Default methods

An interface may supply a default body for a method (`Equatable.ne` is
`pickup eq(a,b) -> false else -> true`). When an implementation omits that
method, the dictionary field is filled by the default body **closed over the
instance's other methods** (so the default `ne` calls *this* instance's `eq`).
Implementations may override the default by providing their own clause.

### 3.4 Coherence table + resolution

A new elaborator-scoped registry: `interface_id → head_type_id → dictionary_ref`
(anonymous instances) plus `name → dictionary_ref` (named instances). It lives
alongside the existing `Inductive`/builtin registries in the signature/env so it
survives across module boundaries (imports contribute their instances).

**Global uniqueness:** registering a second anonymous instance for an existing
`(interface, head type)` is a hard error `{:overlapping_instance, iface, head}`.
An anonymous instance whose head type is defined in *another* module than both
the interface and the instance is an `{:orphan_instance, …}` error (Rust/Haskell
orphan rule; enforced at registration). **Builtin/primitive head types**
(`Int`, `Float`, `Bool`, `String`, `Atom` — none of which has a defining
module) are exempt from the module-triangulation check by construction: the
comparison only fires between two *user* modules, so a moduleless head type
never triggers `{:orphan_instance, …}`. This is not a corner case — it is the
common path: every stdlib primitive `Equatable` implementation (§5) has
`interface_module == instance_module == Std.Equatable` and a moduleless head
type, and must register cleanly.

**Resolution** at a method-call site `m(args...)` where `m` is an interface
method. First recover the **head key** — the type constructor the instance is
selected by — from the type of the method's interface-head argument position:

- **Kind-`Type` interface** (`Equatable`, `Ord`, `Show`, `Access`): the head
  argument's type `T` (for `eq(x,y)`, the type of `x`) is itself the head; the
  key is `T`'s head type constructor.
- **Higher-kinded interface** (`Functor`, head `f : Type → Type`): the head
  argument's type has the shape `f(a)` in the method signature, so the key is
  extracted by **pattern-fragment unification** — solve `?f(?a) =?= T` where `?f`
  is a metavariable of kind `Type → Type` applied to a distinct rigid `?a`. For
  `fmap(xs, g)` with `xs : List(Int)`, this yields `?f := List`, `?a := Int`; the
  key is the constructor `List`. This is the decidable Miller pattern fragment
  (Cure already solves index metavariables this way — memories
  `deferred-domain-metavar-finding`, `return-type-flow-finding`); a `T` that is
  not of the form `C(_)` for a known constructor `C` (e.g. a bare `Int` where a
  `Type → Type` head was expected) is `{:no_instance, iface, T}`.

Then, with the head key in hand:
1. **Concrete key** (a known type constructor with a registered anonymous
   instance): resolve to that dictionary and **project + inline the method
   statically** — `eq(x,y)` on `Int` becomes exactly `int_eq(x,y)`, and
   `fmap(xs,g)` on `List` becomes exactly the `List` implementation's body, with
   **no dictionary value at runtime**. This generalises today's type-directed
   `==`/`fmap` dispatch.
2. **Abstract key** (the key is a rigid type variable in scope under a constraint
   — `Equatable(a)`, or `Functor(f)` with `f` a rigid `Type → Type` variable):
   the constraint introduced an **implicit dictionary parameter**, written `dict`
   below (full internal name `dict_<Iface>_<headvar>`, disambiguating multiple
   in-scope constraints by interface and head variable) — `dict : Equatable(a)`.
   The method call **projects from that parameter** — `eq(x,y)` becomes
   `dict.eq x y`.
3. **No instance found** and no constraint in scope: hard error
   `{:no_instance, iface, T}`.
5. **Named instance, explicit reference:** a named implementation
   (`implementation Equatable for Int as strictInt`) is registered under its
   name as an ordinary dictionary-valued binding (§3.2) — no new call syntax is
   needed. A caller selects it explicitly with plain record projection,
   `strictInt.eq(x, y)`, exactly as it would project a field from any other
   record value. This is the only way a named instance is ever used; it never
   participates in steps 2-3's automatic resolution.

### 3.5 Constraints as implicit dictionary parameters

A constrained signature is written with Cure's contextual `requires` clause,
which comes **after** the return type —
`fn f{a: Type}(x: a) -> Bool requires Equatable(a) = …` (parsed by
`parse_constraint_list`/`parse_single_constraint`, `parser.ex` ~2345-2354 /
~4505-4536, into a `{:function_call, [constraint: true], [a]}` AST node).
Constraint-position `where` is retained temporarily as a deprecated migration
spelling; `where` now denotes function-local definitions. Elaborating the
`requires` clause introduces an
**implicit parameter** `{dict : Equatable(a)}` immediately after the type
parameter `a`.

**Quantity is NOT free.** The ordinary implicit-param path
(`declarations.ex:567`, `q = if implicit, do: :erased, else: :present`)
unconditionally assigns quantity `:erased` to every `{...}` parameter, and
`Cure.Elab.Relevance` (M8.3) is a pure validator — it *rejects* relevant use of
an erased binder, it never promotes one to `:present` (locked, memory
`erasure-relevance-check-decision`: "do NOT auto-promote"). A constraint-
introduced dict parameter therefore needs its own, separate quantity
assignment, distinct from the generic implicit-param default:

- A constraint-introduced dict parameter is elaborated with its body
  *optimistically* at quantity `:present` (ω) — the opposite default from the
  generic `declarations.ex:567` implicit-param path, which is
  `:erased`-always. `:present` never causes a false `Relevance.check`
  rejection (a present binder tolerates any use), so the body always
  elaborates and kernel-checks cleanly regardless of whether it ends up using
  the dictionary.
- **After** elaboration, a lightweight occurs-check over the resulting Core
  body asks whether the dict binder appears at all. If it never occurs,
  the quantity is retroactively demoted to `:erased` (0); otherwise it stays
  `:present` (ω). This is a one-way, safe **demotion** (present → erased only
  when provably unused), never a **promotion** (erased → present) — so it
  does not conflict with the locked "do NOT auto-promote" discipline (memory
  `erasure-relevance-check-decision`), which is specifically about not
  rescuing an erased binder that turns out to be used, not about avoiding a
  safe downgrade of an unused present one.
- `Relevance.check` still runs as the general soundness backstop on the final
  quantity assignment, exactly as it does for every other def — it can only
  ever confirm the demotion was safe (an erased binder that occurs would be a
  contradiction, since the occurs-check that produced `:erased` already
  proved no occurrence).

Calls to constrained functions pass the resolved dictionary implicitly
(resolution §3.4 applied at the call's concrete type argument).

### 3.6 Deriving

`deriving Equatable` (decl-attached) or `derive Equatable for T` (standalone)
generates an `implementation Equatable for T` whose method is a **structural
recursive equality**:

- For each constructor pair, `eq` matches both scrutinees; equal constructors
  compare fields pairwise via **each field's own `Equatable`** (recursively
  resolved — enabling `deriving` on recursive/nested types); different
  constructors give `false`.
- First-order data (no function-typed fields) MAY emit to BEAM `==` as an
  optimisation, but the *semantics* are the generated structural eq (this is the
  law-abiding replacement for `struct_eq`'s "compare erased representations").
- `deriving Ord` / `deriving Show` are generated analogously (lexicographic
  constructor-then-field order for `Ord`; constructor-name + field rendering for
  `Show`). Deriving is available for all three of `Equatable`, `Ord`, `Show`.

## 4. The `==`/`struct_eq` reconciliation

### 4.1 Torn out

- `struct_eq`/`struct_ne` builtin-op globals: `builtins.ex` `@struct_ops` and
  their body-less-def seeding; `normalise.ex` `builtin_op_fold` struct_eq/ne
  arm; `emit.ex` `lower_builtin_op` + `builtin_op_wrapper` struct_eq/ne arms;
  `guard_lint.ex` struct_eq/ne handling.
- The 4-way `==`/`!=` dispatch in `elaborator.ex` `build_binop`
  (`:bool→eq`, `:int→int_eq`, `:float→float_eq`, `:error→struct_eq`): the
  `:error` (structural) arm is **deleted**. `==`/`!=` on ANY type now resolve via
  `Equatable`/coherence (§3.4). The primitive arms are subsumed: on `Int`,
  resolution finds `equatable_Int` and inlines `int_eq` — same emitted code as
  today, reached through the interface instead of a hardcoded switch.
- **Pre-existing tests that assert struct_eq/struct_ne behaviour directly**
  must be deleted or rewritten as part of this tear-out, not left to fail
  incidentally: `test/cure/core/builtin_op_test.exs`'s "Amendment A1:
  struct_eq/struct_ne" describe block (types-as-Pi, folds-on-literals,
  stays-neutral-on-ctors, R1 user-registered-shadow pin) and
  `test/cure/elab/binop_lowering_test.exs`'s two tests asserting ADT `==`/`!=`
  lower to a `struct_eq`/`struct_ne` spine. These assert the retiring feature's
  own contract, so removing/replacing them is the correct action (not
  test-weakening) — each is replaced by the equivalent `Equatable`-resolution
  behavioural test named in §6.

### 4.2 Repointed (kept)

`int_eq`, `float_eq`, `eq` (Bool) stay as builtin-op globals and become the
**method bodies of the primitive `Equatable` implementations**. **Circularity
fix (found during design):** the current `impl Equatable for Int` body is
literally `a == b`; once `==` *is* `Equatable.eq` that is infinite regress. The
migrated primitive implementations must therefore reference the **primitive
builtin-op directly** (`int_eq(a,b)`, not `a == b`).

**Correction: no `string_eq`/`atom_eq` builtin-op exists to repoint.**
`primitive_scrut_kind/2` (`elaborator.ex` ~2822-2829) recognises only
`{:vint_type}`, `{:vfloat_type}`, and Bool's `{:vdata, …}` — there is no
String or Atom arm, and `builtins.ex` defines no `string_eq`/`atom_eq` global
(confirmed absent by search). Today, `String`/`Atom` `==` falls through
`build_binop`'s `:error` branch to the generic `struct_eq`/`struct_ne` spine —
the exact mechanism §4.1 tears out. So `String`/`Atom` are NOT a repoint like
`Int`/`Float`/`Bool`; they need one of:
(a) new `string_eq`/`atom_eq` builtin-op globals seeded alongside `int_eq`/
`float_eq` (mirrors the existing pattern, becomes the new primitive
`Equatable` bodies), or
(b) their `Equatable` impl bodies emit directly to BEAM `==` as a primitive
special case (no named builtin-op global), matching how §3.6 already allows
first-order derived instances to emit to BEAM `==` as an optimisation.
Either is a legitimate, mechanical choice, but the spec must pick one before
migration — this is the *second* non-mechanical item in the stdlib migration,
alongside the circularity fix above (§5.1's "primitive impls reference
builtin-ops directly" undersells this: for `String`/`Atom` there is no
existing builtin-op to reference).

### 4.3 `Ord` comparison operators

`<`, `<=`, `>`, `>=` currently dispatch to `int_*`/`float_*` in `build_binop`.
These are similarly re-expressed as `Ord` method resolution, with the primitive
`int_lt`/… repointed as the primitive `Ord` implementations' method bodies.
Non-`Ord` operand types now error via `{:no_instance, Ord, T}` instead of the
current `{:unsupported_operand_type, _}`.

**`Ordering` needs its own `Equatable` instance.** `Std.Ord`'s own derived
helpers (`lt`/`le`/`gt`/`ge`, `ord.cure:57-66`) are defined as
`compare(a,b) == LessThan()` / `!= GreaterThan()` — i.e. they use `==`/`!=` on
the `Ordering` ADT that `Std.Ord` itself declares. Migrating `Ord` therefore
also requires `Ordering` to carry a (derived) `Equatable` instance
(`type Ordering = LessThan | EqualTo | GreaterThan deriving Equatable`);
without it, `lt`/`le`/`gt`/`ge` break with `{:no_instance, Equatable,
Ordering}` the moment `==`/`!=` retire. This is scope for §5's `Ord` item, not
an incidental side effect to discover later.

## 5. Migration of the 5 stdlib protocol modules

Rewrite each from `proto`/`impl` to `interface`/`implementation`. (`Equivalent`
and `JSON` are dropped from this list — see §1's correction: neither has any
`proto`/`impl` to rewrite.)

1. **Equatable** — primitive impls reference builtin-ops directly (§4.2);
   `ne` default method; `String`/`Atom` need a new primitive builtin-op or a
   BEAM-`==` special case, not a repoint (§4.2 correction).
2. **Ord** — repoint `int_*`/`float_*` comparisons (§4.3); `Ordering` itself
   needs a derived `Equatable` instance for `Ord`'s own `lt`/`le`/`gt`/`ge`
   helpers (§4.3 correction).
3. **Show** — `show : a → String`; primitive impls; deriving.
4. **Functor** — corrected to **true HKT** (§3.1): the head becomes
   `f : Type → Type` and the method
   `fmap : {a b} → (container: f(a), g: a → b) → f(b)` (element type changes
   `a → b`), NOT the old degenerate `Functor(g)` with `g : Type` that returned an
   opaque same-typed container. The `List` implementation is
   `implementation Functor for List` with
   `fmap({a},{b}, container: List(a), g: a → b) -> List(b) = Std.List.map(container, g)`.
   Existing call sites (`fmap([1,2,3], fn x -> x + 10)`) keep working: resolution
   extracts `f := List`, `a := Int` from the container's type `List(Int)` by
   pattern-fragment unification (§3.4). Preserve the current argument order
   (`fmap(container, g)`) and the `fmap` method name so callers are unchanged.
5. **Access** — mechanical surface rewrite; verify resolution. Note the
   `Any`-typed `==`/`!=` uses inside its keyword-list helpers (§7 risk) may
   make this module a documented blocker rather than a clean rewrite.

Each migrated module must elaborate through the **dependent** pipeline cleanly.
Where a module is not yet dependent-clean (memory `value-surface-parity-program`
notes most stdlib still leans on classic Codegen), making its interface/impl
elaborate is in scope; making unrelated value code dependent-clean is NOT — if a
module cannot elaborate for reasons unrelated to typeclasses, that is a
documented blocker, not silently worked around.

**Old `proto`/`impl` keywords:** left in the lexer/parser as now-unreachable
classic-pipeline surface (their removal belongs to #18, the classic-pathway
rip-out). No stdlib module uses them after migration.

## 6. Testing strategy

Strict red-green TDD throughout: write the failing test for a behaviour
before the implementation code that satisfies it, then write only enough to
turn it green. Behavioural tests (elaborate real `.cure` source, assert Core
shape and/or run the emitted BEAM), not implementation-coupled. **Tests are
immutable once green**: a test only changes if it is itself proven wrong
(stated and justified before editing it) — going green is always achieved by
fixing implementation code, never by loosening or deleting a test. The one
documented exception is §4.1's tear-out of the two pre-existing struct_eq/
struct_ne tests, which is not a weakening: it removes tests of a feature this
design deliberately retires, each replaced by an equivalent behavioural test
below. Coverage:

- **Parse:** `interface`/`implementation` (anonymous + named + deriving) produce
  the expected AST nodes; a red parser test first.
- **Interface → record type:** elaborating an interface registers a record type
  of the right field shape.
- **Implementation → dictionary:** registers a dictionary; duplicate anonymous
  instance ⇒ `{:overlapping_instance}`; orphan ⇒ `{:orphan_instance}`; a
  primitive impl (moduleless head type, e.g. `Equatable for Int`) registered
  in the interface's own module does NOT falsely trigger `{:orphan_instance}`
  (§3.4's builtin exemption).
- **Concrete resolution:** `eq(1,2)` elaborates to the inlined `int_eq` spine
  (no dictionary), runs to `false`.
- **Abstract resolution:** a constrained polymorphic `fn` projects the method
  from its implicit dictionary parameter; runs correctly for two different
  instances.
- **Higher-kinded resolution (Functor):** `fmap(xs, g)` with `xs : List(Int)`
  resolves by extracting `f := List` from `List(Int)` via pattern-fragment
  unification (§3.4), inlines the `List` implementation, and runs
  (`fmap([1,2,3], fn x -> x + 10)` ⇒ `[11,12,13]`); the element type genuinely
  changes (`fmap([1,2,3], fn x -> x > 1) : List(Bool)` typechecks and runs). A
  `Functor` method applied to a non-`_( _ )` type (e.g. a bare `Int`) is
  `{:no_instance, Functor, Int}`, not a crash.
- **Named-instance selection:** a named implementation is never chosen by
  automatic resolution (an unqualified call still resolves to the anonymous
  instance, or errors if none exists); explicit projection off the named
  binding (`strictInt.eq(x, y)`) runs the named instance's method.
- **Erasure:** a constrained `fn` that never calls a method erases the
  dictionary (quantity 0); one that does keeps it (quantity ω).
- **Default method:** an implementation omitting `ne` gets the default closed
  over its `eq`.
- **Deriving:** `deriving Equatable`/`Ord`/`Show` on a recursive ADT generates a
  working structural instance; a nested/recursive value compares/renders
  correctly.
- **`==` retirement:** `struct_eq`/`struct_ne` no longer seeded (assert absent);
  `==` on an ADT with a derived instance works; `==` on a type with NO instance
  is `{:no_instance, …}` (behavioural change from struct_eq's accept-anything).
- **End-to-end:** each migrated stdlib module compiles + its methods run.
- **Differential oracle (cure-porting):** a `typeclass` oracle cluster with
  paired `.cure`/`.idr` interface/implementation programs, verifying Cure's
  acceptance/rejection matches Idris2 for resolution, coherence, and deriving.

## 7. Risks

- **Blast radius of `==` retirement.** Every `==`/`!=` in the codebase and tests
  currently relying on struct_eq's accept-anything behaviour may change verdict
  (a no-instance type now errors). Mitigation: primitive types keep identical
  emitted code; ADTs used with `==` in tests get derived instances; run the full
  suite and triage each newly-failing `==` site (real regression vs. a type that
  legitimately now needs a derived instance). **A structurally distinct case:
  `==`/`!=` on statically `Any`-typed operands** (e.g. `lib/std/access.cure:532`,
  `kw_fetch`'s `k == key` where both are `Any`). §3.4's resolution has no rule
  for this at all — `Any` is neither a concrete head with a registered instance
  nor a rigid type variable under a constraint, so this isn't even a clean
  `{:no_instance, Equatable, T}` (there is no single `T`). Any dependent-clean
  module using `==`/`!=` on `Any` (a common idiom) hits this. Out of scope to
  solve here (§5's blocker rule covers it: such a module's migration is a
  documented blocker until it is), but it must be surfaced explicitly rather
  than assumed to fall out of the "type gets a derived instance" mitigation
  above, which does not apply when there is no static type to derive one for.
- **Higher-kinded resolution (Functor).** Extracting the type constructor from
  `f(a) =?= List(Int)` requires higher-order unification, which is undecidable in
  general. Mitigation: restrict to the **Miller pattern fragment** (`?f` a
  metavariable applied to *distinct rigid* arguments) — decidable, and the only
  shape a well-formed `Functor` method argument (`f(a)`) can take. Anything
  outside the fragment is `{:no_instance, …}`, never a divergent solve. Cure
  already solves index metavariables in this fragment (memories
  `deferred-domain-metavar-finding`, `return-type-flow-finding`); this reuses
  that machinery rather than adding a general HO-unifier. If the existing
  unifier cannot be reused for the `Type → Type` head case without a kernel
  change, that is a HARD-STOP-and-review (see TCB surface below), not an ad-hoc
  elaborator hack.
- **Resolution non-termination.** Recursive deriving (`eq` on a recursive type
  calling `eq` on its own sub-values) must resolve to the *same* instance, not
  loop in the resolver. Mitigation: resolution memoises `(interface, head)` and
  the generated recursive method refers to itself by name. **This handles only
  self-recursion** (a type whose own derived instance calls itself); it does
  NOT by itself handle **mutual recursion** — two or more types, each deriving
  an instance whose method calls the other's (e.g. mutually-recursive ADTs
  `A`/`B`). None of the 5 stdlib modules in §5 requires this for v1, but the
  deriving facility (§3.6) is general, not scoped to self-recursive types
  only. Mitigation: mutually-recursive deriving requests in the same
  elaboration batch must be registered in two passes — forward-declare all
  participating instances' dictionary *signatures* first (so each generated
  body can resolve the others by name), then fill in bodies — mirroring how
  mutually-recursive function groups already elaborate. If this two-pass
  registration isn't implemented for v1, that is an explicit, documented
  scope cut here (mutual recursion in deriving deferred), not a silent gap.
- **Stdlib not dependent-clean.** Some of the 5 modules may not elaborate
  through the dependent pipeline for unrelated reasons. Mitigation: §5's blocker
  rule — surface it, do not paper over it. If a module is blocked, its migration
  is deferred with a written reason and the run continues with the rest.
- **Import-order / global coherence coupling** (flagged at `program.ex:224`).
  The coherence table must aggregate instances across imported modules
  deterministically. Mitigation: instances registered at elaboration in import
  order; overlap check is order-independent (any two anonymous instances for the
  same key collide regardless of order).
- **TCB surface.** Dictionaries reuse existing dependent-record Core; no new
  kernel node is anticipated. If resolution/erasure turns out to need a kernel
  change, that is a HARD-STOP-and-review per the porting charter, gated by the
  full Antigen + test suite (memory `tcb-change-blanket-approval` pre-approves
  Agda/Lean-aligned kernel changes but still requires the full gate).

## 8. Later extensions (explicitly out of scope for v1)

- Interface heads of kind **beyond single-argument `Type → Type`** —
  multi-argument type constructors (`Bifunctor`, `f : Type → Type → Type`) and
  higher-order kinds. **Single-argument `Type → Type` HKT (`Functor`) IS in v1**
  (§3.1) — it is a faithfulness requirement, not deferred.
- Superclass/interface inheritance, multi-parameter interfaces, functional
  dependencies, and compile-time instance selection (v1 threads runtime
  dictionaries at abstract sites; specialisation is a perf optimisation later).

## 9. Non-goals

- Re-litigating the locked surface (§2).
- Removing the classic `proto`/`impl` parser/runtime (that is #18).
- Making unrelated stdlib value code dependent-clean (only interface/impl
  elaboration is in scope).
- SMT/refinement interactions (refinements are removed, memory
  `smt-trust-boundary-decision`).

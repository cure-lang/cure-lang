# Anonymous ADTs (`Int | String`) — Design

**Date:** 2026-07-11
**Status:** Approved (design gate passed)
**Scope:** Surface + elaborator + emit. **Zero TCB change.**

## 1. Motivation

Three distinct needs, all served by the same feature:

1. **Ergonomics.** `fn parse(s: String) -> Int | String` should read the way it does
   in a spec language, without forcing the author to declare a named ADT.
2. **FFI honesty.** Erlang boundaries genuinely return heterogeneous values. Typing
   them should not require inventing a named ADT per call site.
3. **Throwaway heterogeneity (the strongest reason).** Putting three unrelated types
   into a `Map` today requires declaring a public ADT that exists only to be a
   container tag, is never used again, and pollutes the module's namespace.

## 2. Constraints discovered before design

These are facts about the current tree, verified, with citations. They are what make
the design come out the way it does.

- **`|` in type-*expression* position is unclaimed grammar.** `parse_type_expr/1`
  (`lib/cure/compiler/parser.ex:4681`) never peeks for `:bar`. `|` is consumed only
  inside a `type … = …` *declaration body* (`parser.ex:3293-3344`), where it separates
  named constructors.
- **The kernel cannot express anonymous sums.** The Core term taxonomy is closed
  (`lib/cure/core/term.ex:60-81`): the only sum is a *named* inductive
  (`{:data}` / `{:ctor}` / `{:case}`).
- **The kernel has no value-level subtyping.** Its only subtyping is universe
  cumulativity (`lib/cure/core/kernel.ex:1474-1506`); everything else is definitional
  conversion via NbE.
- **`believe_me` / opaque `Any` were deliberately deleted** (2026-07-11) as "a
  proliferation of unchecked casts that fought the type system"
  (`test/cure/stdlib/dependent_elaboration_parity_test.exs:17-21`). This design must
  not reintroduce them.
- **Indices may be arbitrary terms.** `{:data, name, params, indices}` places no sort
  restriction on indices (`term.ex:67`, `term.ex:107-108`), and the kernel accepts
  literal indices — `test/cure/core/k6_param_ctor_infer_test.exs:19` synthesizes
  `Equivalent(Int, 3, 3)` from `{:int_lit, 3}`. `Std.Char` is
  `typealias Char = Bounded(1114112)` (`lib/std/char.cure:17`), a literal in an index
  slot, shipping today. *This design does not need that capability, but it establishes
  that literals in type position are not exotic.*
- **Dependent ctor erasure:** nullary constructor → bare atom; n-ary → tagged tuple of
  present fields (`lib/cure/elab/emit.ex:12-14`).
- **Cross-module remote references already work** — `Program.import_origins/1` threaded
  into `Emit.compile_forms/4` (commit `87f6755`).

## 3. Rejected alternatives

### 3.1 Untagged (TypeScript-style) unions — REJECTED as impossible

An untagged union is a refinement of the raw value: nothing is boxed, and `match`
compiles to runtime type tests. Cure cannot do this, for two independent reasons.

**Discrimination is undecidable on the erased representation.** Per locked decisions,
`String` **is** `List(Char)`, so `String | List(Int)` are both Erlang lists and cannot
be told apart at runtime. `Nat | Int` both erase to Erlang integers.
`Char` is `Bounded`, which `emit.ex` erases to an integer, so an `Int` and a `Char` can
erase to the same Erlang term.

**The coercion is unsound.** An identity coercion `Int ⟶ Int | String` requires the
kernel to accept a term of type `Int` at type `Union(…)`. That means either kernel
subtyping (does not exist) or a postulated cast — i.e. reintroducing `believe_me`,
deleted this morning by deliberate decision.

### 3.2 Row polymorphism / polymorphic variants — REJECTED as out of scope

Permitting a type variable as a member (`a | Int`) makes the generated family's
*identity* depend on instantiation: if `a := Int`, a two-constructor family must
collapse to one. That is row polymorphism, a substantially larger feature with its own
unification theory. Out of scope; see §5.2.

### 3.3 Transparent erasure for all-literal unions — REJECTED for v1, deferrable

Tempting: since literal members are distinct *values*, discrimination by literal
comparison is decidable, so `3 | 4` could erase to raw `3` / `4` and be drop-in for
`@extern`.

The safety condition is not "all members share a base type" — that is wrong in both
directions. `"4" | :4` are different base types but erase to an Erlang list and an
Erlang atom, which *are* distinguishable. Meanwhile `4 | 'x'` share the "literal"
shape but `Char` erases to an integer, so an `Int` literal and a `Char` literal can
erase to **the same Erlang term**.

The correct condition is "**the members' erased values are pairwise distinct as Erlang
terms**," which is statically decidable but *value-level and subtle*: `3 | 4` would be
transparent while `3 | '\x04'` is silently tagged, with nothing in the syntax to tell
the reader which. Rejected for v1 in favour of one uniform tagged rule. It may return
later as an **explicit opt-in** with pairwise-distinctness as its admission test.

## 4. Chosen design

`A | B` elaborates to a **real, compiler-generated discriminated inductive family**
with constructors auto-derived from the member types. Injection is inserted by the
elaborator at check-position; elimination is by type-pattern. Nothing about it is
TypeScript except the syntax.

The kernel is untouched: no new type former, no new conversion rule, no subtyping, no
cast. Everything lives in the parser, the elaborator, and emit.

## 5. Surface syntax

### 5.1 Grammar

A new production in **`parse_type_expr/1`** (`parser.ex:4681`) at the **lowest
precedence — below `->`**. Therefore `Int | String -> Bool` parses as
`(Int | String) -> Bool`. A leading `|` is permitted, matching the existing
declaration-body style. It produces a new AST node:

```
{:union_type, meta, [member, member, ...]}
```

A **member** is either:
- a **type expression** — `Int`, `List(Int)`, `Map(String, Bool)`; or
- a **literal** — `3`, `4.0`, `"north"`, `:north`, `'c'`, `true`.

The node is legal anywhere a type annotation is: parameters, return types, `typealias`
RHS, `let` ascriptions, and type arguments (`Map(String, Int | Bool)`).

**The declaration-body grammar is untouched.** `type Foo = A | B` still means "named
ADT with constructors `A` and `B`" and always will. Unions exist only in type-*expression*
position. `typealias Payload = Int | String` names one; being an alias, it introduces no
constructors.

**A second, smaller grammar addition: typed patterns in `match` arms.** §9's elimination
syntax (`n: Int => …`, `s: String => …`) needs a pattern shape — `identifier : TypeExpr`
— that does not exist today at the *top level* of a match arm's pattern. Patterns are
parsed by reusing the expression grammar (`parse_match_arm` calls `parse_expr/2`,
`parser.ex:2076-2079`), and the only existing `identifier`-then-`:` handling is
`parse_map_pair`'s field-punning shorthand (`key: value`, `parser.ex:973`), which is
reachable in pattern position only *nested inside* a record/map pattern's braces
(`Point{x: 1, y}`) — it associates a field name with a sub-pattern, not a bare binder
with a type. A top-level `n: Int` pattern needs a genuinely new production. This is
new, but small and consistent with the rest of this design: one new pattern-parse
rule, no new pattern grammar for anything *other* than a bare identifier followed by a
type expression, and it elaborates to an ordinary bind-then-check (a checked `case`
branch pattern), so it stays inside the "Surface + elaborator" scope and does not
touch the kernel. The rule belongs at the level `parse_expr` recurses through for
*any* sub-pattern (so it also works nested inside a constructor argument, e.g.
`Cons(n: Int, rest)`), not as a special case wired only into `parse_match_arm`'s
top-level entry — a union member can appear anywhere a type can, so its pattern
counterpart should be admissible anywhere a pattern can.

### 5.2 Admission rules

- **Members must be ground and closed** — no free type variables, no unsolved
  metavariables. `a | Int` is rejected (see §3.2), and is a compile error.

**REVISED (post-implementation, commit `583fafe`): a literal unioned with its own
type is ADMITTED, not rejected.** The original design above rejected `Int | 3` on
the theory that `let x: Int | 3 = 3` "admits two distinct injections and there is no
subtyping to break the tie." That theory does not hold: the two paths never compete.
`union_literal_ctor/5` is the *first* clause of the elaborator's literal `cond`, so a
literal *expression* always wins the literal member outright; anything else injects
via its *inferred type* (`maybe_inject_union/5`), which for a bare `3` is `Int` —
never the singleton `3` member. There is no ambiguity to break a tie for, so the
overlap check was defensive, not load-bearing, and was removed.

This unlocks the sentinel/refinement pattern generally — `-1 | Int`, `:north | Atom`
— and the union is a genuine **disjoint sum**, not a set union: `Int(3)` and the
literal `3` member are distinct values of `Int | 3`, and which one a given value is
depends on how it was *written* (a literal expression vs. an `Int`-typed term), not
on what it equals. The same most-specific-wins precedence governs the FFI boundary
(§10): an exact-value guard for the literal is emitted before the class guard for its
own type, so a raw `3` re-tags as the sentinel and any other integer as `Int`.

## 6. Canonical form and family identity

A union's **identity is its canonical member list**, computed by:

1. **Flatten** — `(A | B) | C` ≡ `A | B | C`. `typealias` members are unfolded first,
   so with `typealias P = Int | String`, the type `P | Bool` is a three-member union.
2. **Normalise** each member (unfold `typealias`, then reduce to **full normal
   form** via `Cure.Core.Normalise.nf/3` — not `Normalise.whnf/3`) to a ground Core
   type or a literal. This must be `nf`, not `whnf`: `Normalise` (`lib/cure/core/
   normalise.ex:1-9`) is explicit that the two are different reduction *policies*
   (`whnf/3` at `normalise.ex:24-33`, `nf/3` at `normalise.ex:35-44`, selected by a
   `:mode, :whnf | :nf` option), and plain `eval` (`lib/cure/core/eval.ex:62-63`)
   evaluates a `{:data, name, params, indices}` node's params/indices as *values* but
   leaves a neutral global application inside an index (`{:app, {:global, :+}, …}`,
   e.g. an index written `1+1`) as a stuck neutral rather than the literal `2` —
   folding that requires the certified-δ pass `Normalise` gates behind its `:delta`
   option (`normalise.ex:15-22`; the literal-spine folder is `Eval.fold/2`,
   `eval.ex:266-320`, referenced from `eval.ex:68-69`). Without full nf, two ground,
   closed, *definitionally equal* members — `Bounded(1+1)` and `Bounded(2)`, or two
   `typealias`es that unfold to the same type through different arithmetic — could
   print as different keys and silently produce two distinct generated families for
   what the kernel considers one type, breaking the cross-module identity property
   in §13.
3. **Key** each member by its **type-distinguishing canonical printing**: `Int`,
   `List(Int)`, `"4"`, `:4`, `4`. The key carries the syntax that identifies the
   *type*, not merely the value — this is what keeps `"4"` (a `String`) and `:4` (an
   `Atom`) distinct rather than colliding on `4`. **Numerals key as `(type, value)`**,
   so `4 : Int` and `4 : Nat` are different members; the union-member position defers
   to the existing numeric-literal defaulting rule rather than inventing one.
   **The key is derived from the *resolved* family identity, not the bare surface
   name.** Cure already has a case where two distinct types can carry the same bare
   display name — a local declaration shadowing an imported one — and the existing
   E-layer fix (`Resolution.rekey_module_env`, Approach B, `lib/cure/elab/resolution.ex`)
   re-keys the loser to a qualified `:"Mod#Name"` atom precisely so the two stay
   distinguishable. Canonicalisation must key off that *already-disambiguated* atom
   (post-rekeying, qualified when the member is a shadowed or module-private type),
   not a naive `display/1`-style name. Keying off the bare name would let two modules
   that each declare an unrelated local `Point` collide into one generated
   `Union⟨…,Point,…⟩` family and be treated as definitionally equal — the same shape
   of provenance bug this codebase already has an open, unfixed instance of elsewhere:
   anonymous typeclass-implementation names are mangled from `iface`/`head`/`method`
   only, with no module component (`:"__impl_#{iface}_#{head}_#{method}"`,
   `lib/cure/elab/implementation.ex:306`), so two modules' unrelated anonymous
   `impl Show for Int` blocks generate the identical atom and a cross-module overlap
   goes undetected. This design must not repeat that mistake for union family names.
4. **Dedupe** by key.
5. **Sort** keys lexicographically. `Int | String` and `String | Int` therefore produce
   the identical list.
6. **Collapse** — a one-member union *is* that member (`Int | Int` is just `Int`; no
   family is generated). A zero-member union is unwritable by construction.

**Ordering note.** §5.2's admission checks (ground/closed, literal-type overlap) run
*after* step 2's normalisation, not on the raw surface member list — otherwise
`typealias T = Int` followed by `T | 3` would slip past the literal/type-overlap
rejection, since the checker would see an opaque alias name `T` rather than `Int` at
the point of comparison. Both admission rules in §5.2 are defined over the
*canonical* (post-normalisation) member list.

The sorted key list **names** the generated family: `Union⟨Int,String⟩`.

**This is the whole trick.** Two modules independently writing `Int | String` derive the
same name, hence the same `{:data, name}`, hence they are **definitionally equal with
zero kernel involvement**. Set-semantics (`Int | String` ≡ `String | Int`) is obtained
by construction rather than by a new conversion rule.

**Consequence — content-addressed emission.** Because the name is content-derived rather
than gensym'd, each distinct family must be **emitted exactly once per program**, into a
synthetic module, and referenced **remotely** from every user. The machinery for exactly
this exists (`Program.import_origins/1`, `87f6755`). Emitting it per-module would produce
duplicate BEAM definitions.

## 7. The generated family

Each canonical member becomes one constructor, named by its key:

```
Int | String
  ⟶  data Union⟨Int,String⟩ = Int(Int) | String(String)

3 | :north | List(Int)
  ⟶  data Union⟨3,:north,List(Int)⟩ = 3 | :north | List(Int)(List(Int))
```

- **Type members carry a payload** of that type.
- **Literal members are nullary** — the value is fully determined by the constructor,
  so there is nothing to store. This is exactly "the values are sentinels for the case
  branch." No singleton type, no index, no `idx_to_core` change is required.

Constructor names are **injective by construction**: distinct members have distinct keys
(or they would have been deduped in §6). BEAM atoms may be quoted, so the key *is* the
atom — `:'List(Int)'`, `:'"4"'`, `:':4'` — with no mangling scheme to get wrong.

Properties of the generated family:

- Parameterless, index-free.
- **Non-recursive** — there is no name for it to refer to itself by — hence trivially
  strictly positive. The positivity and termination checkers never have to consider it.
- Universe level = max of its type members' levels.
- Users never write these constructors. They surface only in `Show` output and crash
  dumps, where seeing `Int` or `:north` is the desired reading.

## 8. Introduction — injection at check-position

Union subsumption is an **elaborator-inserted coercion in check mode only**, never a
kernel rule.

When checking a term `e` against expected type `U = A | B | …`:

| Case | Action |
|---|---|
| `e`'s inferred type is definitionally a member `A` | insert injection `Union⟨…⟩.A(e)` |
| `e` is a literal matching a literal member | insert the nullary constructor: `3 ⟶ Union⟨3,4⟩.3` |
| `e`'s type is a union whose members are a **subset** of `U`'s | insert a generated **widening**: a `case` remapping each constructor to its counterpart in the wider family |
| otherwise | type error (§10) |

Widening is a **real function**, not a cast — the two families are distinct types.

**Unions live in check mode, not infer mode.** A bare `42` infers `Int`, never
`Int | String`. A union must come from an annotation, a parameter type, a return type,
or a container's type argument. This is precisely what keeps the feature zero-TCB: there
is no principal-type problem, no unification *against* a union, and no metavariable is
ever solved to a union.

**Why the `Map` case works.** `Map(String, Int | String | Bool)` places the union in the
value position, and every `insert` checks its value argument *against* that type — check
position — so the injection fires. This requires **no variance rule**:
`Map(String, Int) <: Map(String, Int | String)` does **not** hold and is not needed.

**The cost, stated plainly.** Check-mode-only means some annotations that feel inferable
are mandatory:

```cure
let xs = [1, "a"]                      -- ERROR: no expected type
let xs: List(Int | String) = [1, "a"]  -- OK
```

This is accepted as the correct trade for a zero-TCB feature.

## 9. Elimination — type patterns

```cure
fn describe(x: Int | String | :north) -> String =
  match x {
    n: Int    => "int " <> show(n)
    s: String => "string " <> s
    :north    => "north"
  }
```

- **Type members** bind their payload at that type (`n : Int`, fully checked).
- **Literal members** match as bare literals and bind nothing.

The elaborator rewrites the whole `match` to an ordinary `case` on the generated family.
Therefore **coverage, exhaustiveness, and totality all come from existing machinery**: a
missing branch is a normal non-exhaustive-match error, and there is no such thing as an
extra branch, because the compiler knows the member set exactly.

**Sub-union branches.** A branch may name a sub-union, binding the narrowed value:

```cure
match x {
  n: Int              => …
  rest: String | Bool => …   -- rest : String | Bool
}
```

This is §8's widening remap run backwards. It is what makes wide unions bearable to
consume, and is in scope for v1.

A sub-union branch's constructor set may overlap an earlier branch's (e.g. `n: Int`
then `m: Int | Bool`) — no new overlap rule is needed, but this must be resolved at
*elaboration* time, not deferred to runtime: Core's `:case` takes one branch per
constructor name (`branch :: {atom(), non_neg_integer(), t()}`, `term.ex:49`), so it
cannot express two competing branches for the same member. The elaborator assigns
each member to exactly one generated Core branch — the first surface branch (in
source order) that names it — before lowering, exactly as ordinary overlapping
`match`/`case` patterns are already resolved to a single-branch-per-constructor
`:case` today.

## 10. Erasure and emit

**One uniform tagged rule. No exceptions.**

| Member kind | Erased form |
|---|---|
| Nullary (literal) | bare constructor atom: `:'3'`, `:':north'`, `:'"4"'` |
| Type member | tagged 2-tuple: `{:'Int', 42}`, `{:'List(Int)', [1,2,3]}` |

This is exactly the existing dependent-ctor erasure rule (`emit.ex:12-14`) with no
special-casing. Anonymous unions deliberately do **not** join the
`Bool`/`Nat`/`Bounded`/`List` transparent-erasure club at `emit.ex:263-300` — see §3.3.

**REVISED (post-implementation, commit `06be19e`): an `@extern` CAN directly return an
anonymous union.** The original design above reasoned that this would be a lie — Erlang
hands back a raw, untagged value, so a union-typed `@extern` would claim a constructor
tag that is not there. The revision does not weaken that claim; it closes the gap a
different way: **the compiler generates the discriminating wrapper itself**, at the
`@extern` boundary, rather than requiring the author to hand-write one.
`Declarations.check_extern_not_union/2` requires every member to be pairwise
distinguishable from an untagged value (`Union.discriminable/1` — literals by exact
value, type members by an ORDERED class guard, most-specific first, e.g. `is_boolean`
before `is_atom` so `Bool | Atom` is admissible) *before* accepting the declaration;
`Emit.union_dispatch/2` then emits a `case` on the raw result, guarding and re-tagging
each recognisable member, with **no catch-all** — an Erlang value outside the declared
union is a broken FFI contract, and the honest outcome is a `CaseClauseError`, not a
silent miscompile. This is mechanically the same "discriminating shim" the original
design already endorsed (a guard-ordered dispatch over the raw value) — the change is
*who writes it*: the compiler, from the declaration, rather than the author, by hand.
No `believe_me`, no opaque `Any`; the discriminability check is exactly what makes this
zero-TCB — an indistinguishable pair (`Int | Nat`, both raw Erlang integers) is rejected
at the declaration the author can see, never silently miscompiled.

```cure
@extern(:erlang, :abs, 1)
fn raw(n: Int) -> Int | Binary        -- compiler-generated discriminating wrapper
```

A union **nested** inside the return type (`List(Int | Bool)`) remains rejected
(`Declarations.check_extern_not_union/2`'s `_ -> if Elaborator.union_goal?(codomain) ...`
branch) — the boundary would have to walk an arbitrary structure to re-tag it, which is
still out of scope.

Generated families are emitted once per program into a synthetic module and referenced
remotely (§6).

## 11. Error taxonomy

Four new diagnostics, each naming the offending member(s). **A fifth — "literal/type
overlap" (`Int | 3`) — is NOT a diagnostic** as of `583fafe` (§5.2): it is admitted,
disambiguated by most-specific-wins, not rejected.

| Condition | Diagnostic |
|---|---|
| Non-ground member | `a \| Int` — member `a` is not a ground type; unions cannot be parameterised |
| Ambiguous numeral | a numeral in member position that the existing numeric-literal defaulting rule cannot resolve to a single type (`Int` vs `Nat`). If defaulting always resolves, this diagnostic is unreachable and its test asserts that. |
| No matching member | value of type `Bool` checked against `Int \| String` |
| Non-member branch | `match` branch names `Bool`, not a member of `Int \| String` |

**Non-exhaustive `match` needs no new code** — it is the existing coverage error on the
generated family.

## 12. Classic-pipeline coexistence

The parser is shared, so the classic checker will encounter `{:union_type, meta, members}`
in type-expression position and must not crash.

Classic **already has** a structural `{:union, [...]}` type with real subtyping
(`lib/cure/types/type.ex:24-29`, `212-219`), produced today only from the
declaration-body path (`checker.ex:484`, classifying `type X = A | B` as a union of
pre-existing aliases) — no `.cure` source exercises it from type-*expression*
position. `Type.resolve/1`, which *does* dispatch on type-expression AST, has no
clause for the new `{:union_type, meta, members}` node, so it falls through to the
existing catch-all `def resolve(_), do: :any` (`type.ex:362`). That catch-all is what
makes "must not crash" true — it is a **pre-existing, unconditional fallback**, not a
new lowering path, so this really does cost zero new classic code. But it does **not**
map the new node onto `{:union, [...]}` — an anonymous union is opaque to classic as
`:any` (Cure's top type), not a real structural union with the subtyping described
above. "Serviceable approximation" overstates it: classic's approximation is the
*coarsest* one available, not the tailored `{:union,…}` type. Wiring the new node to
the real `{:union,…}` type would need one new `Type.resolve/1` clause — small, but not
zero, and not required, since classic's role here is only to not crash while the
dependent pipeline does the real checking.

No new classic work, and no coupling to the #18 rip-out in either direction.

## 13. Testing

- **Canonicalisation is a pure function** and is unit-tested directly:
  - `Int | String` and `String | Int` produce the identical family name.
  - `Int | Int` collapses to `Int` (no family generated).
  - `(A | B) | C` flattens to three members.
  - `"4"` and `:4` do not collide.
  - `typealias` members unfold before keying.
  - **Full-nf soundness** (§6 step 2): two definitionally-equal-but-syntactically-distinct
    ground members (e.g. a `Bounded` index written as a reducible arithmetic expression
    vs. its already-reduced literal) key identically, not as two distinct families.
  - **Resolved-identity soundness** (§6 step 3): two unrelated same-named local types
    declared in two different, non-importing modules (the shadowing case) key
    *differently* — they must NOT be merged into one cross-module family.
  - **Admission-order soundness**: `typealias T2 = Int` followed by `T2 | 3` keys
    identically to `Int | 3` — alias unfolding happens *before* keying, so the two
    are the same family (not "rejected"; see the §5.2 revision — a literal unioned
    with its own type is admitted, so this now pins identity, not rejection).
- **Cross-module identity** — the load-bearing property. Two modules independently
  writing `Int | String` must produce the same `{:data, name}` and interoperate. A
  link-tier test in the shape of the existing `dependent_emit_link_test`.
- **Oracle programs** in `test/oracle/` for the three motivating cases: a heterogeneous
  `Map`, a literal-sentinel union, and an FFI discriminating wrapper.
- **Round-trip**: construct → match → recover the value, executed on **generic-unix
  AtomVM** (the real target; per repo convention, validate on host before hardware).
- **Negative tests** for all four diagnostics in §11 (§5.2's revision retired the fifth).
- **Non-regression**: existing `type Foo = A | B` declarations still elaborate as named
  ADTs.

## 14. Out of scope (v1)

Deliberately excluded, each recoverable later:

- Type variables as members (row polymorphism) — §3.2.
- Transparent erasure for literal unions — §3.3; may return as an explicit opt-in.
- Union members in *inference* position — §8.
- Container covariance (`Map(String, Int) <: Map(String, Int | String)`) — §8.
- A union **nested** inside an `@extern`'s return type (`List(Int | Bool)`) — §10.
  (`@extern` returning a union *directly* is IN scope as of `06be19e`; see §10's
  revision.)
- Typeclass instances declared *on* an anonymous union.

# The `match` Construct
## Language Specification, Version 1.0.0

**Status.** Stable.
**Revision.** 1.0.0 (initial formal specification of an existing construct).
**Companion construct.** `pickup` (predicate dispatch); see `docs/PICKUP.md`.
**Related references.** `docs/PATTERNS.md` (pattern reference), `docs/LANGUAGE_SPEC.md` § "Pattern Matching" (overview), `docs/BINARIES.md` (binary segment grammar).

---

## Table of Contents

1. Introduction
2. Conformance Terminology
3. Lexical Syntax
4. Grammar
5. Patterns
6. Static Semantics
7. Dynamic Semantics
8. Formal Operational Semantics
9. Formatting Rules
10. Interaction with `pickup`
11. Examples
12. Algebraic Laws
13. Exceptions and Divergence
14. Tail-Position Behaviour
15. Compilation and Lowering
16. Constant Folding and Specialization
17. Macro and Quote Interaction
18. Pattern Surface Positions
19. Tooling and IDE Integration
20. Errors and Diagnostics
21. Non-Goals
22. Stability, Versioning, and Deprecation
23. Summary
24. Appendix A — Acceptance Test Suite
25. Appendix B — Glossary
26. Appendix C — Change Log
27. Appendix D — Index of Normative Requirements
28. Appendix E — Reference Implementation Sketch
29. Appendix F — Worked Pattern Examples
30. Appendix G — Style Guide and Idioms
31. Appendix H — Anti-Patterns
32. Appendix I — Reserved Future Syntax
33. Appendix J — Soundness Proof Sketch
34. Appendix K — Bibliography and Related Work
35. Appendix L — Open Questions and Future Directions
36. Appendix M — Specification Metadata and Colophon

---

## 1. Introduction

`match` is a control-flow expression that selects one of several branches by attempting to match a single *scrutinee* value against a series of *patterns* in source order. It is the structural-dispatch counterpart to `pickup`, which dispatches on free-standing boolean guards. Together, `match` and `pickup` are the only branching constructs in the language.

The construct is governed by a single mental model:

> **`match` walks the clauses and picks up the first one whose pattern matches the scrutinee.**

`match` differs from `pickup` along two axes:

- **Pattern dispatch.** Selection is by structural shape, not by predicate truth. Patterns may bind names from sub-positions of the scrutinee.
- **Decidable exhaustiveness.** For algebraic data types and other finite-shape domains, the compiler computes coverage exactly via a Maranget-style algorithm (§ 6.3) and rejects non-exhaustive blocks at compile time.

Every other rule in this document exists to make these two intuitions mechanically precise.

## 2. Conformance Terminology

The key words **MUST**, **MUST NOT**, **SHALL**, **SHOULD**, **SHOULD NOT**, and **MAY** are interpreted as in RFC 2119, restricted to the language's compiler, parser, type checker, optimizer, formatter, and language server.

## 3. Lexical Syntax

### 3.1 Reserved Words

`match` and `when` are reserved keywords. They MUST NOT be used as identifiers, type names, module names, or labels. `when` is reserved globally; its only normative position is as the guard separator in a clause (§ 4, § 5.12), but reservation prevents accidental shadowing elsewhere.

### 3.2 Pattern-Position Sigils

The following lexical sigils are recognized in pattern position and have no special meaning outside it:

- `_` — wildcard (§ 5.6).
- `^` — pin operator (§ 5.13). Followed by an identifier.
- `%[ ... ]` — tuple pattern (§ 5.8).
- `%{ ... }` — map pattern (§ 5.10).
- `<< ... >>` — binary pattern (§ 5.14).

A `_` followed immediately by an identifier (e.g. `_unused`) is a *silent binding* (§ 5.5), not a wildcard.

### 3.3 Layout

`match` participates in the language's standard indentation-sensitive layout. No new lexical rules are introduced; the rules already governing `pickup` and other indented constructs apply unchanged.

## 4. Grammar

The grammar is given in EBNF. `INDENT` and `DEDENT` denote synthetic tokens emitted by the layout pass.

```text
match_expr   ::= "match" expression NEWLINE INDENT clause_list DEDENT

clause_list  ::= clause { NEWLINE clause } [ NEWLINE ]

clause       ::= pattern [ "when" expression ] "->" expression

pattern      ::= -- defined in § 5
```

### 4.1 Notes on the Grammar

- A `match` block MUST contain at least one clause.
- The expression after `match` is the *scrutinee*. It is evaluated exactly once per evaluation of the `match` expression, before any pattern is attempted (§ 7.1).
- Each clause has the shape *pattern* `->` *expression*, optionally with a guard `when` *expression* between the pattern and the arrow.
- The right-hand side of any clause is a full expression and MAY itself be a `match`, a `pickup`, a `let`, a function call, or any other expression form.
- There is no terminal `else` clause analogous to `pickup`'s. Totality is established structurally (§ 6.3); a final `_ -> ...` or similarly-exhaustive pattern serves the same role when needed.

### 4.2 Block Termination (Parser Rule)

A `match` block extends through every consecutive line indented strictly deeper than the column of the `match` keyword. It ends at the first subsequent line whose indentation is less than or equal to that column, or at end-of-file, whichever comes first. Blank lines are insignificant to the parser.

This rule is identical to the rule for `pickup` and is shared with every other indented-block construct in the language. The formatter applies a stricter discipline (§ 9.1).

## 5. Patterns

### 5.1 Pattern Sub-Grammar

```text
pattern         ::= literal_pattern
                  | wildcard_pattern
                  | variable_pattern
                  | silent_pattern
                  | tuple_pattern
                  | list_pattern
                  | map_pattern
                  | record_pattern
                  | constructor_pattern
                  | pin_pattern
                  | binary_pattern
                  | negated_literal

literal_pattern    ::= integer | float | string | atom | bool_literal | char | "null"
negated_literal    ::= "-" literal_pattern               -- only literal_integer / literal_float
wildcard_pattern   ::= "_"
variable_pattern   ::= identifier                        -- starting with a non-underscore lowercase letter
silent_pattern     ::= "_" identifier                    -- e.g. `_unused`
tuple_pattern      ::= "%[" [ pattern { "," pattern } ] "]"
list_pattern       ::= "[" [ list_body ] "]"
list_body          ::= pattern { "," pattern } [ "|" pattern ]
                     | pattern { "," pattern }           -- fixed-length form
map_pattern        ::= "%{" [ map_entry { "," map_entry } ] "}"
map_entry          ::= literal ":" pattern
                     | identifier                        -- punning shorthand for `name: name`
record_pattern     ::= TypeName "{" [ rec_entry { "," rec_entry } ] "}"
rec_entry          ::= identifier ":" pattern
                     | identifier                        -- punning shorthand for `field: field`
constructor_pattern::= ConstructorName [ "(" [ pattern { "," pattern } ] ")" ]
                                                          -- nullary requires "()"
pin_pattern        ::= "^" identifier
binary_pattern     ::= "<<" [ bin_segment { "," bin_segment } ] ">>"
bin_segment        ::= -- see docs/BINARIES.md
```

The non-terminals `TypeName` and `ConstructorName` are PascalCase identifiers per the language's general lexical rules.

### 5.2 Pattern Semantics (Matching)

A pattern is matched against a value `v` under an environment `σ` to produce one of three outcomes:

- **Success** with an extended environment `σ'` that binds every variable introduced by the pattern.
- **Failure**, leaving `σ` unchanged and indicating that the next clause should be tried.
- **Type error** — only if the pattern is statically ill-typed against the scrutinee, in which case the program does not compile (§ 6.1).

Matching is *non-mutating*: failed match attempts do not modify `σ` and do not produce observable side effects.

### 5.3 Variable Bindings

A variable pattern (§ 5.1) on its first occurrence within a clause binds the corresponding sub-value to the named slot in `σ'`. Variables introduced in a pattern are visible:

- in the clause's `when` guard (and to any synthetic guards injected by repeated-variable handling, § 5.7, or pin handling, § 5.13);
- in the clause's right-hand side;
- nowhere else.

In multi-clause function heads each clause starts from a fresh empty pattern scope, so names MAY be reused freely across clauses without conflict.

### 5.4 Linearity

Pattern variables are *non-linear in source* but *linear in semantics*: a variable name MAY appear more than once in a single pattern, but every occurrence after the first is treated as an equality test against the binding established by the first occurrence (§ 5.7). The resulting binding in `σ'` is unique per name.

### 5.5 Wildcards and Silent Bindings

The wildcard pattern `_` matches any value and binds nothing. It MAY appear arbitrarily many times in a single pattern.

A silent binding `_name` (an identifier prefixed with `_`) matches any value and binds `name` to it. It is *equivalent* to a plain variable binding except that the language MUST NOT emit `W-UNUSED-VARIABLE` for the binding even if `name` is never referenced. This is the canonical way to document an intentionally-unused sub-value.

### 5.6 Literal Patterns

A literal pattern matches the scrutinee iff the scrutinee is structurally equal to the literal under the language's general equality. Recognized literal forms include integer, float, string (as UTF-8 binary), atom, boolean, character, and `null`. A leading unary minus on an integer or float literal in pattern position is folded at parse time into the negated literal (so `-1` in a pattern matches the integer `-1`, not the unary-minus operator).

### 5.7 Repeated Variables

A name that appears at multiple positions within a single pattern binds at its first occurrence and emits a synthetic equality guard at every subsequent position. The clause's pattern-bound `when` guard is conjoined with these synthetic equalities via short-circuit `&&` before the right-hand side is evaluated.

```text
match pair
  %[x, x] -> :equal
  _       -> :different
```

The above clause matches a tuple iff its two components are equal.

### 5.8 Tuple Patterns

A tuple pattern `%[p_1, ..., p_n]` matches a tuple value of arity exactly `n` whose `i`-th component matches `p_i`. Tuples of any other arity fail. The empty-tuple pattern `%[]` matches the empty tuple.

### 5.9 List Patterns

The list-pattern grammar admits three forms:

- `[]` — matches the empty list.
- `[p]`, `[p_1, p_2]`, `[p_1, ..., p_n]` — fixed-length forms; match a list of exactly that length whose elements match the corresponding patterns.
- `[p_1, ..., p_k | p_tail]` — multi-head cons; matches any list of length at least `k` whose first `k` elements match `p_1, ..., p_k` and whose remainder matches `p_tail`.

The multi-head cons form is desugared at parse time into right-associated `cons` cells: `[a, b, c | rest]` is equivalent to `[a | [b | [c | rest]]]`. The desugaring is purely syntactic; the resulting pattern is type-checked and lowered as nested cons.

### 5.10 Map Patterns

A map pattern `%{ k_1: p_1, ..., k_n: p_n }` matches a map value `m` iff every key `k_i` is present in `m` and the corresponding value matches `p_i`. Keys not mentioned in the pattern are *ignored* (open matching).

Map keys in pattern position MUST be literal atoms. A non-atom or non-literal expression at a map-key position is rejected with `E093` (the general type-mismatch diagnostic; the historical dedicated `E023` code is retired).

A bare identifier at a map-key position is permitted as *punning shorthand*: `%{ x, y }` is equivalent to `%{ x: x, y: y }`. The desugaring expands before pattern matching is performed.

### 5.11 Record Patterns

A record pattern `T{ f_1: p_1, ..., f_n: p_n }` matches a value `v` iff `v` is a record of type `T` (i.e. has the `__struct__` tag corresponding to `T`) and every named field `f_i` of `v` matches `p_i`. Fields not mentioned in the pattern are ignored (open matching, mirroring map semantics § 5.10).

A bare identifier at a field position is punning shorthand: `T{ name }` is equivalent to `T{ name: name }`.

Field references that do not exist in `T`'s declared schema emit `E022` as an error (the same code construction and update use for an unknown/missing field; the historical claim that this was `E021`-at-warning-severity is wrong -- `E021` names an unknown record *type*, and every `E`-prefixed code is error severity). A sub-pattern whose static type is incompatible with the declared field type also emits `E022`.

### 5.12 ADT Constructor Patterns

An ADT constructor pattern `C(p_1, ..., p_n)` matches a value built with constructor `C` and decomposes its arguments against `p_1, ..., p_n`. The constructor name MUST be a PascalCase identifier; PascalCase distinguishes constructor patterns from variable patterns at the lexical level.

Nullary constructors MAY be written bare (`None`) or with explicit empty
parentheses (`None()`). A bare PascalCase identifier is resolved as a nullary
constructor of the scrutinee type; a bare lowercase identifier remains a
variable pattern (§ 5.3).

The number of arguments in the pattern MUST match the constructor's declared arity. Arity mismatches are rejected at type-checking time with the language's general arity diagnostic.

### 5.13 The Pin Operator

The pin pattern `^x` matches a value `v` iff `v` is structurally equal to the value already bound to `x` in the enclosing scope at the time the `match` expression is evaluated. It does *not* introduce a new binding; the name `x` MUST be in scope when the clause is elaborated, otherwise the ordinary unknown-name diagnostic `E091` is emitted (the historical dedicated `E024` code is retired).

```text
let target = get_tag()

match event.tag
  ^target -> :hit
  _       -> :miss
```

The pin is lowered by the compiler to a fresh variable binding plus an equality guard (`V_fresh =:= V_x`). When `^x` references an unbound name, the compiler falls back to a plain binding for `x` to recover from the error and continue analysis; the program is still rejected at the source level.

### 5.14 Binary Patterns

The parser accepts the full segment grammar of `docs/BINARIES.md`: each segment is *value* `[::` *specifier-chain* `]`, where the specifier chain covers type, signedness, endianness, `size(expr)`, and `unit(n)`. The elaborator, however, only lowers a plain byte segment (a bare literal 0-255 or a bare variable/`_`) and a single trailing unsized tail (`rest::binary`, `::bytes`, `::bitstring`, or `::bits`, no `size`). Any sized or otherwise typed segment (`x::16`, `x::float`, `x::utf8`, ...) is rejected under `E093`.

```text
match frame
  <<tag, len, _::binary>> -> len
  <<>>                    -> 0
```

A binary match desugars to guarded byte-offset reads rather than an inductive case split, so it is open by construction: it MUST end in a wildcard/variable catch-all or the compiler rejects it under `E119` (§ 20).

### 5.15 Guards (`when` Clauses)

A clause MAY carry a guard between the pattern and the arrow:

```text
match value
  pat_1 when g_1 -> e_1
  pat_2          -> e_2
```

Guards are full expressions of type `Bool` evaluated in the scope extended by the pattern's bindings. A guard that fails causes the clause to fail and the next clause to be attempted, exactly as if the pattern itself had failed. Guards are evaluated under the same strict-`Bool` discipline as `pickup` guards (§ 6.1.4): no truthy/falsy coercion.

Synthetic guards introduced by repeated variables (§ 5.7) and pin patterns (§ 5.13) are conjoined with the user-written guard via short-circuit `&&` in source order: synthetic equalities first, then the user guard.

### 5.16 Refutability

A pattern is *irrefutable* iff it cannot fail to match any value of its statically-known type. Variable patterns, wildcards, silent bindings, and tuple/record patterns whose sub-patterns are all irrefutable are irrefutable. Literal patterns, ADT constructor patterns, list patterns of fixed length, map patterns with required keys, pin patterns, and binary patterns are *refutable*.

Irrefutability is the criterion that allows a pattern to appear in `let` position without a totality warning (§ 18.3).

### 5.17 Nested Patterns

Patterns may nest to arbitrary depth: a tuple pattern's components may be record patterns; a record field's value may be an ADT constructor pattern whose argument is a list pattern; and so on. The semantics of a nested pattern is defined compositionally: matching succeeds iff every leaf pattern matches its corresponding sub-value, and the resulting `σ'` is the union of every leaf's contributions.

## 6. Static Semantics

### 6.1 Typing (Informal)

#### 6.1.1 Scrutinee

The scrutinee MUST type-check against some type `τ_s`. Each pattern in the block MUST be statically compatible with `τ_s`; pattern/scrutinee type mismatches are rejected with the language's general type-error diagnostic (or, for record fields specifically, with `E022`).

#### 6.1.2 Branches

The result type of a `match` expression is the least upper bound of the types of its branches under the language's existing subtyping rules. If no such bound exists, the program is rejected with `E-MATCH-BRANCH-MISMATCH` (the general type-mismatch diagnostic `E093`; the historical dedicated `E033` code is retired).

#### 6.1.3 Pattern Variables

Each variable introduced by a pattern receives the type of the sub-position from which it was extracted, narrowed by the constraints of the enclosing pattern. For example, in `Some(x)` where the scrutinee has type `Option(Int)`, `x` has type `Int`.

#### 6.1.4 Guards

A `when` guard MUST have type `Bool`. No implicit conversion is performed; a non-`Bool` guard is rejected with the same diagnostic class used by `pickup` (§ 5.1 of `PICKUP.md`).

### 6.2 Exhaustiveness

A missing constructor is reported under a single code, `E118` (Pattern Coverage), whether the gap is at the top level of the scrutinee or at a tuple element position:

- **Top level.** Every scrutinee type's constructors MUST appear (directly, or via a wildcard/variable catch-all). A missing one is `E118` naming the constructor.
- **Tuple positions.** When arms are tuple patterns of ADT constructors, a missing constructor at a given tuple position is `E118` naming both the branch and the position.

`E118` also covers a constructor listed more than once (`:duplicate_branch`) and an `impossible`-marked arm whose constructor is in fact reachable (`:reachable_impossible`).

This check is a compile-time **error**, not a warning: it blocks compilation. There is no separate flat/nested pass and no historical `E004`/`E025` split -- those numeric codes are retired.

### 6.3 Maranget's Algorithm (Normative Behaviour)

The compiler's coverage check follows the structure of Maranget's *Warnings for Pattern Matching* (2007). The algorithm operates on a *clause matrix* `P` whose rows are the patterns of each clause and whose columns initially form a single column carrying the scrutinee type. The algorithm:

1. Picks a column to specialize on (typically the first).
2. For each constructor `c` of the column's type, computes the *specialized matrix* `S(c, P)` and recurses.
3. For the *default matrix* `D(P)` (rows whose head pattern is a wildcard or variable), recurses on the remaining columns.
4. Reports as missing any constructor of an exhaustive type for which no specialized row exists and no default row covers it.

The implementation is permitted to terminate early upon finding the first missing witness (it does, today), provided the diagnostic is still actionable. Implementations MUST NOT report a witness that is in fact covered by some clause.

### 6.4 Reachability (Redundancy)

A clause `i` is *unreachable* iff every value matched by clause `i`'s pattern (and satisfying its guard) is also matched by some clause `j < i` (with that earlier clause's guard). The historical general-purpose `W-MATCH-UNREACHABLE` / `E032` check is retired; the compiler catches two specific, verified cases instead: a clause appearing after a wildcard/variable catch-all is `E119` (`:unreachable_after_default_pattern`), and a guarded arm shadowed by the disjunction of earlier guards is a separate compiler warning from the guard-exhaustiveness lint. There is no general Maranget-style redundancy check across arbitrary non-constructor pattern shapes today.

### 6.5 Scoping

Each clause introduces its own lexical scope. Specifically:

- The pattern `pat_i` extends the enclosing scope with any bindings the pattern introduces (§ 5.3).
- The guard `g_i` is evaluated in the pattern-extended scope.
- The right-hand side `e_i` is evaluated in the same pattern-extended scope.
- Bindings from `pat_i`/`g_i`/`e_i` are not visible in any other clause.
- No binding introduced inside a clause escapes the `match` expression.

### 6.6 Typing Judgment (Formal)

Let the typing judgment for `match` extend the language's general typing relation. We use `Γ ⊢_p p : τ → Γ'` ("under context `Γ`, pattern `p` matches type `τ` and extends `Γ` to `Γ'`") for pattern typing.

```text
   Γ ⊢ s : τ_s
   for each i in 1..n:
       Γ ⊢_p p_i : τ_s → Γ_i
       Γ_i ⊢ g_i : Bool                  (if guard present; otherwise omit)
       Γ_i ⊢ e_i : τ_i
   τ = τ_1 ⊔ ... ⊔ τ_n
   exhaustive(p_1, ..., p_n, τ_s)        (error E118 otherwise)
   ───────────────────────────────────────────────────────────  (T-Match)
        Γ ⊢ match s with p_1 [when g_1] -> e_1
                       | ... | p_n [when g_n] -> e_n  : τ
```

The pattern-typing relation `⊢_p` is defined inductively over the pattern sub-grammar of § 5.1.

### 6.7 Effect Analysis

```text
   eff(match s with p_1 -> e_1 | ... | p_n -> e_n)
       ⊆ eff(s) ∪ eff(g_1) ∪ eff(e_1) ∪ ... ∪ eff(g_n) ∪ eff(e_n)
```

This is a sound over-approximation. Pattern matching itself is pure — the matching machinery produces no effects. Only the scrutinee, guards, and selected branch contribute observable effects.

### 6.8 Reachability Lattice

Reachability is computed on the lattice `⊥ < Unreachable < Maybe-Reachable < Reachable`. Clause `i` is `Unreachable` iff the values it matches are statically known to be wholly covered by clauses `1, ..., i-1`. The Maranget machinery of § 6.3 provides decidable reachability for ADT/finite-shape patterns; arbitrary guards force the analysis to fall back to `Maybe-Reachable`.

### 6.9 Free Variables

```text
   FV(match s with p_1 [when g_1] -> e_1 | ... | p_n [when g_n] -> e_n)
       =  FV(s) ∪ ⋃_{i=1..n} (FV_clause(p_i, g_i, e_i))

   FV_clause(p, g, e) = (FV(g) ∪ FV(e)) \ BV(p)
```

where `BV(p)` is the set of variables bound by pattern `p`.

### 6.10 Substitution

```text
   [v/x] (match s with p_1 -> e_1 | ... | p_n -> e_n)
       = match [v/x]s with [v/x]_clause(p_1, g_1, e_1) | ...
```

Substitution does not descend into a clause whose pattern binds `x`; the standard capture-avoiding rules apply.

### 6.11 Well-Formedness

A `match` is well-formed iff: (1) its clause list is non-empty; (2) every pattern is statically compatible with the scrutinee's type; (3) every guard types to `Bool`; (4) branch types admit a join; (5) variable bindings within each pattern are linear in the sense of § 5.4; (6) every pinned variable is in scope at the clause's source location; (7) every record-field reference resolves against the record's declared schema; (8) every map-key pattern is a literal value.

### 6.12 Decidability

Type-checking, well-formedness, scoping, and the join computation are decidable in time linear in the size of the `match` expression, modulo the language's general type-checking and join operations. Exhaustiveness is decidable for the fragment of patterns whose type domains are statically finite (ADTs, booleans, records, fixed-length tuples, fixed-length lists). Reachability inherits exhaustiveness's decidability where guards are absent and is undecidable in general otherwise.

### 6.13 Erasure Properties

After type checking and exhaustiveness analysis, static information attached to a `match` is erased before code generation, except that:

- pattern-bound variable types remain visible to the runtime effect / contract system;
- diagnostics remain attached to source spans for tooling;
- record-tag information is preserved for the `__struct__` runtime check (§ 5.11).

### 6.14 Polymorphism and Generics

A `match` participates in generalization and instantiation as any expression position would. Pattern variables introduced into a polymorphic context are themselves polymorphic; the type checker generalizes them at the same point at which it would generalize an explicit `let`-binding.

### 6.15 Refinement-Type Interaction

If the language admits refinement types, each branch's right-hand side is type-checked under a refinement context strengthened by:

- the structural assertion that the scrutinee matches `pat_i`;
- the negation of every preceding clause's pattern; and
- the user-written guard `g_i`.

Within `e_i`, references to pattern-bound variables therefore carry refinement information drawn from both the structural and predicate constraints.

### 6.16 The Pure Fragment

A `match` is *pure* iff its scrutinee, every guard, and every branch is pure. The pure fragment is admissible in any position the language reserves for pure expressions (type-level computation, contract preconditions, compile-time constant evaluation).

### 6.17 Soundness

For closed `e` with `· ⊢ e : τ`, evaluation terminates with `v : τ`, raises an exception (including `case_clause` if the block is not statically exhaustive), or diverges. Stuck states are unreachable. The proof discharges via Progress and Preservation; the `match` cases follow from T-Match (§ 6.6) and the small-step rules of § 8.2. A proof sketch is given in Appendix J.

### 6.18 Static-Semantics Conformance Summary

A static-semantics implementation conforms iff it: (1) implements T-Match (§ 6.6); (2) computes branch joins per § 6.1.2; (3) performs the well-formedness checks of § 6.11; (4) computes a sound exhaustiveness approximation per § 6.2 and the Maranget structure of § 6.3; (5) emits the diagnostics of § 20; (6) tracks purity and effects per §§ 6.7 and 6.16; (7) discharges § 6.17's proof obligation.

## 7. Dynamic Semantics

### 7.1 Evaluation Order

The scrutinee is evaluated exactly once, before any pattern is attempted. Patterns are then attempted in source order. The first clause whose pattern matches *and* whose guard (if any) evaluates to `true` is selected; only that clause's right-hand side is evaluated.

### 7.2 Result

A `match` evaluates to the value of the selected branch. If no clause matches and no guard succeeds, the runtime raises `case_clause` (or its language-level analogue). Statically exhaustive `match` expressions can be proved unreachable (§ 6.2); for non-exhaustive blocks, the failure is observable.

### 7.3 Side Effects

The scrutinee's side effects are observed once. Guards and branches MAY have side effects. Side effects in `g_i` are observed iff every clause `j < i` had a failing pattern *or* a failing guard, and `pat_i` matched. Side effects in `e_i` are observed iff `e_i` is selected.

## 8. Formal Operational Semantics

Write a `match` expression as `match s with C`, where `C` is a clause list. Write `(p, g, e) ; C'` for a clause list whose head clause has pattern `p`, optional guard `g`, body `e`, followed by remaining clauses `C'`.

### 8.1 Big-Step Semantics

Let `match(p, v) = ⊥ | σ'` denote the result of attempting pattern `p` against value `v`: `⊥` for failure, or an environment extension `σ'` for success.

```text
   σ ⊢ s ⇓ v   match(p, v) = σ'   σ ∪ σ' ⊢ g ⇓ true   σ ∪ σ' ⊢ e ⇓ w
   ─────────────────────────────────────────────────────────────────  (M-Hit)
        σ ⊢ match s with (p, g, e) ; C ⇓ w

   σ ⊢ s ⇓ v   match(p, v) = ⊥   σ ⊢ match s with C ⇓ w
   ───────────────────────────────────────────────────────  (M-Skip-Pat)
        σ ⊢ match s with (p, g, e) ; C ⇓ w

   σ ⊢ s ⇓ v   match(p, v) = σ'   σ ∪ σ' ⊢ g ⇓ false
   σ ⊢ match s with C ⇓ w
   ────────────────────────────────────────────────────  (M-Skip-Guard)
        σ ⊢ match s with (p, g, e) ; C ⇓ w

   σ ⊢ s ⇓ v
   ─────────────────────────────────────────────  (M-NoClause)
        σ ⊢ match s with [] ⇓ raise(case_clause(v))
```

Rules omitting `g` (clauses without a `when`) are obtained by treating the missing guard as `true`.

### 8.2 Small-Step Reduction

The small-step relation reduces the scrutinee first, then proceeds clause by clause. Once the scrutinee is a value `v`, a head clause is processed as follows:

```text
                   σ ⊢ s → σ' ⊢ s'
   ────────────────────────────────────────────────────────  (SM-Scrut)
   σ ⊢ match s with C → σ' ⊢ match s' with C

   match(p, v) = σ_p   σ ∪ σ_p ⊢ g ⇓ true
   ────────────────────────────────────────────────────  (SM-Hit)
   σ ⊢ match v with (p, g, e) ; C → σ ∪ σ_p ⊢ e

   match(p, v) = ⊥
   ────────────────────────────────────────────────────  (SM-Skip-Pat)
   σ ⊢ match v with (p, g, e) ; C → σ ⊢ match v with C

   match(p, v) = σ_p   σ ∪ σ_p ⊢ g ⇓ false
   ────────────────────────────────────────────────────  (SM-Skip-Guard)
   σ ⊢ match v with (p, g, e) ; C → σ ⊢ match v with C

   ────────────────────────────────────────────────────  (SM-NoClause)
   σ ⊢ match v with [] → σ ⊢ raise(case_clause(v))
```

### 8.3 Evaluation Contexts

```text
   E ::= ...  | match E with C
```

There is no production `match v with (p, g, E) ; C'` and no production `match v with (p, E_g, e) ; C'`. Implementations MUST NOT step inside any guard or branch body of an unmatched clause; the only place reduction can occur within an unselected `match` is the scrutinee.

### 8.4 Properties

- **Determinism.** Exactly one rule applies per step; the result is unique up to underlying determinism.
- **Progress.** Every well-typed non-value `match` expression has a step.
- **Preservation.** Reduction preserves the typing judgment.
- **Equivalence.** `σ ⊢ match s with C ⇓ v` iff `σ ⊢ match s with C →* σ' ⊢ v`. Divergence and exception cases correspond.
- **Confluence.** Trivial under determinism.

### 8.5 Cost Model

For `n` clauses with patterns `p_1, ..., p_n`:

- the scrutinee is evaluated once: `cost(s)`;
- each clause contributes pattern-match cost `cost_match(p_i)` plus, if the pattern matches, guard cost `cost(g_i)`;
- exactly one branch's body is evaluated: `cost(e_k)` for the selected `k`.

Pattern-match cost is bounded by the structural depth of the pattern. Implementations MAY share decomposition across clauses via a decision tree (§ 15), reducing overall cost from `Σ cost_match(p_i)` to `O(depth)`.

### 8.6 Memory Model

`match` introduces no fresh allocation, no synchronization, and no atomicity beyond what its sub-expressions require. Pattern matching reads from the scrutinee and the lexical environment but performs no observable writes.

## 9. Formatting Rules

### 9.1 Keyword and Clause Layout

The `match` keyword and its scrutinee MUST occupy a single line. Each clause MUST occupy a line by itself, indented exactly one `indent_step` (§ 9.7) deeper than the keyword.

### 9.2 Arrow Alignment

Within a single block, the formatter MUST align all `->` tokens by padding the clause-head column with spaces. The clause head consists of the pattern and, if present, the guard (`pat when g`). Alignment is local to a block; sibling blocks are not aligned with each other.

```text
match shape
  Circle(r)          -> r * r * 3
  Square(side)       -> side * side
  Triangle(a, b, _c) -> a * b / 2
```

### 9.3 Guard Placement

A `when` guard appears between the pattern and the arrow, separated from each by at least one space:

```text
match person
  Person{age: a} when a >= 18 -> :adult
  _                           -> :minor
```

For wrapped clauses (§ 9.8), the `when` guard appears at the end of the pattern line, with the body on the next line indented one step deeper.

### 9.4 Block Separation

After the last clause of a `match`, the formatter MUST insert exactly one blank line before any sibling statement at the same indent level as the keyword. The rule applies only at the outermost sibling boundary; nested arms do not get the blank-line treatment. (Same rule as `pickup`; see `PICKUP.md` § 8.4.)

### 9.5 Comments

Recognized positions:

- **Block-leading.** Above the `match` keyword, same indent.
- **Clause-leading.** Above a clause, clause indent.
- **Trailing in-clause.** Same line as the right-hand side.
- **Internal stray.** Between pattern and `->`, between `when` and guard, or other awkward positions; relocated by the formatter with `H-MATCH-COMMENT-RELOCATED`.

### 9.6 Single-Clause `match`

A `match` containing only one clause whose pattern is irrefutable is rewritten by the formatter to a `let` binding with `H-MATCH-USE-LET`:

```text
-- Before:
match value
  Person{name, age} -> body

-- After:
let Person{name, age} = value
in body
```

The rewrite is applied only when (a) the pattern is irrefutable (§ 5.16) and (b) the surrounding syntactic position admits a `let`. It MAY be suppressed by a clause-leading comment indicating intentional single-arm dispatch.

### 9.7 Configuration

- `indent_step`: positive integer, default `2`.
- `max_line_width`: positive integer, default `100`.
- `alignment_limit`: positive integer, default `40`.
- `align_when`: boolean, default `true` — whether the `when` part of one clause influences arrow alignment of sibling clauses without a `when`.

### 9.8 Long Patterns and Line Wrapping

When aligned form would exceed `max_line_width`, the formatter falls back, in order:

1. Drop alignment for the offending block.
2. Wrap right-hand sides onto a new line indented one `indent_step` deeper. *All* clauses in the block MUST adopt this form together; mixing is forbidden.
3. If even wrapping cannot fit, leave the block unchanged and emit `H-MATCH-LINE-TOO-LONG`.

### 9.9 Multi-Line Right-Hand Sides

If any branch is multi-line, every branch in the block MUST use the wrapped form: `->` at the end of the pattern (or guard) line; body on the next line, indented one step deeper.

### 9.10 Idempotence

`format(format(s, c), c) = format(s, c)`. Implementations MUST verify idempotence as part of conformance testing.

### 9.11 Comment Fidelity

The multiset of comment tokens in input and output MUST be identical. Comments may be relocated (§ 9.5) but never lost, duplicated, or character-modified.

### 9.12 Diff Minimality

Where multiple legal formattings are admissible, the formatter SHOULD select the one minimizing the textual diff. Whitespace within unchanged regions MUST NOT be touched.

### 9.13 Tab and Space Normalization

Indentation in output MUST be all spaces. Tabs are replaced; mixed indentation is normalized; trailing whitespace is stripped; the file ends with exactly one terminating newline.

### 9.14 Alignment Computation Algorithm

```text
   1. If any clause is multi-line or wrapping is required by § 9.8,
      emit wrapped form and stop.
   2. Let h_i be the rendered clause-head text of clause i,
      including any `when` guard.
   3. Let w = max(grapheme_width(h_i)).
   4. If w > alignment_limit, emit unaligned form and stop.
   5. For each clause emit:
        (indent + step) spaces + h_i + (w - grapheme_width(h_i)) spaces
        + " -> " + rhs_inline + NEWLINE
   6. Apply the blank-line rule (§ 9.4) before the next sibling.
```

### 9.15 Stability under Refactoring

Modifying a single clause MUST NOT alter formatting of any other `match` block in the file, nor any source outside the affected block beyond the blank-line rule.

### 9.16 Round-Trip Property

For formatter-produced source `s`: parsing `s` yields AST `A`; re-rendering `A` yields `s' = s` byte-for-byte. Formatted source is therefore canonical.

### 9.17 Edge Cases

- Single-clause `match` with irrefutable pattern: rewritten per § 9.6.
- Single-clause `match` with refutable pattern: legal; no rewrite.
- `match` at end of file: file-terminator newline rule applies; no additional trailing blank line.
- Adjacent `match`es at the same outer indent: exactly one blank line between them.

### 9.18 File-Level Invariants

Single trailing `\n`; no trailing whitespace on any line; all indentation is spaces in integer multiples of `indent_step`; line endings follow the language's standard for the target platform.

### 9.19 Performance Bounds

For input of `N` characters with `K` blocks totalling `M` clauses, formatting MUST complete in `O(N + M log M)` time and `O(N)` space.

### 9.20 Encoding and Unicode

UTF-8 input. Pattern-head widths in alignment are computed in grapheme clusters per Unicode UAX #29.

### 9.21 Plugin Interface

If exposed, the plugin interface MUST surface, per block: the AST node, resolved indent / alignment / wrapping mode, ordered clauses with patterns / guards / right-hand sides / trivia, and emitted diagnostics. Plugins MUST NOT mutate the AST.

### 9.22 Editor Folding Integration

Each `match` defines exactly one foldable region from the keyword's column through the last clause's last line. A folded view shows the keyword and scrutinee followed by an ellipsis and the clause count, e.g. `match req ... (5 clauses)`.

### 9.23 Conformance Test Set

The conformance corpus MUST include: one test per rule in §§ 9.1-9.22; one test per formatter-emitted diagnostic in § 20; an idempotence test on every expected output; a round-trip test on every expected output; one test per edge case in § 9.17.

### 9.24 Final Formatter Grammar

```text
FormattedMatch     ::= IndentBlock "match" SP Scrutinee NEWLINE
                       IndentedClauseList
                       [ NEWLINE ]              -- enforced if sibling follows

IndentedClauseList ::= AlignedClauses
                     | UnalignedClauses
                     | WrappedClauses

AlignedClauses     ::= ( ClauseIndent HeadPadded " -> " RhsInline NEWLINE )+

UnalignedClauses   ::= ( ClauseIndent Head     " -> " RhsInline NEWLINE )+

WrappedClauses     ::= ( ClauseIndent Head     " ->" NEWLINE
                         ClauseIndent IndentStep RhsBlock NEWLINE )+

Head               ::= Pattern [ SP "when" SP GuardExpr ]
HeadPadded         ::= Head padded with spaces to aligned column width
```

Mixing the three forms is forbidden (§ 9.9).

### 9.25 Formatter Conformance Summary

A formatter conforms iff it: (1) produces output matching § 9.24; (2) applies §§ 9.1-9.6; (3) honours § 9.7 with prescribed defaults; (4) implements §§ 9.8-9.9; (5) handles comments per § 9.5 with fidelity per § 9.11; (6) satisfies idempotence (§ 9.10), diff minimality (§ 9.12), normalization (§ 9.13), stability (§ 9.15), and round-trip (§ 9.16); (7) handles every edge case in § 9.17; (8) operates within § 9.19 and § 9.20; (9) passes the corpus referenced in § 9.23.

## 10. Interaction with `pickup`

`match` and `pickup` share a uniform grammar of the form *keyword scrutinee_opt CLAUSES*. They are orthogonal: `match` dispatches on the structure of a single scrutinee using patterns; `pickup` dispatches on free-standing boolean guards. They MAY be nested without closing-keyword ceremony.

When `match` admits guards on its clauses (`pat when g -> e`), those guards follow the same typing and short-circuit rules as guards in `pickup`. `pickup` is not a substitute for `match` guards; it is the canonical form when there is no scrutinee. `match` is not a substitute for `pickup`; using `match` with a scrutinee whose only role is to enable wildcard fall-through is a `pickup` in disguise (see Appendix H).

## 11. Examples

### 11.1 Simple Literal Dispatch

```text
match n
  0  -> "zero"
  1  -> "one"
  -1 -> "minus-one"
  _  -> "other"
```

### 11.2 ADT Decomposition

```text
match shape
  Circle(r)          -> r * r * 3
  Square(side)       -> side * side
  Triangle(a, b, _c) -> a * b / 2
```

### 11.3 Nested Patterns with Guards

```text
match value
  %[_, %{list: [head | tail]}, _] -> handle(head, tail)
  Person{name: n, address: Address{city: c, zip: _}} when c == "Madrid" ->
    greet(n)
  _ -> :ignored
```

### 11.4 Result Unwrapping

```text
match parse(input)
  Ok(Some(v)) -> use(v)
  Ok(None())  -> default
  Error(_)    -> default
```

### 11.5 Map Routing

```text
match request
  %{method: "GET",  path: p} -> fetch(p)
  %{method: "POST", path: p} -> submit(p)
  %{method: m}               -> reject(m)
  _                          -> :malformed
```

### 11.6 Pin Operator

```text
let target = get_tag()

match event.tag
  ^target -> :hit
  _       -> :miss
```

### 11.7 Binary Decoding

```text
match frame
  <<tag, len, _::binary>> -> len
  <<>>                    -> 0
```

## 12. Algebraic Laws

The following equivalences hold under §§ 7 and 8. Each law presumes the absence of side effects on the scrutinee and on patterns where stated; pattern matching itself is pure.

### 12.1 Wildcard absorption

A clause whose pattern is `_` absorbs all subsequent clauses; subsequent clauses are unreachable.

### 12.2 Variable absorption

A clause whose pattern is a single variable `v -> e` absorbs all subsequent clauses (variables match every value, just like wildcards). The body MAY refer to `v`.

### 12.3 Single-clause irrefutable equivalence

`match s with p -> e` ≡ `let p = s in e` when `p` is irrefutable.

### 12.4 Order is contractual

Clause reordering is admissible only when patterns are pairwise non-overlapping. The compiler MAY perform such reordering only if it can prove non-overlap.

### 12.5 Pattern rewriting

A pattern may be rewritten to a structurally equivalent form: `[a, b, c | rest]` ≡ `[a | [b | [c | rest]]]`; punning expansions; and so on. These are syntactic.

### 12.6 Constructor case fusion

When two adjacent clauses share the same outermost constructor and differ only in nested patterns, they MAY be fused into one outer-constructor clause containing a nested `match` on the inner positions, and vice versa. The fusion is purely syntactic and preserves order.

### 12.7 Match-of-Match flattening

`match (match s with C₁) with C₂` is *not* generally simplifiable: the outer scrutinee depends on the inner result, and the laws above do not let the two collapse. The compiler treats nested `match` opaquely.

## 13. Exceptions and Divergence

An exception in the scrutinee propagates and the `match` itself is not entered. An exception in a guard propagates and aborts selection. An exception in a selected branch propagates as in any expression position. Non-termination in the scrutinee, a guard, or a selected branch makes the `match` diverge.

A non-exhaustive `match` whose runtime scrutinee falls outside every pattern raises `case_clause` (or its language-level analogue) with the offending value. The compile-time error of § 6.2 rejects the enumerable-constructor case outright; `case_clause` remains reachable only for domains § 6.2 does not cover (e.g. `Int` scrutinees without a catch-all).

## 14. Tail-Position Behaviour

A branch right-hand side is in tail position with respect to the `match` iff the `match` is itself in tail position. The scrutinee, guards, and pattern-matching machinery are *not* in tail position. This guarantees proper tail calls in any branch:

```text
loop xs acc =
  match xs
    []          -> acc
    [x | rest]  -> loop rest (acc + x)
```

## 15. Compilation and Lowering

A `match` block is lowered to a *decision tree* over the patterns, computed by the algorithm of § 6.3. The decision tree is a sequence of single-position tests (head-shape tests, equality tests, field projections) that converge on the index of the matching clause without re-testing positions already inspected.

Canonical lowering for an ADT `match`:

```text
  test tag(s)
  case Cons_1: bind sub-positions; goto L_1
  case Cons_2: bind sub-positions; goto L_2
  ...
  case Cons_n: bind sub-positions; goto L_n
  default:     goto L_else                  -- unreachable iff exhaustive

L_1: e_1; goto L_end
...
L_n: e_n; goto L_end
L_else: raise(case_clause(s))
L_end:
```

Implementations MAY use jump tables, branch chains, or hybrid strategies, provided they preserve clause order, the side-effect set of guards and branches, and the value produced by the selected clause. Speculative guard execution is forbidden.

## 16. Constant Folding and Specialization

The compiler MUST fold the following statically-determinable cases:

- A `match` whose scrutinee is a literal value reduces to the unique selected clause's right-hand side, with sub-position bindings substituted. If no clause matches, `case_clause` is raised statically (and `W-MATCH-STATIC-NOMATCH` MAY be emitted).
- A wildcard or variable pattern reached as the first clause replaces the entire `match` with the (possibly bound) right-hand side.
- Adjacent literal clauses sharing a right-hand side MAY be fused syntactically into a single or-pattern after the language adds or-patterns (Appendix I.1); today they remain separate clauses.

When a `match` is reduced, source-level diagnostics that previously attached to the keyword span MUST be remapped to the surviving expression's span.

## 17. Macro and Quote Interaction

A `match` is a first-class AST node carrying a head token, a scrutinee expression, and an ordered list of clauses. Each clause carries a pattern, an optional guard, and a right-hand side. Pattern nodes form their own AST sub-grammar (§ 5.1).

- **Hygiene.** Pattern variables introduced inside a macro-generated clause are hygienic with respect to the macro's calling context.
- **Splicing.** A list of zero or more clauses MAY be spliced into a `match` body. Macros constructing `match` nodes are responsible for the linearity of pattern variables (§ 5.4) within each generated clause.
- **Construction.** A macro-generated `match` lacking any clauses is rejected at the macro invocation site with the language's general "empty match" diagnostic (E-MATCH-EMPTY).
- **Source mapping.** Spans propagate from macro template fragments into the generated AST per the language's standard rules.

## 18. Pattern Surface Positions

The pattern sub-grammar of § 5 appears in four distinct surface positions in the language. Their semantics relative to `match` are:

### 18.1 `match` Arms

Canonical position. All of §§ 4-17 apply.

### 18.2 Multi-Clause Function Heads

```text
fn f(...) | p_1 -> e_1 | p_2 -> e_2 | ...
```

A multi-clause function is semantically equivalent to a single-clause function whose body is a `match` on the argument tuple. Each clause's pattern is the argument-tuple pattern; per-clause `when` guards are admitted with the same syntax. Diagnostics reuse the `match` codes (§ 20).

### 18.3 `let` Bindings

```text
let p = e
```

A `let` binding is a single-arm `match` whose pattern MUST be irrefutable (§ 5.16). A refutable `let` pattern is rejected under `E118`, the same pattern-coverage error `match` uses; it does not compile (the historical dedicated `E034` warning code is retired).

The formatter rewrites a `match` containing a single irrefutable-pattern clause into a `let` binding (§ 9.6).

### 18.4 Single-Clause Function Heads

```text
fn f(p) -> e
```

A single-clause function whose head pattern is more refined than a bare variable is desugared to `fn f(_arg) -> match _arg with p -> e`. The rest of the spec applies to the desugared form.

### 18.5 Try-Catch Handlers

```text
try ... catch p_1 -> e_1 | p_2 -> e_2 | ...
```

Catch handlers are clauses whose patterns match against raised exception values. They reuse the pattern grammar of § 5 and the static / dynamic semantics of §§ 6-8 unchanged, except that the scrutinee is the exception value rather than an explicit expression.

### 18.6 Comprehension Generators

`for p <- xs`-style generators use the pattern grammar of § 5 to bind names from each element of `xs`. A pattern that fails to match the element is treated as a filter: the element is silently skipped. This is the only surface position in which a refutable pattern's failure is non-observable; it is documented here for completeness.

## 19. Tooling and IDE Integration

A conforming language server MUST:

- highlight `match` and `when` as keywords; `->` as operator; PascalCase as constructor; `^` as the pin operator;
- on hover of `match`, display the mental-model line (§ 1);
- on hover of a pattern variable, display its narrowed type (§ 6.1.3);
- on hover of a constructor pattern, display the ADT and arity;
- on hover of `when`, display the guard's type;
- provide code actions:
  - *Add wildcard `_` clause* for `E118`;
  - *Convert single-clause `match` to `let`* for `H-MATCH-USE-LET`;
  - *Insert missing constructor* for each Maranget-witnessed missing case;
  - *Inline pin* (rewrite `^x -> ...` as `x_ -> ... when x_ == x`);
- treat each `match` as a foldable region but not as a top-level document symbol;
- grow smart-selection from a clause to its enclosing block in one step.

## 20. Errors and Diagnostics

The compiler MUST produce diagnostics with the following stable identifiers; implementations MAY refine wording but MUST preserve codes. Numeric codes match the current Cure compiler diagnostic registry (`lib/cure/diagnostic/registry.ex`); descriptive aliases are provided for cross-spec consistency. Every `E`-prefixed code is error severity and every `W`-prefixed code is warning severity by construction; there is no per-code override.

- `E118` / `E-MATCH-NONEXHAUSTIVE` — missing constructor at the top level or a tuple position, a duplicate constructor branch, or a reachable branch wrongly marked `impossible` (§ 6.2). Severity: error. Also used for a refutable `let` pattern (§ 18.3). Supersedes the retired `E004`/`E025`/`E034`.
- `E119` / `E-MATCH-STRUCTURE` — a pattern binds a name twice outside the sanctioned repeated-variable form, more than one catch-all, an `impossible`-marked catch-all, a branch after a catch-all, or an open binary/map match with no trailing fallback. Severity: error. Supersedes the retired `E031`/`E032` for these specific shapes.
- `E021` / `E-MATCH-UNKNOWN-RECORD` — the named record type itself is not in scope. Severity: error.
- `E022` / `E-MATCH-RECORD-FIELD-TYPE` — a field reference does not exist in the record's declared schema, or a sub-pattern's static type is incompatible with the declared field type. Severity: error.
- `E091` / `E-MATCH-UNKNOWN-CONSTRUCTOR` — PascalCase pattern name is not a
  constructor of the scrutinee type; also covers an unbound pin reference
  (§ 5.13, superseding the retired `E024`).
- `E093` / `E-MATCH-TYPE-MISMATCH` — general type mismatch, covering a non-literal-atom map key (superseding the retired `E023`) and a branch join with no common upper bound (superseding the retired `E033`).
- `E-MATCH-EMPTY` — `match` block contains no clauses (macro-generated case). Severity: error.
- `E-MATCH-CONSTRUCTOR-ARITY` — constructor pattern arity disagrees with declaration. Severity: error.
- `H-MATCH-USE-LET` — single-arm irrefutable-pattern `match` rewritten to `let`. Severity: hint.
- `H-MATCH-LINE-TOO-LONG` — clause cannot fit within `max_line_width` even when wrapped. Severity: hint.
- `H-MATCH-COMMENT-RELOCATED` — internal stray comment relocated by the formatter. Severity: hint.

The following descriptive aliases from earlier revisions of this document no longer correspond to a reachable diagnostic: `W-MATCH-UNREACHABLE` (general-purpose clause subsumption is not checked; see § 6.4 for the narrower checks that remain), `W-MATCH-EFFECTFUL-GUARD`, and `W-MATCH-STATIC-NOMATCH`.

## 21. Non-Goals

- **Predicate dispatch without a scrutinee.** Use `pickup`.
- **Truthy/falsy coercion in guards.** `match` guards are strictly `Bool` (§ 6.1.4).
- **Implicit constructor fields.** Bare constructor resolution applies only to
  nullary constructors. Constructors with fields must spell and pattern-match
  those fields explicitly.
- **Fall-through.** Each evaluation selects exactly one clause.
- **Pattern-level effects.** Pattern matching is pure. Side effects belong in the scrutinee, the guards, or the branch bodies.

## 22. Stability, Versioning, and Deprecation

- Specification version: 1.0.0.
- Behaviour of `match` defined in §§ 1-21 is stable. Future revisions MAY add capabilities (Appendix I, Appendix L) but MUST NOT alter the value, side-effect set, or termination behaviour of any program conforming to this revision.
- `match` and `when` are reserved indefinitely.
- The pattern sub-grammar of § 5 is stable. New pattern shapes (or-patterns, view patterns, range patterns, dependent matches) MAY be added in minor revisions; existing shapes MUST NOT be removed.
- Numeric diagnostic codes are immutable and MUST NOT be reused for different conditions. (Post-1.0.0 note: the compiler's dependent-pipeline rewrite retired several codes this specification originally cited -- `E004`, `E023`-`E025`, `E031`-`E034` -- and consolidated their conditions under `E091`, `E093`, `E118`, and `E119`; see § 20.)

## 23. Summary

`match` is a strict, ordered, structural-dispatch expression. It evaluates a scrutinee once and matches it, in source order, against a non-empty list of patterns; the first matching pattern (whose guard, if any, succeeds) selects the corresponding branch. Patterns introduce hygienic, linear bindings into branch and guard scope. Exhaustiveness is checked by a Maranget-style algorithm and reported as a compile-time error (`E118`); a `match` over an enumerable-constructor scrutinee that omits a reachable constructor does not compile.

> **`match` walks the clauses and picks up the first one whose pattern matches the scrutinee.**

`match` and its companion `pickup` (`docs/PICKUP.md`) are the only branching constructs in the language.

## 24. Appendix A — Acceptance Test Suite

### A.1 Selection

```text
match 0
  0 -> :a
  1 -> :b
  _ -> :c
-- expected: :a

match 1
  0 -> :a
  1 -> :b
  _ -> :c
-- expected: :b

match 99
  0 -> :a
  1 -> :b
  _ -> :c
-- expected: :c
```

### A.2 Variable Binding and Scope

```text
match Some(42)
  Some(x) -> x + 1
  None()  -> 0
-- expected: 43

match %[1, 2, 3]
  %[a, b, c] -> a + b + c
  _          -> 0
-- expected: 6
```

### A.3 Repeated Variables

```text
match %[7, 7]
  %[x, x] -> :equal
  _       -> :different
-- expected: :equal

match %[7, 8]
  %[x, x] -> :equal
  _       -> :different
-- expected: :different
```

### A.4 Pin Operator

```text
let target = :hit_tag

match :hit_tag
  ^target -> :ok
  _       -> :no
-- expected: :ok

match :other
  ^target -> :ok
  _       -> :no
-- expected: :no
```

### A.5 Guards

```text
match 5
  n when n < 0 -> :neg
  n when n > 0 -> :pos
  _            -> :zero
-- expected: :pos
```

### A.6 Static Rejection

```text
match x
  "yes" -> 1
  42    -> 2
-- E-MATCH-BRANCH-MISMATCH (Int and String have no LUB)

match value
  Missing -> 0
-- E091 / E-MATCH-UNKNOWN-CONSTRUCTOR

match m
  %{(1 + 1): v} -> v
-- E093 (map key is not a literal atom)

match v
  ^undefined -> 0
  _          -> 1
-- E091 (pin references an unbound name)
```

### A.7 Exhaustiveness

```text
type RGB = | Red | Green | Blue

match c
  Red()   -> 1
  Green() -> 2
-- E118 (missing: Blue)

match %[a, b]
  %[Ok(_),    Ok(_)]   -> :both
  %[Error(_), Ok(_)]   -> :left
-- E118 (missing witness e.g. %[Ok(_), Error(_)] at position 2)
```

### A.8 Reachability

```text
match x
  _ -> :a
  0 -> :b   -- E119 (branch after a catch-all)
```

### A.9 Layout

```text
match xs
  []         -> :empty
  [h | _t]   -> :nonempty
z + 1
-- parses as `match` followed by an independent expression

match req

  %{method: m} -> m

  _            -> :unknown
-- parses identically to the dense form
```

## 25. Appendix B — Glossary

- **Arm / Clause.** A line of the form *pattern* [`when` *guard*] `->` *expression*.
- **Block.** The indented region of clauses following the `match` keyword.
- **Branch.** Synonym for *right-hand side*: the expression to the right of `->`.
- **Constructor pattern.** A pattern of the form `C(p_1, ..., p_n)` matching values built with constructor `C`.
- **Decision tree.** The data structure produced by lowering a `match` (§ 15).
- **Exhaustive.** A clause list is exhaustive iff every value of the scrutinee's type is matched by some clause.
- **Guard.** The optional `when` expression between a pattern and its arrow (§ 5.15).
- **Irrefutable.** A pattern that cannot fail to match any value of its statically-known type (§ 5.16).
- **Linear (in semantics).** A name bound at most once per pattern in `σ'`; later occurrences become equality tests (§ 5.4).
- **Maranget's algorithm.** The decidable exhaustiveness procedure for ADT-and-finite-shape patterns (§ 6.3).
- **Pattern.** A syntactic form that matches a value's structure and binds sub-positions to names (§ 5).
- **Pin.** The `^x` operator that compares against an already-bound value (§ 5.13).
- **Punning.** The shorthand `%{x, y}` ≡ `%{x: x, y: y}` and `T{name}` ≡ `T{name: name}`.
- **Refutable.** A pattern that may fail to match.
- **Scrutinee.** The expression after the `match` keyword whose value is dispatched on.
- **Selection.** Choosing exactly one clause to execute per evaluation.
- **Silent binding.** A pattern variable named `_name`; binds but suppresses the unused-variable warning.
- **Wildcard.** The pattern `_`, which matches any value and binds nothing.

## 26. Appendix C — Change Log

- **1.0.0** — Initial formal specification of the existing `match` construct. Consolidates and supersedes the pattern-matching content in `docs/LANGUAGE_SPEC.md` § "Pattern Matching"; refers to `docs/PATTERNS.md` as a complementary tutorial reference. Locks numeric diagnostic codes (`E004`, `E021`-`E025`, `E031`-`E034`) and introduces descriptive aliases. (Several of these codes were later retired by the dependent-pipeline rewrite and their conditions consolidated under `E091`, `E093`, `E118`, and `E119`; see § 20.)
- **v0.33.0 publication** — Specification published into HexDocs alongside `docs/PICKUP.md` via `mix.exs` `docs.extras`. `docs/LANGUAGE_SPEC.md` § "Pattern Matching" cross-references this document as the normative source. The companion `pickup` page on the Cure website (`/pickup`) and the `/match` user-facing tutorial both link to this document. No normative content changed.

## 27. Appendix D — Index of Normative Requirements

- § 3.1 — `match`/`when` are reserved.
- § 4.1 — Block non-empty; scrutinee on the keyword line; clauses on their own lines.
- § 5.4 — Pattern variables are linear in semantics; later occurrences are synthetic equality guards.
- § 5.10 — Map keys MUST be literal values; non-literal keys are rejected.
- § 5.12 — Nullary constructors MUST be written with `()`.
- § 5.13 — Pin references MUST resolve to in-scope bindings.
- § 6.1 — Patterns MUST be statically compatible with the scrutinee; branches MUST share a join.
- § 6.2 — Implementations MUST reject a missing reachable constructor, at the top level or a tuple position, under `E118`.
- § 7.1 — Scrutinee evaluated exactly once; clauses tried in source order.
- § 9.1-9.25 — Formatter rules in full.
- § 14 — Branches in tail position iff `match` is; scrutinee, guards, and pattern machinery are not.
- § 15 — Lowerings MUST preserve clause order, side-effect set, and selected value; speculative guard execution forbidden.
- § 16 — Compiler MUST perform the listed constant folds.
- § 17 — Macro-generated `match` MUST contain at least one clause.
- § 19 — Language server MUST provide the listed surfaces.
- § 22 — Behaviour stable; existing diagnostic codes immutable.

## 28. Appendix E — Reference Implementation Sketch

This appendix provides non-normative pseudocode that an implementer MAY use as a starting point.

### E.1 Parser

```text
parse_match(tokens):
  expect("match")
  s = parse_expression()
  expect(NEWLINE)
  expect(INDENT)

  clauses = []
  while peek() != DEDENT:
    p = parse_pattern()
    g = nil
    if peek() == "when":
      advance()
      g = parse_expression()
    expect("->")
    e = parse_expression()
    clauses.append(Clause(pattern = p, guard = g, rhs = e))
    if peek() != DEDENT:
      expect(NEWLINE)

  expect(DEDENT)
  return MatchNode(scrutinee = s, clauses = clauses)
```

### E.2 Pattern Compiler

```text
compile_pattern(p, subject_var, scope):
  if p is Wildcard:
    return ([], scope)
  if p is Variable(name):
    if name in scope:
      fresh = gensym()
      return ([guard(fresh == scope[name])], scope ∪ {name → subject_var})
    return ([], scope ∪ {name → subject_var})
  if p is Pin(name):
    if name not in scope: error E091
    return ([guard(subject_var == scope[name])], scope)
  if p is Literal(v):
    return ([test(subject_var == v)], scope)
  if p is Tuple(elems):
    return compile_decompose(:tuple, elems, subject_var, scope)
  if p is List(...):
    return compile_list(p, subject_var, scope)
  if p is Map(entries):
    return compile_map(entries, subject_var, scope)
  if p is Record(tag, fields):
    return compile_record(tag, fields, subject_var, scope)
  if p is Constructor(tag, args):
    return compile_constructor(tag, args, subject_var, scope)
  if p is Binary(segments):
    return compile_binary(segments, subject_var, scope)
```

### E.3 Exhaustiveness Checker

```text
check_exhaustive(clauses, scrutinee_type):
  -- Top-level pass
  shapes = {flat_classify(c.pattern) for c in clauses}
  missing = expected_shapes(scrutinee_type) \ shapes
  for m in missing: error E118 with witness m

  -- Tuple-position pass for tuples of enumerable elements
  if scrutinee_type is enumerable_tuple:
    matrix = [pattern_row(c.pattern) for c in clauses]
    witness = maranget_first_uncovered(matrix, scrutinee_type)
    if witness != none: error E118 with witness
```

### E.4 Type Checker

```text
type_match(Γ, node):
  τ_s = type(Γ, node.scrutinee)
  τ_acc = fresh()
  for c in node.clauses:
    Γ_p = pattern_type(Γ, c.pattern, τ_s)        -- E022, E021, E091 etc.
    if c.guard:
      unify(type(Γ_p, c.guard), Bool)            -- general guard-type error
    τ_e = type(Γ_p, c.rhs)
    τ_acc = join(τ_acc, τ_e)                     -- E093 on failure
  check_exhaustive(node.clauses, τ_s)            -- E118
  return τ_acc
```

### E.5 Formatter

```text
format_match(node, config):
  -- Single-arm irrefutable rewrite
  if len(node.clauses) == 1
     and is_irrefutable(node.clauses[0].pattern)
     and node.clauses[0].guard is nil
     and surrounding_admits_let(node):
       emit_hint(H-MATCH-USE-LET)
       return format_let(node.clauses[0].pattern, node.scrutinee,
                          node.clauses[0].rhs, config)

  heads = [render_head(c) for c in node.clauses]
  width = max(grapheme_width(h) for h in heads)

  any_multiline = any(is_multiline(c.rhs) for c in node.clauses)
  fits_aligned  = (config.indent + config.indent_step + width + 4 +
                   max_rhs_width(node)) <= config.max_line_width
  too_wide      = width > config.alignment_limit

  form = (Wrapped if any_multiline
          else Unaligned if (too_wide or not fits_aligned)
          else Aligned)

  return render(node, form, config)
```

## 29. Appendix F — Worked Pattern Examples

### F.1 Literal Tour

```text
match n
  0  -> "zero"
  1  -> "one"
  -1 -> "minus-one"
  42 -> "the answer"
  _  -> "other"
```

### F.2 Tuple and List Tour

```text
match t
  %[a, b]    -> a + b
  %[a, b, c] -> a + b + c
  _          -> 0

match xs
  []                -> "empty"
  [_]               -> "singleton"
  [_, _]            -> "pair"
  [_, _, _ | _rest] -> "three-or-more"
```

### F.3 Map Routing with Punning

```text
match request
  %{method: "GET",  path: p} -> "fetch "  <> p
  %{method: "POST", path: p} -> "submit " <> p
  %{method: m}               -> "other "  <> m
  _                          -> "malformed"

match m
  %{x, y} -> x + y         -- punning: %{x: x, y: y}
  _       -> 0
```

### F.4 Records and Nested ADT

```text
match person
  Person{name, age}                    -> salute(name, age)
  Person{name, address: Address{city}} -> greet(name, city)

match result
  Ok(Some(v)) -> v
  Ok(None())  -> default
  Error(_)    -> default
```

### F.5 ADT With Guards

```text
match shape
  Circle(r)          when r > 0 -> r * r * 3
  Square(s)          when s > 0 -> s * s
  Triangle(a, b, _c) when a > 0 && b > 0 -> a * b / 2
  _                                       -> 0
```

### F.6 Pin and Repeated-Variable Combination

```text
let expected = compute_target()

match incoming
  %[^expected, ^expected] -> :both_match
  %[x, x]                 -> :both_equal_but_unexpected
  _                       -> :neither
```

### F.7 Binary Decoding

```text
match frame
  <<0xC0, code, _::binary>> -> {:cmd, code}
  <<0xC1, code>>            -> {:err, code}
  <<>>                      -> :empty
  _                         -> :unknown
```

### F.8 Recursive Loop

```text
fn sum(xs: List(Int)) -> Int =
  match xs
    []         -> 0
    [h | rest] -> h + sum(rest)
```

## 30. Appendix G — Style Guide and Idioms

Non-normative.

### G.1 Use `match` for Structural Dispatch, `pickup` for Predicate Dispatch

When the deciding question is *"what shape does this value have?"*, use `match`. When it is *"which of these conditions holds?"*, use `pickup`. Do not destructure with `match` only to immediately re-test parts of the bound value with a chain of `if`s or a `pickup`; use a guard (`when`) inside the `match` clause instead.

### G.2 Order Clauses From Specific to General

Place the most specific patterns first. A clause placed after a wildcard/variable catch-all is rejected outright (`E119`); use this as a sanity check. The compiler does not, however, catch every case of a more specific clause shadowed by an earlier non-catch-all clause -- ordering discipline still matters.

### G.3 Make Coverage Visible

If a `match` is statically exhaustive, do not add a defensive `_ -> ...` clause. Let the type checker prove totality. A defensive wildcard hides future coverage gaps when new constructors are added to the matched type.

### G.4 Use `_name` for Intentional Discards

Bind but do not warn. `[_first, _second | _rest]` reads as "I see three positions, I do not need them, and that is intentional."

### G.5 Prefer Punning for Records and Maps

`Person{name, age}` and `%{x, y}` are clearer than the explicit `name: name` / `x: x` forms. Reserve the explicit form for fields whose pattern is non-trivial.

### G.6 Use the Pin Operator for Equality Tests Against Closed Values

`^x` is more direct than introducing a fresh variable and writing `_y when _y == x`. The compiler lowers `^x` to exactly that, so the runtime cost is identical, but the intent is clearer at the source level.

### G.7 Keep Patterns Shallow Where Possible

A pattern that is more than three levels deep is a candidate for two passes: an outer `match` that destructures the top, an inner `match` that destructures the result. The compiler can always fuse them; the reader can rarely de-fuse them.

### G.8 Prefer Pure Guards

A guard that performs I/O is evaluated only after a pattern matches but before the branch is selected. This is rarely the user's intent. Restrict effects to the scrutinee or the branch bodies.

## 31. Appendix H — Anti-Patterns

Non-normative.

### H.1 `match` as a Replacement for `pickup`

```text
match _
  _ when ready?    -> launch ()
  _ when timed_out? -> retry ()
  _                 -> wait ()
```

A `match` whose patterns are uniformly wildcards is a `pickup` in disguise. Use `pickup` directly:

```text
pickup
  ready?     -> launch ()
  timed_out? -> retry ()
  else       -> wait ()
```

### H.2 Bare Nullary Constructors

```text
match opt
  Some(x) -> x
  None    -> default
```

This is equivalent to writing `None()`. Bare PascalCase names are resolved
against the scrutinee type, so an unknown name produces a constructor
resolution error rather than becoming a variable.

### H.3 Defensive Wildcards on Closed ADTs

```text
type RGB = | Red | Green | Blue

match c
  Red()   -> 1
  Green() -> 2
  Blue()  -> 3
  _       -> impossible ()    -- silences the future E118 error
```

The wildcard prevents the type checker from rejecting the `match` when a new variant is added to `RGB`. Drop it; let `E118` guide future updates.

### H.4 Deep Nested Patterns Without Naming

```text
match req
  Request{user: User{profile: Profile{settings: Settings{theme: t}}}} -> use(t)
```

Easy to write, hard to read, and brittle under refactoring of the inner records. Either destructure progressively, or name the intermediate values.

### H.5 Effectful Guards

```text
match x
  _ when log_and_check(x) -> handle(x)
  _                       -> default
```

Side effects in guards are conditional on every prior clause's outcome. Move the side effect into the scrutinee or the branch, keep the guard pure.

### H.6 Recapitulating the Pattern in the Branch

```text
match s
  Some(x) -> Some(x + 1)
  None()  -> None()
```

When the branch reconstructs the same constructor it just destructured, prefer a higher-order operation (`Option.map`) or a more general combinator. Pattern-match only to extract; let combinators handle the wrapping.

## 32. Appendix I — Reserved Future Syntax

The following forms are reserved by the language. They MUST NOT be accepted by a 1.0.0 conforming parser; their reservation exists so future revisions may add them without breaking source.

### I.1 Or-Patterns

```text
match value
  Red() | Green() | Blue() -> :primary
  _                        -> :other
```

A future revision MAY admit or-patterns combining alternative shapes that bind disjoint or compatible variable sets.

### I.2 View Patterns

```text
match xs
  view(reverse, [last | _]) -> last
  _                         -> nil
```

A future revision MAY admit view patterns: applying a function before matching against the result.

### I.3 Range Patterns

```text
match age
  0..12   -> :child
  13..19  -> :teen
  _       -> :adult
```

Reserved; today the compiler rejects range patterns at parse time.

### I.4 Dependent / Type-Level Patterns

```text
match (n, vec)
  (Z(),    Nil())               -> base
  (S(k),   Cons(x, xs))         -> step k x xs
```

A future revision MAY extend exhaustiveness to dependently-typed scrutinees, where the shape of one position constrains the type of another.

### I.5 As-Patterns

```text
match xs
  [h | _] as whole -> consume whole h
```

A future revision MAY admit as-patterns binding both a sub-shape and the whole. Today a clause may achieve the same effect by pattern-matching the whole into a variable and re-matching its parts inside the body.

## 33. Appendix J — Soundness Proof Sketch

Non-normative.

### J.1 Statement

Given the typing rule T-Match (§ 6.6) and the small-step rules of § 8.2:

**Theorem (Soundness).** If `· ⊢ e : τ` and `· ⊢ e →* σ ⊢ e'`, then either `e'` is a value `v` with `· ⊢ v : τ`, or `e'` is a raised exception (including `case_clause` for a non-exhaustive `match`), or there exists `e''` such that `σ ⊢ e' → σ' ⊢ e''`.

### J.2 Proof Structure

By Progress and Preservation, with new cases for `match`.

**Progress.** For every `· ⊢ e : τ` with `e = match s with C`:

- If `s` is not a value, SM-Scrut applies (by IH on `s`).
- If `s` is a value `v` and `C` is empty, SM-NoClause applies (raising `case_clause(v)`).
- If `s` is a value `v` and `C = (p, g, e_1) ; C'`:
  - if `match(p, v) = ⊥`, SM-Skip-Pat applies;
  - if `match(p, v) = σ_p`:
    - if `g` is absent or evaluates to `true`, SM-Hit applies;
    - if `g` evaluates to `false`, SM-Skip-Guard applies;
    - if `g` is non-value, the language's general expression-reduction step applies under the guard's evaluation context.

**Preservation.** Each of SM-Scrut, SM-Hit, SM-Skip-Pat, SM-Skip-Guard, SM-NoClause preserves the typing judgment of the residual:

- SM-Scrut: by IH on the scrutinee.
- SM-Hit: by T-Match's branch-typing premise on `e_1` under `Γ_1`.
- SM-Skip-Pat / SM-Skip-Guard: the residual `match v with C'` is well-typed by T-Match restricted to `C'` (using the branch-join sub-derivation).
- SM-NoClause: `raise(case_clause(v))` is well-typed at every type by the language's exception rule.

### J.3 Corollaries

- **Totality (with caveat).** A statically exhaustive `match` (§ 6.2) cannot produce `case_clause`; SM-NoClause is unreachable.
- **Pattern purity.** Pattern matching itself contributes no observable effects; all effects in a `match` come from the scrutinee, guards, or selected branch.

## 34. Appendix K — Bibliography and Related Work

Non-normative.

- **Maranget, L.** *Warnings for Pattern Matching* (2007). The reference algorithm for decidable exhaustiveness and redundancy on ADT patterns; the basis for § 6.3.
- **Standard ML.** First mainstream language to combine algebraic data types with exhaustive pattern compilation; influence visible in `match`'s emphasis on totality.
- **OCaml.** Generalizes ML pattern matching with or-patterns, view patterns, and exception patterns; the source of several reserved-future-syntax candidates (Appendix I).
- **Erlang.** Source of the `^` pin operator and the `when` guard syntax adopted here.
- **Elixir.** Source of the `%{...}` map and `^pin` conventions; close source of inspiration for Cure's surface-level pattern syntax.
- **Haskell.** Pattern guards and view patterns; comparison point for design discussions in Appendix L.
- **Scala.** `match`/`case` with extractors; the closest cousin to our reserved view-pattern form (I.2).
- **Wadler, P.** *Views: a way for pattern matching to cohabit with data abstraction* (1987). Foundational for any future view-pattern extension.

## 35. Appendix L — Open Questions and Future Directions

Non-normative.

### L.1 (Resolved) Non-Exhaustive `match` and `let` Are Errors

This was an open question in earlier drafts of this specification. It is resolved: both a non-exhaustive `match` over an enumerable-constructor scrutinee and a refutable `let` pattern are compile-time errors (`E118`), not warnings.

### L.2 Or-Patterns

Reserved (Appendix I.1). The non-trivial design point is the typing of variables bound in only some alternatives; the conservative answer is to require every or-alternative to bind exactly the same variable set with compatible types.

### L.3 View Patterns

Reserved (Appendix I.2). Requires a careful purity story: the viewing function MUST be pure to keep pattern matching pure (§ 6.7).

### L.4 Range Patterns

Reserved (Appendix I.3). The non-trivial design point is exhaustiveness over open numeric domains; a `1..10` range partitions `Int` into a proper subset, complicating Maranget.

### L.5 Dependent / Type-Level Matching

Reserved (Appendix I.4). The interaction with the language's existing dependent-type fragment (`docs/DEPENDENT_TYPES.md`) is non-trivial and out of scope for 1.0.0.

### L.6 Maranget Completeness for Refinement Types

The compiler currently runs Maranget on ADT shapes and a hand-rolled descent for `Bool`/`Result`/`Option`-tupled scrutinees (`docs/PATTERNS.md` § Exhaustiveness). A future revision MAY consult the refinement-type system (§ 6.15) to refine the analysis on integer-range and string-set scrutinees.

### L.7 Decision-Tree Sharing Across `match` Blocks

The optimizer currently lowers each `match` to its own decision tree. A future revision MAY share decision-tree fragments across `match` blocks that scrutinize the same value with overlapping patterns — for example, two consecutive `match`es over a parsed token stream.

### L.8 Statement-Position `match`

Like `pickup` (`PICKUP.md` § L.7), this revision treats `match` exclusively as an expression. A future revision MAY admit statement-position `match` whose branches MAY have side-only effects.

## 36. Appendix M — Specification Metadata and Colophon

### M.1 Metadata

- **Document title.** The `match` Construct — Language Specification.
- **Specification version.** 1.0.0.
- **Status.** Stable.
- **Companion construct.** `pickup` (predicate dispatch); see `docs/PICKUP.md`.
- **Related references.** `docs/PATTERNS.md` (pattern-shape tutorial), `docs/LANGUAGE_SPEC.md` § "Pattern Matching" (overview, superseded by this document for normative purposes), `docs/BINARIES.md` (binary segment grammar).
- **Reserved keywords introduced.** `match`, `when`.
- **Pin sigil.** `^` (in pattern position only).
- **Reserved keywords for future use.** `as`, `view`, `..`, the or-pattern `|` alternative form (positional, in pattern position).

### M.2 Document Structure

The specification is organized in five strata:

1. **Surface** (§§ 1-5): introduction, conformance terminology, lexical syntax, grammar, patterns.
2. **Semantics** (§§ 6-8): static, dynamic, and operational semantics.
3. **Surface conventions** (§§ 9-11): formatting, interaction with `pickup`, examples.
4. **Theory and machinery** (§§ 12-19): laws, exceptions, tail calls, compilation, folding, macros, surface positions, tooling.
5. **Closure** (§§ 20-23): diagnostics, non-goals, stability, summary.

Appendices A-D supply conformance criteria, glossary, change log, and a normative-requirement index. Appendices E-L supply non-normative implementer guidance, idioms, anti-patterns, reserved syntax, the soundness sketch, related work, and deferred questions. Appendix M (this) supplies metadata.

### M.3 How to Read This Document

- An **implementer** writing a parser or pattern compiler should read §§ 3-5, § 8, Appendix A, and Appendix E.
- An **implementer** writing a type checker should read §§ 5-6, § 8, § 17, Appendix A, and Appendix J.
- An **implementer** writing a formatter should read § 9 in full, § 20, and Appendices A and E.
- A **language-server author** should read §§ 5-6, § 9, § 19, and § 20.
- A **language user** writing code should read §§ 1, 5, 11, 18, 21, and Appendices F (worked examples), G (style guide), and H (anti-patterns).
- A **language designer** considering an extension should read §§ 22 and 23, and Appendices I, K, and L.

### M.4 Relationship to `docs/PATTERNS.md`

`docs/PATTERNS.md` is a tutorial-style reference for the *pattern shapes* accepted by the compiler. It uses concrete Erlang-mapping examples to ground each shape. This document, by contrast, is a *normative specification* for the `match` construct as a whole, using the pattern shapes of `PATTERNS.md` as building blocks. The two are intended to coexist: when in doubt, consult `MATCH.md` for what is required; consult `PATTERNS.md` for what compiles to what.

### M.5 Review Procedure

Errata and proposed amendments to this specification follow the language's general request-for-comments process. Editorial corrections that do not alter normative requirements MAY be applied without a version bump; any change to a MUST or MUST NOT clause requires a new minor or major revision and a corresponding entry in Appendix C.

### M.6 Colophon

This specification is intended to be read end-to-end at first encounter and consulted by section thereafter. Its prose is deliberately repetitive at the joints between informal and formal sections, so that a reader picking up at any one section receives the full context of the rule under discussion.

The mental model that a reader should retain after closing this document is exactly one sentence:

> **`match` walks the clauses and picks up the first one whose pattern matches the scrutinee.**

Everything else in the specification exists to make that intuition mechanically precise.

---

## End of Specification

The specification of `match` at version 1.0.0 is complete. An implementation that satisfies every MUST clause in §§ 1-22 and Appendix D, refuses every program identified as a static error in § 20, and produces every diagnostic listed in § 20 is conforming. Anything beyond is implementation-defined.

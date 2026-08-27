# The `pickup` Construct
## Language Specification, Version 1.0.0

**Status.** Stable.
**Revision.** 1.0.0 (Initial release).
**Predecessor.** None. `pickup` replaces the legacy `if`/`elif` construct, which is removed in this revision.
**Companion construct.** `match` (structural dispatch).

---

## Table of Contents

1. Introduction
2. Conformance Terminology
3. Lexical Syntax
4. Grammar
5. Static Semantics
6. Dynamic Semantics
7. Formal Operational Semantics
8. Formatting Rules
9. Interaction with `match`
10. Examples
11. Algebraic Laws
12. Exceptions and Divergence
13. Tail-Position Behaviour
14. Compilation and Lowering
15. Constant Folding and Specialization
16. Macro and Quote Interaction
17. Migration from `if`
18. Tooling and IDE Integration
19. Errors and Diagnostics
20. Non-Goals
21. Stability, Versioning, and Deprecation
22. Summary
23. Appendix A — Acceptance Test Suite
24. Appendix B — Glossary
25. Appendix C — Change Log
26. Appendix D — Index of Normative Requirements
27. Appendix E — Reference Implementation Sketch
28. Appendix F — Worked Migration Examples
29. Appendix G — Style Guide and Idioms
30. Appendix H — Anti-Patterns
31. Appendix I — Reserved Future Syntax
32. Appendix J — Soundness Proof Sketch
33. Appendix K — Bibliography and Related Work
34. Appendix L — Open Questions and Future Directions
35. Appendix M — Specification Metadata and Colophon

---

## 1. Introduction

`pickup` is a control-flow expression that selects one of several branches by evaluating boolean guards in source order. It is the predicate-dispatch counterpart to `match`, which dispatches on the structural shape of a value. Together, `match` and `pickup` are the only branching constructs in the language. There is no `if`, no `unless`, no ternary form.

The construct is governed by a single mental model:

> **`pickup` walks the clauses and picks up the first one whose guard is true.**

Every other rule in this document exists to make that intuition mechanically precise.

## 2. Conformance Terminology

The key words **MUST**, **MUST NOT**, **SHALL**, **SHOULD**, **SHOULD NOT**, and **MAY** are interpreted as in RFC 2119, restricted to the language's compiler, parser, type checker, optimizer, formatter, and language server.

## 3. Lexical Syntax

### 3.1 Reserved Words

`pickup` and `else` are reserved keywords. They MUST NOT be used as identifiers, type names, module names, or labels. `else` is reserved globally — including in positions where it currently has no meaning — so that future syntactic extensions cannot break source.

### 3.2 Layout

`pickup` participates in the language's standard indentation-sensitive layout. No new lexical rules are introduced; the rules already governing `match` and other indented constructs apply unchanged.

## 4. Grammar

The grammar is given in EBNF. `INDENT` and `DEDENT` denote synthetic tokens emitted by the layout pass.

```text
pickup_expr     ::= "pickup" NEWLINE INDENT clause_list DEDENT

clause_list     ::= guard_clause { NEWLINE guard_clause } NEWLINE terminal_clause [ NEWLINE ]
                  | terminal_clause [ NEWLINE ]

guard_clause    ::= expression "->" expression

terminal_clause ::= "else" "->" expression
                  | "true" "->" expression       -- alternative form, normalized by the formatter
```

### 4.1 Notes on the Grammar

- A `pickup` block MUST contain at least one clause. The single clause MAY be the terminator alone.
- The terminator MUST be last; any clause following it is a syntax error.
- `expression` is the language's existing expression non-terminal. Any expression of type `Bool` is admissible as a guard (§ 5.1).
- The right-hand side of any clause is a full expression and MAY itself be a `pickup`, a `match`, a `let`, a function call, or any other expression form.
- The `"true" "->" expression` form is grammatically a guard clause; it satisfies the totality check of § 5.2 only when it appears in last position, in which case it is normalized to `else -> expression` by the formatter (§ 8.3).

### 4.2 Block Termination (Parser Rule)

A `pickup` block extends through every consecutive line indented strictly deeper than the column of the `pickup` keyword. It ends at the first subsequent line whose indentation is less than or equal to that column, or at end-of-file, whichever comes first. Blank lines are insignificant to the parser.

This rule is identical to the rule for `match` and is shared with every other indented-block construct in the language. The formatter applies a stricter discipline (§ 8.1).

## 5. Static Semantics

### 5.1 Typing (Informal)

Each guard MUST have type `Bool`. No implicit conversion is performed; a non-`Bool` guard is rejected with `E-PICKUP-GUARD-TYPE`. The result type of a `pickup` expression is the least upper bound of the types of its branches; if no such bound exists, the program is rejected with `E-PICKUP-BRANCH-MISMATCH`.

### 5.2 Exhaustiveness

A `pickup` block MUST terminate in a clause that is statically known always to succeed. Two forms qualify:

1. an `else -> e` clause (canonical), or
2. a clause whose guard is the literal `true` (alternative).

A block satisfying neither is rejected with `E-PICKUP-NO-ELSE`. The formatter normalizes form (2) to form (1) per § 8.3. Either form makes `pickup` total: a well-typed `pickup` cannot fail with a "no clause matched" condition at runtime.

### 5.3 Reachability (Informal)

A guard `g_k` is *unreachable* if the compiler can prove that for every program state in which the `pickup` is evaluated, at least one of `g_1, ..., g_{k-1}` evaluates to `true`. The compiler SHOULD warn (`W-PICKUP-UNREACHABLE`) but MUST NOT reject. A provably unreachable terminator triggers `W-PICKUP-DEAD-ELSE` and is retained syntactically. (Neither warning is currently emitted by the compiler; the corresponding registry codes `W081`/`W082` are retired with "no first-party producer remains".)

### 5.4 Scoping

Each clause introduces its own lexical scope:

- A guard `g_i` is evaluated in the scope enclosing the `pickup`, extended with bindings introduced by `g_i` itself.
- The right-hand side `e_i` is evaluated in the scope of `g_i`.
- Bindings from `g_i`/`e_i` are not visible in any other clause.
- No binding introduced inside a clause escapes the `pickup` expression.

### 5.5 Typing Judgment (Formal)

```text
                       Γ ⊢ e_else : τ
   ─────────────────────────────────────────────  (T-Pickup-Else)
        Γ ⊢ pickup (else -> e_else) : τ

   Γ ⊢ g : Bool       Γ ⊢ e : τ_1
   Γ ⊢ pickup C : τ_2     τ = τ_1 ⊔ τ_2
   ─────────────────────────────────────────────  (T-Pickup-Cons)
        Γ ⊢ pickup (g -> e ; C) : τ
```

`⊔` denotes the least upper bound under the language's subtyping relation. If the join does not exist, the rule does not apply and `E-PICKUP-BRANCH-MISMATCH` is emitted.

### 5.6 Subtyping at the Join Point

Branch types unify by repeated application of the binary join:

```text
   τ_pickup = τ_1 ⊔ τ_2 ⊔ ... ⊔ τ_n ⊔ τ_else
```

Type-level reordering of branches is sound because `⊔` is associative and commutative; semantic reordering of guards is not (§ 6.1).

### 5.7 Effect Analysis

```text
   eff(pickup g_1 -> e_1 ; ... ; else -> e_else)
       ⊆ eff(g_1) ∪ eff(e_1) ∪ ... ∪ eff(g_n) ∪ eff(e_n) ∪ eff(e_else)
```

This is a sound over-approximation. A guard whose effect set escapes the language's `Pure` capability triggers `W-PICKUP-EFFECTFUL-GUARD`.

### 5.8 Reachability Lattice

Reachability is computed on the lattice `⊥ < Unreachable < Maybe-Reachable < Reachable`. Clause `i` is `Unreachable` iff `¬g_1 ∧ ... ∧ ¬g_{i-1}` is statically known to be `false`. The terminator is `Unreachable` iff `¬g_1 ∧ ... ∧ ¬g_n` is unsatisfiable. The analysis is sound but, in general, incomplete; the terminator is always retained syntactically.

### 5.9 Free Variables

```text
   FV(pickup g_1 -> e_1 ; ... ; else -> e_else)
       =  FV(g_1) ∪ FV(e_1) ∪ ... ∪ FV(g_n) ∪ FV(e_n) ∪ FV(e_else)
```

with bindings introduced inside any clause removed from that clause's contribution before the union.

### 5.10 Substitution

```text
   [v/x] (pickup g_1 -> e_1 ; ... ; else -> e_else)
       = pickup [v/x]g_1 -> [v/x]e_1 ; ... ; else -> [v/x]e_else
```

with capture-avoiding renaming applied per clause. A clause re-binding `x` is not entered.

### 5.11 Well-Formedness

A `pickup` is well-formed iff: (1) its clause list is non-empty; (2) it has a valid terminator (§ 5.2); (3) every guard types to `Bool`; (4) branch types admit a join; (5) each clause is independently well-formed. No partial well-formedness is permitted.

### 5.12 Decidability

The checks of §§ 5.1, 5.2, 5.5, 5.6, 5.9, 5.11 are decidable in time linear in the size of the `pickup` expression, modulo the language's general type-checking and join operations. Reachability (§§ 5.3, 5.8) is undecidable in general; the specification mandates a sound but possibly incomplete approximation.

### 5.13 Erasure Properties

After type checking and reachability analysis, static information attached to a `pickup` is erased before code generation, except that:

- the terminator is preserved syntactically even when proved `Unreachable`;
- diagnostics remain attached to source spans for tooling;
- effect annotations propagate to the language's effect system but do not appear in generated machine code.

### 5.14 Polymorphism and Generics

A `pickup` participates in generalization and instantiation as any expression position would: if every branch generalizes to a scheme `∀α₁...αₙ. τ`, the `pickup` does too; if branches admit different schemes, the result is generalized to the meet of their quantifier sets and the join of their bodies. Type variables introduced by guards are scoped strictly within the introducing clause.

### 5.15 Type Inference Algorithm

```text
   infer(Γ, pickup C):
     1. τ_acc := fresh type variable.
     2. For each guard clause (g_i -> e_i) in source order:
          a. Constrain  infer(Γ, g_i) ≡ Bool.
          b. Unify       τ_acc  with  infer(Γ, e_i).
     3. Unify τ_acc with infer(Γ, e_else).
     4. Return τ_acc.
```

Where the language admits subtyping, steps 2(b) and 3 use `⊔` from § 5.6 in place of equality. Failures emit `E-PICKUP-GUARD-TYPE` or `E-PICKUP-BRANCH-MISMATCH` at the first source span at which the conflict became detectable.

### 5.16 Refinement-Type Interaction

If the language admits refinement types `{x : τ | φ(x)}`:

- within `e_i`, the refinement context is strengthened with `g_i ∧ ¬g_1 ∧ ... ∧ ¬g_{i-1}`;
- within `e_else`, the refinement context is strengthened with `¬g_1 ∧ ... ∧ ¬g_n`.

These strengthenings are inert for compilers without refinement typing.

### 5.17 The Pure Fragment

A `pickup` is *pure* iff every guard and every branch is pure. The pure fragment is closed under the algebraic laws of § 11 without re-checking purity, and pure `pickup` expressions are admissible in any position the language reserves for pure expressions (type-level computation, contract preconditions, compile-time constant evaluation).

### 5.18 Effect Ascription

The effect of a `pickup` is the union of guard effects — always included — and branch effects — included unless statically proved unreachable. An always-include implementation is conforming.

### 5.19 Soundness

For closed `e` with `· ⊢ e : τ`, evaluation terminates with `v : τ`, raises an exception, or diverges. Stuck states are unreachable. The proof discharges via Progress and Preservation over the small-step relation; the `pickup` cases follow immediately from T-Pickup-Else and T-Pickup-Cons. A proof sketch is given in Appendix J.

### 5.20 Static-Semantics Conformance Summary

A static-semantics implementation conforms iff it: (1) implements T-Pickup-Else and T-Pickup-Cons; (2) computes joins per § 5.6; (3) performs the well-formedness checks of § 5.11; (4) computes a sound reachability approximation; (5) tracks purity and effects per §§ 5.17-5.18; (6) discharges § 5.19's proof obligation.

## 6. Dynamic Semantics

### 6.1 Evaluation Order

Guards are evaluated in source order. Once a guard yields `true`, no subsequent guard is evaluated, and only the selected right-hand side is evaluated. If every guard yields `false`, the terminator's right-hand side is evaluated. This order is contractual, not an optimization.

### 6.2 Result

A `pickup` evaluates to the value of the selected branch. By § 5.2 a clause is always selected; `pickup` never raises a "no clause matched" condition.

### 6.3 Side Effects

Guards and branches MAY have side effects. Side effects in `g_i` are observed iff `g_1, ..., g_{i-1}` all evaluated to `false` and selection reached `g_i`. Side effects in `e_i` are observed iff `e_i` is selected.

## 7. Formal Operational Semantics

Write a `pickup` expression as `pickup C`, and `g -> e ; C` for a clause list whose head is `(g, e)` followed by the remainder `C`.

### 7.1 Big-Step Semantics

```text
              σ ⊢ e_else ⇓ v
   ────────────────────────────────────  (P-Else)
       σ ⊢ pickup (else -> e_else) ⇓ v

       σ ⊢ g_1 ⇓ true       σ ⊢ e_1 ⇓ v
   ──────────────────────────────────────────  (P-Hit)
       σ ⊢ pickup (g_1 -> e_1 ; C) ⇓ v

   σ ⊢ g_1 ⇓ false     σ ⊢ pickup C ⇓ v
   ─────────────────────────────────────────  (P-Skip)
       σ ⊢ pickup (g_1 -> e_1 ; C) ⇓ v

            σ ⊢ g_1 ⇓ raise(x)
   ──────────────────────────────────────────  (P-Guard-Raise)
   σ ⊢ pickup (g_1 -> e_1 ; C) ⇓ raise(x)

                σ ⊢ g_1 ⇑
   ─────────────────────────────────────  (P-Guard-Diverge)
       σ ⊢ pickup (g_1 -> e_1 ; C) ⇑
```

The applicable rule is fully determined by the head clause and the evaluation of `g_1`.

### 7.2 Small-Step Reduction

```text
                σ ⊢ g_1 → σ' ⊢ g_1'
   ──────────────────────────────────────────────────────────  (SP-Guard)
   σ ⊢ pickup (g_1 -> e_1 ; C) → σ' ⊢ pickup (g_1' -> e_1 ; C)

   ──────────────────────────────────────────────────────────  (SP-Hit)
        σ ⊢ pickup (true -> e_1 ; C) → σ ⊢ e_1

   ─────────────────────────────────────────────────────  (SP-Skip)
        σ ⊢ pickup (false -> e_1 ; C) → σ ⊢ pickup C

   ─────────────────────────────────────────────────  (SP-Else)
       σ ⊢ pickup (else -> e_else) → σ ⊢ e_else

            σ ⊢ g_1 → σ' ⊢ raise(x)
   ──────────────────────────────────────────────────  (SP-Guard-Raise)
       σ ⊢ pickup (g_1 -> e_1 ; C) → σ' ⊢ raise(x)
```

### 7.3 Evaluation Contexts

```text
   E ::= ...  | pickup (E -> e_1 ; C)
```

There is no production `pickup (g -> E ; C)` and no production `pickup (else -> E)`. Implementations MUST NOT step inside any branch body or any non-head guard; the only place reduction can occur within an unselected `pickup` is the head guard.

### 7.4 Properties

- **Determinism.** Exactly one rule applies per step; the result is unique up to underlying determinism.
- **Progress.** Every well-typed non-value `pickup` expression has a step.
- **Preservation.** Reduction preserves the typing judgment.
- **Equivalence.** `σ ⊢ pickup C ⇓ v` iff `σ ⊢ pickup C →* σ' ⊢ v`. Divergence and exception cases correspond.
- **Confluence.** Trivial under determinism.

### 7.5 Cost Model

For `n` guard clauses:

- best case `cost(g_1) + cost(e_1)`;
- worst case `Σ cost(g_i) + cost(e_else)`;
- general case `(Σ_{i=1..k} cost(g_i)) + cost(e_k)`, where `k` is the index of the first guard to evaluate to `true`, falling back to the worst case if none does.

Selection contributes O(1) overhead per guard, irrespective of the lowering chosen in § 14.

### 7.6 Memory Model

`pickup` introduces no fresh allocation, no synchronization, and no atomicity beyond what its sub-expressions require. Selection is observable only through the values and side effects it produces.

## 8. Formatting Rules

### 8.1 Keyword and Clause Layout

The `pickup` keyword MUST occupy a line by itself. Each clause MUST occupy a line by itself, indented exactly one `indent_step` (§ 8.7) deeper than the keyword.

### 8.2 Arrow Alignment

Within a single block, the formatter MUST align all `->` tokens by padding the guard column with spaces, including the terminator. Alignment is local to a block; sibling blocks are not aligned with each other.

```text
pickup
  x > 0     -> :positive
  x < 0     -> :negative
  even? x   -> :zero_even
  else      -> :zero_odd
```

### 8.3 Default-Clause Keyword

A guard whose syntactic form is the literal `true` and whose clause is the terminator MUST be rewritten by the formatter to `else`, with `H-PICKUP-PREFER-ELSE`. A `true` guard appearing in a non-terminal position is left untouched but renders all subsequent clauses unreachable; `W-PICKUP-UNREACHABLE` follows.

### 8.4 Block Separation

After the last clause of a `pickup`, the formatter MUST insert exactly one blank line before any sibling statement at the same indent level as the keyword. The rule applies only at the outermost sibling boundary; nested arms do not get the blank-line treatment.

```text
pickup
  x > 0 -> f y
  else  -> 0

z + 1
```

### 8.5 Comments

Recognized positions:

- **Block-leading.** Above the `pickup` keyword, same indent.
- **Clause-leading.** Above a clause, clause indent.
- **Trailing in-clause.** Same line as the right-hand side.
- **Internal stray.** Between guard and `->`, or other awkward positions; relocated by the formatter with `H-PICKUP-COMMENT-RELOCATED`.

Block-leading and clause-leading comments are preserved verbatim and travel with their associated construct under refactoring. Trailing comments are preserved; alignment is dropped for a block if a trailing comment would push past `max_line_width`.

### 8.6 Single-Arm `pickup`

A `pickup` containing only the terminator is rewritten to its right-hand side with `H-PICKUP-DEGENERATE`.

### 8.7 Configuration

- `indent_step`: positive integer, default `2`.
- `max_line_width`: positive integer, default `100`.
- `alignment_limit`: positive integer, default `40`.
- `align_else`: boolean, default `true`.

The configuration MUST be discoverable from a single, version-controlled file at the project root. Output MUST be deterministic for identical (input, configuration) pairs.

### 8.8 Long Guards and Line Wrapping

When aligned form would exceed `max_line_width`, the formatter falls back, in order:

1. Drop alignment for the offending block (one space between guard and `->`).
2. Wrap right-hand sides onto a new line indented one `indent_step` deeper. *All* clauses in the block MUST adopt this form together; mixing is forbidden.
3. If even wrapping cannot fit, leave the block unchanged and emit `H-PICKUP-LINE-TOO-LONG`.

### 8.9 Multi-Line Right-Hand Sides

If any branch is multi-line, every branch in the block MUST use the wrapped form: `->` at the end of the guard line; body on the next line, indented one step deeper.

```text
pickup
  cond_1 ->
    let x = compute()
    in process x
  cond_2 ->
    match parse value
      {:ok, v}    -> v
      {:error, e} -> abort e
  else ->
    default()
```

### 8.10 Idempotence

`format(format(s, c), c) = format(s, c)`. Implementations MUST verify idempotence as part of conformance testing.

### 8.11 Comment Fidelity

The multiset of comment tokens in the input and output MUST be identical. Comments may be relocated (§ 8.5) but never lost, duplicated, or character-modified.

### 8.12 Diff Minimality

Where multiple legal formattings are admissible, the formatter SHOULD select the one minimizing the textual diff. Whitespace within unchanged regions MUST NOT be touched.

### 8.13 Tab and Space Normalization

Indentation in output MUST be all spaces. Tabs are replaced; mixed indentation is normalized; trailing whitespace is stripped; the file ends with exactly one terminating newline.

### 8.14 Alignment Computation Algorithm

```text
   1. If any clause is multi-line or wrapping is required by § 8.8,
      emit wrapped form and stop.
   2. Let g_i be the rendered guard text of clause i (or "else").
   3. Let w = max(length(g_i)).
   4. If w > alignment_limit, emit unaligned form and stop.
   5. For each clause emit:
        (indent + step) spaces + g_i + (w - length(g_i)) spaces
        + " -> " + rhs_inline + NEWLINE
   6. Apply the blank-line rule (§ 8.4) before the next sibling.
```

### 8.15 Stability under Refactoring

Modifying a single clause MUST NOT alter formatting of any other `pickup` block in the file, nor any source outside the affected block beyond the blank-line rule.

### 8.16 Round-Trip Property

For formatter-produced source `s`: parsing `s` yields AST `A`; re-rendering `A` yields `s' = s` byte-for-byte. Formatted source is therefore canonical.

### 8.17 Edge Cases

- Single-clause `pickup`: two-line block plus the trailing blank line.
- Degenerate `pickup` (terminator only): rewritten per § 8.6.
- `pickup` at end of file: file-terminator newline rule (§ 8.13) applies; no additional trailing blank line.
- Adjacent `pickup`s at the same outer indent: exactly one blank line between them.
- `pickup` as sole expression of a function body: no leading blank line; trailing blank only if siblings follow.

### 8.18 File-Level Invariants

Single trailing `\n`; no trailing whitespace on any line; all indentation is spaces in integer multiples of `indent_step`; line endings follow the language's standard for the target platform.

### 8.19 Performance Bounds

For input of `N` characters with `K` blocks totalling `M` clauses, formatting MUST complete in `O(N + M log M)` time and `O(N)` space.

### 8.20 Encoding and Unicode

UTF-8 input. Identifier widths in alignment are computed in grapheme clusters per Unicode UAX #29. Bidirectional text does not influence columns. Zero-width characters contribute zero to width.

### 8.21 Plugin Interface

If exposed, the plugin interface MUST surface, per block: the AST node, resolved indent / alignment / wrapping mode, ordered clauses with trivia, and emitted diagnostics. Plugins MUST NOT mutate the AST. Round-trip (§ 8.16) MUST hold regardless of plugin participation.

### 8.22 Editor Folding Integration

Each `pickup` defines exactly one foldable region from the keyword's column through the last clause's last line. A folded view shows the keyword followed by an ellipsis and the clause count, e.g. `pickup ... (4 clauses)`.

### 8.23 Conformance Test Set

The conformance corpus MUST include: one test per rule in §§ 8.1-8.22; one test per formatter-emitted diagnostic in § 19; an idempotence test on every expected output; a round-trip test on every expected output; one test per edge case in § 8.17.

### 8.24 Final Formatter Grammar

```text
FormattedPickup    ::= IndentBlock "pickup" NEWLINE
                       IndentedClauseList
                       [ NEWLINE ]              -- enforced if sibling follows

IndentedClauseList ::= AlignedClauses
                     | UnalignedClauses
                     | WrappedClauses

AlignedClauses     ::= ( ClauseIndent GuardPadded " -> " RhsInline NEWLINE )+
                       ClauseIndent ElsePadded " -> " RhsInline NEWLINE

UnalignedClauses   ::= ( ClauseIndent Guard " -> " RhsInline NEWLINE )+
                       ClauseIndent "else" " -> " RhsInline NEWLINE

WrappedClauses     ::= ( ClauseIndent Guard " ->" NEWLINE
                         ClauseIndent IndentStep RhsBlock NEWLINE )+
                       ClauseIndent "else ->" NEWLINE
                       ClauseIndent IndentStep RhsBlock NEWLINE
```

Mixing the three is forbidden (§ 8.9).

### 8.25 Formatter Conformance Summary

A formatter conforms iff it: (1) produces output matching § 8.24; (2) applies §§ 8.1-8.6; (3) honours § 8.7 with prescribed defaults; (4) implements §§ 8.8-8.9; (5) handles comments per § 8.5 with fidelity per § 8.11; (6) satisfies idempotence (§ 8.10), diff minimality (§ 8.12), normalization (§ 8.13), stability (§ 8.15), and round-trip (§ 8.16); (7) handles every edge case in § 8.17; (8) operates within § 8.19 and § 8.20; (9) passes the corpus referenced in § 8.23.

## 9. Interaction with `match`

`pickup` and `match` share a uniform grammar of the form *keyword scrutinee_opt CLAUSES*. They are orthogonal: `match` dispatches on the structure of a single scrutinee using patterns; `pickup` dispatches on free-standing boolean guards. They MAY be nested without closing-keyword ceremony. Where `match` admits guards on its clauses (`pat when g -> e`), those guards follow the same typing and short-circuit rules as guards in `pickup`. `pickup` is not a substitute for `match` guards; it is the canonical form when there is no scrutinee.

## 10. Examples

### 10.1 Sign Classification

```text
pickup
  x > 0 -> :positive
  x < 0 -> :negative
  else  -> :zero
```

### 10.2 HTTP Status Routing

```text
pickup
  status >= 500 -> :server_error
  status >= 400 -> :client_error
  status >= 300 -> :redirect
  status >= 200 -> :ok
  else          -> :informational
```

### 10.3 Nested with `match`

```text
match request
  {:get, path}  -> pickup
                     cached? path -> serve_cache path
                     stale? path  -> revalidate path
                     else         -> serve_fresh path
  {:post, body} -> handle_post body
  {:error, e}   -> log_and_drop e
```

### 10.4 As an Expression

```text
let label = pickup
              n > 0 -> "positive"
              n < 0 -> "negative"
              else  -> "zero"
in
  emit label
```

## 11. Algebraic Laws

The following equivalences hold under §§ 6 and 7. Pure-guard hypotheses apply where stated.

- **Degenerate `pickup`:** `pickup else -> e ≡ e`.
- **False-guard elimination:** a clause `false -> e_k` may be removed.
- **True-guard absorption:** a clause `true -> e_k` truncates the block at index `k`, replacing the terminator with `else -> e_k`.
- **Order is contractual:** guard reordering is admissible only when statically constant.
- **Boolean rewriting:** any pure guard may be replaced by a provably equivalent boolean expression.
- **`pickup`-in-`else` flattening:** a `pickup` whose terminator is itself a `pickup` admits syntactic merge; the formatter offers this as a code action but does not apply it automatically.

## 12. Exceptions and Divergence

An exception in `g_i` propagates and aborts selection. An exception in a selected `e_i` propagates as in any expression position. Non-termination in `g_i` or in a selected `e_i` makes the `pickup` diverge. `pickup` itself never raises a "no clause matched" condition.

## 13. Tail-Position Behaviour

A branch right-hand side is in tail position with respect to `pickup` iff `pickup` is itself in tail position. Guards are never in tail position. This guarantees proper tail calls in an `else` arm:

```text
loop n acc =
  pickup
    n == 0 -> acc
    else   -> loop (n - 1) (acc + n)
```

## 14. Compilation and Lowering

Canonical lowering is a flat sequence of conditional branches:

```text
  test g_1 ; branch-if-true L_1
  test g_2 ; branch-if-true L_2
  ...
  test g_n ; branch-if-true L_n
  goto L_else

L_1: e_1; goto L_end
...
L_n: e_n; goto L_end
L_else: e_else
L_end:
```

Implementations MAY substitute decision trees, jump tables, or fused tests, provided they preserve guard evaluation order, the side-effect set, and the selected value. Speculative guard execution is forbidden; predicate side effects are observable.

## 15. Constant Folding and Specialization

The compiler MUST fold:

- All-`false` guards: replace with `e_else`.
- `g_1` literal `true`: replace with `e_1`.
- Some `g_k` literal `true` with `k > 1`: replace terminator with `else -> e_k`, drop clauses after `k`, emit `W-PICKUP-DEAD-ELSE` if reached unconditionally.

Additional reductions enabled by abstract interpretation are permitted but not required. Diagnostics MUST be remapped to the surviving expression's span.

## 16. Macro and Quote Interaction

A `pickup` is a first-class AST node carrying a head token, a list of guard clauses (pairs of guard and body), and a terminator. Hygiene applies as for any other binding context. Splicing of clause lists is permitted; splicing of the terminator only at the terminal position. A macro-generated `pickup` lacking a terminator is `E-PICKUP-NO-ELSE` reported at the invocation site. Source spans propagate through the macro according to the language's general source-mapping rules.

## 17. Migration from `if`

Earlier revisions admitted `if`/`elif`/`else`. As of 1.0.0, `if` is removed.

### 17.1 Two-Arm Form

```text
  if c then e_1 else e_2
≡
  pickup
    c    -> e_1
    else -> e_2
```

### 17.2 Multi-Arm Form

```text
  if c_1 then e_1
  elif c_2 then e_2
  ...
  elif c_n then e_n
  else e_else
≡
  pickup
    c_1  -> e_1
    c_2  -> e_2
    ...
    c_n  -> e_n
    else -> e_else
```

### 17.3 Dangling Form

`if c then e` (no `else`) was never permitted in expression position. There is no migration path; such forms remain errors.

### 17.4 Automated Rewrite

The compiler ships `cure rewrite if-to-pickup`, which preserves comments, transfers end-of-line comments to corresponding clauses, and runs the formatter on every modified file. After migration, the parser MUST reject `if` with `E-IF-REMOVED` and a fix-it pointing at the rewriter.

## 18. Tooling and IDE Integration

A conforming language server MUST:

- highlight `pickup` and `else` as keywords; `->` as operator;
- on hover of `pickup`, display the mental-model line (§ 1);
- on hover of a guard, display its static type and reachability;
- on hover of `else`, display the result type;
- provide code actions: *Add missing else*, *Rewrite `true ->` as `else ->`*, *Inline degenerate `pickup`*, *Flatten nested `pickup` in `else`* (non-default);
- treat each `pickup` as a foldable region but not as a top-level document symbol;
- grow smart-selection from a clause to its enclosing block in one step.

## 19. Errors and Diagnostics

The compiler MUST produce diagnostics with the following stable identifiers; implementations MAY refine wording but MUST preserve codes. Numeric codes match the current Cure compiler diagnostic registry (`lib/cure/diagnostic/registry.ex`).

- `E076` / `E-PICKUP-NO-ELSE` — `pickup` lacks a valid terminator (§ 5.2). Severity: error.
- `E077` / `E-PICKUP-ELSE-NOT-LAST` — clause(s) follow the `else` clause. Severity: error.
- `E078` / `E-PICKUP-MULTIPLE-ELSE` — more than one `else` clause. Severity: error.
- `E093` / `E-PICKUP-GUARD-TYPE` — guard not of type `Bool` (the general type-mismatch diagnostic; there is no dedicated pickup-guard code). Severity: error.
- `E093` / `E-PICKUP-BRANCH-MISMATCH` — branch right-hand sides have no common upper bound (also the general type-mismatch diagnostic). Severity: error.
- `E-IF-REMOVED` — legacy `if` keyword encountered (§ 17.4). Severity: error, with fix-it.
- `H-PICKUP-PREFER-ELSE` — `true ->` rewritten to `else ->`. Severity: hint.
- `H-PICKUP-DEGENERATE` — single-arm `pickup` reduced to its right-hand side. Severity: hint.
- `H-PICKUP-LINE-TOO-LONG` — clause cannot fit within `max_line_width` even when wrapped. Severity: hint.
- `H-PICKUP-COMMENT-RELOCATED` — internal stray comment relocated by the formatter. Severity: hint.

`W-PICKUP-UNREACHABLE`, `W-PICKUP-DEAD-ELSE`, and `W-PICKUP-EFFECTFUL-GUARD` are specified in § 5.3 and § 5.7 but are not currently emitted by the compiler (the registry's `W081`/`W082` codes are retired with "no first-party producer remains"; there is no registered code for an effectful-guard lint).

## 20. Non-Goals

- **Pattern matching.** Use `match`.
- **Truthy/falsy coercion.** `pickup` is strict about `Bool`.
- **Inline syntax.** No single-line form. Two-arm decisions use the same block shape as ten-arm decisions.
- **Fall-through.** Each evaluation selects exactly one clause.
- **Implicit terminator.** Omitting the terminator is never permitted, even when guards collectively appear total.

## 21. Stability, Versioning, and Deprecation

- Specification version: 1.0.0.
- Behaviour of `pickup` is stable. Future revisions MAY add capabilities but MUST NOT alter the value, side-effect set, or termination behaviour of any program conforming to this revision.
- `pickup` and `else` are reserved in 1.0.0 and indefinitely thereafter.
- Removal of `if` is final; the keyword MUST NOT be re-introduced with legacy semantics.
- New diagnostic codes MAY be added in minor releases. Existing codes MUST NOT be reused for different conditions and MUST NOT be removed.

## 22. Summary

`pickup` is a strict, total, ordered, short-circuiting predicate-dispatch expression. It contains a non-empty sequence of guarded clauses ending in a mandatory terminator (`else -> e` canonical, or `true -> e` accepted and normalized), scoped per clause, terminated by indentation, and aligned by the formatter. It is the only way in the language to branch on a free-standing boolean condition.

> **`pickup` walks the clauses and picks up the first one whose guard is true.**

## 23. Appendix A — Acceptance Test Suite

### A.1 Selection

```text
let r = pickup
          true  -> 1
          else  -> 2
in r           -- expected: 1

let r = pickup
          false -> 1
          else  -> 2
in r           -- expected: 2

let r = pickup
          false -> 1
          true  -> 2
          true  -> 3
          else  -> 4
in r           -- expected: 2

let r = pickup
          false -> 1
          false -> 2
          else  -> 3
in r           -- expected: 3
```

### A.2 Short-Circuit Observability

```text
let log = ref []
let _ = pickup
          true                       -> :ok
          (log := :touched ; true)   -> :unreached
          else                       -> :unreached
in !log        -- expected: []

let log = ref []
let _ = pickup
          true  -> :ok
          else  -> (log := :touched ; :unreached)
in !log        -- expected: []
```

### A.3 Static Rejection

```text
pickup
  x > 0 -> :positive
  x < 0 -> :negative
-- E-PICKUP-NO-ELSE

pickup
  else  -> :zero
  x > 0 -> :positive
-- E-PICKUP-ELSE-NOT-LAST

pickup
  x > 0 -> :positive
  else  -> :zero
  else  -> :other
-- E-PICKUP-MULTIPLE-ELSE

pickup
  "yes" -> :positive
  else  -> :zero
-- E-PICKUP-GUARD-TYPE

pickup
  cond -> 1
  else -> "two"
-- E-PICKUP-BRANCH-MISMATCH
```

### A.4 Reachability and Hints

```text
pickup
  cond -> :a
  true -> :b
-- legal (true clause is the terminator); H-PICKUP-PREFER-ELSE
-- formatter output:
--   pickup
--     cond -> :a
--     else -> :b

pickup
  else -> e
-- formatter output: e ; H-PICKUP-DEGENERATE

pickup
  true -> :a
  cond -> :b
  else -> :c
-- W-PICKUP-UNREACHABLE on `cond -> :b` and W-PICKUP-DEAD-ELSE on `else -> :c`
```

### A.5 Layout

```text
pickup
  x > 0 -> :positive
  else  -> :zero
z + 1
-- parses as `pickup` followed by an independent expression

pickup

  x > 0 -> :positive

  else  -> :zero
-- parses identically to the dense form

match req
  {:get, p} -> pickup
                 cached? p -> serve_cache p
                 else      -> serve_fresh p
  {:post, b} -> handle_post b
-- parses as one match with two clauses; the inner pickup is the body of {:get, p}
```

### A.6 Tail Calls

```text
loop n acc =
  pickup
    n == 0 -> acc
    else   -> loop (n - 1) (acc + n)

loop 1_000_000 0
-- terminates without stack overflow
```

## 24. Appendix B — Glossary

- **Block.** The indented region of clauses following the `pickup` keyword.
- **Branch.** Synonym for *right-hand side*: the expression to the right of `->` in a clause.
- **Clause.** A single line of the form *guard* `->` *expression* or `else ->` *expression*.
- **Else clause / terminator.** The mandatory final clause that always succeeds, in canonical (`else ->`) or alternative (`true ->`) form.
- **Guard.** The boolean expression to the left of `->` in a non-`else` clause.
- **Predicate dispatch.** Selection of a branch by evaluating boolean guards in source order.
- **Selection.** The act of choosing exactly one clause to execute in a single evaluation.
- **Short-circuit.** The guarantee that no guard is evaluated after the first guard yields `true`, and only the selected branch is evaluated.
- **Totality.** Every well-typed `pickup` evaluates to a value of its result type or diverges through ordinary means.

## 25. Appendix C — Change Log

- **1.0.0** — Initial release. Introduces `pickup` as the sole predicate-dispatch construct; removes `if`/`elif` from the language; reserves `else` globally; ships the `cure rewrite if-to-pickup` migration tool.
- **v0.33.0 publication** — Specification published into HexDocs alongside `docs/MATCH.md` via `mix.exs` `docs.extras`. `docs/LANGUAGE_SPEC.md` gains a `## Conditional Dispatch (`pickup`)` section that points at this document as the normative source. The Cure website grows a dedicated `/pickup` user-facing page that mirrors the existing `/match` shape and cross-links this document. No normative content changed.

## 26. Appendix D — Index of Normative Requirements

- § 3.1 — `pickup`/`else` are reserved.
- § 4.1 — Block non-empty; terminator last; terminator present in either form.
- § 5.1 — Guards MUST be `Bool`; branches MUST share a join.
- § 5.2 — Terminator MUST be present in canonical or alternative form.
- § 6.1 — Guards evaluated in source order; short-circuit guaranteed.
- § 7 — Implementations MUST realize the operational semantics in either big-step or small-step formulation.
- § 8.1-8.25 — Formatter rules in full.
- § 13 — Branches in tail position iff `pickup` is; guards never.
- § 14 — Lowerings MUST preserve order, side-effect set, and selected value; speculative guard execution forbidden.
- § 15 — Compiler MUST perform the listed constant folds.
- § 16 — Macro-generated `pickup` MUST contain a terminator.
- § 17.4 — Parser MUST reject `if` post-migration.
- § 18 — Language server MUST provide the listed surfaces.
- § 21 — Behaviour stable; existing diagnostic codes immutable.

## 27. Appendix E — Reference Implementation Sketch

This appendix provides non-normative pseudocode that an implementer MAY use as a starting point. Conformance is determined by the rules of §§ 1-22, not by adherence to this code.

### E.1 Parser

```text
parse_pickup(tokens):
  expect("pickup")
  expect(NEWLINE)
  expect(INDENT)

  clauses = []
  loop:
    if peek() == "else":
      advance()
      expect("->")
      e_else = parse_expression()
      clauses.append(ElseClause(rhs = e_else))
      break
    else:
      g = parse_expression()
      expect("->")
      e = parse_expression()
      clauses.append(GuardClause(guard = g, rhs = e))
      if peek() == DEDENT: break
      expect(NEWLINE)

  expect(DEDENT)
  return PickupNode(clauses = clauses)
```

The parser does not enforce the totality rule (§ 5.2); that check is performed by the well-formedness pass.

### E.2 Well-Formedness Check

```text
check_pickup(node):
  if node.clauses is empty:
    error E-PICKUP-NO-ELSE at node.span

  terminator_seen = false
  for i, c in enumerate(node.clauses):
    if terminator_seen:
      error E-PICKUP-ELSE-NOT-LAST at c.span
    if c is ElseClause:
      if any preceding clause is ElseClause:
        error E-PICKUP-MULTIPLE-ELSE at c.span
      terminator_seen = true
    elif c is GuardClause and c.guard is the literal true and i == len - 1:
      terminator_seen = true       -- alternative form, § 5.2
    elif c is GuardClause:
      pass

  if not terminator_seen:
    error E-PICKUP-NO-ELSE at node.span
```

### E.3 Type Checker

```text
type_pickup(Γ, node):
  τ_acc = fresh()
  for c in node.clauses:
    if c is GuardClause:
      τ_g = type(Γ, c.guard)
      unify(τ_g, Bool)         -- E-PICKUP-GUARD-TYPE on failure
      τ_e = type(Γ, c.rhs)
      τ_acc = join(τ_acc, τ_e) -- E-PICKUP-BRANCH-MISMATCH on failure
    elif c is ElseClause:
      τ_e = type(Γ, c.rhs)
      τ_acc = join(τ_acc, τ_e)
  return τ_acc
```

### E.4 Lowering

```text
lower_pickup(node):
  L_end = fresh_label()
  L_else = fresh_label()
  result = []
  body_blocks = []

  for c in node.guard_clauses:
    L_i = fresh_label()
    result.append(test(c.guard))
    result.append(branch_if_true(L_i))
    body_blocks.append((L_i, c.rhs))

  result.append(goto(L_else))
  for (L_i, rhs) in body_blocks:
    result.append(label(L_i))
    result.append(emit(rhs))
    result.append(goto(L_end))
  result.append(label(L_else))
  result.append(emit(node.terminator.rhs))
  result.append(label(L_end))
  return result
```

### E.5 Formatter

```text
format_pickup(node, config):
  -- Step 1: rewrite trailing `true ->` to `else ->`
  if node.last_clause is GuardClause and node.last_clause.guard == true_literal:
    node.last_clause = ElseClause(rhs = node.last_clause.rhs)
    emit_hint(H-PICKUP-PREFER-ELSE)

  -- Step 2: degenerate
  if len(node.clauses) == 1 and node.clauses[0] is ElseClause:
    emit_hint(H-PICKUP-DEGENERATE)
    return format_expression(node.clauses[0].rhs, config)

  -- Step 3: choose form
  guards = [render_guard(c) for c in node.clauses]
  width  = max(grapheme_width(g) for g in guards)

  any_multiline = any(is_multiline(c.rhs) for c in node.clauses)
  fits_aligned  = (config.indent + config.indent_step + width + 4 +
                   max_rhs_width(node)) <= config.max_line_width
  too_wide      = width > config.alignment_limit

  form = (Wrapped if any_multiline
          else Unaligned if (too_wide or not fits_aligned)
          else Aligned)

  return render(node, form, config)
```

## 28. Appendix F — Worked Migration Examples

Each example shows pre-migration `if` source on the left and post-migration `pickup` source on the right. The `cure rewrite if-to-pickup` tool produces the right column mechanically.

### F.1 Simple Two-Arm

```text
-- Before:
let bonus = if score > 100 then 50 else 0

-- After:
let bonus = pickup
              score > 100 -> 50
              else        -> 0
```

### F.2 Three-Arm Chain

```text
-- Before:
let label =
  if   score >= 90 then "A"
  elif score >= 80 then "B"
  elif score >= 70 then "C"
  else                   "F"

-- After:
let label = pickup
              score >= 90 -> "A"
              score >= 80 -> "B"
              score >= 70 -> "C"
              else        -> "F"
```

### F.3 Nested `if` Inside `match`

```text
-- Before:
match resp
  {:ok, body} ->
    if length body > 0 then process body
    elif retry?         then refetch ()
    else                     :empty
  {:error, e} -> log e

-- After:
match resp
  {:ok, body} -> pickup
                   length body > 0 -> process body
                   retry?          -> refetch ()
                   else            -> :empty
  {:error, e} -> log e
```

### F.4 `if`-as-Expression Inside an Argument

```text
-- Before:
emit (if verbose? then full_message else short_message)

-- After:
emit (pickup
        verbose? -> full_message
        else     -> short_message)
```

### F.5 `if` With Side-Effecting Branches

```text
-- Before:
if dirty? then save_to_disk () else log :clean

-- After:
pickup
  dirty? -> save_to_disk ()
  else   -> log :clean
```

### F.6 Comment Preservation

```text
-- Before:
if user.admin? then
  -- elevated privilege path
  grant_all ()
elif user.member? then
  grant_basic ()  -- standard members
else
  deny ()         -- guests

-- After:
pickup
  user.admin?  -> grant_all ()      -- elevated privilege path
  user.member? -> grant_basic ()    -- standard members
  else         -> deny ()           -- guests
```

The rewriter normalizes comments per § 8.5: end-of-line comments stay attached to their clauses; comments above an arm become clause-leading comments above the corresponding `pickup` clause.

## 29. Appendix G — Style Guide and Idioms

This appendix is non-normative. It captures the conventions a reader should expect to see in idiomatic source.

### G.1 Use `pickup` for Predicate Dispatch, `match` for Structural Dispatch

When the deciding question is *"what shape does this value have?"*, use `match`. When the deciding question is *"which of these conditions holds?"*, use `pickup`. Mixing the two by destructuring with `match` only to immediately re-test parts of the bound value with `pickup` is a smell; consider `match` clauses with guards (`pat when g -> e`) instead.

### G.2 Order Guards Deliberately

`pickup` is order-sensitive. Two reasonable orderings:

1. **By specificity.** More specific predicates first, falling through to general ones.
2. **By likelihood.** Most-likely predicates first, optimizing the cost model of § 7.5.

Pick one for a given block and stay consistent. Document the choice in a clause-leading comment when the order is non-obvious.

### G.3 Prefer Pure Guards

A guard with side effects executes conditionally on every prior guard's result. This conditional ordering is rarely the user's intent. Prefer pure guards; perform side effects in the selected branch. Reach for an effectful guard only when the side effect *is* the test (e.g. `lock_acquired? lock`).

### G.4 One Predicate Per Guard

Guards built from many `&&` or `||` operators are hard to read and hard to align. Split a compound guard into multiple `pickup` clauses when the resulting structure is clearer:

```text
-- Less clear:
pickup
  ready? && healthy? && quota_ok? -> launch ()
  else                            -> wait ()

-- Clearer:
pickup
  not ready?    -> wait ()
  not healthy?  -> wait ()
  not quota_ok? -> wait ()
  else          -> launch ()
```

The rewritten form makes each precondition explicit and lets the reader scan for any one of them.

### G.5 Use `else`, not `true ->`

The formatter rewrites `true ->` to `else ->` (§ 8.3), but human-written source SHOULD use `else` directly. The literal `true` as a guard reads as if a real condition is being tested; `else` reads as the default arm.

### G.6 Keep Branches Symmetric

When all branches return values of the same kind (all integers, all status atoms, all results), say so at the type level and let the reader confirm by scanning the arrows. Heterogeneous branches that happen to share a join type are admissible but obscure intent.

### G.7 Annotate the Block, Not the Branches

A long `pickup` block benefits from one block-leading comment explaining the dispatch axis, more than from many clause-leading comments explaining each arm. The latter become redundant if the guards are well-named.

## 30. Appendix H — Anti-Patterns

Non-normative. Each item is a construct that compiles but is discouraged.

### H.1 Boolean Coercion via Comparison

```text
pickup
  is_nil x == false -> use x
  else              -> default
```

`is_nil x == false` is a contortion to satisfy strict `Bool` typing. Use `not (is_nil x)` or, better, structural matching with `match`.

### H.2 `pickup` as a Replacement for `match`

```text
pickup
  is_ok? r    -> handle_ok r
  is_error? r -> handle_error r
  else        -> impossible ()
```

This is a `match` with extra steps. The `else` arm exists only to satisfy totality despite the structural exhaustion already implicit in the type. Use `match` and let the type checker prove totality.

### H.3 Guard With Hidden State

```text
pickup
  next_token () == :open  -> parse_block ()
  next_token () == :colon -> parse_label ()
  else                    -> parse_atom ()
```

Each `next_token ()` call advances state. The guards observe a different stream than the reader thinks. Bind the result first, then dispatch:

```text
let t = next_token ()
in pickup
     t == :open  -> parse_block ()
     t == :colon -> parse_label ()
     else        -> parse_atom ()
```

### H.4 Excessively Wide Alignment

A block whose longest guard is fifty characters and shortest is three forces the formatter to drop alignment (§ 8.8). Either pull the long guard into a named helper, or accept unaligned form. Do not fight the formatter.

### H.5 Order-Dependent Side Effects in Branches

```text
pickup
  cond_1 -> log :a ; do_a ()
  cond_2 -> log :b ; do_b ()
  else   -> log :c ; do_c ()
```

If the logging is the point, fine. If the logging exists to confirm which branch fired, factor it out:

```text
let chosen = pickup
               cond_1 -> :a
               cond_2 -> :b
               else   -> :c
in log chosen ; dispatch chosen
```

### H.6 Recapitulating the Guard in the Branch

```text
pickup
  x > 0 -> "positive: " ++ to_string x   -- x > 0 already established
  x < 0 -> "negative: " ++ to_string x
  else  -> "zero"
```

This is fine in isolation but fragile under refactoring: a future change that weakens the guard silently weakens the branch's invariants. Where the language admits refinement types (§ 5.16), the strengthening of the branch's context makes such recapitulation unnecessary.

## 31. Appendix I — Reserved Future Syntax

The following forms are reserved by the language. They MUST NOT be accepted by a 1.0.0 conforming parser; their reservation exists so future revisions may add them without breaking source.

### I.1 `pickup as`

```text
pickup as which
  cond_1 -> ...
  cond_2 -> ...
  else   -> ...
```

A future revision MAY introduce binding of the selected clause's index, name, or guard to a name `which` for use inside the corresponding branch. Reserved for that purpose.

### I.2 `pickup with`

```text
pickup with shared_env
  ...
```

A future revision MAY introduce a shared-environment form that evaluates `shared_env` once and threads it through every guard and branch.

### I.3 `pickup async`

```text
pickup async
  ...
```

A future revision MAY introduce parallel evaluation of guards under a strict purity restriction. Reserved; today's `pickup` is strictly sequential.

### I.4 Trailing `where`

```text
pickup
  guard_a -> ...
  guard_b -> ...
  else    -> ...
where
  guard_a = ...
  guard_b = ...
```

A future revision MAY allow named guards introduced after the block. Reserved.

### I.5 Use Outside Reserved Forms

The reserved keywords (`as`, `with`, `async`, `where`) outside `pickup` retain whatever meaning the language already assigns them. The reservation is positional: only their appearance immediately following `pickup` is constrained.

## 32. Appendix J — Soundness Proof Sketch

This appendix sketches the soundness proof referenced in § 5.19. It is non-normative; a conforming implementation need not reproduce the proof, only respect its conclusion.

### J.1 Statement

Given the typing rules T-Pickup-Else and T-Pickup-Cons (§ 5.5) and the small-step rules SP-Guard, SP-Hit, SP-Skip, SP-Else, SP-Guard-Raise (§ 7.2):

**Theorem (Soundness).** If `· ⊢ e : τ` and `· ⊢ e →* σ ⊢ e'`, then either `e'` is a value `v` with `· ⊢ v : τ`, or `e'` is a raised exception, or there exists `e''` such that `σ ⊢ e' → σ' ⊢ e''`.

### J.2 Proof Structure

By Progress and Preservation.

**Progress.** For every `· ⊢ e : τ` with `e = pickup C`:

- If `C = (else -> e_else)`, then SP-Else applies.
- If `C = (g -> e_1 ; C')` and `g` is a value:
  - if `g = true`, SP-Hit applies;
  - if `g = false`, SP-Skip applies;
  - other values are excluded by T-Pickup-Cons (`Γ ⊢ g : Bool`).
- If `C = (g -> e_1 ; C')` and `g` is not a value:
  - by inductive hypothesis on `g`, either `g` steps (SP-Guard applies), `g` raises (SP-Guard-Raise applies), or `g` diverges (the proposition holds vacuously).

**Preservation.** For every `· ⊢ pickup C : τ` and `pickup C → e'`:

- SP-Hit: `e' = e_1`. By T-Pickup-Cons, `· ⊢ e_1 : τ_1` and `τ = τ_1 ⊔ τ_2`. By subsumption (in the language's general subtyping), `· ⊢ e_1 : τ`.
- SP-Skip: `e' = pickup C'`. By T-Pickup-Cons, `· ⊢ pickup C' : τ_2` and `τ = τ_1 ⊔ τ_2`. By subsumption, `· ⊢ pickup C' : τ`.
- SP-Else: `e' = e_else`. By T-Pickup-Else, `· ⊢ e_else : τ`.
- SP-Guard: `e' = pickup (g' -> e_1 ; C')` where `g → g'`. By inductive hypothesis on `g`, `· ⊢ g' : Bool`, hence T-Pickup-Cons applies and `· ⊢ e' : τ`.
- SP-Guard-Raise: `e' = raise(x)`, which is well-typed at every type by the language's exception rule.

The four `pickup`-specific cases discharge the obligation; the remaining cases reduce to the language's general Preservation lemma.

### J.3 Corollaries

- **Totality.** Every well-typed `pickup` terminates with a value, raises an exception, or diverges; it cannot reach a stuck state.
- **No "no clause matched" runtime failure.** The terminator clause is mandatory (§ 5.2); SP-Else is reachable from any well-typed `pickup` whose guards all yield `false`.

## 33. Appendix K — Bibliography and Related Work

Non-normative.

- **Erlang `if`.** Per-clause guard tests, otherwise-clause via `true ->`. Direct ancestor of the alternative-form terminator (§ 5.2).
- **Elixir `cond/1`.** Macro form `cond do ... end` with first-true-wins semantics over a list of clauses, exactly the dispatch mechanism `pickup` formalizes.
- **Haskell guards.** Per-equation guard chains with implicit fall-through to the next equation. `pickup` differs in being an expression, not a clause-level mechanism, and in mandating an explicit terminator.
- **Scheme `cond`.** The classical predicate-dispatch form, extended with the `=>` syntax for binding the guard's value into the branch. `pickup` does not currently admit such binding (reserved as `pickup as`, see Appendix I).
- **Predicate dispatch (Ernst, Kaplan, Chambers, 1998).** Generalizes method dispatch over arbitrary boolean predicates. `pickup` is the expression-level analogue at the source-language tier.
- **Common Lisp `cond`.** Closest semantic ancestor; `pickup` adopts its first-true-wins ordering and explicit-terminator discipline, eschewing its default-`nil` behaviour in favour of strict totality.

## 34. Appendix L — Open Questions and Future Directions

Non-normative. Items in this appendix are explicitly *not* part of the 1.0.0 specification. They are listed to set expectations about possible future revisions.

### L.1 Decidable Reachability Fragments

The reachability analysis of § 5.8 is sound but incomplete. A future revision MAY mandate completeness for specific decidable fragments (e.g. linear-arithmetic guards over integer variables, finite-domain enums) by way of a built-in SMT-style decision procedure.

### L.2 User-Defined `Bool` Coercion

§ 5.1 forbids implicit coercion. A future revision MAY allow a user-defined `IntoBool` type-class whose instances are eligible to participate as guards, with strict warnings when an instance is non-trivial.

### L.3 Guard-Local Bindings (`pickup as`)

Appendix I.1 reserves `pickup as which`. A future revision MAY define its semantics, allowing branches to refer to the index, name, or guard expression of the selected clause without recomputing.

### L.4 Parallel Guard Evaluation (`pickup async`)

Appendix I.3 reserves `pickup async`. A future revision MAY admit parallel evaluation of pure guards under a strict purity restriction, with selection still occurring in source order on completion. The cost model would be revised to reflect a max-of-guards rather than a sum-of-guards lower bound.

### L.5 Refinement-Aware Reachability

§ 5.16 already strengthens refinement contexts inside branches. A future revision MAY require the reachability analysis of § 5.8 to consult the refinement system, raising the precision of `W-PICKUP-UNREACHABLE` and `W-PICKUP-DEAD-ELSE` in refinement-typed code.

### L.6 Compile-Time Specialization Across `pickup` and `match`

When `pickup` and `match` are nested, fusion is sometimes profitable (turning a `match` with a `pickup` in every arm into a single decision tree). A future revision of the optimizer guidance MAY characterize when such fusion is admissible without altering observable order.

### L.7 Statement vs Expression Status

This revision treats `pickup` exclusively as an expression. A future revision MAY admit statement-position `pickup` whose terminator is `()` (or the language's unit value) and whose branches MAY have side-only effects, possibly with a relaxed totality requirement. The current revision deliberately rejects this; consistency with `match` is preferred.

## 35. Appendix M — Specification Metadata and Colophon

### M.1 Metadata

- **Document title.** The `pickup` Construct — Language Specification.
- **Specification version.** 1.0.0.
- **Status.** Stable.
- **Companion construct.** `match` (specified separately).
- **Predecessor.** Legacy `if`/`elif`/`else`, removed in this revision.
- **Migration tool.** `cure rewrite if-to-pickup`.
- **Reserved keywords introduced.** `pickup`, `else`.
- **Reserved keywords for future use.** `as`, `with`, `async`, `where` (positional, immediately following `pickup`).

### M.2 Document Structure

The specification is organized in five strata:

1. **Surface** (§§ 1-4): introduction, conformance terminology, lexical syntax, grammar.
2. **Semantics** (§§ 5-7): static, dynamic, and operational semantics.
3. **Surface conventions** (§§ 8-10): formatting, interaction with `match`, examples.
4. **Theory and machinery** (§§ 11-18): laws, exceptions, tail calls, compilation, folding, macros, migration, tooling.
5. **Closure** (§§ 19-22): diagnostics, non-goals, stability, summary.

Appendices A through D supply conformance criteria, glossary, change log, and a normative-requirement index. Appendices E through L supply non-normative implementer guidance, idioms, anti-patterns, reserved syntax, the soundness sketch, related work, and deferred questions. Appendix M (this) supplies metadata.

### M.3 How to Read This Document

- An **implementer** writing a parser, type checker, or evaluator should read §§ 3-7, § 19, Appendix A (acceptance tests), and Appendix E (reference implementation sketch).
- An **implementer** writing a formatter should read § 8 in full, § 19, and Appendices A and E.
- A **language-server author** should read §§ 5, 7, 8, 18, and 19.
- A **language user** writing code should read §§ 1, 9, 10, 11, 17, 20, and Appendices G (style guide) and H (anti-patterns).
- A **language designer** considering an extension should read §§ 21 and 22, and Appendices I, K, and L.

### M.4 Review Procedure

Errata and proposed amendments to this specification follow the language's general request-for-comments process. Editorial corrections that do not alter normative requirements MAY be applied without a version bump; any change to a MUST or MUST NOT clause requires a new minor or major revision and a corresponding entry in Appendix C.

### M.5 Colophon

This specification is intended to be read end-to-end at first encounter and consulted by section thereafter. Its prose is deliberately repetitive at the joints between informal and formal sections, so that a reader picking up at any one section receives the full context of the rule under discussion.

The mental model that a reader should retain after closing this document is exactly one sentence:

> **`pickup` walks the clauses and picks up the first one whose guard is true.**

Everything else in the specification exists to make that intuition mechanically precise.

---

## End of Specification

The specification of `pickup` at version 1.0.0 is complete. An implementation that satisfies every MUST clause in §§ 1-21 and Appendix D, refuses every program identified as a static error in § 19, and produces every diagnostic listed in § 19 is conforming. Anything beyond is implementation-defined.

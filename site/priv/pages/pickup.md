%{
  title: "Conditional Dispatch (pickup)",
  description: "The total, ordered, short-circuiting predicate-dispatch construct that replaces if/elif/else. Mandatory else terminator, strict Bool typing, source-order evaluation, refinement narrowing, formatter alignment, and a complete migration story.",
  order: 12
}
---
> **Normative source (v0.33.0).** The `pickup` construct is specified
> at version 1.0.0 in
> [`docs/PICKUP.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/PICKUP.md).
> That document covers the grammar, the static / dynamic / operational
> semantics, the formatter rules, the algebraic laws, the legacy `if`
> migration story, the diagnostic catalogue, and a soundness proof
> sketch. This page is the user-facing tutorial complement; for any
> conflict, the formal specification is the authority.

`pickup` is the only way in Cure to branch on a free-standing boolean
condition. It replaced the legacy `if` / `elif` / `else` chain and is
governed by a single mental model:

> **`pickup` walks the clauses and picks up the first one whose guard
> is true.**

Every other rule in the construct exists to make that intuition
mechanically precise.

## The shape

A `pickup` block is a non-empty list of guarded clauses ending in a
mandatory terminator:

```cure
fn classify_status(status: Int) -> Atom =
  pickup
    status >= 500 -> :server_error
    status >= 400 -> :client_error
    status >= 300 -> :redirect
    status >= 200 -> :ok
    else -> :informational
```

Each clause is one of two forms:

- **Guarded** -- `expression -> expression`. The left-hand expression
  is the guard; it MUST type to `Bool`.
- **Terminal** -- `else -> expression`. There is exactly one, and it
  MUST be the last clause. The literal `true` in last position is
  accepted as an alternative form and rewritten to `else` by the
  formatter.

The terminator is mandatory. A `pickup` without `else` (or
last-position `true`) is rejected with `E-PICKUP-NO-ELSE`.

## Total by construction

The mandatory terminator means a well-typed `pickup` cannot fail with
a "no clause matched" condition at runtime. Compare this with `match`:
non-exhaustive `match` is only a warning, and the non-covered case
raises `case_clause` at runtime. With `pickup`, totality is
syntactically guaranteed.

## Strict `Bool` typing

Each guard MUST type to `Bool`. There is no truthy / falsy coercion;
`pickup` is uncompromising about types:

```cure E093
# Rejected: 1 is not Bool
pickup
  1     -> :truthy
  else  -> :falsy
# E-PICKUP-GUARD-TYPE
```

The branch right-hand sides MUST share a common upper bound under the
language's subtyping relation. If they do not, the program is
rejected with `E-PICKUP-BRANCH-MISMATCH`:

```cure E093
# Rejected: branches are Int and String
fn choose(cond: Bool) =
  pickup
    cond -> 1
    else -> "two"
# E-PICKUP-BRANCH-MISMATCH
```

## Evaluation order

Guards evaluate in source order. As soon as one yields `true`, no
subsequent guard runs and only the selected branch evaluates. If
every guard yields `false`, the terminator runs.

```cure
fn next_step(ready: Bool, timed_out: Bool) -> Atom =
  pickup
    ready -> :launch
    timed_out -> :retry
    else -> :wait
```

If `ready?` is `true`, `"checking timeout"` is never logged. The
order is contractual, not an optimisation; the compiler rearranges
guards only when their value is statically constant.

## Per-clause scoping

Each clause introduces its own lexical scope:

- A guard `g_i` sees the scope enclosing the `pickup`, extended with
  bindings introduced by `g_i`.
- The right-hand side `e_i` sees the scope of `g_i`.
- Bindings from `g_i`/`e_i` are not visible in any other clause.
- Nothing escapes the `pickup` expression.

## Refinement narrowing

Inside the `i`-th branch, the refinement context is strengthened with
`g_i ∧ ¬g_1 ∧ ... ∧ ¬g_{i-1}`. Inside the `else` branch, it is
strengthened with the conjunction of every preceding negation. This
lets the type checker prove safety of the branch body without an
explicit refinement annotation:

```cure
fn safe_div(n: Int, d: Int) -> Int =
  pickup
    d != 0 -> n / d        # `d` is refined to {x: Int | x != 0}
    else   -> 0
```

## Tail-position behaviour

A branch right-hand side is in tail position with respect to `pickup`
iff `pickup` is itself in tail position. This guarantees proper tail
calls in any branch, including the `else`:

```cure
fn loop(n: Int, acc: Int) -> Int =
  pickup
    n == 0 -> acc
    else   -> loop(n - 1, acc + n)
```

`loop(1_000_000, 0)` terminates without stack overflow.

## `pickup` as an expression

`pickup` is an expression, never a statement. It returns the value
of the selected branch and is admissible everywhere an expression is:

```cure
fn label(n: Int) -> String =
  pickup
    n > 0 -> "positive"
    n < 0 -> "negative"
    else -> "zero"
```

It nests freely with `match` and other constructs:

```cure
fn request_kind(method: Atom) -> Atom =
  pickup
    method == :get -> :get
    method == :post -> :post
    else -> :malformed
```

## Migrating from `if` / `elif` / `else`

`if` / `elif` / `then` / `else` are deprecated in favour of `pickup`,
but the parser still accepts them: each `if` still lowers to the same
conditional it always has, and parsing one emits a deprecation event
so editors and the LSP can surface a migration hint. `cure migrate`
rewrites the whole rule registry, including `if`/`elif` to `pickup`,
refuses to touch a dirty working tree, and reprints canonically:

```cure
fn grade(score: Int) -> String =
  pickup
    score >= 90 -> "A"
    score >= 80 -> "B"
    score >= 70 -> "C"
    else -> "F"
```

```bash
cure migrate --check src
cure migrate src
```

`mix cure.rewrite` is an older, narrower task that applies only this
one rule without the git-cleanliness guard; it is retained for
backward compatibility and now delegates to the same migration engine.
Neither tool currently turns a lingering `if` into a hard compile
error.

## Formatter conventions

The formatter aligns all `->` tokens within a single `pickup` block,
including the `else` clause:

```cure
fn parity(x: Int) -> Atom =
  pickup
    x > 0 -> :positive
    x < 0 -> :negative
    else -> :zero
```

Other formatter rules:

- A trailing `true ->` is rewritten to `else ->`.
- A degenerate `pickup` whose only clause is the terminator collapses
  to its right-hand side.
- Multi-line right-hand sides switch every clause in the block to
  the wrapped form (`->` at the end of the guard line, body indented
  one step deeper). Mixing aligned and wrapped forms is forbidden.
- Comments are preserved verbatim. Block-leading and clause-leading
  comments stay attached to their construct under refactoring.
  Internal stray comments may be relocated by the formatter (see the
  Diagnostics section below for the status of the hint codes these
  rewrites were once catalogued under).
- The formatter is idempotent
  (`format(format(s, c), c) = format(s, c)`) and round-trip-safe
  (formatted source re-parses byte-identically).

## Diagnostics

The three structural checks below are live, numbered codes (run
`cure explain <code>` for the full text); the old `E-PICKUP-*` spelling
from earlier drafts of this page survives only as a descriptive alias
in that explanation text, not as an argument `cure explain` accepts:

- **E076** -- `pickup` lacks a valid terminator (`E-PICKUP-NO-ELSE`).
- **E077** -- clauses follow the `else` clause (`E-PICKUP-ELSE-NOT-LAST`).
- **E078** -- more than one `else` clause (`E-PICKUP-MULTIPLE-ELSE`).

A guard that is not `Bool`, or branches with no common upper bound, are
reported through the general type-mismatch diagnostic (`E093`) rather
than a `pickup`-specific code. The reachability warnings and formatter
hints once catalogued here as `W-PICKUP-UNREACHABLE`, `W-PICKUP-DEAD-ELSE`,
`H-PICKUP-PREFER-ELSE`, and `H-PICKUP-DEGENERATE` are not currently
emitted by the compiler, even though the formatter still performs the
rewrites they described.

## Idioms

### Use `pickup` for predicates, `match` for shape

If the deciding question is *"what shape does this value have?"*,
use `match`. If it is *"which of these conditions holds?"*, use
`pickup`. A `match` whose patterns are uniformly wildcards is a
`pickup` in disguise.

### Order guards deliberately

Pick one of two orderings and stay consistent within a block:

1. **By specificity.** More specific predicates first, falling
   through to general ones.
2. **By likelihood.** Most-likely predicates first, optimising the
   cost of evaluation.

### Prefer pure guards

A guard with side effects executes conditionally on every prior
guard's result. Restrict effects to the selected branch unless the
side effect *is* the test (e.g. `lock_acquired?(lock)`).

### Bind once, dispatch many

```text
# Less clear: each `next_token()` call advances state
pickup
  next_token() == :open  -> parse_block()
  next_token() == :colon -> parse_label()
  else                   -> parse_atom()

# Clearer:
let t = next_token()
pickup
  t == :open  -> parse_block()
  t == :colon -> parse_label()
  else        -> parse_atom()
```

### Use `else`, not `true`

The formatter rewrites `true ->` to `else ->`, but human-written
source SHOULD use `else` directly. The literal `true` reads as if a
real condition is being tested; `else` reads as the default arm.

## See also

- The full normative specification is at
  [`docs/PICKUP.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/PICKUP.md).
- The `match` construct -- the structural-dispatch counterpart -- is
  documented at [`/match`](/match) and specified normatively at
  [`docs/MATCH.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/MATCH.md).
  Both specifications were published into HexDocs in v0.33.0.
- For the broader language reference, see
  [`docs/LANGUAGE_SPEC.md`](https://github.com/cure-lang/cure-lang/blob/main/docs/LANGUAGE_SPEC.md).

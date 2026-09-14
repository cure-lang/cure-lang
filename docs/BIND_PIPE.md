# The Binder Pipe `|x|>`
## Language Specification, Version 1.0.0

**Status.** Stable.
**Revision.** 1.0.0 (Initial release).
**Companion constructs.** `|>` (pure pipe), `do` (effect sequencing), `match` (structural dispatch).
**Normative relationship.** `|x|>` is *pure surface sugar*. It introduces no new
semantics: every binder-pipe expression has a definitionally-equal `do` block
(§ 7). Where this document is silent, the semantics of the desugaring target
govern.

---

## Table of Contents

1. Introduction
2. Conformance Terminology
3. Lexical Syntax
4. Grammar
5. Static Semantics
6. Dynamic Semantics
7. Desugaring (Normative)
8. Interaction with `|>`, `do`, and `match`
9. Formatting Rules
10. Examples
11. Errors and Diagnostics
12. Non-Goals
13. Stability, Versioning, and Deprecation
14. Summary
15. Appendix A — Acceptance Test Suite
16. Appendix B — Glossary
17. Appendix C — Normative Requirements Index

---

## 1. Introduction

`|x|>` is a *binder pipe*: like `|>` it threads a value through a sequence of
stages, but each stage *names* the value produced by the previous stage, and the
whole chain is threaded through a **monad** (typically `Result`, `Option`,
`Effect`, `List`, or `Iter`) rather than applied as a plain function argument.

The construct is governed by a single mental model:

> **`|x|>` pipes the previous stage's *unwrapped* value into `x`, and short-circuits
> on the monad's failure arm.**

It exists to flatten the "staircase" of nested `match` on `Result`/`Option` into a
linear sequence, without introducing the `do` keyword or an extra indentation
level:

```text
fn reserve(ledger: Ledger, id: Int, amount: Money) -> Result(Ledger, String) =
  find_account(ledger.accounts, id)
  |account|> Exchange.Money.subtract(account.balance, amount)
  |new_balance|> Exchange.Money.add(account.held, amount)
  |new_held|> update_account(ledger, Account{account | balance: new_balance, held: new_held})
```

`|x|>` is **not** a new control construct. It is a notation for the existing
`do`-sequencing node (§ 7). One AST node, two spellings.

## 2. Conformance Terminology

The key words **MUST**, **MUST NOT**, **SHALL**, **SHOULD**, **SHOULD NOT**, and
**MAY** are interpreted as in RFC 2119, restricted to the language's compiler,
parser, type checker, optimizer, formatter, and language server.

## 3. Lexical Syntax

### 3.1 No New Lexeme

`|x|>` introduces **no new token**. It is composed of existing tokens:

```text
:bar  :identifier  :bar  :gt
 |        x         |     >
```

The lexer MUST NOT be modified to recognise `|x|>`; recognition happens in the
parser (§ 4.2). This guarantees that every existing use of `|` and `>` lexes
unchanged.

### 3.2 Binder Name

The identifier between the bars is an ordinary identifier token
(`:identifier`). It MAY be any valid Cure identifier, including one beginning
with `_` (a silent binding, § 5.5). It MUST NOT be a reserved word.

### 3.3 Whitespace

Whitespace is **not** permitted between the four tokens. `| x |> e`, `|x |> e`,
and `|x| > e` are all syntax errors (`E120`). The four tokens MUST be adjacent
in the source character stream. (This is the one place the construct is stricter
than `|>`, which tolerates surrounding whitespace; the strictness is what makes
the construct unambiguous against `|` followed by an expression.)

### 3.4 Layout

A binder pipe participates in ordinary indentation-sensitive layout. A chain MAY
span multiple lines, with each `|x|>` stage beginning a continuation line
(mirroring the leading-`|>` idiom). A stage's right-hand side MAY itself be a
multi-line expression.

## 4. Grammar

### 4.1 Grammar

```text
bind_pipe_expr ::= expr { bind_stage } [ final_stage ]

bind_stage     ::= "|" identifier "|>" expr
final_stage    ::= expr
```

The construct is left-associative and binds at the same precedence as `|>`
(the `Pipe` precedence group, § 4.3).

### 4.2 Parser Rule

At `Pipe` precedence, when the parser observes the four-token sequence
`:bar :identifier :bar :gt` (with no intervening trivia), it MUST parse:

1. the binder identifier `x`;
2. the stage expression `e` at `Pipe`-right binding power;
3. and emit the AST node described in § 7.1.

A `:bar` **not** followed by `:identifier :bar :gt` is parsed as today (list
cons separator, or a syntax error in expression position) — the rule is
strictly a four-token lookahead and never changes the meaning of a lone `|`.

### 4.3 Precedence

`|x|>` shares the `Pipe` precedence group with `|>`:

```text
precedencegroup Pipe
  associativity: left
```

Consequently `a |x|> f(x) |> g |y|> h(y)` parses left-associatively, and pure
`|>` and monadic `|x|>` stages MAY interleave freely (§ 8.1).

### 4.4 Block Termination

A binder-pipe chain extends through consecutive `|x|>` stages at the same
indentation. It ends at the first stage expression, which is the chain's result.
There is no closing delimiter.

## 5. Static Semantics

### 5.1 Typing (Informal)

Let the chain be `e₀ |x₁|> e₁ |x₂|> e₂ … |xₙ|> eₙ`. Each stage expression `eᵢ`
MUST have type `m(τᵢ)` for a single monad `m` in scope, where `m` has an
`and_then` (bind) operation available by coherence (§ 5.3). The binder `xᵢ` has
type `τᵢ` — the **unwrapped** payload — inside `eᵢ₊₁ … eₙ`.

The type of the whole chain is `m(τₙ)` where `τₙ` is the type of the final stage
after auto-lifting (§ 5.4).

### 5.2 Monad Uniformity

Every stage MUST resolve to the **same** monad `m`. A chain mixing `Result` and
`Option` stages is rejected with `E121` (`:bind_pipe_monad_mismatch`), reported
at the first stage whose monad disagrees with the chain's.

### 5.3 Bind Resolution (Coherence)

The bind operation for `m` is resolved by the language's ordinary interface
coherence, exactly as `<>` resolves through `Std.Semigroup` and `+` through
`Std.Arithmetic`. The `Monad(m)` interface provides:

```cure
interface Monad(m)
  fn pure(x: a) -> m(a)
  fn and_then(ma: m(a), f: a -> m(b)) -> m(b)
```

Instances MUST exist for at least `Result`, `Option`, and `Effect`; `List` and
`Iter` SHOULD provide instances. If no `Monad` instance is in scope for the
stage's type, the chain is rejected with `E122` (`:bind_pipe_no_monad`).

### 5.4 Final-Stage Auto-Lift

The final stage `eₙ` is **checked against the unwrapped result type** `τₙ` and
lifted with `pure`:

- If `eₙ : m(τₙ)` already, it is used as-is.
- If `eₙ : τₙ` (pure), it is lifted to `pure(eₙ) : m(τₙ)`.

This mirrors `do`'s existing effect-goal auto-lift and is why the worked example
in § 1 needs no `Ok(...)` wrapper on its last line. The lift is `Monad.pure`
resolved by the same coherence as § 5.3.

### 5.5 Bindings and Scoping

Each binder `xᵢ` is introduced by the stage it precedes and is in scope in every
**subsequent** stage expression and in the final stage. It is NOT in scope in
its own stage's expression `eᵢ` (the value does not exist until `eᵢ` has run).

A binder named `_name` is a *silent binding*: it binds but suppresses the
unused-variable warning. A bare `_` is a wildcard and binds nothing.

Binders are hygienic and do not escape the chain.

### 5.6 Effects

`eff(chain) ⊆ ⋃ᵢ eff(eᵢ)`. The construct itself contributes no effect beyond
those of its stages and the resolved `and_then`/`pure`.

### 5.7 Free Variables

`FV(chain) = FV(e₀) ∪ ⋃ᵢ (FV(eᵢ) \ {x₁…xᵢ₋₁})`.

### 5.8 Substitution

Capture-avoiding, per stage: `[v/z]` distributes into every stage expression,
with a stage re-binding `z` shielding its own body.

### 5.9 Well-Formedness

A binder-pipe chain is well-formed iff: (1) it has at least one `|x|>` stage;
(2) all stages share one monad (§ 5.2); (3) that monad has an in-scope `Monad`
instance (§ 5.3); (4) every stage expression is independently well-formed; (5)
the final stage is well-formed at the unwrapped result type (§ 5.4).

### 5.10 Decidability

The checks of §§ 5.1–5.5 and 5.9 are decidable in time linear in the size of the
chain, modulo the language's general type-checking and coherence resolution.

## 6. Dynamic Semantics

### 6.1 Evaluation Order

Stage expressions are evaluated left to right. `e₀` is evaluated first; its
unwrapped payload is bound to `x₁`; then `e₁` is evaluated; and so on. The final
stage is evaluated last.

### 6.2 Short-Circuit

If any stage evaluates to the monad's failure arm (`Error` for `Result`, `None`
for `Option`, etc.), the chain evaluates to that failure value **without
evaluating any subsequent stage**. This is the defining behaviour: the staircase
it replaces has the same short-circuit, and the binder pipe preserves it exactly.

### 6.3 Result

If no stage short-circuits, the chain evaluates to the final stage's value,
lifted per § 5.4.

### 6.4 Side Effects

A stage `eᵢ`'s side effects are observed iff every stage `e₀…eᵢ₋₁` produced a
success value. No stage after a failure is evaluated, so no side effect after a
failure is observed.

## 7. Desugaring (Normative)

### 7.1 AST

A binder-pipe chain parses to the **exact** AST node a `do` block parses to:

```elixir
{:block, [do: true, …],
 [
   {:assignment, [let: true, do_bind: true, …], [pattern, value]},
   …
   final_expression
 ]}
```

where each `|xᵢ|> eᵢ` contributes one `{:assignment, …, [xᵢ, eᵢ]}` and the final
stage contributes `final_expression`. This is identical to the node produced by
`parse_do/2` and by the `let`-chain folder; the parser MUST NOT introduce a
distinct node type.

### 7.2 Elaboration

The node elaborates through the existing `do`/`let`-block path. The elaborator
MUST generalise its effect-only dispatch so that a stage whose RHS type is
`m(a)` for any monad `m` with an in-scope `Monad` instance lowers to
`and_then(rhs, fn(x) -> rest end)`, and the final stage to `pure(final)` when
pure. The `Effect` case MUST remain byte-for-byte identical to today's lowering
(`Effect`'s `and_then` is the existing `let`-as-bind).

### 7.3 Equivalence

For every well-formed binder-pipe chain, there is a `do` block that is
*definitionally equal*:

```text
a |x|> f(x) |y|> g(y)
≡
do
  x <- a
  y <- f(x)
  g(y)
```

and a `let`-chain that is definitionally equal:

```text
a |x|> f(x) |y|> g(y)
≡
let x <- a
let y <- f(x)
g(y)
```

The three spellings are interchangeable; the formatter (§ 9) canonicalises
toward the binder pipe where a chain is linear and each binder is used.

## 8. Interaction with `|>`, `do`, and `match`

### 8.1 With `|>`

Pure `|>` stages and monadic `|x|>` stages MAY interleave. A `|>` stage applies
its left operand as the first argument of its right operand (unchanged); an
`|x|>` stage threads the monad and binds. Example:

```text
find_account(ledger.accounts, id)
|> validate_non_empty            # pure: Result -> Result
|account|> Exchange.Money.subtract(account.balance, amount)
|> Std.Result.map(fn(m) -> m)    # pure step over the monadic value
```

### 8.2 With `do`

`|x|>` and `do` are the same construct (§ 7). A chain MAY NOT mix the two
spellings in one expression; a `do` block's statements are `let`/`<-` binds, and
a binder-pipe chain's stages are `|x|>` stages. The formatter MAY rewrite a
`do` block whose body is a linear bind chain into a binder-pipe chain, and vice
versa, under `H-BIND-PIPE-CANONICAL` (off by default).

### 8.3 With `match`

A binder pipe does **not** peel a monadic scrutinee. `match e` where `e : m(a)`
remains an error; bind first (`|x|> match x …`) or match on the bound payload.
This preserves `do`'s existing discipline and keeps every sequencing point
visible.

## 9. Formatting Rules

### 9.1 Stage Layout

Each `|x|>` stage MUST begin on its own line, indented one `indent_step` deeper
than the chain's first operand, EXCEPT when the entire chain fits on one line
within `max_line_width`, in which case it MAY be rendered inline.

### 9.2 Binder Alignment

When stages are multi-line, the `|` of each stage SHOULD align at the same
column.

### 9.3 Round-Trip

The formatter MUST round-trip a binder-pipe chain byte-for-byte: parsing a
formatted chain and re-rendering it yields the same text. The formatter MUST
emit `|x|>` (not `do`, not a `let`-chain) for a chain that was authored as a
binder pipe.

### 9.4 Comment Fidelity

Comments attached to a stage travel with that stage. No comment is lost,
duplicated, or character-modified.

## 10. Examples

### 10.1 The Ledger Reserve (the motivating example)

```text
fn reserve(ledger: Ledger, id: Int, amount: Money) -> Result(Ledger, String) =
  find_account(ledger.accounts, id)
  |account|> Exchange.Money.subtract(account.balance, amount)
  |new_balance|> Exchange.Money.add(account.held, amount)
  |new_held|> update_account(ledger, Account{account | balance: new_balance, held: new_held})
```

### 10.2 Option

```text
fn first_even(xs: List(Int)) -> Option(Int) =
  Std.List.find(xs, fn(x) -> x % 2 == 0 end)
  |x|> Some(x * 2)
```

### 10.3 Effect

```text
fn ping(s: Subject(Cmd)) -> Effect(Option(Cmd)) =
  s
  |_|> Std.Otp.subject_send(s, Ping())
  |reply|> Std.Otp.subject_receive(s, 1000)
```

### 10.4 Mixed `|>` and `|x|>`

```text
fn charge(wallet: Wallet, amount: Money) -> Result(Receipt, String) =
  wallet
  |> normalize
  |w|> debit(w, amount)
  |new_balance|> Ok(Receipt{wallet: w, balance: new_balance})
```

## 11. Errors and Diagnostics

- `E120` / `E-BIND-PIPE-MALFORMED` — the four tokens `|`, identifier, `|`, `>`
  are not adjacent, or the binder is a reserved word. Severity: error.
- `E121` / `E-BIND-PIPE-MONAD-MISMATCH` — stages resolve to different monads.
  Severity: error, reported at the first disagreeing stage.
- `E122` / `E-BIND-PIPE-NO-MONAD` — no `Monad` instance is in scope for a
  stage's type. Severity: error.
- `H-BIND-PIPE-CANONICAL` — a `do` block was rewritten to a binder pipe (or vice
  versa). Severity: hint; formatter opt-in only.

## 12. Non-Goals

- **Pattern binders.** The binder is an identifier, not a pattern. Destructure
  inside the stage (`|x|> match x …`) or bind and destructure in the next stage.
- **Per-stage failure handling.** A stage cannot "catch" the previous failure;
  use `Std.Result.or_else` on the whole chain, or `match` the result.
- **Parallel stages.** Stages are strictly sequential.
- **A new control construct.** `|x|>` is sugar (§ 7); it adds no semantics.

## 13. Stability, Versioning, and Deprecation

Specification version 1.0.0. Behaviour is stable. `|x|>` is pure sugar over
`do`; if `do`'s semantics ever change, `|x|>` follows by § 7.3. New monad
instances MAY be added; the construct's surface MUST NOT change.

## 14. Summary

`|x|>` is a left-associative, `Pipe`-precedence binder pipe. Each stage threads
the previous stage's unwrapped value into a named binder and short-circuits on
the monad's failure arm; the final stage auto-lifts with `pure`. It is
definitionally equal to the equivalent `do` block and `let`-chain — one AST
node, three spellings — and introduces no new token and no new semantics.

> **`|x|>` pipes the previous stage's unwrapped value into `x`, and short-circuits
> on the monad's failure arm.**

## 15. Appendix A — Acceptance Test Suite

### A.1 Selection and Short-Circuit

```text
ok(1) |x|> ok(x + 1) |y|> ok(y * 2)
-- expected: Ok(4)

error(:e) |x|> ok(x + 1) |y|> ok(y * 2)
-- expected: Error(:e)   (stages after the error are not evaluated)

ok(1) |x|> error(:mid) |y|> ok(y)
-- expected: Error(:mid)
```

### A.2 Final-Stage Auto-Lift

```text
ok(1) |x|> x + 1
-- expected: Ok(2)   (the pure final stage is lifted with `pure`)

ok(1) |x|> ok(x + 1)
-- expected: Ok(2)   (an already-monadic final stage is used as-is)
```

### A.3 Option

```text
Some(3) |x|> Some(x * 2) |y|> Some(y + 1)
-- expected: Some(7)

None() |x|> Some(x * 2)
-- expected: None()
```

### A.4 Scoping

```text
ok(1) |x|> ok(x + 1) |y|> ok(x + y)
-- expected: Ok(3)   (`x` is in scope in the stage that binds `y` and in the final stage)
```

### A.5 Static Rejection

```text
ok(1) |x|> Some(x)          -- E121 (Result then Option)
ok(1) |x |> x + 1           -- E120 (whitespace between tokens)
ok(1) | x |> x + 1          -- E120
```

### A.6 Equivalence with `do`

```text
-- These two MUST elaborate to the same Core (definitional equality):
ok(1) |x|> ok(x + 1)
do
  x <- ok(1)
  ok(x + 1)
```

## 16. Appendix B — Glossary

- **Binder pipe.** The `|x|>` construct.
- **Stage.** One `|x|> e` segment of a chain.
- **Binder.** The identifier `x` naming a stage's unwrapped payload.
- **Short-circuit.** The guarantee that no stage after a failure is evaluated.
- **Auto-lift.** The `pure`-lifting of a pure final stage (§ 5.4).
- **Monad.** A type `m` with `pure`/`and_then` (the `Monad(m)` interface).

## 17. Appendix C — Normative Requirements Index

- § 3.1 — No new lexeme; recognition is parser-side.
- § 3.3 — The four tokens MUST be adjacent.
- § 4.2 — Four-token lookahead; a lone `|` is unchanged.
- § 4.3 — `Pipe` precedence, left-associative.
- § 5.2 — All stages share one monad (`E121`).
- § 5.3 — Bind resolved by coherence (`E122`).
- § 5.4 — Final stage checked at the unwrapped type and lifted with `pure`.
- § 5.5 — Binder scope is subsequent stages only.
- § 6.2 — Short-circuit on failure.
- § 7.1 — MUST parse to the `do` AST node; no distinct node type.
- § 7.2 — Elaborator generalises effect-only dispatch to any monad; `Effect`
  lowering unchanged.
- § 7.3 — Definitionally equal to the `do` block and `let`-chain.
- § 8.3 — No peeling a monadic scrutinee.
- § 9.3 — Formatter round-trips byte-for-byte.

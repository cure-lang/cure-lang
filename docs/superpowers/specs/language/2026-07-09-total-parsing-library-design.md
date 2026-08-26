# `Std.Parse` / `Std.Lex` — a Total Parsing Library

**Date:** 2026-07-09
**Status:** design (operator-requested).
**Reference:** `~/Develop/idris2-parser` (Stefan Höck) — *"Total Lexers and Parsers
for Idris2"*. This spec is a faithful port of that library's core mechanism to
Cure, adapted where the BEAM/AtomVM target demands it.
**Relationship:** the expressive substrate that the `parse` grammar macro
([`macros/2026-07-08-parse-macro-design.md`](macros/2026-07-08-parse-macro-design.md))
lowers onto. Revises that macro's §11 non-goal #2 — see §9.

**Release placement (2026-07-17):** completion of this public library is parked
for Cure 0.35 and feeds the Cure-native parser/diagnostics/self-hosting program
specified in
[`2026-07-17-cure-native-parser-diagnostics-self-hosting-design.md`](2026-07-17-cure-native-parser-diagnostics-self-hosting-design.md).
The 0.34 dependent-type rewrite may retain landed substrate and fix general
compiler gaps it exposes, but does not take on the remaining parser product.

**Implementation status (2026-07-17):** the list-shaped `Consumed` relation,
strict drop constructor, reflexivity, transitivity, the dependent `Step`
result, and strict-suffix accessibility `Acc` have landed in `Std.Data.Suffix`.
Landing `Step` also fixed the general
family-application inference bug it exposed: index-variable types are now
instantiated with the applied family's actual parameters before being placed in
a constructor telescope, so a field such as `Consumed(t, strict, rest, orig)`
correctly refers to the surrounding `t` and earlier named `rest` field. Landing
`Acc` unified dependent-arrow parsing for ordinary annotations and higher-order
constructor fields; both now retain named Π domains through the same AST shape.
The consumption bit follows the reference's lower-bound semantics (`True`
guarantees a proper suffix; `False` makes no guarantee), including a drop
constructor polymorphic in that bit. The structural `weaken`/`weakens`
conversions are the next slice: their honest definitions currently expose a
general dependent-match motive `:branch_type` rejection and must not be replaced
by an unchecked cast.

---

## 1. Purpose & positioning

A **dependently-typed library** for writing lexers and parsers that are
**provably total** — every parser terminates on every input, checked at compile
time, with zero proof cost at runtime. This is *not* a macro and *not* a
grammar-block DSL; it is a library of indexed types and combinator functions, in
the spirit of the reference, whose README makes the load-bearing point: the real
product is the *totality substrate*, and hand-written mutual-recursive parsers
over it beat a combinator library by an order of magnitude while keeping perfect
control over errors. Combinators are convenience on top; the substrate is the
thing.

Two facts make this more than a convenience for this project:

1. **It is the principled substrate under `parse`.** The `parse` macro already
   ledgered (its §11) that "combinators exist only as the lowering target."
   `Std.Parse` *is* that target, exposed as a first-class library. The two
   compose: `parse` is the declarative PEG skin (totality by size-change, no
   first-class values); `Std.Parse` is the expressive layer beneath it
   (first-class, monadic, context-sensitive, hand-tunable, total by an index).
2. **Totality is carried by a type index, not by the size-change checker.**
   That is what lets a `Std.Parse` parser be *monadic and context-sensitive*
   (length-prefixed frames, tag-dispatched bodies) and **still** provably
   terminate — a combination the size-change-only `parse` macro cannot express.

### 1.1 Module layout

| Module | Contents |
|---|---|
| `Std.Data.Suffix` | The general strict-suffix substrate: the consumption index, its Bool strictness algebra, well-founded accessibility, `Step`. Reusable beyond parsing (mirrors the reference's `Data.List.Suffix`). |
| `Std.Lex` | Total lexers: input → `List (Bounded token)`. The reified `Recognise` algebra + `TokenMap` + `run`. |
| `Std.Parse` | Total parsers: `Grammar` over tokens (or chars) → AST. The combinator surface + `run`. |
| `Std.Parse.Error` | `Bounds`, `ParseError`, `InnerError`, farthest-failure — shared by both phases, reconciled with `parse`'s error record. |

---

## 2. The core mechanism — the strict-consumption index

Everything rests on a single idea: **track, in the type, whether a parser is
guaranteed to consume input, and recurse only under a proof that it did.** Port
of `Data.List.Suffix` / `Data.List.Suffix.Result0`.

### 2.1 The consumption index

A parse step relates its input sequence to what remains. The relation carries one
bit — whether *at least one token was consumed*:

```
# Std.Data.Suffix  (list-shaped instance; see §3 for the binary instance)
#
# Consumed(strict, rem, orig) : proof that `rem` is a suffix of `orig`.
# strict = true guarantees at least one element was dropped; false carries no
# strictness guarantee (and therefore admits both equal and proper suffixes).
type Consumed(strict: Bool, rem: List(t), orig: List(t)) =
  | Same  : Consumed(false, xs, xs)                       # nothing consumed
  | Uncons: Consumed(b, h :: t, cs) -> Consumed(b2, t, cs)
```

Two properties, both from the reference, both essential:

- **Erased to an integer.** `Consumed` is a `{0}`-quantity (compile-time-only)
  index; at runtime it is the *count of elements dropped*. `trans`
  (transitivity — composing two consumptions) is **integer addition**. There is
  no proof term on the device.
- **The strictness bit forms a Bool algebra.** Combinators compute it
  structurally:
  - **sequence** `a` then `b` → `Consumed(sa || sb, …)` (consumed if *either*
    step did),
  - **ordered choice** `a / b` → `Consumed(sa && sb, …)` (guaranteed to consume
    only if *both* branches would),
  - `some p` → `true`, `many p` → `false`.

  This is exactly the Bool `||`/`&&` index algebra Cure already generalizes for
  FRP/fsm discipline typing (`Std.Bool` connectives, see
  [[bool-connectives-use-std-bool]]) — pointed at parsing.

### 2.2 The step type

A single consumption step succeeds with a value + remainder (+ erased proof) or
fails. Named **`Step`**, deliberately *not* `Result` — Cure's stdlib `Result(T,
E)` (`Ok`/`Error`) is the ordinary success/failure type and is what `run`
returns (§2.3); `Step` is the suffix-carrying intermediate (the reference's
`Result0`).

```
# Success carries the remainder and an ERASED proof it is a (strict?) suffix
# of the original; failure carries an error.
type Step(strict: Bool, t: Type, orig, e: Type, a: Type) =
  | Succ(val: a, rem: seq(t), {0} p: Consumed(strict, rem, orig))
  | Fail(err: e)
```

`Step` has the same Bool-indexed conversions as the reference
(`weaken : Step(b,…) -> Step(false,…)`, `weakens`, `trans`, `<|>` which `&&`s
the strictness of its two branches). These are the plumbing that lets the
combinator algebra typecheck; they all erase.

### 2.3 Totality by well-founded recursion

Totality does **not** come from Cure's size-change checker here. It comes from
**accessibility on the strict-suffix relation**, ported from the reference's
`SuffixAcc`/`suffixAcc`:

```
# An accessibility witness: for every STRICTLY smaller remainder, we again
# have accessibility. Erased.
type Acc(orig: seq(t)) =
  | MkAcc(step: {ys: seq(t)} -> {0} Consumed(true, ys, orig) -> Acc(ys))
```

A parser typed `… -> Step(true, …)` provably yields a strictly smaller
remainder, so a driver may recurse under `Acc` and Cure accepts it as total:

```
# The canonical driver: repeatedly apply a STRICT step until input is exhausted.
# Provably total — each iteration consumes ≥1 token, Acc guarantees descent.
# Returns Cure's ordinary Result(ok, err) = Ok(List(a)) | Error(e).
fn run(step: (ts: seq(t)) -> Step(true, t, ts, e, a), input: seq(t))
     -> Result(List(a), e) =
  loop([], input, acc(input))    # acc erases; this is a plain BEAM loop (§7)
```

**This is the crux.** Because the descent is witnessed by a value index rather
than syntactic recursion structure, the parser body may do *arbitrary*
computation between consumption steps — including **monadic bind whose
continuation depends on a parsed value** — and remain total, as long as each
recursive call is under a strict-consumption proof. That is the expressive power
the `parse` macro structurally cannot reach.

---

## 3. Input representation — the approved split

The index algebra in §2 is representation-free: only *how you uncons* and *what
the remainder is* differ. v1 ships **two concrete instantiations**, each matched
to where it runs.

### 3.1 Char / lexer phase — over the native binary `String`

The hot path is raw bytes, and on the BEAM the fast path for that is **binary
pattern matching**, which the VM is built for and which the `parse` macro (§6)
and `packet`/`codec` already commit to. So the char phase does **not** use
`List Char`. Its remainder type is the native `String` (a BEAM binary), and
`uncons` *is* a binary match:

```
# uncons over a binary String: the remainder is a ZERO-COPY sub-binary.
#   <<c/utf8, rest/binary>>  in Erlang terms
fn uncons_str(s: String) -> Option((Char, String))
```

The remainder `rest` shares the original buffer — a pointer + offset + length,
no copy. This is precisely the "offset into a shared buffer" that a hand-rolled
binary+offset design would give, obtained **for free from BEAM sub-binaries**,
with no `List Char` ever materialized and no optimizer pass required. The
consumption index over `String` is "the offset strictly increased," bounded by
`byte_size`; the termination measure is `byte_size - offset`.

- **UTF-8:** literals match their UTF-8 encoding; `.`/any consumes one
  well-formed codepoint (`/utf8` segment); character classes are ASCII-only in
  v1. Same decision the `parse` macro reached (its §6). Malformed UTF-8 at a
  `.` is a parse error.

### 3.2 Parser phase — over a `List` of bounded tokens

Tokens are few, already heap-resident, and want structure, so the parser phase
uses the reference's `List`-shaped `Consumed` directly over `List (Bounded
token)`. The structural proof is free here; nothing is gained by a binary.

### 3.3 Why two instantiations, not one interface (v1)

v1 ships §3.1 and §3.2 as **two concrete instantiations that share the Bool
strictness-algebra helpers** (a small amount of duplication), **not** unified
under an `interface Input`. Reason: the typeclass/`interface` feature is still
in-flight ([[typeclass-surface-decisions]], [[classic-pipeline-deletion]]); the
parser library must not sit on its critical path. Unifying both instances under
an `interface Input` with an associated remainder type is desirable and
**ledgered** (§10) for when typeclasses land — at which point the duplication
collapses without changing the surface.

---

## 4. Lexer layer (`Std.Lex`)

Preserve the reference's deliberate asymmetry: **lexers are reified data,
parsers are direct functions.** A lexer (`Recognise`) is a small algebra
interpreted by `run`, so that a `TokenMap` is *data* you can build and
introspect; a parser (`Grammar`, §5) is a plain function, for first-classness
and speed.

```
# A recogniser consumes a (strict?) prefix of the char input.
type Recognise(strict: Bool) =
  | Lift (Shifter(strict))                                   # primitive
  | Seq  (Recognise(b1), Recognise(b2))    -> Recognise(b1 || b2)   # <+>
  | SeqL (Recognise(true), Recognise(b))   -> Recognise(true)      # <++> (lazy tail)
  | Alt  (Recognise(b1), Recognise(b2))    -> Recognise(b1 && b2)  # <|>

# Interpreter, total via Acc (§2.3):
fn run_rec(r: Recognise(b), consumed: SnocList(Char), cs: String, {0} a: Acc(cs))
     -> ShiftRes(b, consumed, cs)
```

Derived recognisers mirror the reference: `empty` (`false`), `opt`, `expect`/
`reject` (zero-width look-ahead), `pred`/`preds`/`preds0` (char predicates),
`many`/`some` (mutually defined, `some = r <++> many r`), `choice`.

A `TokenMap` maps recognisers to token builders; `Std.Lex.run` walks the input,
at each position taking the **first** recogniser that matches a non-empty
prefix, emitting a `Bounded token` (token + source `Bounds`), and — being a
strict step — is driven to exhaustion by the §2.3 loop. Whitespace handling is
an explicit recogniser (no invisible skipping), matching the `parse` macro's
stance.

---

## 5. Parser layer (`Std.Parse`)

**A parser is a direct total function**, generic over token type `t`:

```
# Grammar(strict, t, e, a): consume a (strict?) prefix of a token list,
# yield an `a` or an error `e`.
type Grammar(strict: Bool, t: Type, e: Type, a: Type) =
  (ts: List(Bounded(t))) -> Step(strict, Bounded(t), ts, e, a)
```

Because `t` is a parameter, instantiating `t = Char` over §3.1 gives a
**single-phase char parser** with no separate lexer, when that is simpler.

### 5.1 Combinator surface (v1)

Ported from the reference's `Text.Parse.Syntax` / `Manual`:

| Combinator | Strictness type |
|---|---|
| `pure v` | `Grammar(false, …)` |
| `map f g`, `f <$> g` | preserves `g`'s strictness |
| `<*>`, `*>`, `<*` (applicative) | `‖` of operands |
| `<|>` (ordered choice) | `&&` of operands |
| `optional g` | `false` (wraps in `Option`) |
| `many g` (requires `g : true`) | `false`, yields `List(a)` |
| `some g` (requires `g : true`) | `true`, yields `NonEmpty(a)` |
| `sep_by` / `sep_by1` | as reference (`sep_by1 : true`) |
| `between(open, close, g)` | `true`; `Unclosed` error on EOI |
| `exact tok`, `token`, `eoi`, `any` | primitives |
| **`bind` / `>>=`** (monadic) | `‖` of the two stages |

The `many`/`some` requirement that the repeated parser be `true` (strictly
consuming) is *enforced by the type* — a `many` over a possibly-empty parser
does not typecheck. This is how the library reproduces the `parse` macro's
"repetition over a possibly-empty body" rejection (its §4), but as an ordinary
type error rather than a bespoke grammar check.

### 5.2 Context-sensitivity — the payoff over `parse`

Monadic `bind` lets the next parser depend on a *parsed value* — the thing PEG
cannot express — while staying total:

```
# Length-prefixed frame: read a count, then exactly that many items.
# Total: `count_p` is strict, `repeat_exact n item_p` is strict for n>0,
# the whole bind is strict, and `run` drives it under Acc.
fn frame(item_p: Grammar(true, t, e, a)) -> Grammar(true, t, e, List(a)) =
  count_p >>= fn(n) -> repeat_exact(n, item_p)
```

The same shape covers tag-dispatched bodies (read a tag, dispatch to a
tag-specific parser). These are exactly the formats `parse` must reject; they are
ordinary here.

---

## 6. Errors

Adopt the reference's error model, reconciled with the `parse` macro's positioned
errors so a lowered grammar produces identical diagnostics:

- **`Bounds`** — every token and error carries a source span (`start`/`end`,
  `line:col`, byte offset). Lexers attach bounds; parsers propagate them.
- **`ParseError` / `InnerError`** — structured errors: `Expected [..]`,
  `Unexpected tok`, `EOI`, `Unclosed`, plus a user error slot `e`.
- **Farthest-failure** — report the deepest position any alternative reached,
  not where the outermost choice gave up (`1.2.x` fails at col 5 wanting a
  digit, not at col 1). Standard PEG technique, and the exact behaviour the
  `parse` macro's §5 invests in.
- **Reconciliation:** `Std.Parse.Error` is the single error surface; the `parse`
  macro's `ParseError` record (with its `expects` hints) is a thin presentation
  over it, so grammar-authored and hand-written parsers report the same way.

v1 reports the first (farthest) failure only; recovery/multiple-errors is
deferred (§8), matching `parse`.

---

## 7. Totality, erasure & the device story

- **The accessibility witness erases.** `Acc` and `Consumed` are `{0}`; after
  erasure `run` is a **plain BEAM loop** over a binary (char phase) or a token
  list (parser phase) — no proof objects, no witness allocation.
- **The proof is an integer.** Where consumption counts survive, they are
  integers; `trans` is addition. This is the reference's runtime representation,
  preserved.
- **Pure value surface.** The library is ordinary total functions — no
  `receive`/`spawn` (no E043), no processes, no solver at runtime. It ships to
  ESP32/AtomVM as plain BEAM bytecode; a parser that typechecks carries **zero**
  device-side verification cost. Fits the proven value surface
  ([[value-surface-parity-program]]).
- **Must-verify on-device (not assumed):** AtomVM support for sub-binary
  references and `/utf8` segment matching in binary patterns. The whole char
  phase (§3.1) depends on it. Per this project's rule, verify on generic-unix
  AtomVM first, then hardware, before relying on it — do not assume BEAM
  behaviour transfers to AtomVM.

---

## 8. v1 scope

**In:** §2 substrate (`Std.Data.Suffix`), §3 both input instantiations, §4
lexer core, §5 parser core + the §5.1 combinators including monadic `bind`, §6
error model, §7 erasure/device guarantees.

**Deferred (not v1):**

- The reference's **`Manual`** ultra-high-performance ergonomics (hand-fused
  `AutoTok`/`SafeTok` consumer families). v1 exposes the combinators + `run`;
  the manual style is a later ergonomics layer over the same substrate.
- The **tokenizer DSL** (`Text.Lex.Tokenizer`).
- The **format sub-libraries** (JSON, TOML, TSV, WebIDL). These become
  **tests/examples** proving the library on real grammars, not v1 library code.
- **Streaming / line-oriented input** (UART reality) — see §10.

---

## 9. Relationship to the `parse` macro — revising a non-goal

The `parse` macro's §11 non-goal #2 reads: *"No public parser-combinator library
— the grammar surface IS the API; combinators exist only as the lowering
target."* **This spec revises that**, with justification:

- `Std.Parse` is **not a second way to do the same thing.** It is the strictly
  more powerful lower layer. `parse` cannot express first-class parser values,
  parameterized parsers, or context-sensitive (monadic) grammars; `Std.Parse`
  can. There is no overlap in capability to create a "two ways" hazard — there is
  a capability *ladder*.
- The intended relationship is **`parse` lowers onto `Std.Parse`.** A `parse`
  grammar block elaborates to `Std.Parse` combinators/recursion, inheriting its
  totality and error model. `parse` remains the recommended beginner surface for
  the grammars it can express; `Std.Parse` is where you drop when you need
  power.
- The `parse` docs should therefore say: *"declarative grammars use `parse`;
  reach for `Std.Parse` when you need first-class or context-sensitive
  parsers,"* replacing the flat prohibition. This spec supersedes that non-goal;
  the `parse` spec should be annotated to point here.

Boundary with siblings is unchanged: `packet` owns binary frames, `codec` owns
JSON/CBOR-from-a-type. `Std.Parse` is text/token parsing and the lowering
substrate.

---

## 10. Ledger — separate initiatives, off this critical path

1. **General `List → binary` representation-selection optimization.** The
   independently valuable codegen pass: when a `List(t)` (`t` a fixed-width
   scalar) is sourced from a binary and consumed front-to-back by uncons,
   represent it as a BEAM binary and lower `x :: xs` to `<<x, xs/binary>>` (tail
   = zero-copy sub-binary). Benefits `packet`, `codec`, `Std.String`, any
   decoder — and would let a parser written over a *plain* `List` (not `String`)
   get the §3.1 runtime shape retroactively. **Deliberately not a prerequisite**
   here: it is best-effort (fires only when an escape/usage analysis proves
   front-consumption), a sizable post-erasure pass, and must be verified on
   AtomVM. The library gets the binary shape *by construction* (§3.1) instead of
   betting on it. Spec this on its own merits.
2. **`interface Input` unification.** Collapse §3's two instantiations under one
   `interface Input` (associated remainder type + `uncons` + the consumption
   index ops) once the typeclass feature lands. Surface-compatible with v1.
3. **Streaming / line-oriented input.** A line-oriented mode (feed UART lines,
   parse each) for the embedded reality; full chunk-resumable parsing is a
   harder, separate machine. Matches `parse` §10.2.
4. **`Manual` high-performance layer** (§8) — the hand-fused consumer families
   for perf-critical parsers, once the combinator layer is proven.

---

## 11. Non-goals

- **Not a macro.** No grammar-block syntax here — that is `parse`. This is a
  library of types and functions.
- **No regex.** `Std.Regex` is a dead-end on AtomVM; grammars/parsers replace
  it. (`parse`'s regex-refugee table stands.)
- **No JSON/CBOR schema parsing** — that is `codec`. JSON here exists only as a
  *test* of the library.
- **No fuel / no runtime step budget.** Totality is by the consumption index, not
  a counter. If it typechecks, it terminates; there is nothing to tune.

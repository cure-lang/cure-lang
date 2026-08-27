# `parse` — Total, Typed Text Parsers from Grammar Blocks

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§7.2); sibling of `packet` (§6.3, binary) and `codec` (§7.2, JSON/CBOR).
Built as a `macro` (§5) — zero compiler special-casing.

**Release placement (2026-07-17):** public completion and lowering onto
`Std.Parse` are parked for Cure 0.35 as part of
[`../language/2026-07-17-cure-native-parser-diagnostics-self-hosting-design.md`](../language/2026-07-17-cure-native-parser-diagnostics-self-hosting-design.md).
This is outside the 0.34 dependent-type rewrite.

---

## 1. Purpose & positioning

A `parse` block declares a PEG-style grammar and compiles it to **plain,
total, typed Cure functions** over the input string. Two strategic facts make
this macro more than a convenience:

1. **It retires the `Std.Regex` dead-end on device.** AtomVM has no `:re`
   module — regex is proven unavailable on ESP32 in this project. A grammar
   compiles to pure Cure, so it runs anywhere AtomVM does: the same parser
   works in the firmware, the host tool, and the test suite.
2. **Totality is the headline.** Size-change passes the generated parsers,
   so *your parser provably terminates on every input* — no catastrophic
   backtracking, no ReDoS, no string that wedges the board. Regex engines
   market backtracking limits; Cure markets a theorem.

Per hiding principle 1, the user declares a grammar and result types; the
elaborator manufactures the parser, its ADT wiring, and its errors. Per
principle 2, the two constructions that could break totality (left recursion,
empty repetition) are rejected with a rewrite shown, never a proof asked (§4).

## 2. Surface — declaring a grammar

The parent spec's Semver sketch, expanded to the full flagship:

```cure
type Version = Version(major: Int, minor: Int, patch: Int)

parse Semver
  version <- major "." minor ("." patch)?        -> Version
    expects "a version number like 1.2.3"
  major   <- digits                              -> Int
  minor   <- digits                              -> Int
  patch   <- digits                              -> Int
  digits  <- [0-9]+
```

Each rule is `name <- expression -> Result`. The expressions are PEG:

| Form | Meaning |
|---|---|
| `a b` | sequence — `a` then `b` |
| `a / b` | **ordered choice** — try `a`; if it fails *without consuming*, try `b` |
| `a?` | optional |
| `a*` / `a+` | zero-or-more / one-or-more |
| `&a` / `!a` | and- / not-predicate — lookahead, consumes nothing |
| `"lit"` | literal string |
| `[0-9a-f]` | character class (ranges, sets, `[^…]` negation) |
| `.` | any single character |
| `eof` | end of input (anchoring; a top rule is implicitly anchored, §10.7) |

**Captures are positionally typed.** A rule's `->` names a constructor
(ADT/record ctor or a builtin like `Int`), and the elaborator checks it
against the rule's captures — arity *and* types:

- Sub-rule references capture their declared result type; `version` above
  captures `major : Int`, `minor : Int`, `(… patch)? : Option(Int)`.
- Literals and predicates capture nothing (structure, not data).
- `r*` captures `List(T)` where `T` is `r`'s result type; a class-only rule
  like `digits` with no `->` captures the matched text (`String`) — `-> Int`
  on `major` applies the builtin text→Int conversion.
- Optional-with-default: `patch default 0` makes `Version` always receive
  three `Int`s; declaring the field `Option(Int)` is the alternative.

So **grammar/type drift is a compile error**: add a fourth component to
`version` without touching `Version` and elaboration fails at the rule, in
grammar vocabulary — *"rule version captures 4 values but Version takes 3"*
— never a unification dump (parent §4).

## 3. Generated API

```cure
Semver.parse : String -> Result(Version, ParseError)
```

Each named rule is also exported as an entry point (`Semver.digits`) for
testing and composition. `ParseError` is a record: `offset`, `line`, `col`,
`rule`, `expected : List(String)`, `message` (the `expects` text when
present). Streaming input is ledgered (§10.2); v1 parses a complete `String`.

```cure
match Semver.parse(input)
  Ok(v)    -> boot_if_compatible(v)
  Error(e) -> log.warn(e.message)   # "expected a version number like 1.2.3 at 1:6"
```

## 4. Totality & the no-backtracking-blowup story

PEG with explicit repetition is structurally terminating on finite input —
every construct consumes input or is bounded — **except** two classic traps,
both handled by rejection-with-rewrite at elaboration (hiding principle 2:
correct-by-construction, not proved-correct):

1. **Left recursion.** `expr <- expr "+" term` recurses without consuming.
   Rejected with the standard rewrite shown, not just named:

   ```
   error[E16x]: rule `expr` calls itself before consuming any input
     --> calc.cure:3
    3 |   expr <- expr "+" term -> Add
      |           ^^^^ left recursion — this call can never make progress
     Rewrite the rule as a repetition:
       expr <- term ("+" term)*   -> fold_add
     which parses the same language and provably terminates.
   ```

   Detection is nullable-prefix reachability over the rule graph — direct,
   indirect, and hidden left recursion all fall out of the one check.

2. **Repetition over a possibly-empty body.** `ws*` where `ws <- " "?` can
   match nothing forever. Rejected: *"this repetition can match nothing and
   would loop forever — make the body consume at least one character (e.g.
   `" "+`) or drop the repetition."*

With those two shapes excluded, every recursive call decreases on the
remaining-input suffix, and the **existing size-change checker passes the
generated functions naturally** — no parser-specific totality machinery, no
annotation, no proof. And because PEG choice is *ordered and committed* (no
global backtracking search), no input triggers exponential retry: worst case
without memoization is grammar-depth × input-length re-scans, and opt-in
packrat memoization (§10.1) flattens even that. The marketing sentence, per
the parent's sell-the-symptom rule: *"No input — malicious, malformed, or
fuzzed — can hang this parser. That's checked at compile time, not hoped at
runtime."*

## 5. Runtime input errors — a UX product

A parse failure is the *normal* runtime event this macro must be great at:

- **Position-precise**: every error carries `line:col` plus byte offset.
- **Farthest-failure heuristic** (standard PEG technique): report the
  deepest position any alternative reached, with the expectations live
  there — not where the outermost choice gave up. `1.2.x` fails at column 5
  expecting a digit, not at column 1 expecting a version.
- **Rule-named, human-worded**: errors use the innermost rule's `expects`
  annotation — `expects "a version number like 1.2.3"` replaces the
  token-soup default (`expected [0-9]`); rules without one fall back to an
  auto-generated expectation list.

```
error: expected a digit (the patch part of a version number like 1.2.3)
  --> input 1:5
 1 | 1.2.x
   |     ^ found 'x'
```

This is the parent §4 template pointed at *input* instead of code: what the
input said → what the grammar needed → the `expects` hint. v1 reports the
first (farthest) failure only (recovery ledgered, §10.4) — one excellent
error beats three speculative ones.

## 6. What the invisible machinery does

- **Typed captures** — each rule elaborates to a function returning its
  declared result type; the `->` ctor application is ordinary elaboration,
  so capture/ctor mismatch is caught by the same checker as any Cure call,
  then translated by this macro's explainers.
- **Totality** — §4's rejections make the output size-change-clean; nothing
  parser-specific enters the checker.
- **Erasure** — rule-type indices and provenance metadata erase; the runtime
  artifact is plain recursive functions. On BEAM this lowers to **binary
  pattern matching over the UTF-8 input binary** — the fast path the VM is
  built for, zero interpretive overhead, no grammar table at runtime.
- **Unicode (decision)** — v1 operates on **UTF-8 bytes**: literals match
  their UTF-8 encoding (so `"°C"` just works), character classes are
  **ASCII-only**, and `.` consumes one well-formed UTF-8 codepoint (never
  splits a character; malformed UTF-8 is a parse error there).
  Codepoint-range/category classes are ledgered (§10.3). Recommended:
  embedded text formats (NMEA, AT commands, config lines, semver) are
  ASCII-structured with occasional UTF-8 payload — exactly this split.
- The macro is tier-1 (`syntax` + `elab` over quoted rule declarations);
  the elaboration is a total compile-time Cure function, like `packet`'s.

## 7. The regex-refugee table

For `Std.Regex` users migrating (the module is a dead-end on AtomVM):

| Regex idiom | Grammar rule |
|---|---|
| `\d+` | `digits <- [0-9]+` |
| `colou?r` | `"colo" "u"? "r"` |
| `cat\|dog` | `"cat" / "dog"` (ordered — first match wins, always) |
| `^…$` (anchoring) | top rule is anchored; `eof` ends it explicitly |
| `[a-fA-F0-9]{2}` | `hexbyte <- [0-9a-fA-F] [0-9a-fA-F]` |
| `(?=x)` / `(?!x)` | `&x` / `!x` |
| capture groups | rule references — captures are *named and typed*, not numbered |
| `\s*` between tokens | `ws <- [ \t]+` used explicitly (no invisible skipping) |

Regex **syntax** emulation is a non-goal (§11): grammars name their parts,
type their captures, and provably terminate — the migration is an upgrade,
not a shim. The docs ship this table plus three worked migrations (semver,
NMEA sentence, key=value config line).

## 8. `check` integration

Shipped property templates (parent §7.5):

- **Round-trip where a printer exists**: `prop roundtrip(v: Version) =
  Semver.parse(show(v)) == Ok(v)` — the Semver case verbatim; attaches
  automatically when the result type has a `show`/printer.
- **"No input hangs the parser" is static** — totality (§4). The report
  says so: `✓ terminates_on_all_input — proved by construction; 0 runs`.
  The parent's product moment (types deleting tests), on day one.
- **Adversarial near-misses**: the grammar generates *almost-valid* inputs
  — valid prefixes with one mutation (dropped separator, wrong class,
  truncation) — asserting each yields a positioned `ParseError`, never a
  crash, never an `Ok`. This exercises exactly the error paths §5 invests
  in.

## 9. Relation to siblings

- **`packet`** (§6.3) — disjoint, complementary: `packet` is binary frames
  with length-indexed fields; `parse` is text. They compose: a `packet`
  field may invoke a text grammar for an embedded ASCII payload — canonical
  example **GPS NMEA** (line transport, `$GPGGA,…` text payload):
  `payload: text(Nmea.sentence)` inside a `packet`. Boundary rule: `parse`
  never learns bits/endianness; `packet` never grows repetition/choice.
- **`cli`** (§7.3) — arg parsing may reuse this machinery internally; that
  is `cli`'s implementation detail, ledgered *there*, not here.
- **`codec`** (§7.2) — JSON/CBOR/MessagePack belong to `codec`
  (schema-first from a type). Do not write a JSON grammar in `parse`; the
  docs say so at the top of the macro page.

## 10. Open decisions (ledger)

1. **Packrat memoization** — linear-time but O(input × rules) memory, which
   an ESP32 does not have. Recommended: **off by default, opt-in per rule**
   (`memo` on rules genuinely re-tried across choices).
2. **Streaming input** — UART lines are the embedded reality. A
   line-oriented mode (`parse Nmea by_line` — feed lines, parse each)
   covers most device cases; full chunk-resumable parsing is a separate,
   harder machine.
3. **Unicode scope** — v1 byte/ASCII-class per §6; codepoint-range (`[а-я]`)
   and category classes when a user needs them (codepoint-decode mode).
4. **Error recovery / multiple errors** — v1 first-failure-only
   (recommended, §5); recovery points only if a config-file-sized use case
   demands them.
5. **Grammar composition** — one grammar importing another's rules
   (`use Nmea.checksum` inside a custom sentence grammar). Almost certainly
   wanted; needs the cross-grammar rule-type and provenance story.
6. **Binary-input grammars** — PEG over bytes overlaps `packet`.
   Recommendation: **reject** — keep `parse` text-only per §9; revisit only
   if `packet` proves unable to express some length-free byte protocol.
7. **Anchoring default** — recommended: `parse` is anchored (implicit
   `eof`), plus a generated `parse_prefix` variant returning the remainder.

## 11. Non-goals

- **No regex syntax emulation** — no `~r/…/` compatibility layer, ever; the
  §7 table is the migration path. Grammars are better and total.
- **No public parser-combinator library** — the grammar surface IS the API;
  combinators exist only as the lowering target. A second way to do the
  same thing is exactly what the hiding principles forbid.
- **No full incremental reparsing** — re-parse-on-edit with node reuse is
  editor technology; §10.2's line-oriented mode is the embedded answer.
- **No JSON/CBOR grammars** — that is `codec`'s job (§9).

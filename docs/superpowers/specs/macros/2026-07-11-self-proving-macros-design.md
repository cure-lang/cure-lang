# Self-Proving Macros — Type-Enforced Error Descriptions and Generative Expansion Safety

**Date:** 2026-07-11
**Status:** design — approved direction, extends (does not replace) the macro
facility.
**Base spec:** `macros/2026-07-08-macro-facility-design.md` (the tier tower,
grammar-as-examples-with-holes, `becomes`/`computed by f`, the `explain`
construct, the "default error machinery" floor) and
`macros/2026-07-08-error-explainer-design.md` (the never-raw guarantee). This spec
adds the machinery that turns those from *conventions with a default floor* into
*type-enforced obligations*.
**Reference models:** Lean 4 `syntax`/`macro_rules`/`elab_rules`; Racket
`syntax-parse` (error-quality ceiling); the project's own **Antigen** (kernel
soundness by generation) — the load-bearing analogy of §4.

**Settled decisions (2026-07-12, operator):**
1. **`Diagnosis` is author-extensible, not purely grammar-derived** — an author
   declares *semantic* failure points (protocol/state rules that aren't grammar
   violations) alongside the derived structural ones; all are required-described and
   routed identically (§3.4). This is where DSL error quality actually lives.
2. **Exhaustiveness is lenient** — one reusable `describe` may cover many failure
   points; the bar is "every point covered *by something*," preserving the
   copy-one-example floor (§3.2).
3. **The generative proof is the FULL fuzz on every macro compile** (operator,
   2026-07-12) — a macro is not "compiled" until its full Antigen-budget expansion
   proof passes; slower macro compiles are an accepted cost for an always-fully-proven
   guarantee, with no shallow/deep split (§4.2). (An unchanged macro's result may be
   cached — that is not-redoing-identical-work, not a weaker gate.)
4. Defaults confirmed: first-class `region delimited by { }` is an optional later
   slice (custom layout works via Tier-3 `raw until` now); example-equality is the
   author's per-rule choice of exact-Core vs type-only; this extension sequences
   **after** the base macro facility is implemented.

---

## 1. Goal and the one-sentence thesis

The macro facility must let an author model *basically anything* — including a DSL
with its own surface syntax (brackets instead of indentation) — while keeping
**full type safety**. The base spec already delivers the capability (Racket-complete
tiers) and re-elaborates all macro output through the kernel. What it does **not**
yet do is make two guarantees *mandatory and machine-established* rather than
*optional and author-earned*:

1. that **every way a program can violate a DSL is described in the DSL's own
   vocabulary** (never a raw parser/kernel error), and
2. that **every program the DSL accepts expands to well-typed Core**.

**Thesis:** because a DSL's grammar is a *closed, typed* set, both guarantees can be
made *enforced at macro-compile time* — the first by exhaustiveness (you cannot ship
a macro with an undescribed failure point), the second by generation (the facility
fuzzes the closed grammar and proves expansions type-check, the same way Antigen
proves the kernel). Trust is replaced by proof; discipline is replaced by the
compiler.

## 2. The three-layer safety model

A DSL fails in three disjoint places. The design assigns each the *strongest*
guarantee that layer admits, and no stronger:

| Layer | Failure | Set | Guarantee | Mechanism |
|---|---|---|---|---|
| **Parse** | input violates the grammar | **closed** | exhaustive, **by type** | §3 required descriptions |
| **Expansion** | accepted input → ill-typed Core | closed input, open output | **by generation** + intent pins | §4 fuzz + §5 examples |
| **Type** | residual generated-Core error | open | never-raw, **by fallback** | base error-explainer |

The key structural fact, used throughout: **the parse set is closed** (the grammar
is finite examples-with-holes) and **its holes are typed** (each hole is a category
with a Core type). Closed ⇒ its failures are enumerable (§3). Closed + typed ⇒ its
*inputs* are generable (§4).

Type failures of the *generated* code are explicitly **out of scope for author
description** (operator decision 2026-07-11): they cannot be pre-enumerated, they are
covered by §4 generation + §5 examples proving the macro *doesn't* emit them, and any
irreducible remainder degrades through the base never-raw explainer — bounded, not raw.

## 3. Mechanism 1 — parse-error descriptions become a type-enforced total obligation

### 3.1 The failure enumeration is *derived*, not written

The facility derives, from a `macro`'s closed grammar, the set of **failure points** —
one per place a parse can diverge:

- **each typed hole** `<n: Category>` — "this position expected a `Category`";
- **each literal/keyword token** in a rule — "expected `every` here";
- **each `check … else …`** in a Tier-3 elab — a semantic guard on parsed input;
- **rule-selection ambiguity / no-rule-matched** at each grammar nonterminal.

This set is *closed and known at macro-compile time* — it is a sum type the facility
constructs from the grammar (call it the macro's `Diagnosis`). The author never
writes the constructors; they are the grammar's own shape.

### 3.2 The obligation: exhaustive `explain`, checked like case coverage

Today `explain` is optional and a default message fills the gap. The change: an
`explain` block is checked for **exhaustiveness over `Diagnosis`**, exactly as a
`case` is checked over a family's constructors. A failure point with no `explain`
clause (and no category-level `describe`) is a **compile error in the macro** —
`missing_diagnosis: <point>`, listing the uncovered points, with the same
"non-exhaustive match" ergonomics the kernel already gives.

```
macro every
  syntax every <t: Duration> becomes Timer.repeat(t)

  explain
    Duration =>                       # covers the <t: Duration> hole's failure
      "every needs a duration — write every 500ms or every 2s (got " <> show(here) <> ")"
    keyword "every" =>                # covers the literal token
      "a repeat rule starts with `every`"
    # no other failure points exist for this one-rule grammar → exhaustive.
```

- `here` / `got` bind the offending source term (with srcloc) — the same data the
  default machinery already surfaces; now it flows into an author message that is
  *required* to exist.
- A `describe "duration"` on the `Duration` category still works as the reusable
  default for *every* `Duration` hole across the macro, so the exhaustiveness bar is
  "every point is covered *by something*," not "one clause per point." This keeps the
  copy-one-example floor: a one-rule macro needs one or two lines.
- Descriptions are **total Cure** producing `String` (or the richer structured
  diagnostic of the base error-explainer spec), size-change-checked like every other
  `elab`.

### 3.3 Interception: anything that doesn't parse is routed here

The parser, on failing a rule *inside an active DSL region*, does not emit a parser
error — it constructs the `Diagnosis` value for the failure point and evaluates the
macro's `explain` for it. The user sees the DSL's own vocabulary ("per my rules,
here's the specific way you're out of line"), never `expected :rparen, got :comma`.
This is the base spec's never-raw guarantee, promoted from a registration/fallback
convention to a *derived-and-required* property: the macro **cannot compile** with an
undescribed failure point, so the region **cannot** produce an undescribed parse
error.

### 3.4 Author-declared semantic failures (Diagnosis is extensible)

Structural failures (§3.1) are grammar violations. But most real DSLs also enforce
*semantic* rules that parse fine and are still illegal — a state-machine DSL where a
transition names an undeclared state, a protocol DSL where a `reply` precedes its
`request`. These live as `check`s in a Tier-3 elab. The author declares them as their
own failure points, and the facility folds them into the same `Diagnosis` sum:

```
macro protocol
  ...
  # a semantic failure the grammar cannot express — the author names and raises it
  fail ReplyBeforeRequest(state: Code)     # extends Diagnosis with one constructor
  ...
  elab computed by fn(rules) =
    check request_precedes_reply(rules)
      else fail ReplyBeforeRequest(offending_state(rules))

  explain
    ReplyBeforeRequest(s) =>
      "a reply must follow a request — `" <> show(s) <> "` replies with none open"
```

`fail C(args)` declares an author failure point `C`; raising it in an elab
(`else fail C(…)`) is the only way to produce it. The exhaustiveness check of §3.2
covers **both** the derived structural points **and** every author-declared `C` — a
`fail` constructor with no matching `explain` clause is the same
`missing_diagnosis` compile error. So "the creator defines what a failure *is*" is
literal: authors introduce failure modes their DSL's meaning requires, and the type
system forces each to be described and routes it through the DSL's vocabulary,
identically to a grammar failure. Semantic checks therefore do **not** fall back to
the general never-raw path unless the author deliberately leaves them undeclared;
declared ones are first-class, described diagnostics.

A `fail` point can be **generated** too (§4): the fuzzer that hits a `check … else
fail C` path exercises `C`'s `explain`, so an author-declared failure with a crashing
or ill-typed description is caught at macro-compile like any other.

## 4. Mechanism 2 — generative expansion safety (Antigen for DSLs)

This is the fix for the soft spot: "a program that parses expands soundly" must be
*established*, not trusted.

### 4.1 The move

The grammar is closed and its holes are typed, so the facility can **generate valid
parses**: for each rule, fill every hole `<n: Category>` with a generated well-typed
Core term of the hole's type, drawn from the **existing Antigen term generator**
(`lib/antigen/generators/*`). Nest to the grammar's recursion depth. This enumerates
a statistically thorough sample of the DSL's accepted programs *without an author
writing any of them*.

### 4.2 The property and the gate

For each generated program `p`: **expand `p`, then kernel-check the expansion.** The
property is exactly Antigen's:

> No generated valid parse expands to ill-typed Core.

A counterexample — a valid parse whose expansion the kernel rejects — is a **bug in
the macro's `becomes`/`elab`**, and it makes the **macro fail to compile**, reported
with the offending generated input, the expansion, and the kernel error (shrunk, via
Antigen's existing shrinker). The author fixes the expansion before shipping; the DSL
*user* never meets it as a confusing kernel error at use-time.

**Full run on every compile (settled decision 3).** The **full Antigen-budget** run —
with the coverage manifest — gates *every* macro compile: a macro is not considered
compiled until its expansion proof passes at full depth. Slower macro compiles are an
accepted, deliberate cost (operator, 2026-07-12) — the guarantee is that a macro that
compiles has been fully proven, not smoke-tested, so there is no shallow/deep split to
reason about and no "it passed the quick check but the deep check finds bugs" gap. The
one legitimate optimization is **caching by macro definition**: an unchanged macro
(same grammar + elabs) reuses its prior passing result rather than re-fuzzing —
not-redoing-identical-work, never a weaker gate; editing the macro re-runs the full
proof. The manifest still records which rules and `fail` points were exercised, so
coverage is visible, and a macro whose grammar admits shapes the generator cannot yet
build (a hole type outside type-directed generation's reach, §4.4) reports that gap
rather than passing silently.

### 4.3 Why this is sound to reuse Antigen

Antigen already generates well-typed Core and fuzzes the kernel; here we generate
well-typed Core *for each hole*, assemble it through the grammar into a DSL program,
and fuzz the *macro*. Same generator, same shrinker, same health/coverage manifest
discipline (a macro reports its own expansion-coverage: which rules were exercised,
at what depths). The macro facility thereby inherits the kernel's soundness
methodology one level up: **a user's DSL is proven the way the kernel is proven.**

### 4.4 The one implementation cost, stated

Filling a hole `<n: Category>` needs a generated term of the hole's **specific**
type, i.e. *type-directed* generation ("give me a well-typed term of type `T`"),
which is stronger than Antigen's current "give me some well-typed term." So this
mechanism's real cost is extending the generator with type-directed sampling for the
hole categories a DSL uses (base value/data types first; higher-order/dependent hole
types are a later increment). Everything else — assembly, shrinker, coverage
manifest, the kernel-check gate — is existing Antigen machinery. This is why §4 is
the last slice (§8): it is the highest-value guarantee and the one new engine.

### 4.5 Honest limit

Generation is statistical, like Antigen — it drives the ill-typed-expansion
probability across the accepted-input space to near-zero, not to a formal proof for
an infinite grammar. This is the *same* residual the kernel accepts, and it is a
bounded, reportable defect class, not an unbounded trust.

## 5. Mechanism 3 — required per-rule worked examples (the intent oracle)

Generation proves well-*typedness*; it cannot prove *meaning* (`every 500ms` could
expand to well-typed-but-wrong code). Only an example pins intent.

### 5.1 The obligation

Every `syntax` rule must carry at least one **worked example** — the rule with its
holes filled by concrete values — and its **expected expansion**. A rule without one
is a compile error (`rule_unpinned: <rule>`).

```
macro every
  syntax every <t: Duration> becomes Timer.repeat(t)
    example  every 500ms   expands  Timer.repeat(Duration.ms(500))
```

The facility parses the example through the rule, expands it, and checks the result
(a) **equals** `expands` (up to hygiene/α-renaming) and (b) **type-checks**. Two
things fall out for free:

- **The rule is the documentation, the test, and the intent pin at once.** Because a
  rule already looks exactly like what the user types (base spec §2), the example is
  nearly free to write — fill the holes.
- `cure <macro> report` renders rules-with-examples as living, checked documentation
  that cannot drift from behaviour.

### 5.2 An author may pin *type-only* when exact Core is not the contract

For rules whose exact expansion is an implementation detail, `expands : <Type>`
pins only the output type, checking (a′) the expansion *has* that type instead of
equalling specific Core. This keeps the obligation honest (a pin exists) without
over-committing the expansion shape.

## 6. Capability is unchanged — including brackets-vs-indentation

None of §3–§5 narrows what a macro can express; they constrain only that it be
*described and proven*. The base tiers stand: Tier 1 lexer literals, Tier 2 hygienic
`becomes` templates, Tier 3 total `computed by f` elabs with the read-only reflection
API (`infer`, `expand`). Custom surface syntax — a DSL delimited by `{ }` with its
own layout — is already expressible via a Tier-3 rule taking `raw until <delim>`
(verbatim text with source locations) and parsing it with the author's own grammar.

**Refinement (first-class layout, optional to build):** rather than hand-roll the
region boundary each time, a `macro` may declare its region syntax once —

```
macro flow
  region delimited by { }     # this DSL is brace-delimited, layout-insensitive
  ...
```

`region delimited by { }` (vs the default `region by layout`) tells the *top-level*
Cure parser how to find the DSL's extent and hand the enclosed span to the macro,
so "this DSL uses brackets, not indentation" is a one-line declaration, not
per-rule `raw until` plumbing. The enclosed grammar (§3) and its obligations
(§3–§5) are identical either way. This is a convenience over `raw until`, not a new
capability; it can ship after the safety core.

## 7. What the author writes vs what the facility derives

| Concern | Author writes | Facility derives / enforces |
|---|---|---|
| Grammar | `syntax` rules (examples-with-holes) | the *structural* `Diagnosis` points (§3.1) |
| Semantic failures | `fail C(args)` declarations + `check … else fail C` | folds `C` into `Diagnosis` (§3.4) |
| Failure descriptions | `explain` clauses / category `describe` | exhaustiveness over the *whole* `Diagnosis` (§3.2/§3.4); interception (§3.3) |
| Expansion | `becomes` / `computed by f` | generative valid-parse fuzz + kernel-check gate (§4) |
| Intent | one `example … expands …` per rule | parse+expand+check the examples (§5) |
| Layout | `region delimited by …` (or default) | hand the span to the macro (§6) |

An author cannot ship a macro that (a) leaves a failure point undescribed, (b) can
generate a valid parse expanding to ill-typed Core, or (c) leaves a rule's meaning
unpinned. Those are the three new compile errors.

## 8. Integration and staging

- **Depends on:** the base macro facility (tiers, grammar, `explain`, reflection
  API) and Antigen (`lib/antigen/*` generator + shrinker + coverage manifest). No
  kernel (TCB) change — all of this is compile-time host Cure/Elixir over existing
  machinery; macro output is still re-elaborated and kernel-checked unchanged.
- **Slice order:** (1) derive `Diagnosis` from a grammar + exhaustive-`explain`
  check + interception; (2) required per-rule examples (parse+expand+check); (3)
  generative expansion fuzz reusing the Antigen generator + a per-macro coverage
  manifest; (4) optional `region delimited by …` first-class layout. Each is
  independently landable and gated; (1)+(2) already close most of the soft spot,
  (3) is the proof.
- **Testing discipline for the implementation:** each slice is strict red-green with
  a named failing test first — e.g. slice 1's red test is "a macro with an
  undescribed hole compiles" (must flip to a `missing_diagnosis` error); slice 3's
  is "a macro whose `becomes` drops a hole's type is accepted" (must flip to a
  generated counterexample at macro-compile). Tests assert behaviour (a macro
  compiles / fails to compile with a specific diagnosis), never internal structure,
  and are immutable once green.

## 9. Non-goals and honest residuals

- **Not** a formal proof of expansion well-typedness — §4 is statistical (Antigen's
  own ceiling). Stated, not hidden.
- **Not** author-described *type* errors of generated Core (out of scope by
  decision) — covered by §4/§5 + the base never-raw fallback.
- **Not** a semantic-correctness proof — §5 pins the examples the author wrote; an
  untested-shape, well-typed, wrong-meaning expansion is the irreducible remainder,
  now bounded to "the author's examples were incomplete."
- **Not** a change to the tier tower's *capability* — §3–§5 add obligations, not
  limits; §6 confirms full custom syntax including layout.

## 10. The symmetry, stated plainly

The kernel is trusted because Antigen generates well-typed terms and proves the
checker never accepts garbage. Under this design a **DSL** is trusted because the
facility generates the DSL's own valid programs and proves its **expansion** never
produces garbage — and forces the author to describe every violation and pin every
meaning. Same generator, same philosophy, one level up. That is what makes "model
basically anything, with full type safety" a property the compiler establishes
rather than a promise the author makes.

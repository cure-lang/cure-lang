# The `macro` Facility — Cure's One Frontend Feature

**Date:** 2026-07-08
**Status:** design (operator-decided architecture). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
§5, consolidating it and its §9 items 1–8 into the facility's own home. Every
other 2026-07-08 macro spec (`board`, `driver`, `packet`/`codec`, tasks,
units, `config`/`secret`, `check`, web trio, `schema`, `parse`, `cli`/`job`,
`workflow`/`bot`, `sim`/`pattern`, `reducer`, `protocol`, `fleet`) is a
*library* built on this.

**The decision (operator, 2026-07-08):** the compiler grows exactly ONE new
frontend feature — this facility. No per-DSL special treatment, ever. This is
also what de-specializes Cure: not an MCU language, but a BEAM language where
libraries are languages.

Reference models: Lean 4's `syntax`/`macro_rules`/`elab_rules` tower
(hygienic, in-language, layered by power); Idris elaborator reflection as the
top-tier shape; Racket for the ecosystem thesis — when extending the language
is library work, the ecosystem writes the languages.

**Power target (operator, 2026-07-08): beginner-friendly at the floor,
Racket-complete at the ceiling** — the facility must be able to do, more or
less, anything Racket's languages-as-libraries machinery can do. §13 is the
capability-by-capability audit against the Racket docs and the additions it
forced; §2 is the meta-grammar that keeps the floor at copy-one-example.

---

## 1. The container

A `macro` is a container in the `fsm`/`actor`/`sup` family with three kinds
of members — grammar rules closed by a tier verb (`syntax … becomes …` /
`syntax … computed by f`), literal rules, and diagnostics (`explain`):

```cure
macro Every
  ## every <period>: run the block that often, supervised.

  syntax
    every <period: Duration>
      <body: Block>
  becomes
    fsm <fresh Tick> with Unit
      Idle --tick--> Idle
      @timer <period>
      on_timer
        (:idle, s) -> { <body>; %[:ok, s] }

  explain
    {:no_instance, Duration, t} ->
      "every needs a duration — write every 500ms or every 2s (got " <> show(t) <> ")"
```

A macro is an ordinary module member; it exports its keywords the way a
module exports functions.

## 2. Grammar — rules are examples with holes

(Notation adopted 2026-07-08, the meta-grammar pass of the Racket audit —
resolution of ledger §11.2's notation half. The sibling macro specs predate
it and use the earlier `category`/`$name:Kind`/`expand ~>` sketch; the
mapping table below reads them 1:1 — update each opportunistically when it
is implemented.)

Design constraint: a driver author defines a macro by copying one example,
without ever learning what a grammar formalism is. The move that buys this:
**a syntax rule looks exactly like what the user will type**, with
placeholders punched into it, read the way every developer already reads CLI
usage strings (`git checkout <branch>`). The full metasymbol inventory is
three items, all pre-known:

| Symbol | Meaning | Already known from |
|---|---|---|
| `<name: Kind>` | a hole | CLI docs: `<branch>`, `<file>` |
| `...` | more of the same | how humans write examples: `f(x, ...)` |
| `( … )?` | optional group | regex-lite |

No `::=`, no alternation bars, no combinators — `category`, `Many(K)`, and
`Indented(K)` from the earlier sketch are retired.

- **Rules.** `syntax <example-with-holes>`, optionally suffixed `is Category`,
  closed by a tier verb: `becomes` (hygienic template) or `computed by f`
  (elab function — "elab" remains the name for the computation tier
  throughout these specs; `computed by` is its surface spelling). A rule
  declares either a top-level form (`every`, `reducer`) or a category
  member. The same `<name>` bracket is the hole in the rule *and* the splice
  in the template — one notation, symmetric.
- **Alternation = clauses.** Alternatives are separate `syntax` lines, like
  function clauses:

  ```cure
  syntax emit <| <model: Code> <| <emission: Code>   is Action
  syntax update <| <model: Code>                     is Action
  syntax reject <err: Code>                          is Action
  ```

- **Categories are created by use.** `is Action` names the rule's category
  and creates it — no forward declaration. Guardrail: a hole kind that no
  rule declares is a compile error with near-miss suggestions (`is Actoin`
  cannot silently mint an empty category).
- **Repetition.** Line-oriented: `<edges: Edge>...` — "this line, repeated."
  Inline: the separator is written before the dots, as in documentation:
  `f(<args: Code>, ...)`. Deliberate simplification: `...` always means
  *zero or more*; "at least one" is not a grammar distinction but a
  `check … else fail` in the elab with a proper explainer — a parse error
  saying `expected Edge` is strictly worse UX than "reducer Door declares no
  transitions — add a `Closed --Msg--> State` line."
- **Bare-name rules** are legal (`syntax now becomes Clock.now()`) — the
  identifier-macro tier, no special casing.
- **Literal rules** (Tier 1) extend the lexer in the one narrow way units
  need: `literal <n: Number> ms becomes Duration.ms(<n>)` — a numeric token
  juxtaposed with a registered suffix. Together with raw holes (§13.2), the
  only lexer extension that exists.

**Hole kinds** (plain-English; closed for built-ins, open via `is` categories
and `literal` rules):

| Kind | Matches | Was (earlier sketch) |
|---|---|---|
| `Name` / `name` | capitalized / lowercase identifier — the kind is written the way the match must be written (self-teaching; call it out in docs, it is subtle) | `UpperIdent` / `Ident` |
| `Number`, `Text`, `Atom` | literals | — |
| `Code` | any expression | `Expr` |
| `Block` | indented code block | `Block` |
| `Type` | type expression | `TypeExpr` |
| `Pattern` | match pattern | `Pattern` |
| `Record` / `RecordBlock` | record literal / indented `field: Type` lines | `RecordLit` / `RecordTypeBlock` |
| `Params` | parenthesized parameter tuple | `ParamTuple` |
| `Duration`, `Percent`, … | whatever `literal` rules target | typed-literal kinds |
| `Edge`, `Clause`, … | whatever `is` creates | `category` declarations |
| `raw until <delim>` | verbatim text with srcloc (§13.2) | — (was a non-goal) |

**Refinement-typed holes**: `<port: Number where 1 <= port and port <= 65535>`
— Racket's parameterized syntax classes, expressed in machinery Cure already
has; the refinement failure feeds the default error.

**Default error machinery** (adopted from syntax-parse, which sets Racket's
error-quality ceiling; this sets the floor *before* any `explain` is
written):

- Every typed hole yields an automatic error: kind name + offending term +
  span (`every needs a Duration here, got "fast"`).
- Categories carry an optional `describe "transition edge"`; defaults name
  the category.
- When several rules could apply, the reported failure comes from the rule
  that parsed **furthest** (progress-ordered selection), with a parsing
  context trace: `while parsing transition edge … in reducer Door`.

**The rule is the documentation.** Strip the hole types and every `syntax`
rule *is* its usage line. Grammar rules are **declarative data**; three
structural dividends, stated as requirements: the LSP consumes the rule set
(per-macro highlighting/completion with zero per-macro work),
`cure <macro> report`-style tools render any macro's grammar as
documentation, and docs/completion snippets cannot drift from the grammar.

**Honest costs.** (a) `<` also appears in comparisons and `<|`: the lexing
rule is that `<` opens a hole iff immediately followed by an identifier (or
`fresh`/`capture`) closing with `: Kind>` or `>` on the same line —
`--<msg: Name>-->` lexes; `<|` is safe (next char `|`); escape hatch `\<`.
If implementation finds pathological cases, the severable fallback is the
`$name:Kind` sigil (Lean/Rust family) — everything else in this section
survives that swap. (b) Implicit categories trade a declaration for a typo
risk; the unknown-kind error above is the mitigation. (c) `becomes` merges
grammar and expansion, so context-dependent expansion has nowhere to live in
Tier 2 — deliberately: that *is* Tier 3, and forcing the escalation keeps
Tier 2 honestly simple.

## 3. The quoted-AST model

Every category (created by `is`, §2) **auto-derives a record/ADT type** for
its parse result (`Syntax(Edge)` ≈ `rec` with one field per hole, each
`is`-clause an ADT alternative). Elab functions (the targets of
`computed by`) are ordinary Cure functions over these types. `quote` builds
syntax values; `$( )` splices them *inside elab code* (the `<name>` form is
the rule/template notation of §2; inside `computed by` bodies, quoting keeps
`$()`); both are *typed against the category being built* — a `quote`
producing a malformed production is a compile error in the macro itself,
not in its user's program.

This is the parent's assumption in the `reducer` worked example
(`schemas.map(fn(s) -> s.state)` — quoted decls as plain records) — adopted
here as the design: **derived typed ASTs, not a universal `Syntax` blob.**
(A generic traversal API over any syntax value exists underneath for tooling;
macro authors normally never need it.)

## 4. Power tiers

One new keyword per rung, ordered as a learning ladder — nobody meets quoted
syntax before Tier 3. (Renumbered 2026-07-08 with the meta-grammar pass;
sibling specs citing the old numbering map 1→3, 2→2, 3→1, 4→4.)

| Tier | Mechanism | Who uses it |
|---|---|---|
| 1 | `literal` rules (`literal <n: Number> ms becomes Duration.ms(<n>)`) | units |
| 2 | `syntax … becomes …` (hygienic templates) | `every`/`on`, `secret` |
| 3 | `syntax … computed by f` (total compile-time Cure over quoted decls, `check … else fail`) | `boarddef`, `driver`, `packet`, `config`, `schema`, `parse` |
| 4 | Tier 3 + reflection API (§8) | `flow`, `reducer`, `view` |
| 5 | module rules + raw holes (§13.1–.2) | `board` module shaping (module-level `let`, auto `start/0`), `parse`-embedded surfaces |

A macro declares nothing about its tier — it simply uses what it needs;
the tiers are a design/teaching taxonomy and a build-order (§10; Tier 5
lands with its consumers, not before).

## 5. Hygiene, expansion, termination

- `becomes` templates are **hygienic**: names introduced by the template
  cannot capture or be captured by user identifiers; `<fresh Name>` mints a
  readable unique name, identical at every mention within one rule (for
  generated containers that need stable-ish module atoms, e.g.
  `fsm <fresh Tick>` → `Cure.FSM.Tick$3`). Deliberate capture (anaphora —
  Racket's syntax-parameter use case) is a marked, greppable escape,
  `<capture it>`: ledgered §11.12 and classified under the holes/`unsafe`
  taxonomy, never silent.
- Templates may be **recursive** (a `becomes` expanding into its own or
  another macro's syntax) provided a decreasing-input check passes — even
  recursive sugar provably terminates; the fuel bound below stays a
  backstop, not the guarantee.
- `elab` functions are **total Cure**, checked by the same size-change
  termination certificate as user code. Combined with a bounded expansion
  depth (a macro's output containing macro forms re-enters expansion;
  the fuel bound is a backstop, the totality check is the real guarantee),
  **Cure compilation provably terminates even with user-defined syntax** —
  a property Lean does not have, and worth a docs headline.
- `elab` runs **staged on the host** at compile time: full stdlib available,
  no AtomVM constraints, but **no ambient effects** — elab functions are pure
  (they may read only what the facility hands them: the quoted input and the
  reflection API). Determinism of builds is non-negotiable.

## 6. Staging & name resolution

User code may reference macro-*derived* names before the macro block
elaborates (the operator's Door example: `type DoorReject =
InvalidTransition(source: Door.State, msg: Door.Msg)` textually precedes the
`reducer` that derives `Door.State`/`Door.Msg`). Resolution is therefore
**two-pass within a module**:

1. **Signature pass** — every macro instance runs a cheap `declares` phase
   (derived from its `elab`'s emitted declaration heads; for Tier-1/2 this is
   syntactic) publishing the names it will define.
2. **Elaboration pass** — bodies elaborate against the full name environment.

Cycles between two macro instances' *derived types* are an error with an
explainer (name the two instances and the cycle). This is ledgered detail
work (§11.3) but the two-pass shape is decided.

## 7. Scoping & composition

- Macro syntax is **scoped by import**: `use Hardware.Every` brings the
  `every` keyword into the module. No global grammar.
- Two imported macros exporting the **same top-level keyword** is an error
  at the `use` site (explainer offers qualified activation:
  `use Hardware.Every only [every]` / renaming ledgered §11.4).
- Category names are namespaced by macro; cross-macro category reuse is
  explicit (`<f: Packet.FieldDecl>`) — this is how `protocol` embeds `packet`
  payload declarations without owning them.
- **Open categories** (Racket's match-expander pattern, §13.3): a macro may
  mark a category `open`; any other macro then *extends* it with an
  ordinary rule — `syntax within <d: Duration> is Reducer.ClauseModifier`.
  Embedding (above) uses a category; extension grows one. Governance is
  ledgered §11.11.

**Composition is a full mechanism of its own** — theorem signatures
(`provides`/`requires` facts on the check-ladder trust rule), parameterized
categories (outer-macro values as inner-macro indices), seam explainers,
and composition templates — specified in
[`2026-07-08-macro-composition-design.md`](2026-07-08-macro-composition-design.md)
(operator-directed: stacked DSLs keep dependent types invisible while the
proofs still compose).

## 8. The Tier-4 reflection API — smallest thing that passes the dogfood

The one genuinely hard design. `reducer`'s `clause_to_arm` must build GADT
match arms and record literals *against types the same elab derived*; `flow`
must infer indices. The API is deliberately minimal, read-only toward the
elaborator, and **advisory** — nothing it returns is trusted (§9):

- `resolve(name) -> Sig | NotFound` — a global's/type's elaborated signature.
- `constructors(type_name) -> [CtorSig]` — for building matches.
- `infer(quoted_expr, env) -> Type | Error` — ask the elaborator to type a
  quoted term in a given quoted context (the expensive one; needed by `flow`).
- `expand(quoted, env) -> quoted | Error` — expand nested macro syntax and
  inspect the result (Racket's `local-expand`; how whole-language macros
  are layered — added by the §13 audit through this section's amendment
  rule).
- `lift(quoted_decl)` — emit a declaration at module top from a nested
  expansion (register-once tables, hoisted compiled grammars; §13.5).
  Template form: `<at module top>`. The one write-shaped member: it appends
  declarations, never mutates existing ones, so the read-only-toward-the-
  elaborator discipline survives.
- `fresh_name`, `fresh_meta`-free — no metavariable access; macros never
  see or create holes (the K3 firewall applies to elab output).

Binding introspection (Racket's `free-identifier=?`-class questions —
keywords matched by *binding*, not spelling, immune to renaming/shadowing)
is `resolve`'s job and needs no separate member.

Explicitly absent: solving, unification hooks, environment mutation,
reduction control. If the dogfood (§10) proves something more is needed, it
is added by amending THIS spec, never ad hoc.

## 9. Soundness — why this is safe to hand to strangers

Macro output is **re-elaborated and kernel-checked exactly like
hand-written code**. The facility sits entirely in the untrusted frontend,
upstream of the elaborator; the Final-Core validator and kernel are
unchanged and unaware of it. Therefore:

- A buggy macro yields a confusing error or a rejected program — **never an
  unsound one**. UX bugs are possible; soundness bugs are not. **TCB delta:
  zero.** (Same layering argument as the elaborator itself.)
- The `explain`/provenance machinery (see the error-explainer spec,
  `2026-07-08-error-explainer-design.md`) exists precisely to turn that
  "confusing error" caveat into a bounded, reportable defect class.
- Elab purity (§5) means a malicious macro cannot exfiltrate or vary builds
  — the worst it can do is generate rejected or weird-but-checked code.

## 10. Dogfood gates & bootstrap order

**Gate 1 (facility "done"):** `fsm` could be re-expressed as a macro
(whether or not it migrates — parent §9.7). This was originally the weak
reading — `fsm`'s grammar expands into the *existing built-in* `fsm`
container, backend untouched. The operator's stated ambition (2026-07-08,
see §14) is stronger: fsm/actor/sup/app fully owned by macros, no bespoke
Elixir compiler backing any of them. **Gate 1b (capability proof, revised
per §14.7's lexer-keyword finding):** `sup`, defined as a macro under a
fresh name (no lexer change needed — `sup` is already soft-keyworded per
`lexer.ex:42`; a fresh name defers the keyword question entirely), exercises
both of §14's new primitives (`behaviour`/`callback` closed vocabulary +
`lift module`) and has the simplest correctness bar of the four OTP
containers (no user-authored callback bodies). **Gate 1c (full
replacement):** the *same* container retakes its literal keyword and its
bespoke Elixir compiler is deleted — gated on demoting it out of the lexer's
hard-keyword list first if the container is `fsm`/`actor`/`proto`/`impl`;
`sup`/`app` can go straight to Gate 1c without that step.
**Gate 2 (Tier 4 "done"):** the `reducer` spec's macro definition compiles
as a library and elaborates the operator's Door program.

Bootstrap order (parent §9.1, resolution proposed here): **facility first,
Tiers 1–3 only**, shipping `board`/`driver`/`packet`/units/tasks as libraries
immediately (none need Tier 4); Tier 4 lands second, unlocking
`reducer`/`flow`/`view` as libraries. This avoids the second permanent
implementation path entirely at the cost of gating the flagship reducers on
Tier 4 — acceptable because `fsm`/`flow` exist built-in today and keep
working throughout.

## 11. Open decisions (consolidated ledger — parent §9 items 1–8 live here now)

1. ~~Bootstrap order~~ — resolution proposed in §10; confirm at
   implementation.
2. **Meta-grammar finalization** — notation adopted in §2 (2026-07-08
   Racket-audit pass: examples-with-holes, `is` categories, `...`/`?`,
   `becomes`/`computed by`). Remaining: layout-repetition interaction with
   the indentation-sensitive lexer, ambiguity policy (recommend: LL-style
   committed choice per leading token; a macro whose rules are ambiguous
   against *imported* macros is an error at import, computed from FIRST
   sets), and `<`-hole lexing edge cases (severable fallback: the
   `$name:Kind` sigil — §2's cost note).
3. **Two-pass details** (§6) — what exactly Tier-4 `declares` may compute
   (must not need the reflection API, or staging cycles return).
4. **Keyword conflict ergonomics** (§7) — `only`/rename surface.
5. **Reflection API completeness** (§8) — frozen until Gate 2 forces
   amendments (the §13 Racket audit already added `expand`/`lift` through
   the sanctioned route).
6. **Quoted-AST versioning** — a macro compiled against category shapes
   that later change (compiler upgrades): derive-and-recompile is the answer
   for source packages; binary macro distribution is a non-goal (§12).
7. ~~Migration of built-ins~~ — resolved 2026-07-08 toward full ownership
   (Gate 1b, §14): fsm/actor/sup/app's bespoke Elixir compilers are audited
   in §14.1, the two missing primitives (closed `behaviour`/`callback`
   vocabulary + `lift module`) are specified in §14.3–§14.4, and the
   migration order is `proto`/`impl` first (§14.7, needs neither primitive),
   fsm/actor/sup/app second. Still open: whether *all five* built-ins
   actually get deleted post-migration or some stay as a fallback — track
   under ledger item 14.
8. **`explain` registration mechanics** — deferred wholesale to the
   error-explainer spec.
9. **Module-rule mechanics** (§13.1) — trigger (board decl? explicit tag?),
   at-most-one module rule per module vs. composition when two imported
   macros both declare one, and interaction with a hand-written `start/0`.
   Absorbs parent §9.14/§9.15 (module-level `let`, auto-`start/0`) — both
   are the `board` macro's module rule, not compiler features.
10. **Raw holes** (§13.2) — delimiter inventory (`until dedent` /
    `until )` / `line`), srcloc threading tokenizer→parser→quoted AST, and
    the embedded-grammar coloring interface (a `parse` grammar exporting its
    own LSP token classes).
11. **Open-category governance** (§13.3, §7) — opt-in marker, extension
    ordering/ambiguity across extenders, whether extensions may shadow.
12. **`<capture>` escape** (§5) — exact semantics and its classification in
    the holes/`unsafe` taxonomy.
13. **Callback-table governance** (§14.3) — whether `OTPBehaviour` is a
    permanently closed built-in enum or ever gains a `library`-registered
    extension point (e.g. a project defining its own OTP-shaped behaviour);
    recommend: closed for now, revisit only if a real non-OTP use case shows
    up (mirrors §13.3's opt-in-only stance on open categories).
14. **Module-minting mechanics** (§14.4) — can one container `lift` more than
    one module; what happens when two `Named` mints in the same compile unit
    collide (recommend: same error shape as §7's keyword-conflict collision);
    and whether the five audited built-ins (§14.1) get deleted outright post
    migration or kept as a documented fallback path.
15. ~~Shared-load-path migration~~ — retracted 2026-07-08 (operator
    correction): NOT independent value. The eager `Code.compile_string` +
    `:code.purge` + `:code.load_binary` in the bespoke Elixir compilers is
    only a hazard for a *retrying/backtracking* caller (§2's future
    progress-ordered rule selection); the current hand-written parser calls
    `dispatch_container` exactly once per container, deterministically, so
    there is no present exposure. The purge-before-load is also plausibly
    load-bearing today, independent of any of this — it is very likely what
    makes recompiling the same actor/sup/app module safe within one running
    VM (REPL iteration, repeated test-suite loads) — so "fixing" it isn't
    even obviously a pure improvement, it's a real design question. Since
    Gate 1c deletes these compilers wholesale, none of this is worth solving
    in code that has a scheduled deletion date. §14.5's actual requirement —
    purity of the *new* `lift module` primitive — is already satisfied by
    its spec (return a `QuotedModule` value; the orchestrator loads once) and
    needs no upstream work in the old compilers to be true.
16. **Verification-logic migration** (§14, not yet designed) — `Cure.FSM.
    Verifier` (reachability/deadlock-freedom/hard-event checks), `Cure.Sup.
    Verifier` (supervision-tree structure), `Cure.App.Verifier`
    (start-phase matching) are real Elixir static-analysis passes with no
    plan yet for becoming elab-time total-Cure computation. In principle
    in-scope for `computed by` (these are decidable graph/structural
    analyses, no different in kind from any other compile-time check elab
    already does), but this is a genuine port of real logic (900+ lines
    across the three verifiers), not a consequence of §14.3/§14.4. Blocks
    *full* ownership of `sup`/`app`/`fsm` (not `proto`/`impl`, which has no
    analogous verifier) even after the two new primitives land.
17. **`lift module` two-pass interaction** (§6, §14.4) — whether a minted
    module's `ModuleName` is published during the cheap `declares`
    signature pass (needed so e.g. a macro-defined `sup` can resolve a
    sibling macro-defined `actor`'s produced module by name, mirroring
    today's pure name-derivation trick) or only after full elaboration.
    Needs an answer before `lift module`'s elaboration logic can be written,
    not just before it's used.

## 12. Non-goals

- No arbitrary compile-time effects in `elab` (no IO, no network, no
  filesystem) — purity is load-bearing (§5, §9).
- No binary/opaque macro distribution — macros ship as source packages.
- No reader-level lexer extensibility beyond `literal` suffix rules and
  **delimited raw holes** (§13.2 — carve-out forced by the operator's
  Racket-complete direction) — Cure's token grammar is otherwise fixed; a
  raw hole opts a delimited block's *content* out, never the file, and
  indentation structure stays sacred.
- No unbounded (Turing-complete) expansion — totality is the trade (§5,
  §13.6); a genuinely non-total metaprogram is holes/`unsafe`-taxonomy
  territory, a marked exception, never the default.
- No proof-producing macros / tactic framework — macros generate programs,
  not proofs; obligations discharge by computation or become domain errors
  (hiding principle 3), and `check`'s certificate elevation is the sanctioned
  proof-automation path.

---

## 13. Racket-parity audit (operator direction, 2026-07-08)

Appended after the §1–§12 consolidation to keep cross-spec references
stable. Method: the facility as specified above, audited
capability-by-capability against the Racket Guide/Reference — the macro
tower including syntax-parse; the `#lang`/languages-as-libraries machinery
(`#%module-begin`, interposition points, readtables/readers, brag); and the
advanced tier (phases, compile-time state, `local-expand`, syntax
parameters, lifting, the macro stepper). Racket's power reduces to five
load-bearing mechanisms; the facility already covered three.

**Already equivalent or better:**

- `syntax-rules` / ellipses / hygiene → Tier 2 (`becomes`, `...`,
  `<fresh>`).
- syntax-parse (syntax classes, `#:description`, side conditions, auto
  errors) → typed holes, `is` categories, refinement-typed holes,
  progress-ordered default errors (§2), `check … else fail`.
- Procedural transformers (arbitrary code at compile time) → `computed by`,
  bounded to total (§13.6).
- Syntax parameters ("`break` legal only inside `loop`"; anaphora) → mostly
  free: block-scoped grammar makes "keyword legal only inside form X" a
  parse-level fact (`emit … is Action` exists only inside `reducer`) —
  Racket needs syntax parameters because its grammar is flat. True anaphora:
  the marked `<capture>` escape (§5, ledger §11.12).
- Phases (`for-syntax`, `for-meta n`, `for-template`) → sidestepped: elab
  code is ordinary total Cure staged at compile time, and
  macros-defining-macros works because the compile-time language
  includes the facility itself. Racket's per-module fresh compile-time
  instantiation — its mechanism for deterministic separate compilation — is
  subsumed by elab purity + totality (§5, §9).
- Compile-time data bus (`define-syntax`-to-a-value + `syntax-local-value`;
  struct-info records consumed by `match`/`struct-copy`/Typed Racket) →
  **the type system is the bus**: macros emit types and globals; later
  code and other macros read them through elaboration and §8 — checked,
  and nothing to teach. No mutable compile-time tables (none wanted: Racket
  itself bans them cross-module for exactly our determinism reasons).
- Syntax properties / `'origin` / `'disappeared-use` / srcloc → provenance
  is mandatory here (error-explainer spec), not per-macro diligence; and
  tooling derives from the declarative grammar, where Racket's `get-info`
  keys (color lexer, indentation, submit predicate, …) are each
  hand-written — a documented pain point of the `#lang` ecosystem (the
  color lexer is a second lexer kept in sync by hand).

**The five gaps, resolved below:** module macros (§13.1), raw holes
(§13.2), open categories (§13.3), two reflection members (§13.4), lifting
(§13.5).

### 13.1 Module macros (`#%module-begin` equivalence)

Racket's deepest hook: a language sees and transforms the **entire module
body** at once. It is where languages stop being sugar — auto-provides, run
loops, whole-program checks, and *subtracting* capabilities (a language
that simply doesn't admit `set!` or general recursion). The catalog already
needs it without naming it: `board :esp32c3` + module-level `let` +
auto-generated `start/0` *is* a whole-module transformation. A macro may
declare one module-level rule:

```cure
macro Board
  syntax module
    board <b: BoardName>
    <decls: Decl>...
  computed by board_module_elab   # sees ALL declarations; emits start/0 +
                                  # runtime boot + pin namespace; may reject
                                  # decls that don't belong on a board module
```

The user's file does not change by a character — `board :esp32c3` is the
trigger. Subtraction (a module admitting only a restricted surface —
Racket's whitelist-by-omission) falls out at the grammar level: the module
rule decides what the body admits. Absorbs parent §9.14/§9.15. Mechanics
ledgered §11.9.

### 13.2 Raw holes — the reader tier, bootstrapped through `parse`

Typed holes ride Cure's lexer; Racket custom readers parse anything
(`#lang datalog`, Scribble prose). Racket's canonical non-S-exp pipeline is
telling: lexer → brag grammar → parse tree whose node heads *are macro
names* — and brag is itself a `#lang`. Cure pulls the same bootstrap with
the `parse` macro (total typed PEG parsers): one hole kind captures
verbatim text with source positions and hands it to a compile-time total
parser:

```cure
syntax datalog
    <rules: raw until dedent>
  computed by fn(rules) -> DatalogGrammar.parse(rules) |> compile_rules
```

Because the embedded grammar is declarative, syntax coloring derives for it
exactly as for macro rules. Totality means a user's grammar cannot
catastrophically backtrack or hang the compiler — brag guarantees neither.
Deliberate scoping: raw holes are delimited blocks, never whole-file or
mid-expression reader replacement — composable, and the file stays
parseable by tools that don't know the macro. (Amends non-goal §12;
delimiters/coloring ledgered §11.10.)

### 13.3 Open categories (match-expander equivalence)

Racket's deepest ecosystem pattern: `racket/match`'s pattern grammar is an
open namespace third parties extend (`define-match-expander`) — a DSL whose
grammar other DSLs grow, keyed by ordinary module bindings (imported,
renamed, hygienic). The composition spec covers *embedding* a category;
this covers *extending* one: `open` categories, extended with the syntax
that already exists (§7). One line, no new concept. Governance ledgered
§11.11.

### 13.4 Reflection API — two members added (through §8's amendment rule)

The audit pins what Tier 4 must offer: everything Racket's ecosystem builds
reduces to §8's queries plus two members, now added there —

- `expand` — Racket's `local-expand`: expand nested macro syntax and
  inspect the result; how whole-language macros (Typed-Racket-shaped) are
  layered as libraries.
- `lift` — §13.5.

Binding introspection needs no new member (`resolve`, per §8).

### 13.5 Lifting

A deeply nested expansion sometimes must emit module-level code —
register-once tables, hoisting a compiled grammar out of a function.
Racket: `syntax-local-lift-expression` and friends, among its most-used
advanced APIs. Here: `lift` in elab code (§8) and one readable template
marker:

```cure
becomes
  <at module top>
    let <fresh table> = Timer.registry()
  Timer.register(<fresh table>, <period>)
```

### 13.6 Where the facility exceeds Racket

The two things Racket's documentation concedes it cannot do are native
here:

- **Termination.** Racket expansion is Turing-complete with no totality
  claim — a self-expanding macro diverges. Elab functions are size-change
  total; recursive `becomes` templates pass a decreasing-input check (§5).
  User-defined syntax can never hang the compiler.
- **Type-directed expansion.** A Racket macro cannot ask what type a
  subexpression has; Typed Racket exists only via the whole-module
  `local-expand` trick, and a research literature (Turnstile, "Type Systems
  as Macros") exists precisely because the base system lacks it. Elab runs
  inside elaboration; `infer` is a query (§8).

Plus: deterministic builds from elab purity (Racket approximates this with
per-module compile-time re-instantiation), derived tooling (vs hand-written
`get-info` keys), mandatory provenance (vs per-macro `'origin` diligence),
and typed-hole default errors (vs opt-in syntax-parse discipline — Racket's
own docs are scathing about the floor without it: macros that "blithely
accept illegal syntax and pass it along to lambda, with strange
consequences").

### 13.7 Deliberately unmatched

- **Unbounded Turing-complete expansion** — traded for totality (§12).
- **`set!`-transformers / identifier assignment virtualization** — no
  mutation to virtualize.
- **Mid-expression reader replacement** (`#reader` splicing arbitrary
  syntax anywhere) — alien syntax is scoped to delimited raw holes
  (§13.2); a composability win, not a loss.
- **Macro-stepper parity is tooling, not facility** — declarative rules
  make an expansion stepper with macro-hiding (show only *your*
  macro's rewrites) nearly free; belongs to the toolchain spec.

None of these subtracts from any catalog entry or Racket showcase worth
replicating: Typed Racket ≈ module macro + `expand` + `infer`; Scribble ≈
raw holes; datalog/brag ≈ `parse` + raw holes; match expanders ≈ open
categories.

---

## 14. BEAM/OTP container access — full container ownership

**Date:** 2026-07-08. **Status:** design (operator direction: the facility
should be powerful enough to define *every* other structure with it,
including `fsm`/`actor`/`sup`/`app` — not just their surface grammar
expanding into the existing built-ins, the Gate 1 reading, but full
ownership with the bespoke Elixir compilers retired). This section audits
what those bespoke compilers actually do today and specifies the two
primitives the facility is missing to subsume them.

### 14.1 Audit — what the current bespoke compilers do

| Container | Codegen strategy | Behaviour | OTP-mandated callbacks | User-authored bodies | Convenience exports |
|---|---|---|---|---|---|
| `fsm` (simple, no `on_transition`) | Raw Erlang abstract forms, returned as plain data (`fsm/compiler.ex:69-90`) | `gen_statem` | `callback_mode/0`, `init/1`, `handle_event/4` — all compiler-synthesized from the transition table | none | `start_link/0,1`, `send_event/2`, `get_state/1`, `transitions/0`, `allowed/2` |
| `fsm` (callback mode, `on_transition` present) | Elixir source string + `Code.compile_string` (`fsm/compiler.ex:314-458`) | `gen_server` (`use GenServer`) | `init/1`, `terminate/2`, `handle_call/3` (×2), `handle_cast/2`, `handle_continue/2`, `handle_info/2` (only if a timer exists) | `on_transition`, `on_enter`, `on_exit`, `on_failure`, `on_timer`, `on_start`, `on_stop` | `start_link/0,1`, `send_event/2,3`, `get_state/1`, `get_fsm_state/1`, `initial_state/0`, `allowed?/2`, `responds?/2` |
| `actor` | Elixir source string + `Code.compile_string` | `gen_server` | `init/1` (from `on_start`), `terminate/2` (from `on_stop`), `handle_info/2` (from `on_message`) | `on_start`, `on_stop`, `on_message` | — |
| `sup` | Elixir source string + `Code.compile_string` (`sup/compiler.ex:100-107`) | `supervisor` | `init/1` (child specs + strategy/intensity/period) | none — declarative header only | `start_link/1` |
| `app` | Elixir source string + `Code.compile_string` (`app/compiler.ex:186-291`) | `application` | `start/2`, `stop/1`, `start_phase/3` (optional) | `on_start`, `on_stop`, `on_phase` | — |

Two structural findings drive §14.3–§14.5:

1. **fsm-simple-mode already proves the pattern this section needs.** It
   returns `{:ok, forms}` — plain data, no side effect — and those forms flow
   through `Cure.Compiler.Codegen.normalize_compile_result/1` →
   `Cure.Compiler.compile_string/2`'s `case forms do forms when is_list(forms)
   -> write_beam_forms(...)` (`compiler.ex:113-127`) → `BeamWriter.compile_forms/1`
   (pure) → `BeamWriter.write_beam/4`, which is the **one and only** place in
   this call chain that touches `:code.load_binary` (`beam_writer.ex:84`).
   This is the *identical* shared path ordinary (non-container) modules use —
   no fsm-specific code past `dispatch_container`.
2. **The other four instead eagerly `Code.compile_string` + `:code.purge` +
   `:code.load_binary` inline**, inside their own `compile/2`, and hand back
   a marker tuple (`{:actor, mod}` etc.) that `compiler.ex`'s `case forms do`
   intercepts *before* `write_beam_forms` (comment: "there is nothing left
   for this orchestrator to write"). This is a real effect — it mutates the
   shared BEAM code server and writes to disk — and it is not required by
   OTP or by what these containers produce: `Code.compile_string/2` itself
   does not load anything; these compilers choose to follow it immediately
   with an explicit, separate load step rather than returning bytecode and
   deferring to the shared path fsm-simple already uses. Almost certainly an
   artifact of these four being easier to write as templated Elixir source
   than as hand-assembled `:compile.forms` tuples (which is why fsm-simple,
   the one written the hard way, is also the one that stayed pure) — not an
   essential requirement of what an actor/sup/app container has to do.

### 14.2 Why not just "emit arbitrary attributes / export arbitrary functions"

Rejected (operator-decided, 2026-07-08), in favor of a closed vocabulary
(§14.3). Reasons:

- **TCB delta.** §9's soundness argument is that macro output is always a
  *typed* thing re-elaborated like hand-written code. Raw attribute/export
  emission is the one place a macro could act on a compiled module's shape
  without going through anything typed — a category of risk nothing else in
  this facility has.
- **Documentation/tooling.** §2's "the rule is the documentation" and §6's
  `declares` signature pass both depend on a macro's output being knowable
  ahead of running it. "Attribute(any_atom, any_term)" isn't enumerable that
  way; "declares a `gen_statem`-shaped container with these callbacks" is.
- **Consistency.** Every other mechanism in this spec (holes, categories,
  even `lift`'s existing module-top form) is closed and typed. A raw BEAM
  escape would be the one unconstrained primitive in an otherwise fully
  checked facility.
- **It's cheap to close.** The target vocabulary (OTP behaviours) is small
  and fixed — four behaviours, a handful of callbacks each — so a closed
  ADT costs nothing in expressiveness for this use case.

### 14.3 `behaviour` and `callback` — the closed vocabulary, as Cure ADTs

The kind is a plain closed Cure sum type, not a `is`-created category (it is
not user-extensible — see ledger §11.13):

```cure
type OTPBehaviour = GenStatem | GenServer | Supervisor | Application
```

One callback ADT per behaviour, derived directly from the §14.1 audit — each
constructor is exactly one OTP-mandated callback, argument positions match
the callback's actual arity:

```cure
type GenStatemCallback =
  | CallbackMode                              # arity 0
  | Init(Params)                              # init(Arg)
  | HandleEvent(Params, Params, Params, Params) # (EventType, Event, State, Data)

type GenServerCallback =
  | Init(Params)                              # init(Arg)
  | HandleCall(Params, Params, Params)        # (Msg, From, State)
  | HandleCast(Params, Params)                # (Msg, State)
  | HandleInfo(Params, Params)                # (Msg, State)
  | Terminate(Params, Params)                 # (Reason, State)
  | CodeChange(Params, Params, Params)        # (OldVsn, State, Extra)

type SupervisorCallback =
  | Init(Params)                              # init(Arg) -> child specs + strategy

type ApplicationCallback =
  | Start(Params, Params)                     # (Type, Args)
  | Stop(Params)                              # (State)
  | StartPhase(Params, Params, Params)        # (Phase, StartType, PhaseArgs) -- optional
```

Surface grammar (§2 meta-grammar — examples with holes):

```cure
syntax behaviour <b: OTPBehaviour>                                is ContainerMember
syntax callback <name: Name>(<params: Params>...) -> <body: Block> is ContainerMember
```

The constraint "a `callback` member's name/arity must be one of the
constructors of the `*Callback` ADT matching this container's own `behaviour`
declaration" is cross-hole (it depends on a *sibling* member, not just the
local rule) — the same shape as the "at least one" case already called out
in §2: not a grammar distinction, a `check … else fail` in the `computed by`
elaboration for the container, with an explainer in the same spirit as the
`Every` example in §1 (`"handle_evnt is not a gen_statem callback — did you
mean handle_event?"`, near-miss suggestion per §2's default-error rule).
Unnamed/undeclared callback names are a compile error, not a silently
accepted extra export — this is precisely what closes off the "arbitrary
export" risk from §14.2.

Convenience exports (`start_link`, `send_event`, `get_state`, `transitions`,
`allowed?`, …) need **no new primitive** — they're ordinary exported `fn`
definitions inside the minted module (§14.4). Only the OTP-mandated
callback surface needed closing.

### 14.4 `lift module` — minting a compiled unit

The missing primitive: everything else `lift` does (§8, §13.5) appends a
declaration to the *current* module's top. fsm/actor/sup/app instead compile
and load their own **separate**, independently-named unit
(`Cure.FSM.<Name>`, `Cure.Actor.<Name>`, …). New template form:

```cure
becomes
  lift module <m: ModuleName>
    behaviour <b: OTPBehaviour>
    callback <name: Name>(<params: Params>) -> <body: Block>
    ...
    <decls: Decl>...
```

Naming is a small closed ADT, carrying over both modes already in use by the
existing compilers unchanged:

```cure
type ModuleName =
  | Named(Text)   # deterministic: e.g. actor's own "Cure.Actor." <> declared_name
  | Fresh(Text)    # gensym'd, for anonymous macro-synthesized containers -- the
                    # existing `<fresh Name>` mechanism (§5) instantiated at ModuleName kind
```

`Named`'s atom-derivation is already a pure `name -> atom` function in the
current code (`actor_module_atom/1`, `sup_module_atom/1`, `fsm_module_atom/1`)
— exposing it costs nothing; `sup`'s existing child-resolution-by-naming-
convention (`Counter as counter` → `:"Cure.Actor.Counter"`) keeps working
unchanged because it was already just name arithmetic, never a live-module
lookup.

### 14.5 Purity — `lift module` produces a value, it does not compile-and-load

`lift module`'s result is a value — call it `QuotedModule(name, decls)` —
collected by elaboration like any other declaration, **not** an inline
`Code.compile_string`/`:code.load_binary` call. This keeps elab pure (§5) and
keeps the soundness argument (§9) intact: nothing happens to the running VM
until the orchestrator commits.

This is not new machinery invented for the macro facility — it is
convergence onto the path §14.1 already showed working:
`dispatch_container` → `normalize_compile_result` → `compiler.ex`'s `case
forms do forms when is_list(forms) -> write_beam_forms(...)` →
`BeamWriter.compile_forms/1` → `BeamWriter.write_beam/4` (the one site that
calls `:code.load_binary`). Every `QuotedModule` a compilation unit's
`lift module` sites produce gets folded into the same batch the orchestrator
already writes for the enclosing module and for simple-mode `fsm` — compiled
and loaded exactly once, in exactly one place, regardless of how many
containers a macro mints.

**Not a prerequisite** (ledger §11.15, retracted after operator correction
2026-07-08): the bespoke fsm callback-mode/`actor`/`sup`/`app` compilers do
*not* need migrating onto this shared path first. The retry/determinism
hazard this would fix only exists for a caller that retries or backtracks
(§2's future progress-ordered rule selection) — the current hand-written
parser's dispatch is deterministic, once-only, and never exposed to it.
Since Gate 1c (§10) deletes these bespoke compilers wholesale once the
macro-based replacement lands, there is nothing to gain by fixing their
internals first. The purity requirement that actually matters is `lift
module` itself being specified correctly from the start (above) — that
does not depend on anything upstream in the old compilers.

### 14.6 Worked example — `actor` fully redefined as a macro

Grounding example, in the same spirit as §1's `Every`:

```cure
macro Actor
  syntax
    actor <name: Name>
      on_start <init: Block>
      on_message <msg: Pattern> <body: Block> ...
      on_stop <cleanup: Block>
  becomes
    lift module Named("Cure.Actor." <> <name>)
      behaviour GenServer

      callback init(arg) -> { <init>; %[:ok, arg] }
      callback handle_info(<msg>, state) -> <body>
      ...
      callback terminate(reason, state) -> <cleanup>

      fn start_link(arg) -> GenServer.start_link(<name>, arg)
      fn send(pid, msg) -> pid <-| msg
```

Everything past `behaviour GenServer` is ordinary Cure: `callback` bodies are
plain Cure expressions checked by the normal pipeline (exactly as
`on_message`/`on_transition` clauses are today, via
`Cure.Compiler.Codegen.compile_expr/1` — the same call FSM's own compiler
already makes, per the classic/dependent-pipeline audit earlier in this
thread), and `start_link`/`send` are ordinary exported functions, no new
primitive required.

### 14.7 Protocols need neither primitive — but that's not the only axis

Noted for sequencing: `proto`/`impl` codegen never leaves the enclosing
module — dispatch functions and impl functions are ordinary forms spliced
into the *same* module (`codegen.ex:471-601`; each protocol method compiles
to one ordinary dispatch function with one runtime type-guarded clause per
impl, not a separate compiled unit per impl). Protocols therefore need
**neither** §14.3's closed callback vocabulary (there's no OTP behaviour
contract to satisfy) **nor** §14.4's `lift module` (no separate compilation
unit to mint) — the already-specified Tier 3/4 (`computed by` + ordinary
same-module `lift`) is very likely sufficient as written.

That makes `proto`/`impl` a good check that Tier 3/4 alone is sufficient —
but it is **not** a good proof of §14's two new primitives, since it never
exercises them, and it does **not** sidestep the lexer obstacle below. Pick
the target by which question is being answered.

**Lexer obstacle (found auditing this section, 2026-07-08):** `fsm`,
`actor`, `proto`, and `impl` are hard lexer keywords (`lexer.ex:47-52`,
`@keywords` — tokenized as `:keyword` before the parser, let alone a
macro, ever sees them). `sup` and `app` are not — the lexer's own comment
(line 42) documents them as already "soft-keyword discipline," ordinary
identifier tokens the parser recognizes contextually. A macro reusing the
*literal* `sup`/`app` spelling needs zero lexer change; reusing `fsm`,
`actor`, `proto`, or `impl` verbatim requires first demoting it out of the
hard-keyword list — a separate, real change with its own blast radius
(anywhere else in the language assumes these are unconditionally reserved).
This is orthogonal to the primitives axis: `proto`/`impl` dodge the
primitives but not the lexer; `sup`/`app` dodge the lexer but not the
primitives; `fsm`/`actor` dodge neither.

Two distinct milestones follow, and they should not be conflated:

- **Capability proof** (does the facility + §14's primitives actually work)
  — needs no lexer change if done under a fresh name first. **Recommend
  `sup` as this target**: zero user-authored callback bodies (purely
  declarative child list + strategy header, per §14.1's audit table — the
  simplest correctness bar of the four OTP containers), already
  soft-keyworded, and it exercises *both* new primitives (`behaviour`
  `Supervisor` + `lift module`), unlike `proto`/`impl` which exercise
  neither.
- **Full replacement** (same keyword, bespoke compiler retired) — gated on
  the lexer demotion for `fsm`/`actor`/`proto`/`impl` specifically; `sup`/
  `app` can go straight to replacement without that step once the
  capability proof lands.

Gate 1b (§10) should read as the capability proof (`sup`, via a fresh name),
not literal replacement — replacement is a later, separate step per
container.

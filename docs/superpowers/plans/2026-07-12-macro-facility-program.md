# Macro Facility — Program Decomposition

> Not an executable task plan. This is the **program roadmap**: the ordered
> sub-projects the "base macro facility + self-proving extension" decomposes into.
> Each sub-project (SP) ships working, testable software on its own and gets its
> OWN task-by-task plan (`docs/superpowers/plans/YYYY-MM-DD-<sp-name>.md`) written
> and executed before the next. Derived from the bootstrap order of
> `macros/2026-07-08-macro-facility-design.md` §10 + §14 and the enforced
> obligations of `2026-07-11-self-proving-macros-design.md`.

**Why decomposed:** the writing-plans scope check — the facility spans several
independent subsystems (parsing, hygiene/expansion, compile-time evaluation,
generative testing, reflection, OTP container minting). A single plan cannot carry
complete code for all of them without becoming placeholders. Each SP below is a
standalone plan.

**Invariant across every SP (from base §9):** the facility lives entirely in the
untrusted frontend, upstream of the elaborator. Macro output is **re-elaborated and
kernel-checked exactly like hand-written code**. **TCB delta = zero** — no SP changes
`lib/cure/core/*`. Any SP that thinks it needs to is mis-scoped; stop and re-plan.

---

## The sub-projects, in build order

### SP1 — Minimal facility: container + grammar + Tiers 1–2
**Ships:** a `macro` container that parses `syntax`/`literal` rules
(examples-with-holes), scoped by `use`, expanding via Tier-1 literal rules and Tier-2
hygienic `becomes` templates; a `units`-style and an `every`-style macro work
end-to-end and their output kernel-checks. **No** Tier-3 elab, reflection, or
generative proof yet.
**Includes:** the quoted-AST model (§3), hygiene + `<fresh Name>` (§5), two-pass
name resolution (§6), import scoping + same-keyword conflict error (§7), the
*default* error machinery floor (§2 typed-hole errors) — NOT yet the type-enforced
exhaustiveness (that is SP2).
**Gate:** a Tier-1 and a Tier-2 macro compile, expand, and their expansions pass the
existing kernel; wrong-arity/unknown-category uses produce a (default-machinery)
diagnostic, not a raw parser error. Full `mix test` green.
**Depends on:** nothing new (existing parser/lexer/elaborator).
**The hard part:** designing how examples-with-holes rules hook into the existing
`lib/cure/compiler/parser.ex`/`lexer.ex` — needs a parser-internals exploration pass
before its plan is written.

### SP2 — Tier 3 + self-proving Mechanisms 1 & 3
**Ships:** `syntax … computed by f` (total compile-time Cure over quoted decls,
`check … else fail`), size-change-certified pure elabs (§5); PLUS the type-enforced
obligations that need no generation: **derived + author-extensible `Diagnosis`**
(`fail C(args)` §3.4), **exhaustive `explain`** checked like case-coverage
(self-proving §3), and **required per-rule worked examples** (self-proving §5). A
Tier-3 macro (e.g. a `schema`/`config`-style one) works, and a macro with an
undescribed failure point or an unpinned rule FAILS TO COMPILE.
**Gate:** the three new macro-compile errors (`missing_diagnosis`, `rule_unpinned`,
plus example-mismatch) fire on red fixtures and are absent on green ones; example
expansions kernel-check. Full suite green.
**Depends on:** SP1.

### SP3 — Self-proving Mechanism 2: generative expansion proof
**Ships:** the Antigen-for-DSLs engine (self-proving §4) — **full fuzz on every macro
compile**: generate valid parses by type-directed filling of typed holes (extends the
Antigen generator with "term of a required type"), expand, kernel-check; a valid parse
expanding to ill-typed Core fails the macro's compile (shrunk counterexample). Caching
by macro definition. Per-macro coverage manifest.
**Gate:** a macro whose `becomes`/elab drops a hole's type is REJECTED at macro-compile
with a shrunk counterexample; a correct macro passes; the manifest reports coverage.
Full suite green; Antigen campaign green.
**Depends on:** SP2 (needs Tier-3 elabs + the grammar to fuzz) + the Antigen generator.
**The one new engine:** type-directed term generation.

### SP4 — Tier 4 reflection API
**Ships:** the read-only advisory API (§8) — `resolve`, `constructors`, `infer`,
`expand`, `lift` (the append-only write member) — enough for `reducer`/`flow`/`view`.
Dogfood Gate 2: the `reducer` spec compiles as a library and elaborates the Door
program.
**Gate:** a `reducer`-style macro builds GADT match arms via `constructors`/`resolve`
and its output kernel-checks; `lift` hoists a declaration; nothing returned by the API
is trusted (a lie from it still yields a rejected-not-unsound program). Full suite green.
**Depends on:** SP2 (Tier-3 elab host). Independent of SP3.

### SP5 — §14 BEAM/OTP container ownership: `behaviour`/`callback` + `lift module`
**Ships:** the closed callback vocabulary as Cure ADTs (§14.3), `lift module`
minting a compiled unit as a VALUE (§14.4–.5, pure — no compile-and-load), and the
first OTP container fully owned by a macro (Gate 1b: `sup` under a fresh name,
simplest correctness bar, no user callback bodies). This is what gives **`Std.Otp`
its ceiling** — `spawn`/`start_link` minting typed handles + gen_server behaviours
compiled from a Cure `process`/`actor` macro.
**Gate:** a `sup`-style macro emits a gen_server/supervisor behaviour that runs on
generic-unix AtomVM (observable), all through `lift module`, no bespoke Elixir backing
it. Then `actor`/`fsm` re-expressed (Gate 1) and their bespoke compilers deletable.
**Depends on:** SP2 (+ SP4 for callback-body elaboration). Ties back to the effect
stack (already landed) — callback bodies are `Effect`-typed.

> **SP5.1–SP5.3 are NON-OPTIONAL prerequisites for SP6.** They were previously
> carried as deferred/optional enhancements (quasiquote "slice 4"; cross-module
> import "T9"; auto-hygiene "T7b"). They are promoted here: SP6's *user-defined DSL
> libraries* cannot be authored ergonomically, distributed across modules, or trusted
> to be hygienic without them. They are independent of SP5's OTP-container work and of
> each other, and each ships and gates on its own.

### SP5.1 — Quasiquotation as the primary authoring surface (`quote` / `$( )`)
**Ships:** a `quote { … }` surface that lifts ordinary Cure syntax to a `Syntax`
value, with `$(expr)` single-node and `$(xs …)` repeated-group splices; splice
position/category checking so a mis-spliced hole is a compile error, not malformed
output. This becomes the DEFAULT authoring surface for `computed by` expanders; the
`Std.Syntax` typed builders and `Std.Syntax.Raw` drop to the escape hatch they were
always meant to be.
**Includes:** reuse of the existing `to_syntax`/`from_syntax` bridge — the quoted body
round-trips through the same reflected repr, so no second AST model is introduced.
**Why non-optional:** expanders today build `Syntax` by hand (verbose, error-prone) —
this was demoted to "optional slice 4." Every macro system people actually author in
(Template Haskell, Lean 4, Scala 3, Racket) makes quote the default and hand-construction
the escape hatch. Cure has it backwards; correct it.
**Gate:** a `derive_actor`-class expander rewritten with `quote`/`$()` produces
byte-identical Core to the hand-built version; a splice of the wrong syntax category is
a compile error; full suite green.
**Depends on:** SP2 (the reflection bridge + typed derived records).

### SP5.2 — Cross-module macro import (formerly deferred T9)
**Ships:** `use SomeModule` brings that module's `syntax` / `macro` / `syntax family`
grammars into scope at the USE site, so macros can be published as ordinary library code
and imported like any other definition.
**The hard part:** expansion runs at PARSE time but import resolution runs at
ELABORATION time (`import_source_env` / `module_slice_env`, `program.ex:699/799`) — so an
imported macro's grammar is not available when the parser needs it. Imported-macro
grammars require the PARSER to locate and parse imported modules, coupling the parser to
import resolution. This is the one genuinely new architectural piece.
**Why non-optional:** without it macros are effectively module-local or std-only — there
is no macro *ecosystem*, and SP6's "user-defined DSL libraries" cannot be distributed or
reused. It is a hard prerequisite for SP6, not a convenience.
**Gate:** a DSL macro defined in module A, `use`d from module B, expands and kernel-checks
in B; a same-keyword grammar conflict across imports produces a real diagnostic (not a raw
parser error); full suite green.
**Depends on:** SP1 (grammar + import scoping) + the elaboration-time import machinery
(already landed).

### SP5.3 — Scope-set hygiene (formerly deferred T7b)
**Ships:** replaces the string-gensym hygiene with Flatt's set-of-scopes model
(uncopyable scope marks), and turns on automatic full hygiene — every template binder is
renamed with no annotation, and the `<capture>` escape hatch remains for intentional
capture into caller scope.
**Closes two characterized correctness holes:** (a) `<fresh e>` silently dropping the arg
when `e` is also a hole; (b) backtick-gensym spoofing — a use-site `` `g$0` `` defeating
the string gensym. Both are exploitable-in-principle, not cosmetic.
**Why non-optional:** the current hygiene is *spoofable*. A macro system whose hygiene can
be defeated is not sound in the way the rest of the facility is — this is correctness debt
that must be retired before the facility can be called done.
**Gate:** red fixtures reproducing both holes now pass; auto-hygiene renames template
binders with no annotation; `<capture>` still binds into caller scope on demand; full
suite green.
**Depends on:** SP1 (the hygiene / `<fresh>` machinery it replaces).

### SP6 — Tier 5 + the concrete DSL libraries
**Ships:** module rules + raw holes (§13.1–.2), then the sibling DSL specs
(`packet`, `board`, `driver`, `protocol`, `parse`, …) as libraries on the finished
facility. Each DSL is its own small plan.
**Depends on:** SP1–SP5 as each DSL requires.

> **SP7–SP9 are first-class but NOT prerequisites for SP6.** Unlike SP5.1–5.3, they do
> not gate the DSL libraries. They are, respectively: a cross-cutting dev-experience
> workstream that can start NOW (SP7), a soundness EXTENSION of SP3 (SP8), and a
> deliberate later high-ceiling capability bet (SP9). Order them by priority, not
> strictly after SP6.

### SP7 — Macro tooling: stepper, expansion introspection, macro-aware errors
**Ships:** a `cure macro expand <file>` that prints each expansion step (the stepper), a
`--trace-macros` flag, and macro-aware error rendering — errors that point at the USE
site in the DSL's own vocabulary and show the expansion, instead of surfacing a
Core-level `unknown_global` from inside generated code (the parked Elm-style rendering).
**Why it matters:** a DSL you cannot watch expand is a DSL you debug by print statement;
Racket's macro stepper is a large part of why authoring in it is tractable. Source
provenance (`source_line`/`source_col`) landed 2026-07-15, so the location channel already
exists — this is now cheap and disproportionately drives whether the facility gets USED.
**Ordering:** can begin immediately — depends only on the landed expansion pipeline + the
provenance channel; independent of SP5.x and SP6. Highest adoption leverage per unit effort.
**Gate:** `cure macro expand` shows the step sequence for a `computed by` macro; an
ill-typed expansion reports at the use site with the DSL keyword and the expansion shown,
not a raw generated-code error; full suite green.
**Depends on:** the landed expansion pipeline + source provenance.

### SP8 — Composition soundness (macro∘macro proofs + expansion confluence)
**Ships:** extends the self-proving story from "one macro's output is well-typed" (SP3) to
two properties SP3 does NOT cover: (1) **composition** — when macro A's output contains a
use of macro B, the composition is proven, not just each in isolation (build against
`macros/2026-07-08-macro-composition-design.md`); (2) **expansion confluence/termination as
a PROVEN per-macro property**, not merely fuel-bounded — today a computed output that
contains further macro uses relies on the fuel backstop.
**Why:** the inside-out expansion order makes composition tractable to state as a theorem;
making "expansion converges" proven rather than fuel-capped extends the guarantee from
"type-safe output" to "well-defined output."
**Ordering:** after SP3 (needs the generative-proof engine) and once interacting macros
exist (the SP5.x / SP6 DSLs are good fodder).
**Gate:** a composed A∘B macro pair is generatively proven at macro-compile; a
non-converging computed macro is REJECTED with a diagnostic rather than silently
fuel-exhausted; full suite + Antigen campaign green.
**Depends on:** SP3 (generative-proof engine).

### SP9 — Type-directed (elaboration-time) macros
**Ships:** a distinct macro KIND that participates in bidirectional elaboration — it
receives the EXPECTED type and may emit typed terms into the elaborator's metavariable
context, rather than being a pure `Syntax -> Syntax` pre-pass. Unlocks overloaded literals,
adaptive `do`-notation (the block's type selects the `Effect` row / monad), and type-driven
deriving — the Lean 4 / Idris `%macro` posture.
**Why it is its own KIND, not an extension of `computed by`:** `computed by` runs BEFORE
elaboration and never sees the expected type; type-directed macros couple to the
elaborator. Keeping them a separate kind preserves the clean syntactic pre-pass for
everything that does not need types.
**Ordering:** the deliberate LATER, high-ceiling bet — start only after the syntactic tier
(SP1–SP6) is proven solid by the OTP-container dogfood. Highest capability ceiling, biggest
architectural risk (elaborator coupling), so it goes last.
**Gate:** a type-directed macro resolves an overloaded literal or adapts a `do`-block to its
checked `Effect` row and its output kernel-checks; a wrong emission still yields
rejected-not-unsound (the reflection/emission trust posture is preserved); full suite green.
**Depends on:** SP2 (Tier-3 host) + the reflection API; the effect stack (already landed)
for the `do`-notation case.

---

## Sequencing summary

```
SP1 (facility + Tiers 1–2)
  └─> SP2 (Tier 3 + typed errors + examples)          ← the spine
        ├─> SP3 (generative proof) ──────────────────> SP8 (composition soundness)
        ├─> SP4 (reflection API)
        └─> SP5 (behaviour/lift module ──> Std.Otp ceiling)

  SP5.1 (quasiquote)          ┐
  SP5.2 (cross-module import) ├─ NON-OPTIONAL prereqs ─> SP6 (Tier 5 + DSL libraries)
  SP5.3 (scope-set hygiene)   ┘  (independent; each depends on SP1/SP2)

Cross-cutting / horizon (off the SP6 critical path):
  SP7 (tooling: stepper, introspection, macro-aware errors) — startable NOW (provenance landed)
  SP9 (type-directed / elaboration-time macros)             — LAST; after the SP1–SP6 tier is proven
```

SP1→SP2 is the spine. SP3/SP4/SP5 fan out from SP2 and can be ordered by priority
(SP5 unblocks the `Std.Otp` ceiling; SP3 delivers the self-proving guarantee's
headline; SP4 unblocks the flagship reducers). SP5.1–5.3 are non-optional
prerequisites for SP6 — DSL libraries need ergonomic authoring (quasiquote),
cross-module distribution, and non-spoofable hygiene — but are independent of the
OTP-container work and of each other. Off the critical path: SP7 (tooling) can start
now on the landed provenance channel; SP8 extends SP3's proof to composition and
proven expansion confluence; SP9 (type-directed macros) is the deliberate last,
high-ceiling bet. Write and execute one SP's detailed plan fully — red-green, gated,
committed — before starting the next.

## Immediate next step

Write **SP1's** task-by-task plan
(`docs/superpowers/plans/2026-07-12-macro-facility-sp1-<name>.md`). Prerequisite: a
focused exploration of `lib/cure/compiler/parser.ex` + `lexer.ex` to fix exactly how
an examples-with-holes `syntax` rule is lexed, parsed into the quoted-AST model, and
matched at a use site — the one genuinely new parsing subsystem. That exploration is
the first thing SP1's plan is written against.

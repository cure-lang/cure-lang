# Error Explainers — Provenance, Registration, and the Never-Raw Guarantee

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§4); priority #2 in the surfaces spec. **Infrastructure, not a macro** —
but every macro's `explain` block (parent §5.1) registers into it, and
every error a macro user ever sees is rendered by it. The parent calls it
"the single most important hiding mechanism"; this spec makes it a
subsystem with a data model, a contract, and tests.

---

## 1. Purpose

`{:cannot_unify, plus(Z, ?0), S(Z)}` must never reach a user. Today,
kernel/elaborator failures are Elixir terms, and the diagnostics registry
(E001–E091) covers hand-written Cure, not macro-generated code — when
`every 500` elaborates into an `fsm` into core terms and the kernel rejects
one, the failure surfaces three layers below anything the user wrote. The
explainer subsystem closes that gap with three commitments:

1. **Attribution** — every macro-elaborated term carries provenance, so
   any failure traces to the surface declaration that produced it (§2).
2. **Translation** — macros register pattern-matched explainers rendering
   failures in domain vocabulary, on a fixed template (§3–§4).
3. **The never-raw guarantee** — a raw kernel error reaching a macro user
   is a defect *by definition*, and the fallback path says so out loud (§7).

Build it now, while the macro count is small (parent §4): retrofitting
per-DSL error reflection across sixteen shipped macros is misery.

## 2. Provenance — the data model

Every term a macro expansion emits carries a provenance record, attached as
term metadata on the **elaborator side**:

```
Provenance = {
  macro:  atom,                    # :driver, :protocol, :reducer, …
  span:     {file, {l0, c0}, {l1, c1}},   # the user's surface text
  decl_path: [String],               # human-readable declaration path
  expansion: [Provenance] | []       # outer layers, innermost-first tail
}
```

- **`decl_path`** is the breadcrumb into the surface declaration, e.g.
  `["reducer Door", "on MotorTimeout from Opening", "emit target"]` — built
  by the expansion machinery walking the surface tree, never by hand.
- **`expansion`** records the chain when macros nest: a `fleet` hub
  expands to `flow`, which expands to core. The head record is the
  *innermost* macro (closest to what the user literally wrote); each
  `expansion` element is one enclosing layer. §3 gives the ordering teeth.

**TCB discipline (non-negotiable):** provenance is diagnostic metadata,
never semantics. The kernel does not read it, branch on it, or know its
shape; the Final-Core validator ignores it; erasure and conversion are
provenance-blind. It is threaded entirely by the elaborator — attached at
expansion, propagated through rewrites, and (the one integration point)
**preserved into error reports**: every failure path that today returns
`{:cannot_unify, t1, t2}` returns `{failure_term, provenance | nil}`, the
provenance read off the term being processed when the failure arose. Kernel
return values are unchanged; the wrapping happens in the elaborator frames
that call it. TCB delta: zero. `nil` provenance means hand-written core
Cure — that branch exits this spec entirely (§7).

## 3. Registration and matching

Macros register explainers in their `explain` block (parent §5.1):

```cure
explain
  {:no_instance, Duration, t} ->
    "every expects a duration — write every 500ms or every 2s (got " <> show(t) <> ")"
```

Formally, an explainer is a partial function over the pair **(failure term
shape, provenance)**: ordinary Cure patterns over the (quoted) failure
term, with the provenance implicitly available in the clause body
(`$provenance.decl_path` etc.) and matchable for context-specific messages.

**Dispatch:**

1. Collect candidate macros from the failure's provenance chain:
   innermost first, then each `expansion` layer outward.
2. Try each macro's explainer clauses in that order; first match wins.
   **Innermost provenance wins** — the layer closest to what the user wrote
   speaks first, because its vocabulary is the user's vocabulary (a `fleet`
   user who wrote a `flow` expression gets the flow-level message).
3. Outer layers may **wrap**: an enclosing macro can register a `wrap`
   clause annotating an inner result with one line of outer context
   ("…inside the hub's `valve` node"). Recommended over the alternative —
   letting the outer macro *replace* the inner message — because
   replacement reintroduces the attribution gap one level up. Replacement
   stays possible (an outer clause claiming the shape outright) but the
   authoring guide discourages it.
4. No clause matches anywhere in the chain → fallback (§7).

Explainer clauses are ordinary compile-time Cure (same staging as `elab`):
size-change-checked, and never allowed to fail into a second error while
rendering the first — a raised explainer is itself a macro bug, routed
to §7.

## 4. The message template

Every rendered message has the fixed shape (parent §4):

1. **What you wrote** — the surface snippet echoed from the provenance
   span, caret under the offending range; the renderer does this, explainer
   authors never re-quote user code.
2. **Why the domain forbids it** — one to three sentences of domain fact.
3. **What to write instead** — concrete and actionable: a named call, a
   rewritten line, a menu of numbered options (fleet's E13x three-way
   choice is the exemplar).
4. **Optional reference** — datasheet section, protocol line, spec anchor
   ("datasheet §3.3", "Provisioning, line 12").

Conformance targets — the shipped explainers must reproduce these existing
examples verbatim: E102 (parent §4, pin capability), E110 (driver §3,
mode), E115 (parent §6.6, bare duration), E118 (parent §6.9, ownership),
E120 (parent §6.8, secret flow), E13x (fleet §5), E14x (protocol §3.2).

**Vocabulary rule:** messages are DOMAIN vocabulary. Type-theory terms —
*unify, unification, metavariable, Pi, sigma, index, refinement, GADT,
elaboration, kernel* — are **banned from user-facing explainer text**.
Enforced, not aspirational: a lint over every explainer's string literals
fails the macro's build on a banned-word hit — cute, cheap, and it keeps
the promise honest as third-party macros arrive. Recommended and adopted.
The list lives with the registry file (§5): versioned, per-macro
whitelistable for false positives.

## 5. Code allocation registry

The parent assigned new-range codes informally; this spec fixes them,
reconciling every informal use (E102, E110, E115, E118, E120, E13x, E14x)
without renumbering anything already written down:

| Range | Owner |
|---|---|
| E001–E099 | Core compiler (existing; E091 effects is the latest) |
| E100–E109 | `board` |
| E110–E114 | `driver` / `regmap` |
| E115–E117 | units of measure |
| E118–E119 | pin/bus ownership |
| E120–E129 | `config` / `secret` |
| E130–E139 | `fleet` |
| E140–E149 | `protocol` |
| E150–E154 | tasks (`every` / `on`) |
| E155–E159 | `packet` / `codec` |
| E160–E164 | `schema` |
| E165–E169 | `parse` |
| E170–E174 | web trio (`api` / `view` / `form`) |
| E175–E179 | `workflow` / `bot` |
| E180–E184 | `cli` / `job` |
| E185–E189 | `reducer` |
| E190–E194 | `sim` / `pattern` |
| E195–E199 | `check` + the macro facility itself |
| E200–E204 | `reef` |
| E205–E209 | `synth` |
| E210–E219 | `dive` |
| E220–E224 | `knit` |
| E225–E229 | `agenttools` |
| E230–E234 | `checklist` |
| E235–E239 | `backtest` |
| E240–E244 | `gates` |
| E245–E249 | `crossword` |
| E250–E254 | `fold` |
| E255–E259 | `a11y` |
| E260–E264 | `flightplan` |
| E265–E269 | `blocks` |
| E270–E279 | macro-composition seam errors (cross-macro; see `2026-07-08-macro-composition-design.md` §6) |
| E280–E289 | `cad` (solid modeling; E280 reuses units' bare-number shape) |
| E290–E299 | `crochet` (E292 = circle-won't-lie-flat; sibling of `knit`) |

**Community macros do not get bare E-codes** — they use a namespaced
form, `greenhouse-macro/E3`. The bare numeric space is first-party
curated: collisions between community packages are otherwise guaranteed,
and a bare `E123` from a random package would counterfeit first-party
authority. Recommended and adopted.

Allocations live in a checked registry file (code → owning macro →
one-line summary; `lib/cure/diagnostics/codes.exs` or equivalent); the
build fails on duplicates, codes outside the owner's block, or an explainer
emitting an unregistered code.

## 6. Context queries — the "free pins right now" problem

The E102 target ends with *"Free output-capable pins on your board right
now: gpio4, gpio5, gpio16, gpio17."* That sentence needs the claimed-pin set
at the failure point; E14x needs the protocol state to say "device answers
Accepted or Rejected". Good suggestions require elaboration-state access —
the hard design point. Design: a **read-only context-query interface** —
alongside its explainers, a macro registers named queries:

```cure
context
  free_output_pins() -> List(Pin) =
    board.pins.filter(fn(p) -> p.output_capable and not claimed(p))
  legal_replies(step: StepId) -> List(MsgName) = ...
```

Rules that keep this honest:

- **Queries are pure functions over data the macro recorded at
  elaboration time.** As it elaborates, a macro deposits artifacts (the
  claimed-pin table, the protocol state chart, the regmap) into a
  per-module, per-macro store keyed by provenance. Queries read that
  store. Nothing else.
- **No re-elaboration during error formatting.** Rendering happens after
  elaboration has failed; the world is whatever the artifact store says it
  was. A query cannot call back into the elaborator, the kernel, or another
  macro's expansion — the interface simply doesn't expose those.
- Queries are scoped to the registering macro's own artifacts;
  cross-macro reads (units wanting the board's pin table) go through the
  other macro's *exported* queries — same rules, explicit dependency.
- Queries obey the same staging/termination discipline as `elab` functions:
  total, host-side, no AtomVM constraints. The store is snapshot-at-failure;
  memory cost at scale is ledgered (§10.3).

## 7. Fallback and the never-raw guarantee

Two exhaustive branches on `provenance`:

- **Provenance present, no explainer matched** (or an explainer raised):
  the raw failure term is shown — honestly, not prettified — **plus** the
  framing: *"This error came from the `driver` macro, which failed to
  explain it. This is a bug in the macro — please report it at <the issue
  URL from package metadata>."* The breadcrumb (decl_path + span) is still
  rendered, so even the fallback is sited at the user's line. Never-raw is
  thus really never-*unowned*: raw text may appear, but always wearing a
  "this is our bug" sign.
- **Provenance absent** (hand-written core Cure): the compiler's normal
  diagnostics pipeline (E001–E099) renders the error, exactly as today.
  This spec does not restyle those — a deliberate scope boundary. Improving
  core-Cure error quality is real, separate work (unifier-level effort à la
  Elm/Rust, not domain translation); coupling it here would stall the
  macro wave.

## 8. LSP integration

The same explainers power the editor — no second rendering path:

- **Diagnostics:** rendered messages become LSP diagnostics at the
  provenance span (not the expansion site), E-code as diagnostic code.
- **Quick fixes:** the "what to write instead" clause, when
  machine-applicable, becomes a code action. Explainer results carry an
  optional structured-fix field —
  `{message, fixes: [{title: String, edits: [{span, replacement}]}]}`.
  E115's `sleep(500ms)` is one fix; fleet's E13x three-way choice is three
  code actions. Absent fixes degrade to message-only; nothing requires
  them. Schema details ledgered (§10.4).
- **Hover** is the positive twin: the same domain-vocabulary discipline
  applied to *types* ("a temperature in Celsius from the BME280", not the
  erased refinement) via macro-registered pretty-printers over the same
  provenance. Mechanism shared; surface deferred to the toolchain spec.

## 9. Testing explainers

- **Golden-file tests per explainer**: a failing input program → the exact
  rendered message, byte-for-byte, in the macro's test tree. The renderer
  is deterministic (spans, breadcrumbs, query results all come from one
  elaboration), so golden files are stable.
- **Initial golden corpus**: the seven conformance targets from §4 (E102,
  E110, E115, E118, E120, fleet E13x, protocol E14x), transcribed from the
  parent and sibling specs — their representative errors stop being
  aspirational prose and become CI.
- **Explainer coverage lint**: a macro's expansion machinery declares (or
  the framework infers from its `elab` failure returns) its failure shapes;
  any shape with no matching `explain` clause is a build warning naming it.
  This dogfoods the never-raw goal — the fallback (§7) should fire only for
  shapes nobody predicted, never shapes nobody bothered to cover.
- The banned-word lint (§4) and registry check (§5) run in the same pass.

## 10. Open decisions (ledger)

1. **Localization** — recommended: not in v1, English-only, but structured
   for later: explainers separate template slots from prose and the
   registry keys messages by code, so a locale layer can swap string tables
   without touching match logic.
2. **Verbosity modes** — recommended: yes, adopt rustc's `--explain` shape.
   Default stays terse (the §4 template); `cure explain E110` prints a
   long-form page, stored next to the code in the registry. CLI surface TBD.
3. **Provenance memory cost at scale** — every elaborated term carries a
   record; big generated programs (fleet projecting many nodes) multiply
   it. Interned spans + shared expansion-chain tails, or strip provenance
   after successful elaboration (keep only on error paths)? Measure first.
4. **Structured quick-fix schema** — the §8 field is minimal; multi-file
   edits, command-style actions, placeholder tabstops? Decide with the LSP.
5. **Runtime reuse of the registry** — bot re-prompts and `api` 400 bodies
   (workflow/bot spec) render the *same* refinement failures at runtime.
   Recommended: yes — one registry, two renderers: compile-time (carets,
   spans) and boundary-time (no source echo; message + instead-clause).
   One vocabulary, one lint, one corpus; parallel tables guarantee drift.
6. **Docs linking** — codes should link to hosted docs
   (`cure.dev/errors/E110`); registry is the source; site generation is out
   of scope (§11) — reserve the URL scheme now.

## 11. Non-goals

- **No AI-generated messages.** Explainers are authored, versioned, linted,
  and golden-tested; a probabilistic paraphrase layer breaks all four.
- **No restyling of core-Cure kernel/elaborator diagnostics** (E001–E099) —
  hand-written-Cure error quality is separate, later work (§7).
- **No documentation-site generation** — the registry is designed to feed
  one (§10.6), but building it is toolchain work, not this subsystem.

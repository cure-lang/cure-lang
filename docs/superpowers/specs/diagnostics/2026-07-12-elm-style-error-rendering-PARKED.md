# Elm-Style Error Rendering — PARKED Initiative Spec

> **STATUS: SUPERSEDED FOR IMPLEMENTATION.** Diagnostic opacity became a direct
> impediment to completing the 0.34 macro work. The shared structured model,
> caret renderer, machine output, and macro provenance are now required by
> [`2026-07-20-structured-compiler-diagnostics-design.md`](2026-07-20-structured-compiler-diagnostics-design.md).
> Cure-native parser self-hosting remains deferred to 0.35.

## Why parked, not staged

Every diagnostic in the compiler routes through a single function,
`Cure.Compiler.Errors.format_diagnostic/5` (`lib/cure/compiler/errors.ex:1730`).
So a later rewrite of *that one function* upgrades every error — parse, type,
codegen, macro — at once. Building new diagnostics (e.g. the macro error floor,
SP1 §2) on the existing renderer therefore loses nothing: when this initiative
lands, those diagnostics inherit the richer rendering for free. Staging the macro
work behind this rewrite would only add latency with no payoff.

## Current state (the baseline this would replace)

`Cure.Compiler.Errors` is already partway to Elm — it is not a raw-tuple dumper:

- `format_error/2` — a large structured dispatch (~40 clauses) mapping each error
  tuple to a human message.
- `format_diagnostic(severity, category, file, line, message)` — renders:
  ```
  error: syntax error
   --> path/to/file.cure:3      (a real editor hyperlink via Cure.Term.Hyperlink)
    | expected becomes, got identifier at column 45
  ```
- `suggest/2` (`:1677`) + `levenshtein/2` (`:1759`) — "did you mean X?" typo hints.

What it **lacks** versus Elm:
1. **Source-snippet rendering** — showing the actual offending source line(s) with a
   caret/underline (`^^^^`) under the exact span. Today only `line` (an integer) is
   carried; there is no region (start/end col) and no access to source text at render
   time.
2. **A formalized region model** — errors carry `line, col` scalars, not a
   `{start_line, start_col, end_line, end_col}` span. Caret rendering needs the span.
3. **A structured multi-part message** — Elm errors are `{ title, region, problem
   prose, hint(s) }`. Today `message` is a single interpolated string; hints are
   inlined ad hoc.
4. **Consistent friendly tone + actionable hints** across all sites (some clauses are
   terse/technical).

## Sketch of the initiative (when unparked)

- **Region model:** thread a `{line, col, end_line, end_col}` (or a `Region` struct)
  through error tuples instead of bare `line, col`. This is the invasive part — every
  `add_error`/error-tuple site in parser/elaborator/codegen must carry spans. Could be
  staged: a `Region` that degrades to `line`-only when a span isn't available, so sites
  migrate incrementally.
- **Source access at render time:** `format_error/2` already takes `file`; give the
  renderer the source text (read once, cached) so it can slice the offending line(s)
  and draw the caret under `[start_col, end_col]`.
- **Structured `Diagnostic` value:** `%Diagnostic{severity, title, region, problem,
  hints: [String.t()]}` with one renderer. `format_error/2` clauses build these instead
  of pre-formatted strings; `format_diagnostic` becomes the `Diagnostic`→string printer
  (terminal + a future JSON/LSP emitter fall out naturally).
- **Reuse existing `suggest`/`levenshtein`** for the "did you mean" hint slot.
- **Elm-style header:** `-- SYNTAX ERROR ---------- file.cure` banner, blank-line-
  separated problem prose, `Hint:` lines.

## Scope + cost (why it's a separate initiative)

Cross-cutting: touches **every** error-producing site (parser `add_error`, elaborator
error returns, codegen, app/release verification, import resolution — dozens of tuple
shapes in `errors.ex`). It is NOT part of the macro facility and would derail the
focused SP1→SP6 build. Own spec, own plan, own review cycle. TCB delta zero (rendering
+ error plumbing only; no `lib/cure/core/*`).

## Forward-compatibility contract (what the macro floor must NOT do)

So the macro error floor (SP1 §2) stays compatible with this future work:
- Route macro diagnostics through `format_error/2` + `format_diagnostic/5` (the central
  renderer) — do NOT hand-format macro error strings at the call site.
- Keep the message CONTENT (friendly prose + a hint + a `suggest` "did you mean") in the
  `format_error` clause, so an Elm-rewrite that adds snippet chrome around the same
  message just works.
- Carry as much region info as the tuple can (at least `line, col`); if/when spans are
  added, macro tuples upgrade with the rest.

## Related

- `docs/superpowers/specs/macros/2026-07-11-self-proving-macros-design.md` — the
  self-proving macro errors (SP2) are about author-ENFORCED message *content*
  (type-required `Diagnosis`), orthogonal to this rendering chrome. They compose:
  author content + Elm rendering = best-in-class DSL errors, but each ships
  independently.
- `docs/superpowers/specs/macros/2026-07-12-racket-syntax-parse-comparison.md` — the
  failure-set → maximal-by-progress → report(message, context, at, within) machinery;
  the "at/within" is the region this initiative would render as a caret.

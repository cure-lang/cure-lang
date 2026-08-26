# Cure-Native Parsing, Diagnostics, and Compiler Parser Self-Hosting

**Date:** 2026-07-17  
**Target:** Cure 0.35  
**Status:** PARTIALLY UNPARKED — the shared structured compiler diagnostic
foundation moved into 0.34 under
`2026-07-20-structured-compiler-diagnostics-design.md`. Cure-native parser
self-hosting, the public parsing platform, bootstrap, and cutover remain parked
for 0.35.

**Related specifications:**

- [`2026-07-10-compiler-error-expansion-design.md`](2026-07-10-compiler-error-expansion-design.md)
- [`2026-07-09-total-parsing-library-design.md`](2026-07-09-total-parsing-library-design.md)
- [`macros/2026-07-08-parse-macro-design.md`](macros/2026-07-08-parse-macro-design.md)

---

## 1. Decision

Cure 0.35 will build a public, Cure-native parsing and diagnostic stack and
then make Cure's own source lexer/parser a flagship client of that stack.

The result must not be a privileged compiler-only parser hidden behind bespoke
Elixir helpers. The same facilities used to parse Cure source and render its
syntax diagnostics must be available to ordinary Cure programs for compilers,
configuration languages, protocol tools, editors, and other structured-input
applications.

The dependency direction is locked:

```text
Compiler.Diagnostic
        ↑
Std.Parse.Error
        ↑
Std.Parse + Std.Lex
        ↑
`parse` grammar macro and hand-written Cure parsers
        ↑
Cure source lexer/parser
```

The compiler parser becomes a client of public libraries. It does not define a
parallel parsing or diagnostic framework.

---

## 2. Release boundary

This work is user-facing 0.35 scope. It is not required for the 0.34
dependent-type rewrite.

The 0.34 branch implements the shared diagnostic model, source-caret and
machine renderers, elaboration/kernel diagnostics, and macro provenance defined
by the 2026-07-20 specification. It must not expand into completing `Std.Parse`
or parser self-hosting merely because those future libraries make useful test
cases.

0.35 starts only after the 0.34 dependent elaborator, erasure model, and code
generation path are stable enough to serve as the implementation platform.

---

## 3. Product outcomes

### 3.1 Public parsing platform

Users can write parsers in Cure itself with:

- totality checked at compile time;
- first-class parser values;
- applicative and monadic/context-sensitive composition;
- typed lexer and parser results;
- precise spans and structured failures;
- farthest-failure selection and useful expectation sets;
- identical libraries on BEAM and AtomVM, subject to the device gates;
- no runtime syntax interpreter or parser-specific compiler privilege.

### 3.2 Elm-class syntax diagnostics

The source parser and user parsers can produce diagnostics with:

- a stable diagnostic code;
- severity;
- primary and secondary labelled spans;
- source excerpts and carets;
- notes and actionable suggestions;
- deterministic rendering in terminal and test output;
- a machine-readable representation for editor/LSP consumers;
- provenance through generated/desugared syntax where applicable.

“Elm-class” here means errors organized around what the user wrote and what
they can do next, not raw parser states, token dumps, or internal tuples.

### 3.3 Cure's parser as proof by use

Cure's own lexer and parser are implemented in Cure using the same public
facilities. They provide a demanding real-world validation of:

- layout and indentation;
- contextual keywords;
- recovery and multiple diagnostics;
- nested and interpolated syntax;
- source preservation required by formatting and migration tools;
- performance on large modules;
- stable AST production across bootstrap boundaries.

---

## 4. Important distinction: syntax diagnostics are not type diagnostics

Self-hosting the source parser can deliver Elm-class lexer and syntax errors.
It does not, by itself, deliver Elm-class elaboration errors or typed-hole-driven
development.

Compiler-wide type diagnostics additionally require the elaborator, unifier,
coverage checker, totality checker, and kernel rejection path to emit structured
diagnostics with retained surface provenance. Typed holes additionally require
metavariables to expose their local telescope, expected type, constraints, and
candidate terms.

Those facilities share `Compiler.Diagnostic` and should be developed in the
same 0.35 program, but they are separate clients:

```text
                    ┌─ lexer/parser diagnostics
Compiler.Diagnostic ├─ elaboration/unification diagnostics
                    └─ typed-hole reports and editor actions
```

Completion claims must preserve this distinction. “The parser is self-hosted”
must never be reported as “typed-hole development is complete.”

---

## 5. Shared diagnostic foundation

The parked compiler-error cleanup spec is expanded into a real presentation
and tooling model rather than a one-line formatter.

The public representation must support at least:

```text
Diagnostic
  code        stable identifier
  severity    error | warning | information | hint
  message     concise summary
  primary     labelled source span
  secondary   zero or more labelled spans
  notes       explanatory text
  suggestions zero or more edits/replacements
  provenance  source/desugaring/macro expansion chain
  payload     domain-specific structured data
```

Requirements:

1. Rendering is separate from diagnostic construction.
2. Human and machine renderers consume the same value.
3. Stable codes survive wording improvements.
4. Source spans use one canonical byte/line/column convention.
5. A diagnostic may be constructed without a span when no honest source
   location exists; invented locations are forbidden.
6. Internal Core terms are not the default user presentation. Types and names
   are re-presented using stable surface vocabulary where possible.
7. Diagnostic metadata must not participate in conversion, normalization, or
   any accept-path soundness decision.

`Std.Parse.Error` is a domain-specific failure model convertible into this
shared `Diagnostic`; it is not a second diagnostic framework.

---

## 6. `Std.Lex`, `Std.Parse`, and error semantics

Complete the total parsing design as the public execution substrate:

- strict-consumption algebra and proof erasure;
- list/token and binary/string input instances;
- total lexer recognizers and token maps;
- direct first-class parsers;
- applicative, alternative, repetition, and monadic composition;
- accessibility-driven recursive runners;
- bounded tokens and source spans;
- structured expected/unexpected/end-of-input/user errors;
- farthest-failure merging;
- controlled recovery with guaranteed progress.

Recovery must be progress-safe. A recovery rule that retries without consuming
or terminating is rejected by construction, just as `many` over a possibly
empty parser is rejected.

The `parse` grammar macro lowers to these ordinary Cure definitions. Generated
runtime code contains direct compiled parser behavior, not a grammar AST
interpreter or runtime macro dispatcher.

---

## 7. Cure source parser migration

The migration is semantic-preservation work, not an opportunity to redesign
the language grammar accidentally.

### 7.1 Required compatibility

For the accepted 0.35 source language, the old and new pipelines must agree on:

- token boundaries and layout;
- contextual-keyword decisions;
- accepted/rejected verdicts;
- canonical AST after trivia is excluded;
- trivia-preserving syntax representation where requested;
- diagnostic location convention;
- macro and migration-tool inputs.

Intentional diagnostic improvements may change wording and recovery count, but
must not silently change the accepted language. Any grammar change requires its
own explicit language decision and fixtures.

### 7.2 Migration shape

1. Implement the Cure-native lexer/parser beside the existing Elixir pipeline.
2. Differentially run both over the repository, fixtures, oracle programs, and
   generated/mutated source corpora.
3. Make the Cure-native pipeline the default only after semantic parity and
   performance gates pass.
4. Retain the old path temporarily as a comparison/bootstrap fallback.
5. Delete the duplicate implementation once the bootstrap artifact and rollback
   story are proven.

No permanent “fast compiler parser” versus “public library parser” fork is
allowed. Performance work belongs in the shared library or generated parser.

---

## 8. Bootstrap strategy

A compiler needs a parser before it can compile the parser's Cure source. The
bootstrap loop must therefore be explicit and reproducible.

Preferred strategy:

1. Check in or release a compiler-generated parser artifact produced from the
   canonical Cure parser sources by the immediately preceding trusted compiler.
2. A bootstrap build loads that artifact to compile the current sources.
3. The current compiler recompiles the canonical parser sources.
4. A reproducibility gate compares the rebuilt artifact or its normalized Core/
   BEAM representation against the expected bootstrap output.

The artifact is derived output, not a second handwritten parser. Its producer
version, source hash, target, and format version must be recorded.

Until this is reliable, the existing Elixir parser may serve as a temporary
stage-0 bootstrap implementation. It must have a deletion gate and must not
remain the semantic authority after the Cure-native parser becomes default.

---

## 9. Typed holes and type-error development

The shared diagnostic work should enable, but not conflate, a parallel typed
hole track.

A useful typed-hole diagnostic contains:

- hole name and stable identity;
- exact source span;
- expected type in surface form;
- local variables with types, quantities, and relevance;
- unsolved constraints that genuinely affect the hole;
- in-scope constructors/functions that typecheck as candidates;
- suggested applications when arguments remain;
- machine-readable edits for editor insertion.

Candidate generation is untrusted search. Every proposed term must pass the
ordinary elaborator and kernel before presentation as a valid solution.

Parser self-hosting is not blocked on sophisticated hole synthesis. It is
blocked only on the common diagnostic/spans foundation required to report
syntax failures consistently.

---

## 10. Ordered implementation phases

### Phase A — diagnostic core

- Audit current lexer, parser, elaborator, kernel, coverage, and totality errors.
- Land the structured diagnostic value and human/machine renderers.
- Establish canonical spans and source-file storage.
- Convert high-value opaque errors without changing verdicts.

### Phase B — provenance and typed-hole minimum

- Retain source provenance through parsing and elaboration boundaries.
- Report typed holes with expected type and local context.
- Provide editor-readable diagnostic and hole output.

### Phase C — total parsing substrate

- Complete `Std.Data.Suffix`, proof erasure, `Step`, and accessibility runners.
- Complete `Std.Lex`, `Std.Parse`, and `Std.Parse.Error`.
- Verify binary/list representations and progress-safe recovery.

### Phase D — `parse` lowering

- Lower grammar blocks to the public parsing library.
- Remove any duplicate runtime grammar machinery.
- Make grammar-authored and hand-written parser diagnostics converge.

### Phase E — Cure-native source lexer/parser

- Port lexer, layout, parser, and trivia/provenance production.
- Run differential corpus and mutation gates.
- Meet compile-time and memory budgets.

### Phase F — bootstrap and cutover

- Produce and verify the bootstrap parser artifact.
- Switch the compiler default to the Cure-native pipeline.
- Exercise rollback once.
- Delete the old semantic implementation after the stabilization window.

### Phase G — Elm-class compiler diagnostics

- Continue structured conversion across elaboration, unification, coverage, and
  totality.
- Add recovery/accumulation where continuing is sound and useful.
- Add suggestions and typed-hole candidate actions.

Phases A–F establish self-hosted parsing. Phase G establishes the broader
Elm-class type-development experience; portions of B and G may proceed in
parallel once A is stable.

---

## 11. Verification gates

The initiative is incomplete until all applicable gates pass:

1. **Verdict parity:** old/new parser accept/reject agreement over repository,
   fixtures, oracle corpus, and generated source corpus.
2. **AST parity:** normalized AST equality for every accepted comparison input.
3. **Round-trip/trivia:** formatter and migration fixtures retain required
   comments and source structure.
4. **Diagnostic snapshots:** malformed-program corpus covers layout, recovery,
   expected sets, secondary labels, suggestions, and stable codes.
5. **Progress:** recovery and repetition cannot loop on zero consumption.
6. **Erasure:** parsing proofs and accessibility witnesses do not allocate or
   dispatch at runtime.
7. **Performance:** agreed time and peak-memory budgets on representative small,
   large, generated, and adversarial modules.
8. **Bootstrap reproducibility:** stage-0 can build stage-1; stage-1 rebuilds the
   parser artifact reproducibly under the chosen normalization rule.
9. **Unix BEAM:** full compiler/test/tooling suite through the new default path.
10. **Unix AtomVM and hardware:** public parser examples and the supported
    binary/UTF-8 subset run correctly; unsupported VM behavior is documented or
    removed from the portable contract.
11. **No semantic fork:** only one authoritative grammar and one public parsing
    implementation remain after cutover.

---

## 12. Non-goals

- Completing this work in 0.34.
- Replacing the entire compiler implementation with Cure in one release.
- Treating parser self-hosting as proof that type diagnostics are complete.
- Making diagnostic metadata part of trusted type equality or normalization.
- Trusting hole synthesis, recovery heuristics, or external solvers to admit a
  program without ordinary elaboration and kernel checking.
- Shipping a permanent runtime grammar interpreter.
- Maintaining two independently evolving Cure grammars.
- Requiring the polished diagnostic UI before general 0.34 dependent-type
  correctness fixes can land.

---

## 13. Parked-state resumption checklist

When 0.35 work begins:

1. Re-audit the then-current parser, diagnostic, LSP, and elaborator state.
2. Reconcile this spec with any completed portions of the three related specs.
3. Confirm the bootstrap artifact policy and repository/release placement.
4. Set explicit parser performance and diagnostic snapshot baselines.
5. Turn the phases above into an ordered implementation plan with commits and
   verification gates.

Until then, this document records direction and boundaries only. It does not
authorize pulling user-facing parser or diagnostic expansion into the 0.34
dependent-type rewrite.

# Structured Compiler Diagnostics for Cure 0.34

**Status:** authoritative design; required for 0.34

**Date:** 2026-07-20

**Applies to:** lexer/parser errors used by the current compiler, macro
expansion, elaboration, unification, coverage, totality, kernel rejection,
code generation, project/release verification, CLI output, tests, Antigen, and
LSP/machine consumers

**Does not include:** Cure-native parser self-hosting, the public `Std.Parse`
platform, or replacement of the current parser implementation. Those remain
0.35 work.

**Mandatory human-presentation subsidiary:**
[`2026-07-20-elm-quality-compiler-diagnostics-design.md`](2026-07-20-elm-quality-compiler-diagnostics-design.md).
It makes the document algebra, exact-range ownership, contextual syntax/type
reports, Elm-style snippet layouts, and presentation verification gates
normative for this work.

## 1. Decision

Cure 0.34 will ship a shared structured diagnostic foundation before the
remaining `actor`, `fsm`, `sup`, and `app` macro implementation is completed.

This work was previously parked as presentation polish. That classification is
no longer accurate. Repeated bare failures such as `:unknown_global` discard
information already available to the compiler and force developers to trace or
instrument rejection paths merely to discover which name failed. Macro
expansion compounds the problem because a generated declaration may fail far
from the authored section responsible for it.

Diagnostics are therefore implementation infrastructure for 0.34. They are
not allowed to alter which programs are accepted, weaken kernel checking, or
introduce diagnostic metadata into definitional equality.

The architecture combines three precedents:

- **Elixir:** `Code.diagnostic/1`, `Code.with_diagnostics/2`,
  `Code.print_diagnostic/2`, `Kernel.ParallelCompiler`, and
  `Mix.Task.Compiler.Diagnostic` define the host-facing diagnostic envelope,
  capture path, coordinate conventions, and Mix/editor integration.
- **Gleam:** domain errors are converted into one shared diagnostic value used
  by both source-caret terminal rendering and LSP output.
- **Racket:** syntax carries source identity independently from expansion
  origin; generated syntax tracks an origin chain, and an error can blame a
  precise subform while retaining its enclosing form and additional sources.
- **Cure:** stable codes, typed/domain payloads, machine-applicable edits,
  macro expansion provenance, and dependent-type context are first-class.

## 2. Product requirement

A diagnostic must answer, without compiler tracing:

1. What failed?
2. Which authored source should the user change?
3. What other source locations explain the failure?
4. What expansion/desugaring path produced the checked term?
5. What did the compiler expect and observe?
6. What safe action can the user take next?
7. Which stable code identifies this condition for tests, tools, and docs?

For example, a missing type in a generated supervisor module must not be:

```text
{:lift_module_error, "App.Root", :unknown_global}
```

It must retain at least:

```text
E??? Unknown type

The generated declaration refers to `SupervisorHandle`, but that type is not
available in this scope.

  primary:   the authored `sup App.Root` section responsible for the declaration
  secondary: the generated `type Handle = ...` declaration or template label
  expansion: sup App.Root -> derive_supervisor_family -> generated Handle alias
  note:      this occurred while checking generated module App.Root
```

The exact renderer wording may improve without changing the stable code or
structured payload.

## 3. Non-negotiable invariants

### 3.1 Rejection-path only

Diagnostic construction, spans, notes, suggestions, and provenance do not
participate in:

- conversion or normalization;
- unification success;
- coverage acceptance;
- totality acceptance;
- erasure or runtime representation;
- emitted runtime control flow.

Removing all diagnostic metadata from a compilation must leave its accept or
reject verdict unchanged.

### 3.2 Information is retained at the point of knowledge

An error producer must not collapse known information into a bare category.
If a producer knows the missing name, expected type, conflicting declaration,
source syntax, or module, it records it immediately.

A renderer is not responsible for reconstructing discarded semantic facts.

### 3.3 Construction and rendering are separate

Compiler phases produce structured diagnostics. They do not hand-format
terminal strings. Terminal, plain-text snapshot, JSON/machine, and LSP
renderers consume the same diagnostic value.

### 3.4 Honest locations

An unavailable location is represented as absent. The compiler must never
invent line 0, column 0, the beginning of a file, or a generated file path as
if it were authored source.

Generated context may be recorded by a template label or generated span, but it
must not displace an available authored primary span.

### 3.5 Authored blame comes first

For expansion failures, the primary label identifies the smallest authored
syntax that can be changed to fix the problem. Generated syntax and outer macro
invocations are secondary context. Internal Core is never the default user
presentation.

### 3.6 Macro abstraction is preserved in diagnostics

A user invoking a macro receives a diagnostic in the vocabulary of that
macro, not a raw parser, elaborator, kernel, or code-generation failure from
its expansion. The default terminal and editor presentation names the macro,
identifies the authored invocation or captured argument, and explains the
failed macro-level obligation.

The compiler still retains the complete underlying diagnostic and generated
source/provenance chain for compiler debugging, verbose output, and machine
consumers. Retaining that evidence must not leak implementation details into
the default user presentation.

There are three blame cases:

- If an invocation violates the macro's declared grammar, categories, or
  verifier rules, the macro's declared diagnostic is primary.
- If authored syntax captured by the macro is semantically invalid, the
  diagnostic describes that semantic error at the captured authored syntax
  and states the macro role in which it was checked.
- If only compiler-generated syntax is invalid, the diagnostic reports a macro
  implementation/compiler defect at the invocation and offers the expansion
  failure only as diagnostic context. It must not instruct the user to edit
  generated code they cannot see or own.

Consequently, an expansion-internal code may be recorded as a cause, but it is
not the public primary code when a macro-specific code applies.

### 3.7 Compatibility is by code, not tuple shape or prose

Tests, Antigen assays, CLI integrations, and editor clients match stable
diagnostic codes and structured fields. They must not require exact internal
error tuple arity or prose, except dedicated rendering snapshots.

## 4. Canonical data model and Elixir envelope

Cure does not invent a second BEAM-facing compiler diagnostic protocol.
`Cure.Diagnostic` is the richer canonical semantic value, and it projects
losslessly into Elixir's compiler diagnostic envelope by storing the complete
Cure value in `:details`. `Code.diagnostic/1` and
`Mix.Task.Compiler.Diagnostic` are host integration formats, not replacements
for Cure's typed payload.

The shared fields deliberately align:

| Cure | Elixir `Code.diagnostic` / Mix |
| --- | --- |
| `severity` | `:severity` |
| primary path | `:file` |
| authored/root path | `:source` |
| primary start | `:position` |
| primary end | `:span` |
| rendered title/message | `:message` |
| complete diagnostic | `:details` |

The host envelope cannot represent multiple labelled ranges, structured edits,
stable codes, typed semantic payloads, or expansion provenance directly. Those
remain in `:details` and in Cure's JSON/LSP projections.

The implementation language may use Elixir structs internally, but the model
is language-neutral and serializable.

### 4.1 Span

```text
Span
  source_id     stable identifier for a source buffer
  path          optional user-facing path
  start_byte    zero-based byte offset, inclusive
  end_byte      zero-based byte offset, exclusive
  start_line    one-based line, matching Code.position
  start_column  one-based Unicode scalar column, matching Code.position
  end_line      one-based line, matching Code.diagnostic :span
  end_column    one-based Unicode scalar column, matching Code.diagnostic :span
```

Byte offsets are authoritative for slicing. Line/column values use Elixir's
one-based `Code.diagnostic` convention and are cached presentation coordinates
derived under one canonical UTF-8 and tab-width policy. At LSP initialization,
the server advertises UTF-8, UTF-16, and UTF-32 position support and prefers
UTF-8 when the client offers it. The LSP adapter converts columns to zero-based
offsets in the negotiated encoding; UTF-16 is the protocol fallback for clients
that do not negotiate. A zero-width span is allowed for insertion suggestions.

Source buffers are stored once in a compilation source registry and referenced
by `source_id`; diagnostics do not copy the complete source string per label.

### 4.2 Label

```text
Label
  span       Span
  message    optional concise explanation
  style      primary | secondary
```

A diagnostic has zero or one primary label and any number of secondary labels.
Secondary labels may refer to different files. Examples include the original
declaration in a duplicate error, the other side of a type conflict, or the
macro definition that generated a failing declaration.

### 4.3 Provenance frame

Source location and expansion origin are distinct.

```text
ProvenanceFrame
  kind          source | desugaring | macro_expansion | generated_declaration
  name          operation/macro/declaration name
  invocation    optional authored Span
  definition    optional macro/template Span
  generated     optional generated Span or stable template label
  parent        optional previous frame identity
```

The ordered provenance list runs from the nearest generated operation back to
the authored root. Cycles are impossible; repeated expansion frames are
permitted when distinct invocations are involved.

### 4.4 Suggestion and edit

```text
Suggestion
  message       actionable explanation
  applicability machine_applicable | maybe_incorrect | manual
  edits         zero or more TextEdit

TextEdit
  span          Span
  replacement   UTF-8 text
```

An edit is machine-applicable only when applying all edits atomically is known
to preserve parse structure and directly addresses the diagnosed condition.
Name-distance guesses and imports with multiple plausible owners are not
machine-applicable.

### 4.5 Diagnostic

```text
Diagnostic
  code          stable public identifier such as E123 or W045
  key           stable internal atom such as unknown_global
  severity      error | warning | information | hint
  title         concise summary
  message       explanatory prose
  primary       optional Label
  secondary     list of Label
  notes         list of explanatory strings
  suggestions   list of Suggestion
  provenance    list of ProvenanceFrame
  payload       code-specific serializable data
```

`payload` retains facts needed by tools and tests, for example:

```text
unknown name:
  namespace: value | type | constructor | module | interface | field
  name: qualified or unqualified source spelling
  candidates: visible candidate names and owners
  checking: optional declaration/module name

conversion failure:
  expected_surface
  actual_surface
  expected_core (debug-only machine field)
  actual_core   (debug-only machine field)

duplicate declaration:
  name
  first_span
  duplicate_span
```

Debug-only fields are omitted from ordinary human rendering unless verbose
diagnostics are requested.

## 5. Error production architecture

### 5.1 Domain errors remain typed

Parser, resolver, elaborator, unifier, coverage checker, totality checker,
kernel, macro verifier, and release builder retain domain-specific error
variants. Each variant carries semantic facts at its creation site.

At a phase boundary the domain error is converted into `Diagnostic`. This
keeps algorithms readable while giving every consumer one presentation model.

### 5.2 No bare error atoms in new code

New error-producing code must return a payload-bearing domain error or a
`Diagnostic`. Bare atoms may remain temporarily only behind a migration adapter
that maps them to a stable code and records that their detail is unavailable.

No new macro verifier may return only `:invalid_graph`, `:unknown_child`, or
`:ambiguous_transition`. It must name and locate the relevant declarations.

### 5.3 Diagnostic conversion is exhaustive

There is no generic domain-error catch-all and no public "unclassified error"
diagnostic. Every error variant that a compiler phase can deliberately return
has an explicit conversion clause, registered stable code, payload schema, and
test. Adding a domain-error variant without its conversion fails development
and CI loudly through `Cure.Diagnostic.UnhandledError`; it must never silently
fall through to `inspect(reason)` or generic prose.

Actual host exceptions and impossible unexpected return shapes cross a
separate top-level crash boundary and become a stable Internal Compiler Error
diagnostic. That boundary accepts exceptions with stacktraces, not ordinary
domain-error terms, and therefore cannot conceal an incomplete converter.

### 5.4 Unknown-name errors

Unknown names are classified before rendering:

- unknown local/value;
- unknown type or type family;
- unknown constructor;
- unknown module;
- unknown module member;
- unknown interface or implementation;
- inaccessible/private name;
- ambiguous name;
- name available only in the other namespace;
- name available from an imported module but not exposed.

The producer records the original spelling, namespace, arity when relevant,
visible candidates, qualified owners, and source span.

The elaborator should diagnose unresolved surface names before emitting a Core
global whenever it has sufficient information. The kernel remains defensive:
an unregistered `{:global, name}` returns an error containing `name`, but no
source location is fabricated.

This avoids putting presentation metadata into trusted Core terms. The caller
may attach the nearest honest elaboration/declaration context to a locationless
kernel diagnostic.

### 5.5 Type and conversion errors

Expected and actual types are retained as semantic values until they can be
re-presented using surface syntax and stable names. The diagnostic may retain
Core forms in a debug payload, but the human message defaults to surface forms.

Dependent mismatches include relevant indices, normalized forms, local
telescope entries, and unresolved constraints without dumping unrelated
compiler state.

### 5.6 Multiple diagnostics and recovery

0.34 does not require global error recovery. A phase may still stop at its
first fatal diagnostic. Where a verifier already examines a closed collection
and can safely report independent failures, it may return multiple diagnostics
in deterministic source order.

No recovery heuristic may change acceptance or allow later phases to run on an
invalid trusted term.

## 6. Source and provenance propagation

### 6.1 Parsed syntax

Every authored AST node capable of receiving blame carries a canonical span.
Legacy line/column-only metadata is normalized at the parser boundary where
token end positions are available.

### 6.2 Generated syntax

Every syntax builder and macro expansion preserves or establishes:

- the span of captured authored syntax;
- the macro invocation span;
- the macro definition/template span when known;
- a stable template label for generated declarations;
- the parent provenance chain.

Copying an authored node preserves its authored identity. Constructing a new
node marks it generated and links it to the responsible invocation. Splicing an
authored node into generated syntax retains the authored node's primary span
while extending its expansion context.

This is Cure's equivalent of Racket's distinction between syntax source
location, `syntax-original?`, and `syntax-track-origin`.

### 6.3 Nested expansion

Inside-out expansion appends frames rather than replacing provenance. An error
inside `beam_ops` generated inside an actor generated inside an application can
report:

```text
beam_ops call
  expanded at actor Worker / on_message
  expanded at sup App.Root / child Worker
  expanded at app MyApp / root App.Root
```

Renderer defaults may collapse unhelpful frames, but machine output retains the
complete chain.

### 6.4 Lifted modules

`LiftModule` preserves provenance per declaration, not merely once on the
module request. A failure is wrapped with:

- generated module name and behavior;
- failing declaration name/kind when known;
- its authored origin and expansion chain;
- the underlying structured diagnostic unchanged.

`{:lift_module_error, module, reason}` with a detail-free `reason` is not an
acceptable final diagnostic.

### 6.5 Kernel boundary

Core terms remain free of renderer metadata. Kernel domain errors retain every
semantic fact known to the kernel, including the missing global name or the two
terms/types involved in a failed check. Source context is attached by the
elaboration/program boundary from the surface operation being certified.

If an error arises from independently supplied Core with no surface origin, the
diagnostic is honestly locationless and identifies the checked definition.

## 7. Rendering

### 7.0 Elixir and Mix adapters

Every `Cure.Diagnostic` can be converted to a `Code.diagnostic`-compatible map
and to `Mix.Task.Compiler.Diagnostic`. The adapter sets `:source`, `:file`,
`:position`, `:span`, `:severity`, and `:message`, retains an honest stacktrace
when one exists, and places the complete Cure diagnostic in `:details`.

BEAM compiler warnings and errors are captured with `Code.with_diagnostics/2`
or received from `Kernel.ParallelCompiler`; adapters preserve their original
`:details` rather than parsing formatted messages.

`Code.print_diagnostic/2` may render a simple, single-location diagnostic when
its output satisfies the Cure presentation contract. It is a fallback and host
interop path, not the canonical renderer: it cannot show Cure's cross-file
labels, macro provenance, structured suggestions, or unsaved source buffers.

### 7.1 Terminal renderer

The default terminal renderer provides:

- stable code, severity, and title;
- source path and location;
- source excerpt with line numbers;
- primary underline/caret and label;
- secondary underlines and labels, including other files;
- concise explanatory prose;
- notes and suggestions;
- a collapsed macro-expansion trace when present.

Example shape:

```text
error[E???]: Unknown type
  --> src/app.cure:18:7
   |
18 |   supervisor Workers as WorkersChild
   |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ this child generated the failing alias
   |
  ::: lib/std/supervisor.cure:47:5
   |
47 |     type Handle = SupervisorHandle
   |     -------------------------------- generated declaration checked here

`SupervisorHandle` is not available in the generated module's type scope.

Expansion: sup App.Root -> derive_supervisor_family -> Handle alias

Hint: import the defining module into the generated behavior module, or emit
the already imported unqualified type name.
```

Exact chrome is renderer policy; diagnostic content is structured.

#### 7.1.1 Elm-style human presentation

The canonical terminal presentation deliberately follows Elm's compiler-error
grammar. A diagnostic begins with a visually scannable banner:

```text
-- UNKNOWN VALUE [E091] -----------------------------------------------
```

The title is short, human, and uppercased by the renderer; it is never an
internal atom such as `unknown_global` or `file_read`. The stable Cure code
remains visible in the banner. Colour may distinguish the banner and marked
source, but the colour-free rendering must preserve the same hierarchy.

The banner is cyan for every severity. Severity colour is reserved for source
markers so the header remains a stable visual separator: error carets are red,
warning carets are yellow, and secondary markers are cyan.

Primary underlines cover the complete offending authored token or expression,
not merely its first column. A two-character arrow receives two carets; a
rejected call or expression receives one caret per displayed character across
its full span. Primary carets are red in a colour-capable terminal. Secondary
labels use a distinct marker and colour so related context cannot be mistaken
for the source of the error. ANSI styling is applied only to semantic emphasis
(the banner and markers), never to the entire paragraph.

After the banner, the renderer presents information in this order:

1. a diagnostic-specific explanation in the vocabulary of the authored Cure
   program;
2. the exact source as written, with line numbers and a precise underline;
3. secondary source excerpts where they materially explain the problem;
4. focused expected/observed information, hiding irrelevant type structure;
5. notes and concrete help, including a safe edit when one is known;
6. a collapsed expansion trace when macro provenance matters.

Whitespace separates these conceptual blocks. A path-and-coordinate line is
supporting navigation, not a substitute for showing the source. Locationless
diagnostics omit the excerpt honestly rather than inventing a position.

This is a semantic presentation requirement, not merely visual styling. An
uppercase banner wrapped around a raw tuple, Core term, generic category, or
unexplained `expected/got` pair does not satisfy it. Each public diagnostic
family owns human prose that explains what the user was trying to do, what
prevented it, and the most useful next action. Internal terms remain available
only in machine/debug payloads.

The repository maintains an error-message catalog driven by real failing Cure
programs. `mix cure.diagnostics` compiles those programs, prints their actual
user-facing diagnostics, and runs the catalog with coverage. A catalog case is
valid only when it asserts that compilation reached its intended stable code;
constructor-only examples supplement this catalog but cannot stand in for a
compiler-path proof.

### 7.2 Plain renderer

A deterministic color-free renderer supports tests, logs, and environments
without terminal capabilities. Paths and source roots are normalized in
snapshots.

### 7.3 Machine renderer

JSON/machine output contains all model fields with stable keys and offsets. It
does not parse information back out of human prose.

### 7.4 LSP renderer

The LSP adapter maps:

- primary label to the main diagnostic range;
- secondary labels to related information;
- stable code to `Diagnostic.code`;
- severity directly;
- machine-applicable suggestions to code actions;
- provenance frames to related information or diagnostic data.

Terminal and LSP consumers must not construct different semantic diagnostics.

### 7.5 Suggestions

Suggestions are scope- and namespace-aware. Candidate generation considers:

- edit distance;
- correct namespace;
- arity where applicable;
- visibility and package boundary;
- imported versus available-but-unimported modules;
- qualified escape hatches for ambiguity;
- constructor/type/value spelling conventions.

Private or inaccessible definitions are never suggested as directly usable.

## 8. Stable codes and compatibility

### 8.1 Code registry

Every public diagnostic has one registered code with:

- stable key and numeric spelling;
- severity;
- title;
- long explanation for `cure explain`;
- payload schema version;
- optional documentation link.

Renaming prose does not change a code. Splitting one semantic condition into
meaningfully different user actions may allocate new codes with a documented
migration.

### 8.2 Category extraction

Provide one compatibility helper that extracts the stable key/code from:

- a `Diagnostic`;
- `{:error, diagnostic}`;
- temporarily supported legacy error atoms/tuples.

Antigen and behavioral tests migrate to this helper before individual error
shapes are expanded.

### 8.3 Snapshot policy

Behavioral tests assert code and payload facts. Dedicated diagnostic snapshots
assert rendering, spans, labels, suggestions, and provenance. Ordinary tests do
not pin whole prose strings.

## 9. Macro-authored diagnostics

`Std.Syntax` exposes safe constructors for structured compile-time diagnostics.
A user-defined macro can report:

- stable macro-local key promoted through the compiler registry/namespace;
- message and notes;
- a primary captured syntax value;
- secondary captured syntax values;
- suggestions expressed as safe syntax replacements;
- inherited expansion provenance.

Macro authors do not forge arbitrary file paths or byte offsets. They select
captured syntax or generated template labels, and the compiler resolves those
to registered spans.

The existing `Failure(name, args)` representation is a migration floor, not the
final interface. It must lower into a structured diagnostic while preserving
all captured syntax arguments and provenance.

Every public macro must define or derive a diagnostic boundary that translates
expansion failures into its own stable diagnostic namespace. Standard macros
(`actor`, `fsm`, `sup`, and `app`) must cover every structural and semantic
failure exposed by their public contracts. A generic expansion failure is
permitted only as the macro-defect fallback described in section 3.6, and its
default rendering still names and blames the macro invocation.

## 10. Security, trust, and performance

- Diagnostics cannot affect kernel acceptance.
- Machine-applicable edits are untrusted convenience output.
- Candidate terms for typed holes or fixes must elaborate and kernel-check
  before being described as valid.
- Source registries avoid copying full buffers into every diagnostic.
- Provenance chains use shared immutable frame identities rather than copying
  entire syntax trees.
- Rendering is lazy and occurs after compilation has selected diagnostics.
- Sensitive absolute paths may be relativized by renderer policy without
  corrupting canonical source identity.

## 11. Required implementation order

### Phase A — reconciliation and audit

1. Update the parked diagnostic specs to point to this 0.34 decision.
2. Inventory error producers and consumers across compiler, tests, Antigen,
   CLI, LSP, and macros.
3. Record which errors retain name, namespace, expected/actual values, span,
   related span, and provenance.

### Phase B — shared model and compatibility

1. Implement `Diagnostic`, `Span`, `Label`, `ProvenanceFrame`, `Suggestion`,
   and `TextEdit`.
2. Implement stable code/category extraction for legacy and new errors.
3. Migrate Antigen and non-rendering tests away from exact legacy shapes.
4. Establish the code registry and `cure explain` integration.
5. Implement lossless `Code.diagnostic` and `Mix.Task.Compiler.Diagnostic`
   adapters with the Cure value retained in `:details`.

### Phase C — renderers and source registry

1. Implement canonical source-buffer registration and span conversion.
2. Implement terminal caret/multi-label rendering.
3. Implement deterministic plain and JSON renderers.
4. Connect LSP diagnostics and code actions to the same values.
5. Capture host compiler diagnostics through `Code.with_diagnostics/2` and
   `Kernel.ParallelCompiler` without scraping terminal prose.

### Phase D — name-resolution vertical slice

1. Expand kernel unknown-global errors to retain the name.
2. Diagnose surface name failures in resolver/elaborator with namespace and
   span before Core emission.
3. Add scope-aware suggestions and qualified/import hints.
4. Preserve generated declaration and macro provenance through `LiftModule`.
5. Convert unknown type/family/constructor/module/member cases.

This phase must eliminate tracing as the normal way to identify a missing name.

### Phase E — high-value type diagnostics

Convert conversion, application, implicit/metavariable, field, coverage,
totality, and FFI-boundary failures, prioritizing errors encountered by the
remaining macro implementation. Add surface type presentation and related
labels.

### Phase F — macro verifier diagnostics

Actor, FSM, supervisor, and application verifiers return structured,
multi-location diagnostics for duplicates, ambiguity, cycles, unknown modules,
invalid policies, dependency errors, and target exclusions.

### Phase G — completion audit

Remove migrated bare errors and adapters, verify code registry coverage, and
document any intentionally locationless errors. Parser self-hosting remains
outside this completion gate.

## 12. Verification gates

The 0.34 diagnostic foundation is complete only when:

1. **Verdict preservation:** before/after corpora have identical accept/reject
   verdicts.
2. **Unknown-name proof:** value, type, constructor, module, member, ambiguity,
   and wrong-namespace cases name the offender and point to authored source.
3. **Caret proof:** Unicode, tabs, multiline spans, zero-width insertions, and
   multi-file labels render correctly.
4. **Macro provenance proof:** nested user-defined expansion and each standard
   OTP macro report authored primary blame plus a complete machine provenance
   chain.
5. **Generated-module proof:** a lifted declaration failure identifies module,
   declaration, authored cause, and underlying diagnostic without tracing.
6. **Suggestion proof:** candidates respect namespace, arity, visibility,
   imports, and package boundaries; applicability is conservative.
7. **Machine parity:** terminal, JSON, and LSP outputs originate from the same
   diagnostic and agree on code and ranges.
8. **BEAM interop:** every Cure diagnostic round-trips through its
   `Code.diagnostic`/Mix envelope without losing its stable code, payload,
   labels, suggestions, or provenance from `:details`; captured BEAM
   diagnostics preserve their native details.
9. **Compatibility proof:** Antigen and behavioral tests use stable code/payload
   matching rather than legacy tuple arity.
10. **TCB gate:** kernel rejection-path changes pass trusted-core tests, complete
   Antigen, and prove no accepted verdict changed.
11. **Performance:** source/provenance retention stays within agreed compile-time
    and memory budgets on repository and generated macro corpora.
12. **Full suite:** formatter, warnings-as-errors, focused suites, and complete
    ExUnit are green.

## 13. Explicitly deferred to 0.35

The following remain governed by
`2026-07-17-cure-native-parser-diagnostics-self-hosting-design.md`:

- public `Std.Lex`, `Std.Parse`, and `Std.Parse.Error` completion;
- a Cure-native implementation of Cure's lexer/parser;
- parser bootstrap artifacts and differential cutover;
- general parser recovery and multiple syntax diagnostics;
- the full typed-hole candidate/action experience beyond the minimum data
  required by existing holes.

The shared model built in 0.34 is the foundation those features must reuse. A
second diagnostic framework is forbidden.

## 14. Reference implementation findings

### 14.1 Elixir

Elixir 1.15 and later provide a shared compiler diagnostic map through
`Code.with_diagnostics/2`, `Code.print_diagnostic/2`, and
`Kernel.ParallelCompiler`. Mix exposes the corresponding
`Mix.Task.Compiler.Diagnostic` for compiler tasks and editor integrations. The
model distinguishes authored `:source` from displayed `:file`, supports a
primary start/end range, carries an optional stacktrace, and reserves
`:details` for producer-specific structured information.

Cure adopts that envelope and its coordinate conventions. Cure retains its own
semantic value because the Elixir envelope has no stable codes, multiple
labels, structured edits, typed payload schema, or explicit macro provenance.

### 14.2 Gleam

The local Gleam compiler (`/Users/ch/Develop/gleam-gleam`) demonstrates:

- one `Diagnostic` consumed by terminal and LSP renderers;
- primary and cross-file secondary labels;
- byte-span source caret rendering through `codespan-reporting`;
- domain-specific unknown-name errors converted at the presentation boundary;
- scope-aware suggestions.

Cure adds stable codes, richer severity, structured edits, typed payloads, and
explicit provenance.

### 14.3 Racket

The local Racket implementation (`/Users/ch/Develop/racket`) demonstrates:

- syntax objects retaining source position and span;
- errors selecting an enclosing form and a more precise offending subform;
- multiple syntax sources attached to one exception;
- origin chains merged by `syntax-track-origin`;
- a distinction between authored and generated syntax.

Cure adopts the semantic separation of source span and expansion origin without
copying Racket's runtime syntax-object or exception architecture.

## 15. Related specifications

- `2026-07-20-elm-quality-compiler-diagnostics-design.md` (authoritative
  human-presentation architecture and completion gates)
- `2026-07-14-compile-time-reflective-beam-macros-design.md`
- `2026-07-10-compiler-error-expansion-design.md` (superseded for implementation
  scope by this document)
- `2026-07-12-elm-style-error-rendering-PARKED.md` (unparked and superseded for
  the 0.34 shared foundation)
- `2026-07-17-cure-native-parser-diagnostics-self-hosting-design.md` (still
  authoritative for the deferred 0.35 parser/public-library phases)

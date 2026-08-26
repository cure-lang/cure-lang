# Elm-Quality Compiler Diagnostics for Cure 0.34

**Status:** authoritative subsidiary specification; required for 0.34

**Date:** 2026-07-20

**Parent specification:**
[`2026-07-20-structured-compiler-diagnostics-design.md`](2026-07-20-structured-compiler-diagnostics-design.md)

**Reference implementation inspected:** local Elm compiler at
`/Users/ch/Develop/elm-compiler`, principally `Reporting.Doc`,
`Reporting.Report`, `Reporting.Render.Code`, `Reporting.Error.Syntax`,
`Reporting.Error.Type`, and `Reporting.Error.Canonicalize`.

## 1. Decision

Cure 0.34 diagnostics will meet Elm's standard of human explanation, not only
imitate Elm's banner and caret styling.

Every public compiler rejection must be represented as a structured semantic
report and rendered as an explanation of the user's authored program. A cyan
heading placed above a raw error tuple, generic `expected/got` message, Core
term, or one-character caret does not satisfy this requirement.

The implementation will add:

- a compositional, styled document algebra shared by every renderer;
- exact authored source ranges owned by lexer, parser, and semantic AST nodes;
- single, paired, separated, multiline, and cross-file source snippets;
- contextual syntax reports instead of token-expectation dumps;
- contextual type reports instead of unqualified actual/expected pairs;
- diagnostic-specific prose, notes, examples, and conservative suggestions;
- deterministic plain text and structured machine projections of the same
  semantic report;
- a compilation-driven catalog proving that each public error path produces
  its intended report.

This specification tightens the human-presentation requirements in section 7
of the parent specification. The parent's diagnostic model, stable-code rules,
macro abstraction boundary, provenance model, and rejection-path invariants
remain authoritative.

## 2. Product standard

A Cure diagnostic is successful only when a programmer unfamiliar with the
compiler implementation can answer:

1. What part of my source is being discussed?
2. What was I trying to do there?
3. Why is that operation invalid?
4. When two things disagree, where did each one come from?
5. What is the smallest useful next action?

The default presentation speaks in surface Cure vocabulary. Names such as
`vdata`, metavariable identifiers, elaborator phases, quoted Core tuples,
generated Erlang forms, and internal exception names are excluded unless the
user explicitly requests verbose compiler-debug output.

The standard is semantic as well as visual. Diagnostics must retain the
context needed to write a specific explanation at the point where that context
is known. The renderer must never be asked to infer the user's intent from an
opaque term after the fact.

## 3. Normative presentation grammar

### 3.1 Banner

Every terminal report starts with one cyan banner:

```text
-- TYPE MISMATCH [E093] ------------------------------- src/main.cure
```

The rules are:

- the title is concise, human, and uppercase;
- the stable diagnostic code is always present;
- the source path, when available, is right-aligned after the fill;
- the whole banner is cyan for errors, warnings, information, and hints;
- severity is expressed by the code and source-marker colour, not by changing
  the banner colour;
- a narrow terminal may shorten the fill, but must not discard the title,
  code, or path;
- absolute paths under the project root are displayed project-relative;
- a locationless diagnostic omits the path honestly.

### 3.2 Explanatory order

The renderer presents blocks in this order when applicable:

1. diagnostic-specific introductory prose;
2. the primary source snippet;
3. prose connecting the primary location to related evidence;
4. related or secondary source snippets;
5. a focused semantic comparison such as two types;
6. a `Note:` or `Hint:` paragraph;
7. actionable suggestions or edits;
8. a collapsed macro-expansion summary.

Blocks are separated by blank lines. Paragraphs reflow to an 80-column target
without reflowing source, code fragments, tables, or edit previews.

### 3.3 Colour

Colour has semantic meaning and is never the only carrier of meaning:

- banner: cyan for every severity;
- primary error marker: red;
- primary warning marker: yellow;
- primary information or hint marker: cyan;
- secondary marker: cyan;
- suggested replacement: green where an edit preview distinguishes removal
  and addition;
- ordinary prose and source text: terminal default;
- selected names or types: restrained semantic emphasis, never whole-paragraph
  colouring.

The plain renderer removes ANSI styling without changing text, ordering, or
markers. The normal CLI enables colour only for a capable terminal. Explicit
`always`, `never`, and `auto` policies are supported; the diagnostics showcase
may use `always` for intentional visual inspection.

### 3.4 Source markers

For a single-line primary range, the underline covers the complete displayed
range. An unexpected `->` receives two carets. A rejected expression receives
one caret for each displayed terminal column occupied by that expression.

```text
12 |   transform(value)
   |   ^^^^^^^^^^^^^^^^ this expression has the wrong type
```

The underline width is at least one terminal column. Tabs and Unicode are
measured by the canonical display-width policy, not byte count or UTF-16 code
units.

For a multiline range, Cure follows Elm's readable gutter treatment rather
than drawing enormous rows of carets. Every relevant displayed source line is
marked with a red `>` in the gutter, and the first or last line may additionally
carry a focused underline when a smaller blamed subrange exists.

Long snippets elide irrelevant middle lines deterministically. Elision never
removes a labelled boundary or a line necessary to understand indentation.

### 3.5 Multiple locations

The renderer supports four source layouts:

- **single:** one primary range and its label;
- **same-line pair:** two distinct ranges on one source line, each retaining
  its own label and marker;
- **separated pair:** two snippets from one file with connecting prose;
- **cross-file:** primary and related snippets with a path banner for each
  additional source.

Duplicate declarations, incompatible branches, annotation/body disagreement,
and macro definition/invocation failures use paired evidence when both
locations materially explain the problem. They must not flatten both locations
into prose-only coordinates.

Overlapping labels are laid out on separate marker rows in deterministic
primary-then-source-order. Marker labels must not overwrite source text or one
another.

### 3.6 Navigation and source availability

The banner path and snippet line numbers provide navigation. A separate
`--> path:line:column` line is optional compatibility chrome, not a substitute
for a snippet and not required in the canonical Elm-style renderer.

Unsaved editor buffers come from the compilation source registry. Rendering
must not reread a changed file when the diagnostic refers to the registered
buffer. If source text is unavailable, the report keeps its prose and honest
location without fabricating a source line.

## 4. Document architecture

### 4.1 Semantic report

The parent `%Cure.Diagnostic{}` remains the public semantic envelope. Its human
content is expressed as a document tree rather than one interpolated string:

```text
Diagnostic
  code, key, severity, title
  primary, secondary
  body          Doc
  notes         [Doc]
  suggestions   [Suggestion]
  provenance, payload
```

During migration, the existing string `message` may project to `Doc.text`, but
no newly migrated diagnostic may rely on parsing, regular expressions, or ANSI
escape injection to recover structure from that string.

### 4.2 Document algebra

`Cure.Diagnostic.Doc` provides at least:

```text
empty
text(string)
concat(documents)
line
blank_line
paragraph(inlines)
stack(blocks)
indent(columns, document)
code(string)
emphasis(role, document)
note(document)
hint(document)
bullet_list(items)
```

Semantic emphasis roles include `name`, `type`, `keyword`, `expected`,
`observed`, `addition`, and `removal`. Roles are not terminal colours; each
renderer decides how to represent them.

The algebra owns wrapping and layout. Domain converters compose documents;
they do not calculate padding, line breaks, or ANSI sequences.

### 4.3 Renderers

All renderers consume the same `Diagnostic` and document tree:

- terminal renderer: styled, width-aware output and source snippets;
- plain renderer: deterministic snapshots and redirected CLI output;
- JSON renderer: stable semantic blocks, labels, edits, payload, and
  provenance, not a terminal string disguised as JSON;
- LSP adapter: primary range, related information, code, severity, and code
  actions;
- Elixir/Mix adapter: host envelope with the complete Cure diagnostic in
  `details`.

There is no parallel store of terminal-only meaning. A fact needed by terminal
prose must remain available to machine consumers as a structured field or
code-specific payload fact.

### 4.4 Width and determinism

The terminal width defaults to 80 columns and may be overridden by renderer
options or detected terminal width. Snapshot tests always supply an explicit
width. Rendering is deterministic across machines after path normalization and
colour removal.

## 5. Exact source ownership

### 5.1 Lexer ranges

Every token records an exclusive end byte and end source coordinate. Operator
ranges cover the entire operator. Literal ranges include delimiters when the
diagnostic concerns the literal as a whole and exclude them when it concerns
only literal content.

The current fixed token-width lookup is a migration bridge only. Completion
requires deleting it from normal diagnostic construction. Width is derived
from token ranges or an explicitly selected authored AST range.

### 5.2 Parser ranges

Parser nodes cover their complete authored constructs. The parser also retains
the narrow token or insertion point responsible for a failure. An error can
therefore distinguish:

- the unexpected token (`at`);
- the construct being parsed (`within`);
- the previous or opening token that provides context;
- a zero-width location where missing syntax should be inserted.

This matches the macro diagnostic distinction between the precise blamed
subform and its enclosing form.

### 5.3 Semantic ranges

Resolver and elaborator operations receive the surface range of the construct
being resolved or checked. Calls retain ranges for the callee, every argument,
and the whole application. Branches retain pattern, guard, and body ranges.
Annotations retain both annotation and declaration-body ranges.

Generated nodes preserve authored captures and expansion provenance according
to the parent specification. Generated ranges never displace an available
authored range.

### 5.4 Display coordinates

Byte offsets remain authoritative for slicing. The renderer converts the
selected UTF-8 slice to terminal display columns using one tested policy for:

- tabs;
- combining marks;
- wide characters;
- emoji sequences;
- invalid UTF-8 recovery at lexer failure;
- zero-width insertion spans.

LSP UTF-16 conversion remains an adapter concern and never determines terminal
caret width.

## 6. Syntax diagnostics

### 6.1 Structured syntax error family

The parser retains a structured error family describing the grammar operation,
not merely an expected token set. It includes contexts for at least:

- modules, imports, exports, and aliases;
- declarations, signatures, definitions, and decorators;
- type applications, arrows, records, tuples, and typeclass constraints;
- calls, operators, pipelines, lambdas, let/case/if expressions, and blocks;
- lists, tuples, records, record updates, fields, and patterns;
- literals, interpolation, escapes, indentation, and delimiters;
- macro/container headers, sections, productions, and captured syntax.

Each error retains the precise problem variant, `at` range, `within` range,
relevant opener or previous token, observed token kind and spelling, and only
the expected alternatives useful for explaining the repair.

### 6.2 Report conversion

Every deliberate parser error variant has an explicit report-conversion
clause. There is no public generic `syntax error: expected X, got Y` fallback.
The converter may share prose helpers, but each variant must select an
actionable explanation appropriate to its grammatical context.

Examples should explain structure:

```text
-- UNFINISHED FUNCTION CALL [E...] ----------------------- src/main.cure

I reached the end of this indented block while reading the arguments to
`transform`.

3 |   transform(value
  |            ^^^^^ the call starts here but never closes

Hint: add `)` after `value`.
```

If the parser knows the exact missing delimiter and insertion point, the
suggestion is machine-applicable. If several repairs are plausible, it gives
examples or a manual hint rather than asserting one edit.

### 6.3 Lexical inspection

Where a token has not yet been constructed, the diagnostic layer may inspect
the registered source at the parser cursor to identify the complete keyword,
operator, name, delimiter, or character sequence. This inspection is
read-only, deterministic, and used only to improve rejection reporting.

It must not duplicate or influence the accepting lexer. Once a lexer token
exists, its recorded range and spelling are authoritative.

## 7. Type diagnostics

### 7.1 Context is part of the error

A type failure records more than actual and expected types:

```text
TypeProblem
  category
  context
  subject_span
  expected
  observed
  expectation_origin
  related_spans
  local_environment_summary
  unresolved_constraints
```

Required expression categories include calls, lambdas, operators, records,
record access/update, tuples, lists, literals, locals, foreign calls, cases,
patterns, annotations, constructors, effects, and macro-generated obligations.

Required contexts include:

- function result;
- numbered function argument and total arity;
- operator left or right operand;
- condition;
- numbered conditional or case branch;
- list element;
- tuple element;
- record field and record update;
- pattern and guard;
- annotation/body disagreement;
- constructor parameter or index;
- implicit argument and unresolved constraint;
- FFI encode/decode boundary;
- actor message/state handler role;
- FSM state/event/payload/transition role;
- supervisor child or application phase role.

### 7.2 Expectation origin

The producer records why a type was expected: an annotation, function domain,
operator declaration, branch sibling, pattern, interface member, macro
contract, or surrounding expression. When that origin has authored source, it
is a secondary label.

This enables reports such as “The second argument to `map` has the wrong type”
and “The annotation says this function returns `Text`” instead of the generic
“expected Text, got Integer.”

### 7.3 Surface type presentation and comparison

Types are localized and reified to stable surface Cure syntax before ordinary
human rendering. The comparison algorithm:

1. normalizes only as required to make the disagreement intelligible;
2. uses source-visible names and respects aliases when helpful;
3. identifies the smallest differing substructure;
4. suppresses identical surrounding structure when that improves clarity;
5. distinguishes parameters from indices and explicit from implicit values;
6. gives unresolved metavariables human roles rather than raw numeric names;
7. retains complete Core forms only in debug payloads.

Expected and observed are separate styled document fragments, not one
interpolated sentence. Differences can therefore be emphasized consistently
in terminal, plain, JSON, and editor views.

### 7.4 Dependent-type context

Dependent mismatches additionally retain:

- relevant indices before and after normalization;
- the local telescope entries actually referenced by the mismatch;
- stuck computations and the constraints blocking them;
- the declaration or constructor establishing the expected index;
- whether a value is implicit, erased, or runtime-relevant when that affects
  the repair.

The default report explains the surface disagreement first. A concise note may
explain a stuck index computation. Full Core and constraint dumps require
verbose/debug mode.

## 8. Name, declaration, and canonicalization diagnostics

Unknown, ambiguous, inaccessible, duplicate, shadowed, arity, import/export,
fixity, and namespace errors each own diagnostic-specific reports.

Suggestions are ranked using namespace, scope, visibility, qualification,
arity, imports, package boundary, and spelling distance. The report explains
whether the proposed name is immediately usable, needs qualification, or
requires an import. An inaccessible name is never presented as a directly
usable correction.

Duplicate and conflicting declarations show both locations. Arity reports
state the declared arity, observed arity, and the range of the relevant
application or type use. Operator-mixing reports show the conflicting operator
regions and offer parentheses only where grouping is semantically unambiguous.

## 9. Macro diagnostics

The macro abstraction requirements of the parent specification apply to every
presentation in this document.

Actor, FSM, supervisor, and application errors use their public vocabulary:
message variant, state, event, transition, child, strategy, phase, dependency,
and generated API. They never default to an error in an expanded helper
function or generated module.

When captured authored code has a type error, the report combines semantic and
macro context, for example “The `Coin` handler returns the wrong actor state
type,” and underlines the authored handler expression. When generated code
alone fails, the public report identifies a compiler or macro implementation
defect at the invocation. The underlying diagnostic and full expansion chain
remain available in machine and verbose-debug data.

Nested expansion is summarized in user-significant frames. The default output
does not dump every internal rewrite. Cross-file macro definition labels are
shown only when the macro author can act on them or verbose diagnostics were
requested.

## 10. Internal compiler errors

Ordinary domain failures never reach a catch-all report. Exhaustive converters
remain mandatory.

An actual exception or impossible return crossing the top-level crash boundary
produces one stable internal-compiler-error report containing:

- a short apology and reproducible-action request;
- compilation phase and current authored declaration when known;
- an incident identifier or deterministic fingerprint;
- verbose/debug access to exception and stacktrace;
- no implication that the user should edit generated or Core code.

The default report does not print an uncontrolled stacktrace. Tests prove that
ordinary domain terms cannot enter this exception boundary.

## 11. CLI behavior

Every CLI command that emits compiler diagnostics uses the canonical renderer,
including compile, check, test-driven compilation, run, docs, package,
release, migration, formatter validation, and macro inspection paths.

Operational errors such as unreadable files, invalid configuration, dependency
resolution, artifact failures, and command usage use the same report model but
do not fabricate source snippets.

Warnings and errors may be interleaved in deterministic source order. Build
progress text is visually separate from diagnostics. Captured BEAM diagnostics
are adapted structurally where possible and clearly identified as host
diagnostics; Cure does not scrape their already-formatted terminal output.

`mix cure.diagnostics` must compile real intentionally failing Cure inputs and
print exactly the canonical user-facing reports. Constructor-only reports are
permitted only for operational conditions that cannot safely be induced in a
test process, and are labelled supplemental.

## 12. Testing strategy

### 12.1 Test layers

Each migrated diagnostic family has:

1. a producer test asserting stable code and semantic payload;
2. a source-range test asserting byte and source coordinates;
3. a plain-render snapshot at a fixed width;
4. focused ANSI assertions for banner and marker roles;
5. JSON/LSP parity assertions where applicable;
6. at least one real compilation catalog case.

Tests do not generally pin incidental prose outside dedicated snapshots.
Snapshots intentionally pin the complete public presentation.

### 12.2 Source rendering matrix

The snippet suite covers:

- one- and multi-character tokens;
- full expressions;
- zero-width insertions;
- same-line disjoint and overlapping labels;
- separated and cross-file labels;
- one-line and multiline ranges;
- long-line horizontal clipping;
- long-snippet vertical elision;
- tabs at different columns;
- ASCII, combining marks, wide Unicode, and emoji;
- source with and without a final newline;
- unavailable and unsaved sources;
- colour `auto`, `always`, and `never`.

### 12.3 Semantic catalog

The catalog includes at least one real failing program for every reachable
public diagnostic code. It records which producer branch and code were reached
using instrumentation or coverage, while the displayed output comes only from
attempted compilation through the public compiler boundary.

Registry coverage is a hard gate: a reachable registered error code without a
catalog case fails CI. Intentionally unreachable compatibility codes must be
explicitly classified with an owner and removal condition; they may not be
silently counted as covered by constructing a diagnostic.

### 12.4 No raw leakage

An automated corpus scans default terminal and plain output and fails on:

- raw domain tuples or inspected maps;
- unclassified atoms such as `unknown_global`;
- Core constructor vocabulary;
- exception dumps outside the ICE debug path;
- generated file locations presented as primary authored blame;
- generic `codegen error` or `syntax error` text where a registered specific
  diagnostic exists.

Allowlisted surface syntax is distinguished structurally, not with a broad
text suppression that could hide regressions.

## 13. Implementation phases

### Phase 1 — document and snippet foundation

1. Implement `Cure.Diagnostic.Doc` and terminal/plain document renderers.
2. Move banner, paragraph wrapping, notes, and hints onto the document model.
3. Put the normalized source path in the cyan banner.
4. Add terminal capability and colour policy handling.
5. Implement single, paired, separated, cross-file, and multiline snippets.
6. Add the complete source-rendering test matrix.

### Phase 2 — exact ranges

1. Add exclusive end positions to lexer tokens.
2. Propagate exact complete and focused ranges through parser nodes.
3. Propagate expression-role ranges through resolution and elaboration.
4. Delete normal reliance on the fixed diagnostic token-width table.
5. Verify byte, scalar, display-column, and LSP coordinate conversions.

### Phase 3 — contextual syntax reports

1. Inventory every parser/lexer failure constructor.
2. Replace generic token failures with the structured syntax family.
3. Implement exhaustive, context-specific report conversion.
4. Add safe delimiter and keyword edits where uniquely determined.
5. Add real compilation cases and snapshots for every variant.

### Phase 4 — contextual type reports

1. Add expression category, checking context, and expectation origin to type
   failures.
2. Implement surface type localization and focused comparison.
3. Migrate applications, annotations, branches, records, constructors,
   implicit arguments, dependent indices, and FFI boundaries.
4. Add actor/FSM handler-specific type reports.
5. Add paired-source and dependent-context snapshots.

### Phase 5 — remaining semantic families

Migrate names, declarations, imports/exports, fixity, patterns, coverage,
totality, effects, typeclasses, kernel rejection, code generation, projects,
packages, releases, and operational CLI failures. Each deliberate producer
variant receives an explicit converter and catalog case.

### Phase 6 — macro and completion audit

1. Verify macro-specific public vocabulary for actor, FSM, sup, app, and
   user-defined macros.
2. Verify authored blame and nested provenance for every macro failure class.
3. Remove migrated string formatters, raw tuple rendering, width guesses, and
   generic adapters.
4. Make registry-to-real-compilation catalog coverage a required CI gate.
5. Run the verification matrix in section 14.

## 14. Completion gates

This specification is complete only when all of the following are true:

1. Every reachable public diagnostic code has a real compilation or safe
   operational-path catalog case.
2. Every deliberate domain-error variant has an exhaustive converter; adding
   a variant without one fails compilation or tests.
3. No normal user-facing path prints a raw tuple, generic category, Core term,
   generated implementation error, or uncontrolled exception.
4. Lexer/parser and semantic diagnostics use exact owned ranges; the fixed
   width table is absent from normal production paths.
5. Full-span, paired, multiline, cross-file, tab, and Unicode rendering tests
   pass in plain and ANSI modes.
6. Syntax reports are contextual and actionable for every parser failure
   family in scope.
7. Type reports retain category, context, expectation origin, surface types,
   and focused differences for every migrated type failure.
8. Actor, FSM, supervisor, and application reports preserve macro abstraction
   and authored primary blame.
9. Terminal, plain, JSON, LSP, and Elixir/Mix projections agree on code,
   severity, ranges, labels, suggestions, and provenance.
10. CLI colour is TTY-aware, the banner is always cyan when coloured, and only
    semantic source markers change with severity.
11. `mix cure.diagnostics` visibly attempts compilation, prints canonical
    reports, runs with coverage, and fails when a reachable code or producer
    branch lacks a case.
12. Diagnostic metadata does not change acceptance, normalization, unification,
    kernel checking, erasure, or emitted runtime behavior.
13. Formatter, warnings-as-errors, diagnostic suites, parser suites,
    elaborator/kernel suites, complete Antigen, macro suites, and full ExUnit
    all pass.
14. The repository contains no superseded public diagnostic examples or docs
    showing legacy output as current behavior.

Passing a focused renderer suite, producing attractive examples, or covering a
small code subset is not completion.

## 15. Explicit non-goals

This work does not:

- replace the current parser with the Cure-native parser planned for 0.35;
- add broad parser recovery or continue trusted compilation after a fatal
  rejection;
- alter the type system or weaken kernel checks to improve messages;
- put spans or presentation metadata into definitional equality or runtime
  terms;
- copy Elm wording verbatim;
- expose compiler implementation details merely because they are available;
- guarantee a machine-applicable edit when more than one repair is plausible.

## 16. Reference findings adopted from Elm

The following behaviors were confirmed in the local Elm source and are
deliberately adopted:

- `Reporting.Report` separates title, region, suggestions, and rich message;
- `Reporting.Doc` uses compositional styled documents, reflowed prose, and
  separate styled/plain encodings;
- `Reporting.Render.Code` supports full single-line underlines, same-line
  paired regions, separated chunks, and multiline gutter marking;
- `Reporting.Error.Syntax` models grammatical situations rather than exposing
  parser token sets directly;
- `Reporting.Error.Type` retains expression category, expectation context, and
  related source origin;
- `Reporting.Error.Canonicalize` gives name, arity, declaration, and operator
  failures purpose-built explanations and suggestions;
- terminal output is colour-capability aware and targets 80-column prose.

Cure additionally requires stable public codes, macro provenance, structured
edits, dependent-type evidence, Elixir/Mix integration, and parity with JSON
and LSP consumers.

## 17. Related specifications

- `2026-07-20-structured-compiler-diagnostics-design.md` — parent semantic
  model and migration requirements.
- `2026-07-14-compile-time-reflective-beam-macros-design.md` — mandatory macro
  implementation and abstraction requirements.
- `2026-07-17-cure-native-parser-diagnostics-self-hosting-design.md` — deferred
  0.35 parser implementation; it must reuse this diagnostic architecture.
- `2026-07-12-elm-style-error-rendering-PARKED.md` — historical document,
  superseded by the parent specification and this presentation specification.

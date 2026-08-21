# Regex Master Implementation Roadmap

**Status:** authoritative implementation goal and sequencing ledger

**Date:** 2026-08-20

**Implementation checkpoint:** Phase 1 is discharged. The canonical pipeline
 carries package identity and explicit module exports through dependency
 artifacts, preserves cross-package interface-edge ownership, and rejects
 non-exported bundled modules before body elaboration. The Regex sources live
under `lib/std_deps/regex`; the stdlib bootstrap performs foundational,
package, and merged-publication stages. The portable BEAM-import closure audit,
generic-unix AtomVM gate, Unicode dependency pin, and cold/warm baseline are
recorded in `2026-08-20-regex-performance-baseline.md`.

The first Phase 2 evidence slice is also landed: successful lookahead and
lookbehind decisions carry an existential package containing the indexed finite
child path, while the existing atomic commitment evaluator remains the
acceptance authority. The assertion-capture sidecar is now landed as well:
positive lookaround branches carry their selected `ExtendedInstruction` routine
into named replay, while negative-assertion frames are discarded. Formal
refutation completeness proofs and several capture interactions remain open.
The capture/backtracking slice now also threads selected assertion markers through
later boundary constraints (including capture-participation conditionals),
preserves the same context in named replay, and covers present/absent optional
assertion captures plus failed-alternative backtracking. Branch backtracking
and nested assertion capture publication are regression-tested. Capture-aware
prefix replay now uses the same ordered finite-machine DFS as assertion
acceptance: it returns the first path that reaches acceptance, carrying the
consumed and unconsumed character lists directly. This preserves lazy
repetition and ordered alternation instead of retrying every endpoint with a
separate greedy scan. The focused named-capture suite and the 138-test Regex
behavior slice pass with this evaluator.
Assertion decisions now consume the certified path search directly; the former
preliminary Boolean scan and reconstructed exhaustion witness are gone, so a
search refutation carries the exhaustion value produced by the same traversal
that attempted every start and destination.
An independent finite oracle now exhaustively compares the admitted positive,
negative, nested lookahead, exact lookbehind, and negative lookbehind behavior
over the `abc` alphabet through length four; the randomized oracle remains as
the broader subject-length check. This validates the observable decision
boundary, while the dependent refutation-tree soundness theorem is still open.
Successful exact and prefix search witnesses now also retain an erased
membership proof for the selected filtered start state, so a witness cannot
silently name a thread that was not present in the machine's start list.
Path refutations now also retain erased equations tying their destination list
to the exact machine transition that produced it. Empty-input exhaustion and
one-step exhaustion use separate indexed constructors, avoiding an opaque
recursive normalization shortcut; active and accepted destination rejection
branches carry the same equation alongside their child and tail failures. This
is a construction-site invariant for the eventual refutation theorem, not the
theorem itself: the current cursor witness still permits a terminal
`MachineStateMembersNil` over a non-empty original list, so generic path
soundness/completeness and the exhaustive admitted-shape proof remain open.
The Phase 2 exit gate is therefore still not discharged.

**Applies to:** the Cure-native typed regex engine, its erased portable runtime,
finite PCRE-family extensions, proof-carrying normalization, runtime pattern
compilation, BEAM interoperability, and AtomVM packaging.

## 0. Authority and goal

This document is the single entry point for completing Cure's regex system. An
implementation agent may be given this file as its goal and must work through
the phases below in order, following every referenced specification and gate.

This roadmap governs **sequence, prerequisites, status, and final acceptance**.
It does not restate every representation, theorem, diagnostic, or API contract.
The referenced specifications remain authoritative for those details.

The final deliverable is:

1. a pure Cure-native, dependently typed, proof-backed regex engine;
2. a separately identified `cure_regex` Cure package containing the portable
   erased implementation, embedded and bundled by the stdlib release but not
   merged into the stdlib's public module namespace, with no OTP `:re`, PCRE,
   NIF, port, ETS, process-global cache, or runtime interpreter dependency;
3. the largest deliberately admitted finite PCRE/OTP-compatible feature set,
   including certified translations of reducible source forms;
4. identical portable execution semantics on standard BEAM and AtomVM;
5. after the erased engine is completely stabilized, a separately layered
   runtime-pattern compatibility API suitable for Erlang, Elixir, and AtomVM.

The runtime compatibility path must reuse the Cure-native parser model,
normalization, finite-machine semantics, and execution implementation. It must
not become a second regex engine.

The erased engine is not merged into the standard library's public module
namespace. The working package name is `cure_regex` (a different name requires
an amendment to this roadmap). It owns the portable first-order machine
runtime, runtime-safe syntax pieces, proof-backed normalization and extraction
adapters, the generic compatibility API, the typed regex implementation, and
the AtomVM artifact. It is an internal package dependency of the stdlib build:
the stdlib bootstrap compiles foundational modules first, then `cure_regex`,
then any thin public `Std.Regex` façade. The package has its own identity,
source/dependency hashes, artifact manifest, and explicit exported-module list.
Its private modules are bundled for calls from its public surface but are not
available for arbitrary `use` or qualified lookup by stdlib consumers.

## 1. Source-of-truth hierarchy

Read all applicable specifications before changing implementation code. When
documents overlap, use this precedence:

1. This roadmap decides global ordering and activation gates.
2. The newest focused specification decides the semantics of the feature it
   explicitly owns.
3. A discharged specification remains authoritative evidence for completed
   work unless a later specification explicitly reopens it.
4. Tests record behavior but do not override an explicit semantic decision.
5. If two focused specifications genuinely conflict and the precedence rules
   do not resolve them, stop and amend the specifications before coding.

The specifications are:

| Document | Authority in this roadmap |
|---|---|
| `2026-07-21-dependently-typed-regex-design.md` | Historical foundation and thesis mapping. Superseded for unfinished work. |
| `2026-07-22-dependent-regex-completion-design.md` | Discharged typed-engine architecture, proof record, API foundation, and verification baseline. |
| `2026-08-10-regex-actor-module-split-design.md` | Binding decision not to split `Std.Regex` without new measurements showing a benefit. |
| `2026-08-18-finite-pcre-extension-design.md` | Detailed finite-PCRE feature semantics and the initial feature-order ledger. |
| `2026-08-19-pure-portable-regex-engine-design.md` | Authoritative portable-engine expansion, generalized assertions, compatibility ledger, certified translations, and parity audit. |
| `2026-08-20-runtime-regex-compatibility-layer-design.md` | Deferred runtime parser, generic ABI, BEAM facade, and AtomVM compatibility layer. |
| `../tooling/2026-08-13-regex-proof-elaboration-assessment.md` | Binding guidance for proof shape and elaboration limitations where referenced by the completion record. |
| `../tooling/2026-07-22-compiler-identity-and-regex-stabilization-plan.md` | Historical compiler prerequisite record; re-open compiler work only for a demonstrated failing invariant. |

The primary external design reference for the typed foundation remains
Katarzyna Marek's *Dependently-typed regex matchers in Idris* (`msc_proj.pdf`).
OTP `re` and PCRE2 are compatibility oracles and inventory references only;
they are never production dependencies or substitutes for Cure proofs.

### 1.1 Package ownership and dependency direction

The package boundary is part of the semantic design:

```text
foundational stdlib modules
              ^
              |
  embedded cure_regex package
  (typed/erased engine, proofs,
   runtime parser/ABI, AtomVM)
              ^
              |
      public Std.Regex façade
      (only declared exports)
```

Package-owned source, tests, manifests, and generated AtomVM artifacts live in
`lib/std_deps/regex` rather than being discovered as ordinary `lib/std`
modules or copied into generated `priv/std` sources. The stdlib build invokes
the ordinary package pipeline in three deterministic stages: foundational
stdlib, embedded `cure_regex`, then public façade. The resulting release may
bundle all verified BEAMs, but module-interface publication exposes only the
package's declared surface and explicit stdlib reexports. External package
consumers may later depend on the same `cure_regex` artifact directly.

The package manifest must declare an explicit module export surface (for
example, an `exports.modules` set). A module being present in the bundled
artifact, or containing public declarations, does not publish it outside the
package. Package-internal calls may resolve private modules; consumer
resolution must reject private module names with a structured package-visibility
diagnostic. Public façades may explicitly reexport selected declarations, and
those reexports are the only transitive visibility path.

## 2. Non-negotiable invariants

Every phase must preserve all of these:

- `Pattern(shape)` and `Regex(result)` remain the typed semantic foundation.
- Successful typed matching produces a result justified by checked evidence;
  it is not reconstructed through an unchecked decoder.
- Failure is total and meaningful: a completed finite search may return
  `NoMatch`; exhaustion, malformed input, unsupported syntax, and internal
  inconsistency must return distinct structured diagnostics.
- Runtime matching contains no source parser, macro dispatcher, Core evaluator,
  runtime proof interpreter, OTP `:re` call, or opaque PCRE handle.
- Proof and index data erase from the generated runtime artifact.
- Generated runtime code follows the same ordinary code-generation path as
  other Cure code.
- Features requiring unrestricted backtracking, recursion, callouts, or other
  unbounded dynamic control remain rejected unless a later foundational spec
  proves a finite interpretation.
- Fuel exhaustion must never be reported as `NoMatch`.
- Scheduler preemption is transparent. Ordinary regex APIs never expose
  `Continue`; AtomVM reductions schedule pure Cure calls and loop backedges.
- Streaming, if later implemented, is a separate incomplete-input API rather
  than a mutation of ordinary `run` semantics.
- No module split is performed merely to move lines. Revisit the accepted
  `Std.Regex` no-split decision only with cold/warm profiles demonstrating that
  a proposed acyclic boundary reduces total work.
- No new compiler workaround may be embedded in regex code. Reproduce a
  compiler defect with a minimal red regression and fix its canonical authority.

## 3. Working protocol for an implementation agent

At the beginning of each phase:

1. Read this roadmap and the focused specifications named by the phase.
2. Inspect the current source, tests, and commit history; do not assume that a
   prose status line proves the checkout still satisfies its gates.
3. Write or identify the smallest red regression for the next unmet obligation.
4. Record the exact current failure and distinguish compiler defects from
   missing regex implementation.

During implementation:

- work at the single semantic or compiler construction site;
- add complete structured diagnostics, including relevant span, declaration,
  term, expected/inferred type, and unresolved identity where available;
- keep proofs, executable code, erasure checks, and compatibility behavior in
  the same vertical slice;
- never replace a proof obligation with a fixture-specific axiom, unchecked
  conversion, partial function, host implementation, or raised timeout;
- run Mix invocations serially because concurrent invocations can destructively
  rebuild the shared Cure stdlib;
- author foundational stdlib source in `lib/std/`, never the generated
  `priv/std` bundle; author regex modules in the embedded package tree;
- preserve user changes and avoid destructive cleanup commands;
- commit each coherent green slice before beginning the next one, without
  co-author trailers or agent attribution.

For each phase, maintain an implementation ledger in the focused specification
or a linked completion record. Credit work as complete only when it exists in a
commit and its stated gates pass.

## 4. Master sequence

The phases below are strictly ordered. Work may proceed within a phase in the
order given by its focused specification, but no later phase may weaken or
bypass an earlier exit gate.

### Phase 0 — Revalidate the discharged typed foundation

**Read:**

- `2026-07-22-dependent-regex-completion-design.md`
- `../tooling/2026-08-13-regex-proof-elaboration-assessment.md`

Treat the dependent-regex completion as discharged, not as work to rewrite.
Revalidate its final architecture, accepting-path construction, Thompson
evidence theorem, total extraction, language soundness/completeness, typed API,
staging, and proof/index erasure against the current checkout.

Required outcome:

- all completion-record tests and proof modules pass;
- the bounded-regex and CharacterLiteral regressions pass;
- no emitted closure contains a bare unresolved definition key;
- no E101/E093 remains on the typed regex path;
- any regression is repaired before extension work begins.

Do not reopen completed proofs solely to restyle them.

### Phase 1 — Establish the embedded package and portable-production guardrails

**Status:** complete. Package identity, physical source move, three-stage build,
merged verified artifact, source lookup, compiled-macro home lookup,
export-surface regressions, portable BEAM-import audit, AtomVM execution gate,
Unicode dependency pin, and cold/warm performance baseline are complete.

**Read:** `2026-08-19-pure-portable-regex-engine-design.md`, especially
Sections 2–5 and Phase 0.

Before adding syntax, create the embedded `cure_regex` package boundary and
make its production closure mechanically auditable:

1. add package metadata, independent source/test roots, and a reproducible
   package build invoked from the stdlib bootstrap;
2. split the build into foundational-stdlib, package, and façade stages;
3. move the regex modules into the package and preserve behavior at every
   migration step;
4. declare the public package/module export surface and reject private-module
   lookup from consumers;
5. ban OTP `:re`, PCRE handles, NIFs, ports, ETS, process-global caches, and
   runtime parsing from the package closure;
6. establish BEAM and AtomVM artifact/closure checks;
7. pin Unicode data and compatibility-oracle versions;
8. establish cold/warm compilation and runtime size/memory baselines;
9. preserve structured rejection for every unsupported construct.

**Exit gate:** the three-stage build is deterministic, private package modules
are inaccessible outside the package, public `Std.Regex` behavior is unchanged,
portability guards fail red when a forbidden dependency is introduced, and the
migrated engine passes its existing behavior gates on both supported runtimes.

### Phase 2 — Complete generalized assertions

**Current checkpoint:** The depth-bounded nested assertion foundation, atomicity
interactions, parent-capture assertion conditionals, and the first
assertion-local capture sidecar are committed
(`9f8af26f` plus the current assertion-conditional slice). Atomic/possessive
scopes inside assertions, assertions inside atomic scopes, and conditional
branches that inspect an already-participating outer capture now use the finite
`LookaroundCompilation` IR and the same commitment relation. The first scoped
inline-option slice is now implemented: `(?i:...)`, `(?m:...)`, `(?s:...)`,
`(?u:...)`, `(?U:...)`, and their `-` removals are represented as lexical AST
nodes and propagated through ordinary, lookaround, atomic, and named
compilations. The source-sensitive `x` mode and execution-level `f`/`E` flags
remain deliberately rejected inside a scope until their source-map and
search-bound semantics have a canonical implementation. Assertion-created
capture markers are now threaded through the shared constraint fold and the
capture-aware replay fold, so a later conditional sees the same participation
decision in ordinary and named execution; optional assertion captures cover both
participating and absent branches. Capture-aware prefix replay follows machine
order for lazy and ordered branches, with regressions for ordered alternation
and lazy repetition. Refutation values now retain dependent child and sibling
failure trees through both exact and prefix path folds, while depth/history
guard failures remain explicit resource certificates. An exhaustive
bounded-subject oracle covers the admitted nested lookaround decision slice;
the formal soundness/completeness audit and exhaustive comparison of every
admitted machine shape remain open, so the phase exit gate is not yet
discharged.

**Read:** `2026-08-19-pure-portable-regex-engine-design.md`, Sections 6–10 and
Feature Phases 1–2. Cross-reference the bounded-lookaround foundation in
`2026-08-18-finite-pcre-extension-design.md` Phase F.

Implement in this order:

1. recursive assertion syntax and typed assertion-program representation;
2. depth-bounded nested positive and negative lookahead;
3. fixed/bounded lookbehind with explicit finite history;
4. checked assertion decisions and witnesses;
5. captures and backtracking behavior inside assertions;
6. interactions among nesting, alternation, repetition, atomicity, greediness,
   conditionals, and boundaries;
7. soundness, completeness, extraction, erasure, and resource-bound proofs.

**Exit gate:** nested admitted assertions have generic proofs and exhaustive
small-model comparisons; rejected depth/history bounds produce structured
diagnostics rather than partial execution.

### Phase 3 — Complete finite PCRE-family syntax and controls

**Read:**

- `2026-08-18-finite-pcre-extension-design.md`, Phases A–E
- `2026-08-19-pure-portable-regex-engine-design.md`, Feature Phases 3–4

Implement remaining features in increasing semantic difficulty:

1. newline policies, Unicode names/properties, class and escape forms;
2. named captures and duplicate-name policy;
3. branch-reset groups;
4. capture-participation conditionals;
5. atomic groups and possessive quantifiers;
6. admitted finite search controls, anchors, greediness/laziness, scan,
   split, replacement, and capture-result behavior.

For every feature, complete one vertical slice: parser, normalized syntax,
typed lowering, finite machine/control metadata, execution, evidence,
soundness/completeness or preservation theorem, extraction, diagnostics,
erasure, fixed tests, properties, oracle comparisons, and AtomVM tests.

**Exit gate:** every claimed feature in the compatibility ledger is either
fully implemented and proved or explicitly rejected with a stable diagnostic.

### Phase 4 — Implement proof-carrying normalization

**Read:** `2026-08-19-pure-portable-regex-engine-design.md`, Sections 15–18,
especially the translation policy and proof-carrying normalization architecture.

Normalize unsupported-looking source forms only when a finite target preserves
the required observable semantics. Operate on parsed syntax trees, never by
unprincipled source rewriting.

Implement, where admitted by the detailed spec:

1. bounded-lookbehind normalization;
2. finite-domain backreference expansion;
3. nested-assertion compilation;
4. acyclic subroutine expansion;
5. other explicitly inventoried finite rewrites.

Each rewrite requires a checked certificate preserving acceptance, selected
match, capture participation and values, ordering/priority, and diagnostics as
applicable. Reject expansion beyond declared resource limits.

**Exit gate:** every enabled rewrite has direct semantics, certificate checking,
negative tests, small-model equivalence properties, and no increase in the TCB.

### Phase 5 — Close the PCRE2/OTP/Elixir compatibility ledger

**Read:** `2026-08-19-pure-portable-regex-engine-design.md`, compatibility
tables and parity-completeness audit.

Audit every syntax, option, control, Unicode, capture, replacement, split,
return-shape, and error family exposed by the pinned OTP `re`, Elixir `Regex`,
and PCRE2 versions. Classify each item as:

- directly supported and proved;
- translated to a supported form with a checked preservation certificate;
- deliberately divergent, with the difference documented and tested; or
- unsupported, with a stable structured diagnostic and rationale.

No unclassified row may remain. “Parity” claims must name the exact subset and
versions; they must not imply support for rejected non-finite facilities.

**Exit gate:** the ledger is exhaustive for the pinned versions and generated
documentation agrees with executable capability tests.

### Phase 6 — Stabilize the erased Cure-native engine

This is the hard prerequisite for all runtime-pattern compatibility work.

Run and pass, serially where required:

1. clean dependency-ordered foundational stdlib build;
2. clean embedded-package build for `cure_regex`, including export filtering;
3. clean public `Std.Regex` façade build against the package artifact;
4. complete `MIX_ENV=test mix test` including documentation fences;
5. TCB and totality suites;
6. proof/index erasure checks;
7. relevant Antigen assays;
8. canonical module-pipeline gate;
9. Unix/escript smoke tests;
10. BEAM and AtomVM behavior vectors;
11. closure audit for forbidden host/runtime dependencies;
12. cold/warm elaboration and runtime benchmarks against recorded budgets;
13. compiler-warning, E101, E093, and unresolved-key audit.

The generated runtime engine must be pure, portable, finite, preemptible normal
BEAM code. AtomVM fairness must be demonstrated with a concurrent heartbeat,
and reachable native primitives must be audited for input-sized uninterruptible
work.

**Exit gate:** every item above is green in committed code. Only then change the
runtime compatibility specification from deferred to active.

### Phase 7 — Extract shared syntax without changing behavior

**Read:** `2026-08-20-runtime-regex-compatibility-layer-design.md`, Phases 0–1.

Move or expose the syntax model, parser grammar, normalization, diagnostics,
capture numbering, and option semantics needed by both compile-time literals
and runtime parsing inside the embedded `cure_regex` package. Preserve the
source-compatible `Std.Regex` typed macro behavior exactly, and expose only the
declared façade/parser surface to consumers.

This phase must not introduce a second grammar, runtime matcher, or public
compatibility API.

**Exit gate:** all existing literal fixtures parse identically through the
shared implementation, including metadata and diagnostic spans.

### Phase 8 — Build the existential runtime plan inside `cure_regex`

**Read:** `2026-08-20-runtime-regex-compatibility-layer-design.md`, Phases 2–4.

Implement the bridge from a runtime pattern string to the same finite engine:

1. runtime parser and total structured diagnostics in the package;
2. capture/reference resolution and proof-carrying normalization;
3. resource admission before machine publication;
4. existential packaging of the hidden typed shape;
5. generic match/capture/span projection;
6. reusable immutable compiled values;
7. `compile`, `run`, `run_prefix`, `scan`, `split`, and literal replacement.

Typed Cure APIs remain primary and must never consume generic runtime matches to
manufacture typed results.

**Exit gate:** compile-time and runtime paths produce equivalent normalized
syntax, machines, matches, captures, and errors over their common admitted set.

### Phase 9 — Publish the neutral BEAM ABI from `cure_regex`

**Read:** `2026-08-20-runtime-regex-compatibility-layer-design.md`, Phase 5 and
Sections 5–10.

Implement:

1. the neutral Erlang-facing API exported by the `cure_regex` package;
2. an idiomatic Elixir adapter layered over that ABI;
3. explicit option/capability registries;
4. versioned and bounded validation of untrusted compiled-pattern terms;
5. scalar offsets and optional byte projections;
6. release/capability manifests and precise compatibility documentation.

Ordinary calls return final success, no-match, or error results. They never
expose `Continue`. Cancellation uses ordinary process supervision; streaming is
a separate future API.

**Exit gate:** Erlang, Elixir, and Cure vectors normalize to identical results,
including malformed and forged terms.

### Phase 10 — Package and qualify the embedded engine for AtomVM

**Read:** `2026-08-20-runtime-regex-compatibility-layer-design.md`, Phases 6–8.

1. compile and package the complete reachable `cure_regex` closure, not the
   complete Cure stdlib, while bundling it as part of the stdlib release;
2. exclude unavailable OTP services and forbidden host dependencies;
3. validate scheduler fairness on interpreter and JIT release targets;
4. audit every native primitive reachable from parsing and matching;
5. measure artifact size, cold start, compilation, execution, and peak memory;
6. run the complete shared BEAM/AtomVM conformance corpus;
7. publish the pinned AtomVM revision and capability manifest.

**Exit gate:** a clean AtomVM bundle executes runtime-compiled patterns with the
same normalized semantics as BEAM and stays within documented resource budgets.

### Phase 11 — Regex integration and release claim

Run every regex gate from a clean checkout before touching OTP packaging.
Confirm that regex documentation,
capability manifests, examples, generated bundles, and release artifacts agree
with the implementation.

The final report must identify:

- every implemented and proved feature;
- every certified translation;
- every deliberate semantic divergence;
- every unsupported construct and diagnostic code;
- exact OTP, Elixir, PCRE2, Unicode, BEAM, and AtomVM comparison versions;
- proof, TCB, erasure, totality, test, performance, and closure-audit results.

Do not advertise total PCRE compatibility. Advertise the exact checked subset
and the stronger Cure-native guarantees it provides.

### Phase 12 — Move `cure-otp` into `lib/std_deps/otp` and depend on it directly

This is deliberately the **last** task in this roadmap. Do not begin it while
any regex proof, runtime compatibility, package-export, AtomVM, performance, or
release gate is incomplete. Regex must already be fully released and stable so
that moving OTP modules cannot obscure a regex regression or change the
performance baseline used to qualify the engine.

Move the repository currently at
`/Users/ch/Develop/esp32-beam/cure-otp` into
`/Users/ch/Develop/esp32-beam/cure-lang/lib/std_deps/otp`. The resulting
`lib/std_deps/otp` tree is the source of truth; it must not be copied into
`lib/std` or rewritten into a second local OTP implementation. Make the Cure
stdlib bootstrap depend directly on that embedded path package using the normal
package resolver and canonical module pipeline.

The moved project is renamed to the canonical package identity `cure_otp`
(`Cure.toml` name and dependency key included); the filesystem directory is
intentionally the shorter `lib/std_deps/otp`, just as the regex package lives
under `lib/std_deps/regex`.
with its own source/dependency hashes, artifact manifest, and package-local
tests. Its `Otp`, `Otp.Raw`, and `Otp.Beam` modules are the direct dependency
surface. Preserve `Std.Otp` and `Std.Otp.Raw` source compatibility through
explicit, thin public façades or qualified adapters only; do not duplicate the
OTP bodies in `lib/std`.

Implement the migration using the same package mechanism as `cure_regex`:

1. preserve the `cure-otp` repository history while renaming the project to
   `cure_otp` and placing it under `lib/std_deps`
   without silently flattening or copying its source files;
2. correct and validate its `Cure.toml` path/dependency declarations for the
   embedded location;
3. compile foundational stdlib prerequisites first, then the direct `cure_otp`
   path package, then thin `Std.Otp`/`Std.Otp.Raw` compatibility façades;
4. declare the package's public export surface and keep private implementation
   modules bundled but inaccessible to arbitrary
   stdlib consumers through `use` or qualified lookup;
5. preserve source compatibility and structured diagnostics for unavailable
   target services;
6. remove the copied OTP sources from `lib/std` and prove that no build task,
   migration helper, or release script copies them back in;
7. audit BEAM, Unix, escript, and AtomVM closures separately, keeping OTP
   services out of the portable `cure_regex` closure;
8. rerun the complete clean-build, incremental, package-visibility, warning,
   and release matrix after migration.

The OTP move must not introduce a dependency from `cure_regex` back to
`cure_otp`, and it must not retroactively alter any regex semantic or runtime
contract. Its completion is a separate release slice after the regex claim has
already been published. The final dependency graph must show the direct path
package edge, not a generated-source copy edge.

**Exit gate:** the embedded `cure_otp` package has a verified export surface and
source-compatible public API, `lib/std/otp*.cure` no longer contains copied OTP
implementations, all target-specific gates pass, the regex package closure
remains unchanged and green, and a clean release contains the direct path
package manifest without exposing its private modules.

## 5. Phase transition checklist

A phase is complete only when all answers are yes:

- Is its implementation committed?
- Did its smallest red regression turn green for the intended reason?
- Are all focused and neighboring tests green?
- Are new failures expressed as structured, actionable diagnostics?
- Are soundness, completeness, preservation, and erasure obligations discharged
  to the extent required by the focused specification?
- Does the generated closure remain pure and portable?
- Did BEAM and AtomVM agree where the phase affects runtime behavior?
- Were resource and performance regressions measured rather than guessed?
- Was the compatibility ledger updated?
- Did the preceding phase remain green?

If any answer is no, remain in the current phase.

## 6. Final acceptance criteria

This master goal is complete only when:

1. the dependent typed foundation remains fully discharged;
2. generalized nested assertions and all admitted interactions are proved;
3. every finite-PCRE feature claimed by the ledger is implemented vertically;
4. all admitted translations carry checked semantic-preservation evidence;
5. the PCRE2/OTP/Elixir inventory has no unclassified capability;
6. the erased Cure-native engine passes the full stabilization gate without
   host regex dependencies, unresolved compiler errors, or unerased proofs;
7. compile-time literals and runtime patterns share syntax, normalization,
   finite-machine semantics, and execution rather than duplicating an engine;
8. the erased engine and typed `Std.Regex` façade are consumable through the
   versioned embedded `cure_regex` package artifact, with private modules hidden
   by the package export surface;
9. the neutral BEAM ABI is versioned, validated, documented, and tested;
10. AtomVM packages and executes the engine fairly and within recorded budgets;
11. all tests, properties, proofs, TCB, totality, erasure, Antigen, canonical
    pipeline, clean-build, Unix/escript, BEAM, and AtomVM gates pass from a clean
    committed checkout;
12. the published compatibility claim is exact, versioned, and no broader than
    the verified implementation;
13. only after items 1–12 above are green, the embedded `cure_otp` package is
    migrated and independently qualified without changing the regex closure.

Completing only the compile-time engine does not complete this roadmap.
Completing only the runtime compatibility layer without the erased engine's
proof and portability gates is forbidden. The implementation is complete only
when both entry paths converge on the same verified finite semantic core and
all phase gates above are discharged.

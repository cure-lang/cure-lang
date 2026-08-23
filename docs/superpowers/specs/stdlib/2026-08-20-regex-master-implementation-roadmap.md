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
child path. Lookahead admission now also requires the atomic prefix traversal
to succeed, and exact/lookbehind admission requires the corresponding atomic
exact traversal, closing the former gap where either certified plain DFS could
backtrack past a closed atomic branch. Successful witnesses retain the selected
`ExtendedInstruction` routine from that atomic decision; lookahead additionally
retains its matched prefix and remainder. Capture-marker extraction and named
replay consume the retained routine instead of running the child machine a
second time, while negative-assertion frames are discarded. The plain path and
atomic selected routine are still produced by two traversals after a successful
decision; atomic rejection and commitment now return immediately without
running the speculative plain DFS. Replacing the successful pair with one
atomic-aware indexed selected-trace/refutation fold remains the next extraction
obligation. The first one-pass construction slice is landed: every successful
atomic start and transition now prepends erased, separately indexed search and
path trace nodes containing the chosen bounded state, source thread, character,
regular routine, preserved constraints, and nested-assertion routine.
Successful lookahead and lookbehind witnesses retain that trace. Selected
transitions now also retain an
erased `MachineStateCursor` from the exact ordered destination list to the
chosen suffix plus a `ListMember` edge at its head and an erased equality tying
the whole candidate list to `lookaround_machine_raw_destinations` for the exact
machine, source thread, and character. Selected starts retain the corresponding
head membership, an erased suffix cursor through the machine's exact raw start
list, and an equality tying that whole list to `pattern_machine_starts(machine)`.
The path trace is indexed by its originating input/rest, exact thread, history,
capture context, newline policy, atomic scope depth, prefix/exact mode,
consumed-prefix accumulator, runtime matched prefix, remaining input, and
selected extended routine. The initial trace adds the exact initial position
and canonical start selection; the
`LookaroundRoutineSearchYes` payload and both witness packages must carry that
exact indexed trace rather than arbitrary erased evidence. Constraint
evaluation now has one construction authority:
`LookaroundConstraintAdmission` produces the selected extended routine,
published capture-slot markers, and nested decision evidence from the same
child decision. Boundary filtering, replay, path evidence, and atomic traversal
project that shared result instead of recursively evaluating three correlated
views. Several
capture interactions remain open; exact and prefix path refutation soundness,
their complete start-search lifts, and constructive evaluator completeness are
now discharged.
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
the broader subject-length check. A second explicit 18-shape manifest covers
lookahead/lookbehind polarity, mixed nesting, alternation, greedy/lazy/
possessive repetition, atomic interactions, anchors, word boundaries, scoped
options, capture conditionals, and exact parsing over all `abcA` subjects
through length three. The manifest gate fails if a declared admitted shape has
no independent oracle case. This validates the observable decision boundary.
The dependent refutation-tree theorems now independently prove that
the exact evaluator cannot return both a rejection and an accepting path for
the same indexed search.
Successful exact and prefix search witnesses now also retain an erased
membership proof for the selected filtered start state, so a witness cannot
silently name a thread that was not present in the machine's start list.
Path refutations now also retain erased equations tying their destination list
to the exact machine transition that produced it. Empty-input exhaustion and
one-step exhaustion use separate indexed constructors, avoiding an opaque
recursive normalization shortcut; active and accepted destination rejection
branches carry the same equation alongside their child and tail failures.
These construction-site invariants are now consumed by both the exact and
prefix path/start-search refutation theorems. The converse evaluator
completeness theorems are discharged; the exhaustive admitted-shape proof
remains open.
Accepting and prefix path witnesses now carry the candidate cursor explicitly,
and every consuming path constructor carries an erased `MachineStateMembers`
witness tying that cursor to the canonical filtered transition list. Its edge
proof is reconstructed at the cursor rather than borrowed from the original
list, so a path cannot silently switch from the list being traversed to the
machine's full destination list. A separate `MachineStateCursor` now proves
that each candidate list is a genuine suffix of that canonical list, including
the recursive tail calls. This supplies the data consumed by the generic
refutation theorem, which now recurses through child and tail failures and
transports the cursor witness across their stored destination equations.
The terminal member-spine transport helper is now also present: when an
exhaustion constructor carries an equation identifying its original
destination list with the canonical empty list, the helper normalizes the
`MachineStateMembersNil` witness to that empty index before a refutation proof
consumes it. This closes the previously implicit empty-index transport case,
which the recursive child/tail refutation theorem now consumes.
Rejected accepting and prefix-path results now carry the erased
`MachineStateCursor` that corresponds to their failure's destination suffix.
The internal member traversals carry the same cursor at every recursive call;
when a child fails, the tail is searched with `MachineStateCursorDrop`, and a
tail failure is rewrapped with the parent cursor rather than leaking the
tail's narrower index. This removes the last untyped hand-off at the
accepting-path result boundary. The generic theorem now consumes these cursors
recursively and proves that every reported rejection excludes an accepting
path.
Consuming path constructors now add an erased `Equivalent` witness tying their
candidate parameter to the exact `Cons(head, tail)` suffix represented by the
cursor and traversal spine. The runtime edge remains ordinary data, but it is
typed against that same candidate list; a path cannot be instantiated for a
fabricated candidate list without an impossible equality proof. The recursive
child/tail refutation theorem now consumes this equality.
The failure-tree constructors now carry the corresponding erased cursor too:
terminal exhaustion records the empty suffix, and each active/accepted
destination rejection records the parent `Cons(head, tail)` suffix alongside
its child and tail failures. The tree therefore contains all of the indexed
transport data needed by the recursive theorem; no cursor needs to be rebuilt
from an unindexed list while consuming a certificate.
The public accepting/prefix rejection wrappers now expose only the complete
root traversal: both their failure and cursor are indexed by the full
destination list, not an arbitrary intermediate suffix. Intermediate suffixes
remain internal member-traversal results. Consequently a child failure embedded
in a destination-rejection node is known to begin at its own `Here` cursor,
while a tail failure retains the dropped-head cursor needed for the eventual
induction. The child fields now make that complete traversal explicit in their
indices (`child_destinations, child_destinations`) rather than retaining an
arbitrary child suffix. `MachineStateCursorSuffix` and its projection from a
member traversal record the remaining structural relation between a parent
failure cursor and an accepting-path cursor; it only admits equality or
dropping a parent head, so a path prefix cannot be smuggled into the theorem.
This is the induction relation consumed by the path-level theorem below.
The generic exact-acceptance path theorem is now discharged. Accepting paths
are indexed by the capture context that computed their transitions, active
continuations carry an erased equation tying the child input to the parent's
remaining input, and destination-rejection equations are indexed by the
failure state's actual thread identity. The proof performs induction on the
input spine before eliminating the failure tree, then consumes the cursor
suffix relation to recurse into either the rejected child or the rejected
tail. Both active-destination forms and accepted destinations are covered, and
the focused regression suite checks that unrelated child destinations remain
uninhabitable. The complete start-list lift is now discharged as well. Search
failures are indexed by both the whole start list and the exact unexamined
suffix. Empty, active-empty, active-consuming, and accepted-consuming
rejections consume exactly that suffix; recursive tails are indexed by the
dropped-head suffix and public rejection results expose only `starts, starts`.
Successful search paths retain their input equation, selected-start
membership, child destination cursor, and child accepting path until
`lookaround_search_failure_excludes_path` consumes them. `Here` invokes the
exact path theorem and `There` invokes the indexed tail certificate. The
prefix/lookahead traversal now has its own smaller failure family: accepted
threads succeed immediately, so exact-only `AcceptedWithInput` and
accepted-destination rejection cases cannot be manufactured. Prefix paths are
indexed by the capture context that computed their transitions; every active
continuation retains its child-input equation, canonical child-destination
equation, cursor suffix, and child path. Prefix search paths retain the selected
start membership and canonical child cursor until
`lookaround_prefix_search_failure_excludes_path` consumes them. Its `Here`
branch invokes the prefix child theorem and its `There` branch invokes the
indexed tail certificate. Exact and prefix search results now retain the
canonical filtered start list as a type parameter instead of hiding it in each
constructor. Given any valid path, the corresponding completeness theorem
eliminates a computed rejection; given any complete failure tree, its dual
eliminates a computed success. Both theorem pairs require erased equality tying
the explicit result argument to the actual evaluator call. The admitted-shape
audit also exposed and fixed a boundary-state conversion bug: child lookahead
was passing “the cursor crosses a word boundary” where `InitialPosition`
requires “the previous scalar is a word character.” All lookahead evaluators
now use the single `lookahead_initial_position` conversion. Resource and
erasure obligations now have executable gates: depth exhaustion is a third
decision outcome that satisfies neither polarity, and emitted functions accept
successful lookahead witnesses and complete refutation trees only through
erased parameters. The remaining Phase 2 proof work is the full atomic
selected-trace correspondence. The `ExtendedInstruction` routine consumed by
named replay now comes from the admitting atomic prefix result, but that result
and the erased plain path are still computed separately. The atomic traversal
must construct the indexed path or an atomic-aware refutation directly,
including commitment evidence for every skipped sibling, so acceptance,
rejection, matched/rest splits, and replay routine all have one construction
authority. The first rejection slice is now landed: `AtomicPathRefutation`
retains indexed input/state exhaustion and child-plus-tail destination failures,
and `AtomicStartRefutation` carries that tree through the ordered start list
into ordinary lookahead/lookbehind refutations. Commitment remains a separate
control outcome, and the generic refutation theorem plus the full selected-trace
correspondence remain open. Destination rejection nodes now carry the admitted
state cursor, head-membership proof, and canonical transition-list equation
needed for that theorem.
The first indexed contradiction lemma,
`atomic_path_input_exhaustion_excludes_trace`, now discharges the active-state
empty-input base case; destination and start-list induction remain.
The admitted-state `LookaroundAdmittedStateCursorSuffix` relation is explicit,
permitting that induction to drop only ordered heads rather than inventing a
candidate prefix. The exact-accepted-with-input refutation is indexed by an
explicit non-empty input spine, and `atomic_path_failure_excludes_trace`
discharges the exhaustion-indexed wrapper without relaxing the selected-trace
indices. The destination-exhaustion cursor base is separately discharged by
`atomic_path_destinations_exhausted_excludes_trace`; recursive destination
rejection and start-list induction remain. The membership-to-cursor bridge
`lookaround_admitted_cursor_suffix_from_member` now packages the exact suffix
and its ordered `Here`/`Drop` proof for that induction. The package is
existential and erased at the matcher boundary, so no runtime candidate list or
membership witness is introduced. A separate
`LookaroundAdmittedStateCursorWitness` mirrors the runtime cursor when its
whole list already contains a skipped prefix, keeping that proposition
distinct from the relative traversal suffix. `AtomicPathSearchYes` now carries
an erased selected whole/current admitted-state list pair and its ordered
`LookaroundAdmittedStateCursorSuffix`. Terminal success uses explicit empty
list witnesses, selected candidates establish the `Here` case, and skipped
candidates extend the relation with `Drop`. Inner commitment escapes now pass
through `atomic_lookaround_routine_add_skipped_candidate`, so a later sibling
success retains every skipped candidate in the original ordered destination
spine. This is construction-site transport only; the recursive theorem that
consumes the selected suffix and proves complete atomic trace/refutation
correspondence remains open.
`AtomicSelectedPathTrace` now indexes its current admitted-candidate suffix, and
active/accepted transition nodes retain the child search's selected
whole/current pair and `LookaroundAdmittedStateCursorSuffix`. The concrete base
slice `atomic_path_destination_rejection_excludes_trace` discharges an active
candidate rejected at the first character against the impossible exhausted
active child trace. The general child/tail induction still needs an explicit
alignment between each refutation cursor and the selected child suffix; this
base lemma must not be mistaken for the Phase 2 exit theorem.
`AtomicPathRefutation` now retains both the canonical admitted-state spine and
the refutation's current suffix, including the child and tail spines in every
destination-rejection node. `AtomicPathSearchNo` transports that whole/current
pair without exposing it at runtime. The ordered suffix relation now has an
explicit composition law, so a future child theorem can combine a refutation
cursor with a selected-trace suffix rather than treating them as interchangeable.
This is construction-site strengthening only: partial cursor failures are still
not interchangeable with root failures, and the complete child/tail alignment
relation remains open.
Every atomic no-result now also transports the erased
`LookaroundAdmittedStateCursorWitness` built alongside the runtime cursor. This
preserves the distinction between “the evaluator is currently at this suffix”
and “the selected path is a suffix of this candidate list”; the eventual
alignment eliminator must consume both witnesses rather than converting one
proposition into the other.
Terminal active-path failures are now distinguished as complete root failures:
`AtomicPathRootRefutation` indexes the failure with `whole = current`, and
`AtomicPathSearchRootActiveNo` / `AtomicPathSearchRootExactNo` are used for the
statically complete empty-candidate terminal cases (active input exhaustion
and exact acceptance with input).
Suffix-local failures remain `AtomicPathSearchNo`; they cannot be passed to a
root theorem without first supplying the missing child/tail alignment. The
remaining atomic work is to lift this root distinction through destination
exhaustion, rejected-child/tail induction, and escaped-commit bookkeeping.
The active root wrapper now has its first consumer theorem:
`atomic_path_root_active_failure_excludes_trace` eliminates the root wrapper
directly to the exhausted-input contradiction, rather than routing it through
the suffix-local result constructor.
Selected transition traces now carry their active source state explicitly in
both transition constructors. This is the canonical construction-site
invariant: an `AtomicSelectedPathTrace` rooted at `ThreadAccepted` cannot
contain a transition at all. The exact-root consumer theorem,
`atomic_path_root_exact_failure_excludes_trace`, therefore eliminates the
unconsumed-input refutation without unfolding the higher-order machine
destination function. The terminal `AtomicSelectedPrefixDone` and
`AtomicSelectedExactDone` constructors are excluded by their non-empty input
index, while both transition constructors are excluded by their active-source
index. This closes the exact counterpart of the active root theorem without a
runtime workaround or an opaque destination lemma.
The destination-exhaustion leaf now has its active-state consumer as well:
`atomic_path_active_destinations_exhausted_excludes_trace` is indexed by a
non-empty input, an active source, and an empty candidate-current spine. It
eliminates every selected-trace constructor directly, so the proof does not
inspect the erased refutation at runtime. This discharges the empty admitted
destination base case; recursive rejected-child/tail alignment and start-list
induction remain open.
The two exhaustion constructors are now indexed at `ThreadActive(source)`
at their definition site rather than accepting an arbitrary thread state.
Their only construction sites already run in the active branch, so this
removes the possibility of manufacturing an exhausted refutation for an
accepted thread and gives the recursive rejection proof a canonical state
discriminator.
`AtomicPathDestinationRejected` now carries the same active-source index and
canonical active destination equation. Its child state remains independent,
so accepted candidates can still carry an exact child refutation while the
parent traversal is statically known to be active; this is the shape needed
for the next child/tail induction.
The accepted-child base now has its own eliminator,
`atomic_path_exact_failure_excludes_trace`: with non-empty input and exact
polarity, `AtomicPathExactAcceptedWithInput` is the only remaining refutation
constructor, while every selected terminal or transition form is indexed
away. The recursive active-child theorem can therefore branch on the admitted
candidate constructor without inspecting an erased accepted failure at
runtime.
`AtomicPathInputExhausted` is likewise indexed at `Nil()` input, not merely
annotated by an erased empty witness. This prevents an exhaustion leaf from
being fabricated at a non-empty input and makes the input split of the next
refutation eliminator canonical.
The first extraction prerequisite is landed: admitted filtered states retain
their original boundary constraints instead of replacing them with `Nil()`.
Their routine still carries the assertion-participation markers used by later
conditions, while path constructors can now reconstruct the actual nested
decision evidence from the preserved constraints. Atomic Boolean consumers
already ignore this metadata, so the change does not re-evaluate an admitted
constraint or alter commitment behavior.
Depth exhaustion is no longer a refutation constructor. The proof-facing
lookahead and lookbehind decisions carry distinct `ResourceExhausted`
constructors, and neither positive nor negative assertion polarity treats
that outcome as satisfied. Authored literals remain rejected earlier with
`NestedAssertionDepthExceeded`, using the same canonical depth bound; the
runtime distinction prevents a manually constructed or proof-facing call from
manufacturing `NoMatch` merely by supplying insufficient depth.
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
interactions, parent-capture assertion conditionals, finite assertion
conditionals, and the first assertion-local capture sidecar are committed
(`9f8af26f` plus the current assertion-conditional slice). Atomic/possessive
scopes inside assertions, assertions inside atomic scopes, and conditional
branches that inspect an already-participating outer capture now use the finite
`LookaroundCompilation` IR and the same commitment relation. The first scoped
inline-option slice is now implemented: `(?i:...)`, `(?m:...)`, `(?s:...)`,
`(?u:...)`, `(?U:...)`, and their `-` removals are represented as lexical AST
nodes and propagated through ordinary, lookaround, atomic, and named
compilations. The source-sensitive `x` mode and execution-level `f`/`E` flags
remain deliberately rejected inside a scope until their source-map and
search-bound semantics have a canonical implementation. Finite assertion
conditionals over positive/negative lookahead and fixed-width lookbehind now
use `LookaroundBoundaryGuard` and the same bounded-history update as ordinary
lookbehind; focused regressions cover both polarities. This slice does not
discharge the remaining selected-trace correspondence for assertion-created
captures or generalized assertion/atomic combinations. Assertion-created
capture markers are now threaded through the shared constraint fold and the
capture-aware replay fold, so a later conditional sees the same participation
decision in ordinary and named execution; optional assertion captures cover both
participating and absent branches. Capture-aware prefix replay follows machine
order for lazy and ordered branches, with regressions for ordered alternation
and lazy repetition. Refutation values now retain dependent child and sibling
failure trees through both exact and prefix path folds, while depth/history
guard failures remain explicit resource certificates. An exhaustive
bounded-subject oracle covers the admitted nested lookaround decision slice;
the exact-path refutation soundness theorem is now implemented, including
capture-context identity and recursive child/tail exclusion. Complete
start-list search soundness is also implemented with a whole/current suffix
index and a constructive membership-spine proof. Prefix/lookahead rejection now
has a separate active-only failure family and matching path/start-search
soundness theorems; its witnesses retain capture-context, child-input,
child-destination, cursor, and selected-start membership evidence until the
proof consumes them. Constructive exact and prefix evaluator completeness is
also discharged: the shared start-list identity is an explicit result
parameter, and path/refutation theorems force the actual computed result into
the corresponding constructor. The exhaustive admitted-interaction manifest
now covers all 18 declared Phase 2 machine-shape classes against an independent
finite oracle. Resource-exhaustion polarity and assertion-proof erasure are
also covered by emitted-runtime regressions. Atomic prefix and exact commitment
have a direct hand-built-machine regression and the negative-atomic assertion
shape is part of the exhaustive oracle. Successful lookahead and lookbehind
witnesses retain the exact atomic routine used by both capture-marker extraction
and named replay, so those consumers no longer rerun the child search. The
atomic traversal now also constructs an erased exact-machine-indexed selected
trace. Transition nodes carry their ordered candidate cursor, selected-head
membership, and a canonical equation identifying the whole list with the exact
machine transition. Start nodes carry their canonical whole-list equation,
ordered suffix cursor, and selected-head membership. The focused
assertion-decision, exhaustive-model, and named-capture gate passes 50 tests.
The canonical constraint-admission fold now supplies the selected routine,
capture markers, and nested decision evidence needed by the indexed trace from
one child evaluation.
The selected routine, result split, originating input/rest, thread, history,
capture context, policy, scope depth, mode, and consumed prefix are now trace
indices. Each transition also retains the exact canonical admission's capture
markers and nested decisions. The clean serialized 50-test gate passed in 386
seconds; that increase needs follow-up elaboration profiling. The
raw-versus-filtered candidate mismatch now has one construction authority:
boundary admission materializes a typed `LookaroundAdmittedState` sidecar, and
the ordinary filtered machine-state list is only a projection of that list.
This prevents proof paths and runtime filtering from independently rebuilding
different admitted candidates. Atomic start and transition selection now
traverse that sidecar directly. Their erased cursors, selected-head membership,
and canonical equations are indexed by `lookaround_admitted_starts` and
`lookaround_machine_admitted_destinations`, so admission metadata and the
chosen path cannot diverge. Successful lookahead and lookbehind witnesses now
consume this selected trace as their proof object; the legacy exact/prefix path
searches have been removed from successful decision branches. This avoids the
invalid alternative of proving two calls equal after the fact: destination
filtering, nested assertion admission, and atomic selection occupy the same
recursive totality SCC, so such calls are intentionally opaque while the SCC is
checked. The serialized assertion-decision, exhaustive-model, and named-capture
gate now passes 51 tests in 267.9 seconds on a warm interface build. The first
cold rebuild after changing these indices took roughly twelve minutes and must
remain a performance follow-up, but the admitted Phase 2 proof/extraction exit
gate itself is discharged.

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

**Current checkpoint:** `\\Q...\\E` quoted literals and the first Unicode
binary properties (`\\p{ASCII}`, `\\p{Cased}`, `\\p{Lowercase}`,
`\\p{Uppercase}`, `\\p{Alphabetic}`, `\\p{White_Space}`,
`\\p{Hex_Digit}`, `\\p{Math}`, and `\\p{Currency_Symbol}`, plus every
canonical name and alias in the pinned Unicode Script table (including
`\\p{Latin}`, `\\p{Greek}`, `\\p{Cyrillic}`, and `\\p{Hiragana}`), with their
negated forms) are implemented. Quoted literals
normalize at compile time to the existing exact-character sequence tree: the
first terminator closes the quote; an absent terminator quotes to the end, and
`\\\\E` after a closed region remains the ordinary literal backslash-E form.
The focused quoted-literal regression passes 3 tests, and the Unicode-property
regression covers positive and negated ASCII and generic boolean properties;
the same property surface now uses the pinned `Std.Char` Unicode predicates
for casing, alphabetic, whitespace, hexadecimal, math, currency, generic
boolean properties, script membership, and `Bidi_Class`/`bc` short and long
values. General-category names (including `General_Category=...`/`gc=...` and
derived names such as `Assigned`), Script (including `Script=...`/`sc=...`),
Bidi (`Bidi_Class`/`bc`, `Bidi_Control`, `Bidi_Mirrored`, Boolean
`Bidi_Paired_Bracket`, and `Bidi_Paired_Bracket_Type`/`bpt`), and generic property names are
validated at macro time and emitted as atoms. Script_Extensions uses the
vendored Unicode 17.0.0 UCD file and defaults to the primary Script value for
code points omitted by that file. Bare `\\N` (including inside a class) now
lowers to the finite complement of Cure's Unicode newline predicate. The
fixed-width `\\uHHHH` and `\\UHHHHHHHH` escapes now share the existing scalar
validator. The
paired-bracket type table is pinned to Unicode 17.0.0 `BidiBrackets.txt`.
The parser now rejects `\\X` with the stable structured diagnostic
`:UnsupportedRegexGrapheme`; it must not silently reinterpret the escape as a
literal `X`. The `Std.Char.unicode_bidi_paired_bracket` API now exposes the
pinned paired scalar while the regex property remains Boolean membership.
Remaining Phase 3 work is grapheme clusters,
duplicate-name and capture-layout policy, other finite control normalizations,
and the remaining control families below. `(*FAIL)` and terminal `(*ACCEPT)`
are already implemented as finite normalizations.

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

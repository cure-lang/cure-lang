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

The package-boundary regression models the embedded sources as the `cure_regex`
package itself (rather than accidentally scanning them as part of `stdlib`).
This keeps the manifest identity, source-hash namespace, export filtering, and
acyclic dependency checks aligned with the package artifact produced by the
stdlib bootstrap. A package-specific ordering property now rebuilds that
manifest from reversed and rotated source lists and requires identical
canonical entries, so filename order cannot rekey the embedded modules.

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
The start-list proof now records `AtomicStartFailureKind` in the refutation
index, distinguishing exhaustion, candidate rejection, and commitment-blocked
nodes without adding a runtime field to the erased `AtomicStartMembersNo`
payload. Skipped starts carry indexed origin evidence, and successful starts
carry the corresponding allowed-selection certificate. Construction-site
consumers now discharge an active rejected head's exhausted child and an
empty rejected tail. The remaining non-empty tail induction must specialize
at the construction site: a generic eliminator may not inspect an erased
refutation sum, and making its kind tag relevant would duplicate evaluator
control metadata rather than preserve proof erasure.
The nested-terminal construction boundary now has proof-only erased
counterparts for both active input exhaustion and exact accepted-with-input
absurdity. These helpers consume the fully indexed selected trace and
refutation with every runtime premise erased, so nested dispatch can discharge
the impossible index directly without manufacturing a runtime argument or
relaxing relevance checking. Direct Runtime compilation and a synthetic
erased-terminal construction regression pass. Recursive non-terminal
destination rejection, tail alignment, and complete start-list correspondence
remain open.
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
The refutation constructors now also carry an erased
`LookaroundAdmittedStateCursorSuffix` value, and the internal member traversal
threads it from the root through every tail drop. Tail suffixes are built by
composing the parent-to-head relation with the canonical head-to-tail drop;
they are never reconstructed from the unindexed cursor after the fact. The
stored suffix is now available at the child theorem boundary. `AtomicPathSearchNo`,
`AtomicPathMembersNo`, and escaped no-results publish that suffix alongside
their refutation, and `AtomicPathDestinationRejected` records both the failed
child suffix and the sibling-tail suffix at the construction site. The first
tail-aligned consumer,
`atomic_path_destination_rejection_excludes_recursive_trace`, uses the
tail-local selected suffix to discharge a rejected candidate whose sibling
tail reaches destination exhaustion. The existing
exhausted-child eliminator still consumes only its specialized empty-input
index; the new construction-site wrapper passes the stored child suffix, the
selected child suffix, and the selected child trace into the aligned-child
eliminator. The eliminator consumes the stored refutation suffix before
delegating to the active-input contradiction; equality between independently
existential child cursors remains a later recursive slice.
Selected transition constructors now retain the erased equivalence between
the child refutation's origin spine and the selected child's origin spine.
`transport_lookaround_admitted_cursor_suffix_outer` and
`atomic_child_cursor_alignment` turn that common-origin equation plus the two
ordered suffixes into an explicit cursor-alignment relation. The relation is
construction-site proof data only; no child list or equality witness survives
in the emitted matcher. The recursive rejected-child consumer still needs to
invoke this bridge for non-terminal child failures.
Atomic no-results now publish an explicit erased origin list and
`origin_equivalence` on both suffix-local and root no constructors. The
members evaluator supplies the canonical admitted-destination spine at the
construction site, and escaped no-results carry that same origin proof through
tail reintroduction. This removes the previous implicit-origin gap; consumers
still need to thread the published proof through the outer failure wrapper.
Atomic destination-rejection nodes now retain the child origin/equivalence and
the sibling-tail origin/equivalence supplied by those no-results. The outer
failure wrapper therefore preserves both canonical spines instead of dropping
them when it builds the recursive refutation tree; the theorem consumer still
needs to invoke the alignment bridge for a non-terminal rejected child.
The first child-specific consumer,
`atomic_path_child_input_exhaustion_excludes_trace`, now matches the stored
refutation suffix before delegating to the active-input contradiction. This
keeps the child boundary indexed even in the base case; recursive child and
sibling-tail alignment remain open.
The exact-acceptance counterpart,
`atomic_path_child_exact_failure_excludes_trace`, performs the same stored
suffix check before discharging an accepted child with unconsumed input. Both
terminal child refutation shapes now have construction-site consumers; only
destination exhaustion and rejected-child/tail recursion remain in this
induction family.
An explicit `LookaroundAdmittedStateCursorAlignment` relation now compares two
candidate suffixes from one common ordered spine in either direction. Its
construction eliminates each surface equality before refining the dependent
branch, so the relation is accepted by the kernel without an E093-shaped
nested-constructor workaround. This is still groundwork: refutation nodes do
not yet retain a suffix proof for every failed child, so the full recursive
child/tail theorem must consume this relation at the next construction site.
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
The corresponding zero-input accepted-destination rejection is now discharged
by `atomic_path_accepted_destination_rejection_excludes_trace`. Its child
refutation would have to be `ThreadAccepted()` at `Nil()` input, but the only
empty-input constructor is active-only; the contradiction is consumed before
any selected trace is inspected.
The first child-alignment eliminator,
`atomic_path_destination_rejection_excludes_aligned_child`, now consumes the
stored child refutation suffix at the active exhausted-input base and receives
the selected child suffix and child trace from the construction site. It then
passes the child trace's indexed empty-input contradiction to
`atomic_path_input_exhaustion_excludes_trace`; no erased witness is inspected
at runtime. The selected transition now also retains the common-origin
equivalence needed to align that suffix with a refutation suffix; the generic
`atomic_child_cursor_alignment` bridge is ready for the recursive consumer.
A first sibling-tail leaf is now also consumed at the construction site, but
recursive rejected-child alignment, non-empty sibling-tail induction, and
escaped-commit bookkeeping remain open.
The recursive destination-list evaluator now has an internal
`AtomicPathMembersResult` indexed by its whole and current admitted-state
spines. Ordinary tail rejection therefore carries the exact `remaining`
suffix needed by the child/tail induction instead of an unconstrained public
search result. An inner commitment that escapes the candidate is retained as
an explicit erased escaped-no branch while the public matcher result remains
unchanged. The focused assertion gate passes 33 tests; the selected-trace
theorem still has to consume this indexed result and account for escaped
commitment separately.
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
The active-child alignment boundary now has an explicit erased indexed witness,
`AtomicPathActiveChildAlignment`. Its `Here`, `There`, and `Reverse`
constructors are produced from the canonical cursor-alignment and selected-suffix
location relations, so a later contradiction consumer can distinguish a
head-selected child from a sibling-tail child without inspecting proof data at
runtime. The focused dependent-assertion suite passes 97 tests and the full
canonical pipeline passes 52 checks (50 tests and 2 properties) with W086
accepted. This is alignment infrastructure only: the construction-site
active-child contradiction, arbitrary sibling-tail induction, and start-list
correspondence remain open.
The selected-trace constructors now derive active and accepted child capture
contexts through the same reducible construction helpers used by refutation
trees. This removes the duplicated spelling of child context at the trace
boundary and keeps the change proof-only; the emitted runtime is unchanged. A
regression covers both transition and start traces, and the focused
dependent-assertion suite passes 98 tests. The active-child parent now
constructs its `AtomicPathActiveChildSelectionPackage` at an erased argument
boundary and eliminates it through a proof-only consumer before invoking the
ordinary contradiction continuation. This avoids a relevant `let` binding of
an erased package (which the kernel correctly rejects as an erased-value
relevance error) without adding a runtime wrapper or tag. The package's
selected child cursor, origin cursor, and child trace therefore remain
available to the construction-site branch. The complete child/tail
contradiction still needs to consume those fields, and arbitrary sibling-tail
induction plus the start-list correspondence remain open.
The Phase 2 exit gate is therefore still not discharged.

The root start-refutation boundary has since been strengthened: the public
`AtomicStartRefutationRoot` now retains the parallel `AtomicStartNoEvidence`
certificate alongside the complete failure tree.  This preserves the
construction-site data required to dispatch arbitrary recursive start-list
failure kinds without reconstructing an erased tail witness.  The first
exhaustion consumer, `atomic_start_root_exhaustion_excludes_trace`, consumes
the indexed failure/evidence pair and reduces the empty-root case to the
existing membership contradiction.  This is a base-case slice only; the
non-empty rejected/blocked start-fold and complete atomic selected-trace
correspondence remain open.  `./cure check` and the focused dependent-
assertion suite (121 tests) pass.

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
remain a performance follow-up. That gate discharges the admitted
 proof/extraction sub-slice, but the full Phase 2 exit remains open while the
 later atomic selected-trace/refutation correspondence is completed.

The atomic path refutation slice now indexes `AtomicPathRefutation` by an
erased `AtomicPathFailureKind`, distinguishing input exhaustion, exact
acceptance with trailing input, destination exhaustion, and recursive
destination rejection. Child and tail refutations carry their own kinds, while
root and search-result wrappers preserve the same index. This keeps the
constructor-specific impossible branches in the proof rather than recovering
the failure reason from runtime data; the kind is proof metadata and adds no
runtime control field. The focused dependent-assertion file passes 63 tests,
and the canonical pipeline gate passes 52 checks (50 tests and 2 properties).
The accepted-destination child suffix now has a named canonical eliminator,
`atomic_path_failure_excludes_selected_suffix`, which delegates at the
construction site to the indexed exact-child contradiction. The serialized
full canonical gate still passes 52 checks with W086 accepted. This is only
the accepted-child slice: arbitrary sibling-tail `Drop` induction and the
remaining active-child/refutation combinations are still open and must not be
treated as discharged by this alias.
The next construction-site slice,
`atomic_path_tail_destinations_exhausted_excludes_selected_suffix`, consumes a
non-empty selected suffix after a rejected head when the stored sibling-tail
refutation is destination exhaustion. Its tail current spine is fixed to
`Nil()` by the refutation index, so the cursor contradiction is discharged
directly by `atomic_path_destinations_exhausted_excludes_trace`; no erased list
is inspected at runtime. The focused dependent-assertion file now passes 64
tests. General recursive rejected-child and multi-head sibling-tail induction
remain open.
The next recursive tail slice is now present in
`atomic_path_tail_rejection_excludes_selected_suffix`: when a sibling tail
rejects an accepted candidate, the construction-site consumer matches the
selected transition before the erased scope witness, refines the accepted
child scope, and forwards an `AtomicPathFailureExactAccepted` child to the
canonical exact-child eliminator. The exact-child theorem's trace metadata is
explicitly erased, so this transport cannot add runtime proof arguments. The
focused dependent-assertion file passes 65 tests, and the full canonical gate
passes 52 checks (50 tests and 2 properties) with W086 accepted. This still
covers only the accepted-child tail branch; active-child rejection,
multi-head `Drop` recursion, and start-list induction remain open.
The active-child base slice is now present in
`atomic_path_tail_active_child_exhaustion_excludes_selected_suffix`: a sibling
tail rejection whose active candidate's child reaches input exhaustion is
consumed through `atomic_path_destination_rejection_excludes_aligned_child`.
The selected parent transition is matched before the erased scope alignment,
and the child cursor suffix remains erased. The focused dependent-assertion
file passes 66 tests, and the full canonical gate passes 52 checks (50 tests
and 2 properties) with W086 accepted. Active-child destination exhaustion and
recursive child rejection, multi-head `Drop` induction, and start-list
induction are still open.
The aligned active-child destination-exhaustion base is now named
`atomic_path_active_child_destinations_exhausted_excludes_trace`; it delegates
to the existing active empty-cursor contradiction while retaining the child
failure and selected trace as erased indices. The focused dependent-assertion
file remains at 66 passing tests and the canonical gate remains 52 passing
checks. This is only the empty-child-cursor leaf; non-empty selected child
suffixes still require the recursive cursor-alignment induction.

The next alignment boundary is now named
`atomic_path_active_child_destinations_exhausted_excludes_aligned_trace`.
It transports the selected child cursor across the published common-origin
equivalence, consumes `atomic_child_cursor_alignment`, and routes the
left-to-right case through `atomic_path_failure_excludes_aligned_trace`.
Right-to-left alignment remains an explicit proof-only continuation rather
than being incorrectly classified as impossible. This is a construction-site
boundary, not the Phase 2 exit theorem: the continuation and the non-terminal
rejected-child, sibling-tail, and start-list cases remain open. The focused
dependent-assertion file now passes 91 tests.

The sibling-tail induction now has a branch-specific construction boundary,
`atomic_path_destination_rejection_excludes_recursive_tail_rejected`. Its
parent refutation remains indexed by the full `remaining` suffix, while the
rejected-tail case is handed to a proof-only continuation. Cure rejects
inspecting the existential tail failure kind after erasure, so this branch is
separated by its indexed constructor rather than by a runtime tag. This is
transport infrastructure for the recursive tail theorem, not the
contradiction itself; the continuation must still consume the tail's child
failure and selected trace. The focused dependent-assertion file now passes
92 tests.

The first child/tail crossing boundary is now named
`atomic_path_tail_active_child_rejection_excludes_selected_suffix`. It fixes
the selected tail head as an active state, retains the child failure and
cursor suffix at the child indices, and exposes the active child transition
trace before handing the recursive contradiction to a proof-only
continuation. The parent and child rejection kinds are separated by their
indexed construction sites; no erased child kind is inspected at runtime.
This is still transport infrastructure—the continuation must consume the
child rejection correspondence. The focused dependent-assertion file now
passes 93 tests.

The child-side cursor bridge is now named
`atomic_path_active_child_rejection_excludes_aligned_trace`. It consumes the
child failure suffix, the selected-origin equivalence, and the selected child
suffix through `atomic_child_cursor_alignment`, then exposes explicit
left-to-right and right-to-left continuations. This keeps the existential
child failure erased while making the cursor direction available at the
construction site; it is the alignment eliminator for the next recursive
child/tail proof, not that proof's completion. The focused
dependent-assertion file now passes 94 tests.

The selected child suffix now has its own indexed location split,
`AtomicPathSelectedChildLocation`, produced by the reducible helper
`atomic_path_selected_child_suffix_location`. Its `Here` branch consumes the
suffix equality to expose the selected head, while `There` preserves the
exact sibling-tail suffix. The split is deliberately proof-only: an attempted
runtime continuation over the erased alignment witness was rejected by E104
and was not retained. The existing aligned bridge therefore remains the
proof-only direction boundary; the next step is to consume this location in a
fully erased child/tail eliminator. The focused dependent-assertion file now
passes 95 tests.

The proof-only consumer is now explicit as
`atomic_path_selected_child_suffix_location_elim`. It accepts a relevant
non-empty selected suffix, reduces the indexed location split at the
construction site, and invokes only zero-argument continuations; no erased
suffix or location is passed to runtime code. This is the safe interface the
future child/tail contradiction can call once its surrounding refutation
constructor exposes a relevant suffix. The focused dependent-assertion file
remains at 95 tests.

The active-child rejection bridge now exposes that relevant suffix at the
construction boundary. It carries an explicit head/tail decomposition of the
generic failure spine together with an `Equivalent` proof to that `Cons` form,
transports the selected whole/suffix equivalence across the decomposition, and
invokes `atomic_path_selected_child_suffix_location_elim` in the
left-to-right alignment branch. The right-to-left branch remains a separate
proof-only continuation. This is the first actual consumer of the
`Here`/`There` location split, not merely another transport alias; the
recursive child contradiction, arbitrary sibling-tail descent, and start-list
correspondence are still open. The focused dependent-assertion file passes 95
tests.

The recursive active-child tail boundary now invokes that bridge directly.
Its construction-site parameters publish the child input as a non-empty
`Cons`, retain the child failure cursor and selected-origin equivalence as
relevant suffix witnesses, and carry the non-empty failure-spine equation
explicitly while keeping the refutation and path payloads erased. The bridge
consumes only those typed cursor/equivalence premises and returns proof-only
continuations; no child failure tag, path witness, or list cursor is promoted
into runtime data. Cure's hidden-index checker required the unused depth index
to be removed and the cursor origins to be explicit-but-erased at this call
site. The focused dependent-assertion file passes 96 tests. This remains a
recursive correspondence boundary: the left-tail continuation, reverse
alignment, arbitrary sibling-tail induction, and start-list proof are not yet
discharged.

The rejected destination now also publishes an
`AtomicPathTailPackage` at the construction site. Its
`AtomicPathRejectedTailAt` alias preserves the sibling-tail input, state,
context, and spine indices while keeping the existential tail failure kind
erased. The first consumer,
`atomic_path_tail_package_destinations_exhausted_excludes_trace`, unwraps that
package only in a proof-only match and reuses the canonical
destination-exhaustion contradiction. The parent consumer obtains the package
through `atomic_path_destination_rejected_tail_package` rather than recovering
the tail failure inline. This is a typed package boundary, not completion of
the recursive rejected-child or multi-head sibling induction; those branches
remain open. The focused dependent-assertion gate passes 99 tests.

The next bounded tail case is now named
`atomic_path_tail_drop_rejection_excludes_selected_suffix`. It retains the
parent-to-selected cursor as an erased `Drop` index for the exact two-state
parent/singleton-selected base and reuses the accepted-child rejection
eliminator without inspecting proof data at runtime. The focused
dependent-assertion file passes 67 tests, and the full canonical gate passes
52 checks (50 tests and 2 properties) with W086 accepted. This is not yet the
arbitrary non-empty-tail induction: recursive child rejection and multi-head
`Drop` transport remain open.

The accepted-head `Drop` transport is now generalized to an arbitrary sibling
tail. `atomic_path_tail_drop_rejection_excludes_selected_suffix` carries an
erased `tail_remaining` list through the parent refutation, tail refutation,
cursor suffix, and selected path indices, so the accepted-child contradiction
does not depend on a singleton tail. This is still the head case of the
induction: selected-later `There` descent, recursive rejected-child
correspondence, and complete start-list induction remain open. The focused
dependent-assertion file passes 100 tests.

The first start-list commitment base is now present in the constructor-specific
eliminators `atomic_start_blocked_active_candidate_excludes_trace` and
`atomic_start_blocked_accepted_candidate_excludes_trace`. They consume the
`AtomicStartFailureBlocked` index together with the matching
`AtomicStartSkipEvidence`/`AtomicStartAllowed` pair, so a candidate suppressed
by an enclosing or candidate atomic commit cannot also be the selected start.
The active and accepted state constructors are separate deliberately: matching
an erased `LookaroundAdmittedState` sum would violate E104, while the indexed
constructor match erases cleanly. The focused dependent-assertion file now
passes 68 tests. This discharges only the blocked-head start base; rejected
child starts, blocked-tail induction, and complete start-list correspondence
remain open.

The accepted-start exact-child base is now present in
`atomic_start_accepted_candidate_rejection_excludes_trace`. For an accepted
candidate whose child refutation is `AtomicPathFailureExactAccepted`, it
consumes the published child cursor suffix and delegates to
`atomic_path_child_exact_failure_excludes_trace`; the selected-start branch is
constructor-indexed, so the erased state sum is never inspected at runtime.
The focused dependent-assertion file now passes 69 tests. Internal
`AtomicStartMembersNo` results now also carry a typed erased
`AtomicStartNoEvidence` witness. Its exhausted, rejected, and blocked
constructors are built at the result construction sites, and the recursive
tail witness is preserved for subsequent induction. The accepted-tail consumer
`atomic_start_tail_accepted_candidate_rejection_excludes_trace`
matches that witness before forwarding the separately indexed exact child
certificate to the accepted-start eliminator; this removes the E093-prone
direct match on the raw dependent tail refutation. The focused file now passes
71 tests. Recursive
rejected starts, active-child/start combinations, blocked-tail induction, and
the complete start-list correspondence remain open.

The active-child recursive start base is now present in
`atomic_start_tail_active_candidate_rejection_excludes_trace`. It consumes the
typed rejected-tail witness at a non-empty current suffix whose head is an
active candidate, then forwards the independently indexed input-exhaustion
child certificate to `atomic_start_candidate_rejection_excludes_trace`.
The focused dependent-assertion file now passes 73 tests. Blocked-tail
induction and complete start-list correspondence remain open.

The blocked-tail bases are now present in
`atomic_start_tail_blocked_active_candidate_excludes_trace` and
`atomic_start_tail_blocked_accepted_candidate_excludes_trace`. Each matches
the typed `AtomicStartNoBlockedEvidence` branch and consumes the same indexed
skip/allow contradiction as the head case, without reconstructing a raw
dependent tail failure. Their current suffix is now arbitrary rather than
singleton, so the commitment contradiction is available at every blocked
head in the recursive start list. The focused dependent-assertion file now
passes 75 tests. Selecting a later unblocked sibling still requires recursive
tail correspondence, and complete start-list correspondence remains open.

A typed accessor, `atomic_start_rejected_tail_evidence`, now packages the
existential failure kind carried by a rejected recursive tail in
`AtomicStartTailEvidence`. This gives subsequent membership-based consumers a
well-typed way to descend through the tail without matching the raw dependent
`AtomicStartMembersRefutation` or guessing its failure index. The focused
dependent-assertion file now passes 76 tests. The next proof must still connect
`ListMember` selection to this accessor and establish correspondence for an
arbitrary later sibling; complete start-list correspondence remains open.

The recursive rejected-tail accessor now also has an `AtomicStartTailPackage`
form that retains the raw tail refutation together with its typed no-result
witness. An active-headed specialization packages that tail under the active
state indices, so the next membership induction can descend without guessing
the existential tail failure kind. The child refutation for the selected head
is intentionally still consumed by the branch-specific eliminator; exposing
that existential child scope and cursor as one more package is a separate
kernel-checked step. The focused dependent-assertion file remains at 78 tests
once the new source regression is included.

`AtomicStartMemberLocation` now makes the induction split explicit: matching
`ListMemberHere` produces a head witness, while `ListMemberThere` preserves
the tail membership witness. The helper is construction-site indexed rather
than a Boolean membership test, so the eventual refutation proof can recurse
on the exact sibling suffix. The focused file now passes 79 tests; the actual
`Here` contradiction and `There` recursive descent are still the next proof
step.

The generic `atomic_start_rejected_member_induction` eliminator now carries a
rejected parent failure and its matching `AtomicStartNoEvidence` witness at
`Cons(head, rest)`, then selects supplied head and tail cases through the
typed membership location. Its tail case is a zero-data continuation, so the
`ListMemberThere` proof is never passed as a runtime argument. This is an
induction boundary only: it does not invent a tail proof or erase the
branch-specific child certificate. A first attempt to make the active branch
call an erased `Empty` continuation was rejected by the kernel's
runtime-erasure check and was removed. The focused file now passes 81 tests;
the actual recursive contradiction remains open.

The first package-to-proof consumer is now present in
`atomic_start_rejected_tail_package_exhausted_excludes_trace`. It unpacks an
`AtomicStartTailPackage` whose remaining start suffix is definitionally empty,
matches its `AtomicStartExhausted` refutation, and forwards the exact tail
membership, failure, and selected trace to `atomic_start_failure_excludes_trace`.
`lookaround_absurd` lifts the resulting `Empty` contradiction into the
polymorphic consumer result. This establishes the exhausted-tail base through
the new package boundary without claiming the non-exhausted rejected or
blocked branches. The focused file now passes 82 tests; head contradiction and
later-sibling recursive descent remain open.

The first construction-site `Here` consumer is now present in
`atomic_start_rejected_member_here_excludes_trace`. It splits the typed member
location before touching the rejected parent; at a selected active head with
empty child input, the parent `AtomicStartCandidateRejected` index admits only
the `AtomicPathInputExhausted` child constructor, so the canonical active-child
contradiction can be applied without recovering an existential child failure
tag or inspecting proof data at runtime. Duplicate/next-member locations are
delegated through a typed tail-package continuation. This is only the active empty
child `Here` base, not arbitrary head failure kinds or recursive `There`
descent. The focused dependent-assertion file now passes 83 tests.

The start-membership induction boundary now carries an
`AtomicStartRejectedTailAt(...)` package to its `There` continuation. The
package is extracted from the single rejected-result constructor, preserving
the recursive tail refutation and no-result witness without classifying the
existential tail failure kind. The active empty-child consumer now accepts and
forwards that typed package as well, so a later sibling can be handled at its
own construction site rather than discarded as a unit-valued branch. This is
transport infrastructure, not the recursive contradiction itself: the
non-empty-sibling `There` consumer and its active/accepted/rejected/blocked
tail cases remain open. The focused dependent-assertion file now passes 84
tests.

The first concrete recursive `There` consumer is now present as
`atomic_start_rejected_member_there_exhausted_tail_excludes_trace`. It splits
the parent `ListMember` spine, leaves the head obligation to its caller, and
forwards the inherited tail membership to
`atomic_start_rejected_tail_package_exhausted_excludes_trace`. The tail is
definitionally `Nil()`, so this discharges the exhausted-tail base without
runtime inspection or fabricated membership. Non-empty recursive tails and
their active, accepted, rejected, and blocked cases remain open. The focused
dependent-assertion file now passes 85 tests.

The non-empty `There` boundary now also has a construction-site continuation
form: `atomic_start_rejected_member_there_nonempty_tail_excludes_trace` carries
the typed `AtomicStartTailPackage`, the selected membership in its non-empty
tail, and the selected trace in its indices, then invokes a zero-argument
continuation that closes over those erased proofs. Cure rejects passing an
erased package, membership, or trace as ordinary callback arguments (E104), so
the continuation is deliberately closure-based and introduces no runtime proof
branch. This is transport infrastructure for the recursive tail theorem, not
the contradiction itself; active, accepted, rejected, and blocked non-empty
tail consumers remain open. The focused dependent-assertion file now passes 86
tests.

The safe proof-only continuation shape is now named
`atomic_start_rejected_member_induction_erased`. It mirrors the package-carrying
membership split but invokes a zero-argument `tail_case`; callers can close over
the erased tail package and membership without passing those witnesses through
a runtime callback. A temporary experiment that made the callback itself
erased was rejected by E104 and removed; the committed helper keeps the
continuation relevant while keeping its captured proof data in erased indices.
This is the canonical bridge for the next non-empty `There` consumer, not the
recursive contradiction itself. The focused dependent-assertion file now passes
101 tests.

The first concrete non-empty-tail head consumer is now present as
`atomic_start_rejected_member_there_active_tail_head_excludes_trace`. It
specializes the later-sibling `There` branch to an active head with an empty
child input, matches the typed `AtomicStartNoRejectedEvidence` witness, and
forwards the indexed child exhaustion certificate and selected trace to the
existing active-tail eliminator. Its proof-only package, membership, and trace
remain in erased indices; the call passes only the explicit erased witnesses
required by the construction-site helper, omitting the implicit result fields.
This is the active-head base for non-empty-tail descent, not the full recursive
correspondence: accepted, rejected, blocked, and arbitrary-tail cases remain
open. The focused dependent-assertion file now passes 87 tests.

The active-head consumer is now connected to the erased induction bridge. It
supplies the exact parent refutation and no-result witness as proof indices,
dispatches `ListMemberHere`/`ListMemberThere` through
`atomic_start_rejected_member_induction_erased`, and leaves later duplicate
members to a zero-argument continuation. The active-child contradiction is
therefore applied only to the selected head branch; a later equal active state
is no longer silently treated as the head. This is still one head case, not
recursive tail completion. The focused dependent-assertion file now passes 102
tests.

The accepted-head consumer is now connected to the same erased induction
bridge. It supplies the exact parent refutation and no-result witness as
erased indices, preserves the exact child input and `False()` prefix mode,
and dispatches `ListMemberHere`/`ListMemberThere` without inspecting a
runtime candidate tag. The accepted-child contradiction is therefore limited
to the selected head branch; later duplicate members remain the zero-argument
tail continuation. This is still a head integration, not recursive tail
completion. The focused dependent-assertion file now passes 103 tests.

The blocked active and blocked accepted head consumers now use the specialized
`atomic_start_blocked_member_induction_erased` bridge. It fixes the parent
refutation and no-result witness to `AtomicStartFailureBlocked()`, preserves
the typed skip/allow commitment, and dispatches both membership branches
without runtime state inspection. This closes all four known non-empty-tail
head shapes at the induction boundary, but it still does not recurse through
the later sibling tail or prove the complete start-list correspondence. The
focused dependent-assertion file now passes 105 tests.

The accepted and blocked non-empty-tail head consumers now take an independent
erased `selected_start` index instead of hard-coding the candidate as the
selected value. Their relevant `ListMember` argument can therefore represent
either `Here` or an arbitrary later `There` sibling; the existing erased
induction bridge handles the split without introducing a runtime membership
branch. The active-head consumer remains specialized to its construction-site
`Here` case; the non-empty recursive dispatcher that links an arbitrary
selected path to that head case is still open.

The accepted-head counterpart is now present as
`atomic_start_rejected_member_there_accepted_tail_head_excludes_trace`. It
specializes the non-empty `There` branch to an accepted head with exact child
input, matches the typed `AtomicStartNoRejectedEvidence` witness, and delegates
to `atomic_start_tail_accepted_candidate_rejection_excludes_trace`, consuming
the indexed exact-child refutation and suffix before forwarding the accepted
start contradiction. The selected trace retains `policy` in its index, and
`atomic_path_child_exact_failure_excludes_trace` now fixes its child-failure
index to `AtomicPathFailureExactAccepted()` instead of accepting an unnecessary
explicit failure-kind witness. This is the accepted-head base, not full
recursive start-list correspondence: rejected and blocked non-empty-tail cases,
arbitrary later siblings, and complete correspondence remain open. The focused
dependent-assertion file now passes 88 tests.

The blocked-active-head counterpart is now present as
`atomic_start_rejected_member_there_blocked_active_tail_head_excludes_trace`.
It consumes the typed `AtomicStartNoBlockedEvidence` witness for a blocked
active head in a non-empty rejected tail and applies the canonical indexed
skip/allow contradiction. The selected `AtomicSelectedTrace` remains an erased
index, so no runtime state inspection or second search is introduced. This is
the blocked-head base only: accepted-blocked heads, rejected-child heads,
arbitrary later siblings, and complete start-list correspondence remain open.
The focused dependent-assertion file now passes 89 tests.

The blocked-accepted-head counterpart is now present as
`atomic_start_rejected_member_there_blocked_accepted_tail_head_excludes_trace`.
It fixes the admitted head to `LookaroundAdmittedAccepted` in both the typed
no-result witness and the erased selected trace, then consumes the same
construction-site skip/allow contradiction without inspecting a runtime state
tag. This is the second blocked-head base only: rejected-child heads,
arbitrary later siblings, and complete start-list correspondence remain open.
The focused dependent-assertion file now passes 90 tests.

The successful search boundary now preserves the missing correspondence
explicitly. `AtomicSelectedStartWitness` packages the selected
`ListMember(LookaroundAdmittedState(...), selected_start, current)` together
with the `AtomicSelectedTrace`; `atomic_start_members_root_to_search` constructs
that package directly from `AtomicStartMembersYes`, and
`LookaroundRoutineSearchYes`, `LookaheadWitness`, and `LookbehindWitness` carry
it forward. The package is entirely erased, so runtime matching still sees
only the matched input, remainder, and replay routine. This removes the old
construction-site loss of membership evidence, but it does not yet implement
the recursive non-empty-tail dispatcher or its active-head generalization.
The focused dependent-assertion file now passes 106 tests.

The selected witness package now indexes both the complete start list and the
current suffix. Its constructor receives those two erased lists explicitly,
so tail transport cannot accidentally reattach a membership proof to an
unrelated spine. The public search and lookahead/lookbehind witness
constructors continue to erase the package and retain only runtime match
data; the recursive membership eliminator is still the next construction-site
step. The focused dependent-assertion file remains at 106 tests.

The active non-empty-tail head consumer now accepts an independent erased
`selected_start` index and dispatches arbitrary relevant membership through
`atomic_start_rejected_member_induction_erased`. Its path remains specialized
to an active head, so the `Here` branch can consume the active-child
contradiction while the `There` branch remains a continuation. The accepted
and blocked head consumers use the same construction-site pattern; the
general recursive tail dispatcher remains open. The focused
dependent-assertion file now passes 108 tests.

`atomic_selected_start_witness_tail` now transports a relevant selected
membership and its erased trace across one sibling boundary. Its result is
indexed at `current = tail_rest`, while retaining the original `whole` list,
so recursive consumers can no longer fabricate a parent-spine witness for a
tail refutation. This is a reusable transport boundary; it does not classify
the existential tail failure kind or discharge the recursive contradiction.
The focused dependent-assertion file now passes 109 tests.

The selected-start witness now also retains the erased `AtomicStartAllowed`
proof together with its `blocked_depth` and `AtomicStartSkipKind` indices.
`atomic_start_members_root_to_search` publishes that proof instead of
discarding it, and the lookahead/lookbehind wrappers preserve the existential
indices while keeping all of the evidence erased. This establishes the
selection-side invariant needed by the eventual blocked-tail dispatcher; it
does not yet relate that proof to an existential skip witness recovered from a
rejected tail. The focused dependent-assertion file passes 112 tests, and the
canonical stdlib pipeline passes with only the accepted W086 cycle warning.

The next proof boundary is now explicit as `AtomicStartScopeSelection`. Its
role index distinguishes blocked from escaping scope decisions, while the
constructors retain the shared `AtomicDepthAtLeast(scope, commit)` or
`AtomicDepthBelow(scope, commit)` witness. `atomic_depth_at_least_excludes_below`
and `atomic_start_scope_selection_excludes` consume that relation structurally;
the kernel rejects the attempted candidate-only tag because both constructors
can inhabit the same candidate-indexed family. This is a sound construction
boundary for the eventual blocked-tail dispatcher, not yet that dispatcher's
integration with existential start evidence. The focused dependent-assertion
file passes 113 tests.

The next transport slice is now landed. `AtomicStartScopeEvidence` records the
erased admitted candidate together with the canonical skip/allow token;
blocked records are carried by `AtomicStartNoBlockedEvidence`, and allowed
records are carried through `AtomicStartMembersYes`,
`AtomicSelectedStartWitnessPacked`, and the rejected-sibling tail transport.
The full admitted state is intentionally not placed in the family indices:
that formulation made the elaborator normalize the large candidate term at
every downstream refutation site and expanded the single-file check from the
42-second baseline to several minutes. The construction-site record retains
the exact candidate and the authoritative indexed skip/allow evidence while
keeping those expensive terms erased. `./cure check` passes; the focused
assertion suite observes 113/113; and the full canonical pipeline passes 52/52
with only the accepted W086 cycle warning.

The blocked-tail dispatcher boundary is now wired. Both blocked-tail theorem
bodies consume their `AtomicStartScopeEvidence` record through the canonical
`atomic_start_scope_record_excludes_allowed` helper before delegating to the
authoritative indexed skip/allow contradiction. The helper pattern-matches the
recorded scope constructor, so a blocked tail cannot silently bypass the
construction-site scope evidence; the separately threaded `AtomicStartSkipEvidence`
and `AtomicStartAllowed` values remain the indexed authority because the
role-only scope family deliberately avoids re-normalizing the full candidate.
The red source regression covers both blocked-tail branches. The focused
dependent-assertion suite now observes 114/114, `./cure check` passes, and the
full canonical pipeline remains 52/52 with only W086. The remaining Phase 2
work is the general recursive tail dispatcher and the final selected-trace /
refutation correspondence; this slice closes the blocked-tail construction
boundary without claiming those later proofs are complete.

The blocked recursive tail now has a typed package boundary of its own.
`AtomicStartBlockedTailPackage` pairs the blocked parent refutation, the
canonical skip/allow indices, the scope record, and the blocked no-result
witness. `atomic_start_blocked_tail_package` constructs that package only at
the blocked evidence boundary, and
`atomic_start_rejected_member_there_nonempty_tail_blocked_excludes_trace`
feeds it to the proof-only `atomic_start_rejected_tail_dispatch_blocked`
consumer. That consumer runs the generic blocked membership induction, so the
active and accepted admitted-state constructors share the same construction
authority without a runtime state-tag match. The selected-later branch is
still an erased continuation for the next tail package; rejected-child and
non-blocked failure kinds remain intentionally outside this slice. The new
focused regressions observe 116/116, `./cure check` passes, and the canonical
pipeline remains 52/52 with only W086.

The accepted recursive tail now has the corresponding typed package boundary.
`AtomicStartAcceptedRejectedTailPackage` keeps the parent rejected-start
certificate, the exact accepted-child `AtomicPathRefutation`, its cursor suffix,
and the typed no-result witness together at the accepted-head indices. The
construction-site bridge
`atomic_start_rejected_member_there_nonempty_tail_accepted_excludes_trace`
unpacks that package only through its erased indices and delegates to
`atomic_start_rejected_member_there_accepted_tail_head_excludes_trace`, which
preserves the recursive tail continuation rather than proving only the head.
The bridge binds the child cursor spines as erased implicits, avoiding the
E011 hidden-index inference failure encountered by the first formulation. The
focused dependent-assertion suite now observes 117/117, `./cure check` passes,
and the full canonical pipeline remains 52/52 with only W086. The remaining
Phase 2 work is the active/rejected non-blocked recursive dispatch, integration
of these construction-site branches with the complete start-search fold, and
the final selected-trace/refutation correspondence.

The active root-tail construction boundary is now named
`AtomicStartActiveRootTailPackage`. It wraps the existing root-child package
instead of reopening the broad `AtomicPathRefutation` GADT at a new constructor
site (the latter formulation was rejected by E093 because input exhaustion
fixes the child cursor to the empty root). The reducible consumer
`atomic_start_active_root_failure_empty` matches that wrapper and forwards the
proof-only recursive continuation; the non-empty-tail bridge
`atomic_start_rejected_member_there_nonempty_tail_active_excludes_trace` gives
the construction site an explicit active/non-blocked name without promoting
the erased package or selected trace into runtime data. This is transport
scaffolding, not the completed active/rejected start-fold or the final
selected-trace/refutation theorem. The focused dependent-assertion suite now
observes 118/118; `./cure check` passes; and the full canonical pipeline remains
52/52 with only W086.

The active non-empty-tail bridge now invokes the existing indexed active-head
eliminator. It carries the parent rejected-start failure/evidence and the
empty-child `AtomicPathRefutation` as erased construction-site arguments, then
checks the root-tail package through a proof-only `with_case` gate before
returning the head contradiction or recursive continuation. A direct attempt
to change the package family index from `ThreadState` to `Bounded` was rejected
by E093 at the GADT constructor, so the state relation remains explicit at
the consumer rather than being smuggled through a weaker package index. This
closes the active-head consumer boundary but does not yet wire it into
`atomic_lookaround_routine_initial_tail_after_failure`; the complete active /
rejected fold and final selected-trace/refutation correspondence remain open.
The focused dependent-assertion suite remains 118/118, `./cure check` passes,
and the canonical pipeline remains 52/52 with only W086.

The active root-tail proof package now keeps the parent and child capture
contexts distinct and carries the already-indexed child exhaustion refutation
directly. Its root/empty-input invariant is enforced by the
`AtomicPathRefutation` indices, avoiding a second root wrapper at the
construction site; the attempted `Bounded` family index remains rejected by
E093 and is not used. `atomic_start_rejected_member_here_excludes_trace`
publishes this package, and
`atomic_start_rejected_member_there_nonempty_tail_active_excludes_trace`
consumes it before invoking the indexed active-head eliminator. The source
regressions and canonical stdlib compilation now pass 119/119 focused tests,
with `./cure check` green and the canonical pipeline still 52/52 with only
the accepted W086 cycle warning. The package is still a construction-site
bridge: wiring it into `atomic_lookaround_routine_initial_tail_after_failure`
and completing the general active/rejected start-fold and final
selected-trace/refutation correspondence remain open.

The atomic destination-rejection fold now has an explicit selected-suffix
dispatcher, `atomic_path_destination_rejection_selected_suffix_dispatch`.
It consumes the relevant cursor relation only through the reducible
`atomic_path_selected_child_suffix_location_elim`: a selected `Here` remains
with the caller's child contradiction, while a selected `Drop` is handed to
the caller's typed recursive-tail continuation. This closes the construction
site's head-versus-sibling distinction without claiming the child contradiction
or recursive tail theorem itself; those continuations are still the remaining
proof obligations. The focused dependent-assertion suite is 122/122,
`./cure check` is green, and `./scripts/check-canonical-module-pipeline --full`
is 52/52 with only the accepted W086 cycle warning.

The non-empty rejected-start `There` boundary now consumes refined rejected
failure and no-result witnesses directly.  It rebuilds the parent membership
with `member_there` and delegates to
`atomic_start_rejected_member_induction_erased`; the existential tail package
is therefore never inspected as runtime control flow.  This is the canonical
erasure-safe shape for the remaining recursive start-list correspondence, and
the source regression pins both the `There` transport and the induction
handoff.  The focused dependent-assertion suite is 123/123, `./cure check` is
green, and the canonical pipeline remains 52/52 with only the accepted W086
cycle warning.

That boundary now accepts distinct `head_case` and `tail_case` continuations.
The indexed induction can therefore discharge a selected non-empty tail head
with its own candidate contradiction while reserving `tail_case` for a deeper
recursive sibling; forwarding the same continuation to both branches was an
incomplete proof shape.  The focused dependent-assertion suite is 124/124,
`./cure check` is green, and the canonical pipeline remains 52/52 with only
the accepted W086 cycle warning.

The non-empty branch of `atomic_start_initial_tail_no` now preserves the active
root proof package instead of collapsing every rejected candidate into the
ordinary `AtomicStartMembersNo` constructor. At the construction site it
reuses `atomic_start_active_root_no_empty` with the actual non-empty input and
the indexed active candidate, retaining the parent membership, child
refutation, tail evidence, and `AtomicStartActiveRootTailPackage` for the same
proof-facing fold used at the empty boundary. Accepted candidates still take
the ordinary rejected result path. The focused dependent-assertion suite now
passes 125 tests, `./cure check` is green, and the full canonical pipeline is
52/52 with only the accepted W086 cycle warning. This closes the active
non-empty construction boundary; the package is still consumed by the
proof-only start-list dispatcher rather than by runtime control flow, so the
general recursive active/rejected fold and final selected-trace/refutation
correspondence remain open.

The recursive active-tail retry now has its own indexed
`AtomicStartMembersTailActiveNo` result. It preserves both the parent
no-result/refutation and the no-result/refutation for the recursive tail while
the parent candidate is reintroduced by
`atomic_start_initial_tail_no_with_active_tail`. The constructor is proof-only,
and the root/blocked adapters map it through the same parent failure/evidence
authority as ordinary no-results; no runtime tag or fallback lookup was added.
The source regression pins the active-tail constructor and the
`AtomicStartMembersActiveRootNo` → retry construction site. The focused
dependent-assertion suite passes 126/126, `./cure check` is green, and the full
canonical pipeline passes 52/52 with only the accepted W086 cycle warning.
This preserves the recursive tail's typed refutation boundary; carrying the
full active proof package through arbitrary sibling retries and completing the
selected-trace/refutation correspondence remain open.

The selected-trace side now has a generic construction-site dispatcher,
`atomic_path_destination_rejection_excludes_recursive_tail`. It accepts an
arbitrary rejected-candidate tail, preserves the indexed `Here`/`There` split
through `atomic_path_selected_child_suffix_location_select`, and keeps the
head and recursive-tail results explicit. The singleton rejected-trace
construction now routes through the corresponding
`atomic_path_destination_rejection_excludes_recursive_tail_empty` dispatcher,
so it uses the same indexed authority instead of a one-off bare match. The
cursor witness remains runtime-relevant at this eliminator because its
constructors are inspected; proof payloads and traces remain erased. This is
the canonical dispatcher boundary for the final path correspondence, not that
correspondence itself: the selected child contradiction and recursive sibling
refutation still need to be consumed through the general fold. The focused
dependent-assertion suite passes 129/129 and `./cure check` is green.

The first destination-tail leaf now uses that dispatcher in an actual
construction site: `atomic_path_tail_destinations_exhausted_excludes_aligned_trace`
builds its typed exhaustion contradiction once, transports the selected cursor
through the rejected candidate with `LookaroundAdmittedStateCursorSuffixDrop`,
and lets the generic `Here`/`There` authority select the result. The cursor is
runtime-relevant only at this indexed proof eliminator; the refutation, path,
and contradiction payloads remain erased. The focused dependent-assertion
suite passes 130/130, `./cure check` passes, and the full canonical gate passes
52/52 with only the accepted W086 cycle warning. Recursive rejected-child and
arbitrary sibling-tail consumers remain the next proof obligations.

The accepted-destination sibling-tail leaf now follows the same route:
`atomic_path_tail_rejection_excludes_selected_suffix` constructs the exact-child
contradiction once and transports its accepted-tail cursor through
`atomic_path_destination_rejection_excludes_recursive_tail`. The indexed
`Drop(head, ...)` relation selects the recursive-tail result; the cursor is
runtime-relevant only at this proof eliminator, while refutations, paths, and
callback payloads remain erased. The focused dependent-assertion suite passes
131/131 and `./cure check` is green. Arbitrary rejected-child alignment,
multi-head sibling recursion, and the complete selected-trace/refutation
correspondence remain open.

The active-child rejected-tail construction now uses the same parent fold:
`atomic_path_tail_active_child_rejection_excludes_selected_suffix` first builds
the child contradiction through
`atomic_path_active_child_rejection_excludes_aligned_trace`, then transports it
across the parent `LookaroundAdmittedStateCursorSuffixDrop` with
`atomic_path_destination_rejection_excludes_recursive_tail`. This keeps the
child's left-to-right head/tail and reverse alignment cases as proof-only
continuations while the parent cursor is the sole runtime branch authority.
The focused dependent-assertion suite passes 132/132, `./cure check` passes, and
the full canonical gate passes 52/52 with only the accepted W086 cycle warning.
The general recursive rejected-child alignment and multi-head sibling fold are
still open.

The active-child alignment theorem now consumes the canonical
`atomic_path_active_child_alignment` result rather than duplicating cursor
transport and direction matching inline. Its indexed `Here`, `There`, and
`Reverse` constructors dispatch to the corresponding proof-only continuations;
the parent active-child construction then carries that result through the
`Drop(head, ...)` destination-rejection fold. This removes a second alignment
authority while preserving runtime erasure. The focused dependent-assertion
suite passes 132/132, `./cure check` passes, and the full canonical gate passes
52/52 with only the accepted W086 cycle warning. Instantiating the recursive
tail continuation for arbitrary rejected children and completing the
multi-head sibling fold remain open.

The accepted-sibling rejected-tail construction now consumes the
constructor-specific `atomic_path_destination_rejection_excludes_recursive_tail_rejected`
dispatcher instead of calling the generic fold directly. Its tail failure is
already indexed as `AtomicPathDestinationRejected`, so this handoff preserves
that constructor fact without inspecting an erased failure tag at runtime; the
candidate, selected trace, and path payloads are proof-only, while the cursor
suffix remains the sole branch authority. The focused dependent-assertion suite
passes 132/132 with all 331 documentation snippets, `./cure check` passes, and
the full canonical gate remains 52/52 with only the accepted W086 cycle
warning. The general rejected-child alignment, arbitrary multi-head sibling
fold, and final selected-trace/refutation correspondence are still open.

The active-child sibling tail now uses the same constructor-specific rejected
dispatcher. `atomic_path_tail_active_child_rejection_excludes_selected_suffix`
passes its statically known `AtomicPathDestinationRejected` tail through
`atomic_path_destination_rejection_excludes_recursive_tail_rejected`, retaining
the active child's aligned contradiction as the tail result and keeping all
failure and trace payloads erased. The cursor suffix remains the only runtime
branch witness. The focused dependent-assertion suite remains 132/132 with all
331 documentation snippets, `./cure check` passes, and the full canonical gate
remains 52/52 with only the accepted W086 cycle warning. General rejected-child
alignment, arbitrary multi-head sibling recursion, and the final
selected-trace/refutation correspondence remain open.

The recursively rejected active-child boundary now has a named, proof-only
consumer: `atomic_path_active_child_rejection_excludes_trace`. The parent
active-child sibling construction routes its ordered `Here`/`There`/`Reverse`
alignment through this consumer, which delegates to the single canonical
`atomic_path_active_child_alignment` authority. It introduces no runtime
failure tag, callback payload, or alternate lookup path; the existing
constructor-specific rejected dispatcher remains the source of the sibling
tail result. This is a construction-site normalization slice, not the final
recursive child theorem: destination-exhaustion transport, arbitrary
multi-head sibling recursion, and selected-trace/refutation correspondence
remain open. The focused dependent-assertion suite passes 133/133,
`./cure check` passes, and the canonical gate is unchanged at 52/52 with only
the accepted W086 cycle warning.

The singleton destination-exhaustion tail is now consumed through the named
`atomic_path_active_child_rejection_excludes_tail_exhaustion` construction-site
consumer. Its failure index fixes the parent as a rejected destination and the
tail as `AtomicPathFailureDestinationsExhausted`; after the indexed cursor
boundary is reduced, it delegates to the active destination-exhaustion
contradiction. The existing singleton rejected-trace fold now uses this
consumer, so the proof no longer duplicates the exhaustion transport in that
branch. All failure, cursor, and selected-trace arguments remain erased. This
is one concrete recursive-tail base case; arbitrary rejected-child recursion,
non-singleton sibling induction, complete start-list correspondence, and the
final selected-trace/refutation theorem remain open. The focused
dependent-assertion suite passes 134/134, `./cure check` passes, and the full
canonical gate passes 52/52 with only the accepted W086 cycle warning.

A two-sibling rejected-tail boundary is now typed explicitly by
`atomic_path_destination_rejection_excludes_nested_tail_rejection`. It keeps
the outer rejected list at `Cons(candidate, Cons(nested_candidate, Nil()))`,
the nested rejection at a singleton cursor, and its nested tail at
`AtomicPathFailureDestinationsExhausted`; the existing singleton recursive
consumer then discharges the nested tail through two erased `Drop` transports.
The proof boundary takes those refined nested refutations as erased arguments,
so an existential tail kind is never inspected at runtime. This is a concrete
multi-head induction slice and construction-site interface; it is not yet the
generic tail-kind refinement or arbitrary-length sibling induction. The
focused dependent-assertion suite passes 135/135, `./cure check` passes, and
the full canonical gate passes 52/52 with only the accepted W086 cycle
warning. Arbitrary rejected-child recursion, complete start-list
correspondence, and the final selected-trace/refutation theorem remain open.

The two-sibling boundary now obtains the nested tail from the parent failure
through `atomic_path_destination_rejected_tail_package`, rather than accepting
independent nested failure witnesses. The new reducible
`atomic_path_rejected_tail_refinement` consumer matches the package only at
the proof-only construction boundary and hands its extracted tail to
`atomic_path_destinations_exhausted_tail_refinement`; both consumers return
`Empty`, so erased failure kinds and cursor evidence never become runtime
values or branch tests. Runtime match data remains explicit because the
underlying trace consumer needs it. This closes the construction-site package
refinement for the concrete two-sibling case without claiming generic
tail-kind elimination or arbitrary-length sibling induction. The focused
dependent-assertion suite passes 137/137, `./cure check` passes, and the full
canonical pipeline passes 52/52 with only the accepted W086 cycle warning.
Arbitrary rejected-child recursion, complete start-list correspondence, and
the final selected-trace/refutation theorem remain open.

A deeper sibling-tail construction slice is now present as
`atomic_path_destination_rejection_excludes_three_tail_rejection`. Starting
from a rejected three-candidate destination list, it extracts the typed tail
package at the second candidate, refines that package at the next
constructor-specific `AtomicPathDestinationRejected` boundary, and then
reuses the singleton rejected-tail refinement for the third candidate. The
two package peels are proof-only; failure kinds, candidate lists, and traces
remain erased, and no runtime failure tag or alternate search is introduced.
This demonstrates the first non-singleton sibling fold beyond the concrete
two-candidate boundary, but it is deliberately not reported as arbitrary
length induction: the generic recursive tail dispatcher, arbitrary rejected
child alignment, complete start-list correspondence, and final
selected-trace/refutation theorem remain open. The source regression passes
in a direct Elixir check. The focused Mix test cannot start in this checkout
because its locked Hex dependencies are unavailable; direct Cure compilation
gets past this new definition and currently stops on the pre-existing
`Std.Char.lowercased_characters` E091 in the regex runtime.

The Regex package is now aligned with the acyclic text-layer boundary from the
stdlib: `Std.Char` owns list-valued Unicode case mappings, while
`Std.String` owns nominal `String` wrappers. `Std.Regex.Runtime` calls the
canonical `Std.Char.lowercased_characters/1` entry point directly and does not
recreate the old `Std.Char -> Std.String` dependency. The complete embedded
package source set (`regex*.cure`) has been checked through the compiler's
`use`-dependency graph and its full qualified-call closure; every component is
a singleton in both views, with the package layers ordered Core -> Runtime ->
Proof/Language -> façade as intended. Regressions now guard both graphs. The
remaining E091 is therefore a stale
published `Std.Char` interface (the old artifact still advertises
`lowercased_charlist`), not an unresolved Regex source dependency; rebuilding
the canonical stdlib generation is required before the direct package compile
can be rerun.

The blocked root-start construction now has an explicit typed bridge,
`atomic_start_root_blocked_tail_dispatch`. It preserves the parent
`AtomicStartMembersRefutation` and matching `AtomicStartNoEvidence`, constructs
the `AtomicStartTailPackage` at the proof boundary, and forwards the candidate
to the existing non-empty-tail blocked dispatcher. The dispatcher is lifted
through `lookaround_absurd`, so its `Empty` contradiction can serve any result
type; the later sibling remains a zero-argument proof-only continuation. A
source regression pins this construction shape, and direct compilation of the
complete `lib/std_deps/regex/regex_runtime.cure` module succeeds. This is still
one construction-site slice: the bridge is not the general non-empty
start-fold or the final selected-trace/refutation correspondence.

The public root wrapper now consumes that bridge through
`atomic_start_refutation_blocked_excludes_trace`. Its failure and no-result
evidence are both refined to the same non-empty `Cons(candidate, remaining)`
spine before dispatch, so the existential root list cannot be peeled by a
runtime tag or by rebuilding a tail witness. A regression pins the wrapper's
`AtomicStartFailureBlocked`/`AtomicStartNoEvidence` pairing and bridge handoff;
the complete Regex runtime compiles directly. The general blocked start-fold
and final selected-trace/refutation theorem remain open.

The public rejected-root path now has the corresponding generic adapter,
`atomic_start_refutation_rejected_excludes_trace`. It refines both existential
root indices to the same non-empty spine and delegates to
`atomic_start_rejected_member_induction_erased`, with separate head and
proof-only tail continuations supplied by the eventual concrete consumers.
The adapter is construction-site only: it does not inspect an erased failure
constructor or claim the general rejected-child theorem. Its source regression
and direct complete-module compilation pass; the concrete rejected head and
arbitrary sibling-tail consumers remain to be wired through the final
selected-trace/refutation correspondence.

The blocked sibling boundary now carries the selected membership and path in a
dedicated `AtomicStartBlockedSelectedTailPackage`.  Its constructor retains
the existential tail failure/evidence pair together with the blocked
skip/allow tokens, while the selected-start predecessor and replay path remain
erased indices.  The blocked non-empty-tail dispatcher and both blocked root
adapters consume this package instead of passing a zero-argument callback, so
later siblings cannot lose the selected trace while the search refutation is
transported.  The package declaration is placed after the complete
`AtomicSelectedTrace` constructor family, which is required for the Cure
declaration collector to register the indexed constructor before body checking.
The complete `Std.Regex.Runtime` source now compiles directly with this
transport and the focused source regression pins the package, dispatcher, and
root callback shapes.  Arbitrary mixed-kind sibling recursion and the final
selected-trace/refutation theorem remain open.

The first concrete rejected-root continuation is now named
`atomic_start_refutation_rejected_active_excludes_trace`. It fixes the root
candidate to an active admitted state with empty child input and forwards the
indexed failure/evidence pair to `atomic_start_rejected_member_here_excludes_trace`.
The latter consumes the active child contradiction at `Here` and retains the
typed `AtomicStartActiveRootTailProofPackage` for a later sibling at `There`.
The bridge is proof-only and does not re-run the machine or inspect an erased
state tag. Its source regression and direct complete-module compilation pass;
the accepted-head and arbitrary recursive-tail continuations remain open.

The first selected-trace consumer at the public root boundary is now named
`atomic_start_refutation_excludes_selected_trace`. Its erased arguments carry
the public `AtomicStartRefutation` wrapper and the same
`whole = Cons(candidate, remaining)` spine as the rejected root failure and
no-result evidence; the selected membership is then forwarded to
`atomic_start_refutation_rejected_excludes_trace`. The consumer is deliberately
restricted to the rejected-root kind while the kernel's erased GADT fields
remain proof-only, so no runtime constructor dispatch or duplicated search is
introduced. A source regression pins the root-list index, wrapper name, and
canonical rejected-fold handoff; direct compilation of the complete Regex
runtime passes. Exhausted and blocked root consumers, arbitrary rejected-child
recursion, and the final all-kinds selected-trace/refutation theorem remain
open.

The non-empty accepted-root case now has its own construction adapter,
`atomic_start_refutation_rejected_accepted_excludes_trace`. It fixes the root
candidate to `LookaroundAdmittedAccepted`, carries the exact
`AtomicPathFailureExactAccepted` child refutation and cursor suffix, and
delegates the `Here` contradiction to the existing accepted-child consumer;
the sibling continuation remains proof-only. Direct compilation and a source
regression pass. Empty-input accepted roots and the arbitrary start-list fold
remain open, so this does not discharge the Phase 2 correspondence gate.

The accepted-root contradiction is now wired through the public selected-trace
root consumer by `atomic_start_refutation_rejected_accepted_selected_trace`.
This construction site carries an `AtomicStartAcceptedRejectedTailPackage`,
passes its indexed membership and exact-child evidence to the canonical
accepted-tail consumer, and then supplies that contradiction to
`atomic_start_refutation_excludes_selected_trace` on the same accepted-head
spine. No erased package or failure tag is inspected as runtime control flow,
and no second machine search is introduced. The direct complete-module compile
and source regression pass. Empty-input accepted roots, blocked-root wiring,
arbitrary sibling recursion, and the final all-kinds selected-trace/refutation
theorem remain open.

Blocked public roots now have the corresponding selected-trace adapter,
`atomic_start_refutation_blocked_selected_trace`. It forwards the indexed
skip/allow evidence, root failure/no-result pair, selected membership, and
trace to `atomic_start_refutation_blocked_excludes_trace`, keeping commitment
control proof-only and leaving sibling recursion to the typed continuation.
The direct complete-module compile and source regression pass. The remaining
root obligations are empty-input accepted roots, arbitrary rejected-child and
sibling recursion, and the final all-kinds selected-trace/refutation theorem.

The selected-tail construction boundary now preserves the inherited membership
needed for arbitrary sibling recursion. `AtomicStartSelectedTailPackage`
bundles the recursive tail refutation/evidence with the `ListMemberThere`
predecessor witness and the unchanged `AtomicSelectedTrace`; the new
`atomic_start_rejected_member_induction_selected_erased` extracts that package
at the rejected `There` branch instead of invoking a zero-argument
continuation. The existing non-empty rejected-tail adapter is wired through
this induction, so the tail's current spine and selected trace remain aligned
without runtime dispatch or a second machine search. A direct source
regression and complete `regex_runtime.cure` compilation pass. The public
root adapters and branch-specific accepted/blocked/active consumers still need
to consume this package to discharge arbitrary rejected-child and sibling
recursion, followed by the all-kinds selected-trace/refutation theorem.

The active rejected-sibling construction now consumes the selected-tail package
at both empty-child boundaries: `atomic_start_rejected_member_there_active_tail_head_excludes_trace`
and its non-empty-tail adapter use the selected induction rather than a
zero-argument continuation. Because the existing active-candidate contradiction
uses a trace indexed to the active head, these helpers carry a separate
`selected_path` indexed to the later selected start; the two paths are never
coerced. The active branch therefore preserves both the head contradiction and
the recursive membership/trace alignment. The source regression and complete
Regex runtime compilation pass. Accepted and blocked sibling branches, public
root wiring, arbitrary rejected-child recursion, and the final all-kinds theorem
remain open.

The accepted rejected-sibling path now carries the same selected-tail contract
through both the exact-child head consumer and its non-empty-tail adapter.
`atomic_start_rejected_member_there_accepted_tail_head_excludes_trace` keeps
the accepted-head `AtomicSelectedTrace` separate from the selected-start trace,
and `atomic_start_rejected_member_there_nonempty_tail_accepted_excludes_trace`
forwards that pair together with an `AtomicStartSelectedTailPackage`. The
accepted public root adapter supplies a typed sibling package and feeds the
selected path into `atomic_start_refutation_excludes_selected_trace`; the
active root adapter now supplies the corresponding package shape as well. This
removes the remaining zero-argument continuation at these accepted/root
construction sites without conflating head and selected indices. Complete
`regex_runtime.cure` compilation and the source regressions pass. Blocked
sibling transport, arbitrary rejected-child recursion, and the final all-kinds
selected-trace/refutation theorem remain open.

The exhausted public root now has the matching selected-trace construction
adapter, `atomic_start_refutation_exhausted_selected_trace`. It carries the
root `AtomicStartRefutation`, its aligned exhausted member/evidence pair, and
the selected-start membership claim into the existing empty-root eliminator.
Because the membership is indexed at `Nil()`, the contradiction is discharged
at the construction site; no runtime failure tag, cursor payload, or second
machine traversal is introduced. The source regression passes and the complete
`regex_runtime.cure` module compiles directly. Empty-input accepted roots,
arbitrary rejected-child/sibling recursion, and the final all-kinds
selected-trace/refutation theorem remain open.

The empty-input accepted-root boundary now has its own indexed consumer,
`atomic_start_accepted_empty_child_excludes_trace`. Its child certificate is
fixed to `ThreadAccepted()` at `Nil()`, so the only possible empty-input
refutation constructor is active-only and reduces to `Empty` at the construction
site. The public adapter
`atomic_start_refutation_rejected_accepted_empty_selected_trace` threads that
contradiction through the shared selected-start fold while keeping the
later-sibling continuation typed and erased. This closes the accepted
empty-child base case without adding a runtime tag or duplicating the child
search; arbitrary rejected-child/sibling recursion and the final all-kinds
selected-trace/refutation theorem remain open. The source regression and direct
complete-module compilation pass.

The destination-rejected sibling-tail fold is now generalized beyond the
singleton and three-sibling fixtures. `atomic_path_rejected_tail_fold_excludes_trace`
recurses over the indexed `LookaroundAdmittedStateCursorSuffix`; its
construction-site package step peels one `AtomicPathDestinationRejected` tail
without inspecting the erased existential failure, and the empty suffix routes
to the aligned destination-exhaustion contradiction. The existing three-tail
consumer now calls this fold, so its proof no longer encodes a fixed sibling
count. The complete `Std.Regex.Runtime` module compiles directly with no
warnings and the source regression passes. This closes only the arbitrary-length
destination-rejection-tail chain; rejected child correspondence, mixed failure
kinds, start-list recursion, and the final all-kinds selected-trace/refutation
theorem remain open.

The generalized destination-rejection fold is now instantiated by a concrete
four-sibling theorem, `atomic_path_destination_rejection_excludes_four_tail_rejection`.
Its indexed candidate spine contains four rejected destinations and four
ordered `Drop` transports before the empty cursor; the complete Regex runtime
compiles with zero warnings, and the source regression confirms that this
instantiation calls the recursive fold rather than introducing another
fixed-arity helper. This is additional coverage of the fold's arbitrary-tail
shape only; mixed tail-failure kinds, rejected-child correspondence,
start-list recursion, and the final all-kinds selected-trace/refutation theorem
remain open.

The accepted-selected-tail case now has a direct recursive construction site,
`atomic_path_rejected_tail_fold_to_accepted_from_failure`. Each
`AtomicPathDestinationRejected` tail constructor exposes the next existential
refutation while the indexed cursor suffix supplies the next sibling; the
`Here` branch first refines the selected `AtomicSelectedTransitionAccepted`
path and then reuses `atomic_path_failure_excludes_selected_suffix` for the
exact-child trailing-input contradiction. Matching the selected path before
the child refutation keeps dependent transport proof-only and passes the
complete Regex runtime compile with zero warnings. No package wrapper,
runtime failure tag, or second machine search is introduced. This closes only
the accepted-head tail recursion; active/rejected child failures, mixed
failure kinds beyond the recursive destination-rejected spine, start-list
recursion, and the final all-kinds theorem remain open.

The active-child alignment witness no longer has a vacuous reverse constructor.
`AtomicPathActiveChildAlignment` now indexes the failed current suffix and
stores an explicit `LookaroundAdmittedStateCursorSuffix` for every direction:
the head case stores the failure-to-head relation, the tail case stores both
the failure-to-selected and tail-to-selected relations, and the reverse case
stores the selected-to-failure relation. The alignment constructor therefore
cannot be fabricated with an unrelated `Unit`; its indexed cursor evidence is
the same authority consumed by the active-child proof dispatcher. The complete
Regex runtime still compiles directly and the focused source regression passes.
This strengthens the proof boundary but does not yet discharge the arbitrary
rejected-child recursion or final all-kinds selected-trace/refutation theorem.

The recursive active-child rejection boundary now keeps the failed child cursor
and the selected child cursor as distinct erased indices.  The former remains
the current list of the `AtomicPathRefutation`; the latter indexes the selected
suffix supplied to `atomic_path_active_child_rejection_excludes_trace`.  The
previous signature forced both cursors to the same list, which made a selected
trace that had advanced through a different ordered sibling spine impossible to
state without an unsound coercion.  The construction site now passes the
selected suffix through its own index while retaining the failure suffix for the
canonical `atomic_path_active_child_alignment` eliminator.  The source
regression pins both binders and the complete `regex_runtime.cure` module
elaborates directly in 52 seconds.  This is an index-separation slice only;
transporting the path's constructor-local suffix into the parent equality,
arbitrary rejected-child recursion, and the final all-kinds
selected-trace/refutation theorem remain open.

The selected child suffix now has an explicit outer-origin transport authority,
`atomic_path_active_child_selection_suffix_transport`.  It transports a
`LookaroundAdmittedStateCursorSuffix` across the selected-child whole-spine
equality instead of asking each caller to rebuild or guess the cursor list.  A
source regression pins the equality and suffix indices.  Parent integration
is intentionally still open: the path constructor's selected suffix carried
its current spine through implicit constructor arguments, so consumers could
not refine that spine at the construction boundary.  The active and accepted
transition constructors now publish `child_whole`, `child_selected_whole`, and
`child_current` as explicit erased fields, and
`atomic_path_active_child_selection_package` packages those
fields together with the selected suffix, its outer-origin transport, and the
recursive child trace.  The complete `regex_runtime.cure` module elaborates
directly in about 51 seconds, and a source regression pins the explicit erased
indices.  The package now also carries the selected-whole `Equivalent` witness,
giving the generic parent alignment one construction-site source for that
equality.  The package consumer now refines that witness to `reflexive` before
invoking its continuation, so the equality cannot be silently discarded at the
erased boundary.  This is still only a local construction-site refinement, not
consumption by the parent contradiction: arbitrary rejected-child recursion and
the final all-kinds
selected-trace/refutation theorem remain open.  No bare-name or unchecked cast
bridge is introduced.

The active-root no-result constructor now publishes an erased
`active_current_equivalence` witness relating its result cursor to the exact
`Cons(active, remaining)` start-list spine.  The root adapter consumes that
equality by matching on `reflexive` before wrapping the failure, so the active
head cannot be silently discarded at the public start boundary.  This is a
construction-site invariant only; arbitrary start-list recursion and the final
selected-trace/refutation correspondence remain open.  The red source
regression passes and the complete `Std.Regex.Runtime` module compiles
directly with no warnings.

The active-root start-list equality is now consumed at every existing
downstream construction site that can carry the no-result forward:
`atomic_start_initial_tail_no_with_active_tail`,
`atomic_lookaround_routine_initial_tail_after_failure`, and
`atomic_start_members_add_skipped_candidate` all match the erased
`active_current_equivalence` witness before reintroducing or prepending a
candidate.  This prevents the exact active-head spine from being dropped
between recursive start traversal and its public refutation wrapper.  The
focused source regression passes and the complete Regex runtime still compiles
with no warnings; arbitrary sibling recursion and final selected-trace
correspondence remain open.

The generic rejected-tail dispatcher now delegates to the named
`atomic_path_destination_rejection_selected_suffix_dispatch` boundary.  That
boundary returns an indexed `AtomicPathSelectedTailDispatch` branch selected
solely from the cursor: `AtomicPathSelectedTailHead` carries the caller's
already-built result, while `AtomicPathSelectedTailTail` carries a typed
`AtomicPathSelectedTailPackage` containing the recursive refutation, the tail
cursor suffix, and the selected path.  All of that evidence remains erased;
the dispatcher uses no higher-order runtime continuation and inspects no
failure tag.  The complete `Std.Regex.Runtime` module compiles directly with
zero warnings.  This centralizes the rejected-tail construction authority and
makes the exact package available for arbitrary sibling recursion, but the
recursive consumers and final all-kinds selected-trace/refutation theorem are
still open.

The first selected-tail consumer is now wired at the destination-exhaustion
base: `atomic_path_selected_tail_dispatch_destinations_exhausted` destructures
the indexed `Tail(package)` branch, refines its existential tail package to
`AtomicPathDestinationsExhausted`, and passes the preserved cursor suffix and
selected path to `atomic_path_failure_excludes_aligned_trace`.  The consumer
is polymorphic in its result type, so it introduces no special `Empty` path or
runtime tag.  A focused source regression and direct zero-warning runtime
compile pass.  Rejected-child recursion and non-empty sibling folds remain
open.

The destination-exhaustion consumer is now used by the singleton rejected-tail
construction site itself.  `atomic_path_tail_destinations_exhausted_excludes_aligned_trace`
passes the indexed dispatch to
`atomic_path_selected_tail_dispatch_destinations_exhausted`, which consumes
the preserved `AtomicPathSelectedTailPackage` rather than rebuilding a tail
failure or discarding the selected suffix.  Direct runtime compilation remains
zero-warning; the arbitrary rejected-child branch is still open.

The active-child side now has a matching proof-only package consumer at the
first concrete tail base:
`atomic_path_active_child_rejection_excludes_tail_package` consumes the indexed
`AtomicPathSelectedTailDispatch`, preserves the head result, and routes a
`Tail(package)` through the existing active destination-exhaustion contradiction.
The `Empty` contradiction is eliminated explicitly at this polymorphic boundary;
no runtime failure tag or unchecked conversion is introduced.  The focused
source regression and direct zero-warning `Std.Regex.Runtime` compile pass.
This helper is intentionally not claimed as the general non-empty rejected-child
fold: wiring the package into that recursive construction site, and consuming
all remaining tail-failure kinds, are still open.

The singleton `atomic_path_destination_rejection_excludes_recursive_trace`
construction site now routes its selected suffix through the generic dispatcher
and consumes the resulting `AtomicPathSelectedTailPackage` with that active-child
consumer.  The direct exhaustion call remains only as the already-built head
result supplied to the dispatcher; the selected tail itself is no longer
reconstructed from a separate refutation value.  A red source regression and a
direct zero-warning runtime compile pass.  The non-singleton rejected-child
fold, all remaining tail-failure kinds, and the final selected-trace/refutation
correspondence remain open.

The first non-singleton sibling peel now follows the same package discipline:
`atomic_path_destination_rejection_excludes_nested_tail_rejection` builds its
singleton nested contradiction, sends the parent `Drop` selection through the
generic dispatcher, and consumes the resulting package at
`atomic_path_rejected_tail_dispatch_excludes_trace`.  The package consumer
keeps the tail refutation and selected path existential and proof-only while
reusing the existing singleton refinement.  A focused source regression and
direct zero-warning runtime compile pass.  Arbitrary-length rejected-child
folding and the final all-kinds selected-trace/refutation theorem remain open.

The three-sibling construction now performs the next package peel through
`atomic_path_rejected_tail_dispatch_excludes_nested_trace`: its parent `Drop`
selection is dispatched once, the existential nested rejection is refined at
that boundary, and the final singleton package is consumed by the same
construction-site contradiction.  The old manually rebuilt inner package is
retained only as the already-built head result for the dispatcher, not as the
selected-tail input.  The focused source regression and direct zero-warning
runtime compile pass; arbitrary-length recursion and the all-kinds theorem
remain open.

The atomic selected-path result now also carries an erased
`AtomicPathSearchOrigin` witness.  Terminal accepted searches use the empty
origin constructor, while consuming active searches publish the exact
filtered transition-list equation from the member traversal.  That witness is
retained on both active and accepted selected-transition traces, so the next
rejected-child induction can compose a failed child's origin equation with
the selected child's canonical origin without rebuilding or guessing a list.
The direct `Std.Regex.Runtime` compile remains zero-warning.  This is a
construction-site transport slice only; the arbitrary rejected-child fold and
final all-kinds theorem remain open until a consumer eliminates the witness.

The active-child selection package now retains that erased
`AtomicPathSearchOrigin` witness instead of dropping it while packaging the
selected child cursors.  Its proof-only consumer matches the indexed active
origin constructor before invoking the child alignment continuation, so the
consumer cannot accept a transition whose child origin was not published by
the canonical member traversal.  The focused source regression and direct
zero-warning `Std.Regex.Runtime` compile pass.  This closes the package handoff
but does not yet prove the arbitrary rejected-child fold or the final
all-kinds selected-trace/refutation correspondence.

The cursor layer now exposes the missing non-empty decomposition authority:
`lookaround_admitted_cursor_suffix_nonempty` packages an erased
`whole = head :: tail` equality from any cursor suffix whose current spine is
non-empty. Its `Here` branch consumes the stored equality and its `Drop`
branch transports the decomposition with the canonical cons congruence. This
is the witness required by the active-child rejected-tail theorem; callers no
longer need to infer or locally rebuild that equality from a child refutation.
The focused source regression and direct zero-warning `Std.Regex.Runtime`
compile pass. The witness is a prerequisite for wiring the arbitrary
rejected-child consumer, not that consumer or the final all-kinds theorem
itself.

The active-child alignment boundary now consumes that non-empty witness at the
canonical construction site. `atomic_path_active_child_alignment_from_nonempty`
matches the erased decomposition and its equality to rewrite the whole cursor
to a `Cons` spine, then uses the existing selected-whole transport to classify
the selected child as head, later sibling, or reverse-aligned. A small indexed
`AtomicPathActiveChildAlignmentCase` carries only that three-way control result;
no erased head, tail, or equality is projected into a relevant argument. The
active-child rejected-tail wrapper packages the construction-site decomposition
once and delegates to this projection. This closes the former erased-to-
relevant proof leak, while arbitrary recursive child failure kinds and the
final all-kinds selected-trace/refutation theorem remain open. The focused
source regression and direct zero-warning runtime compile pass.

The destination-exhaustion branch now has its own typed construction-site
consumer, `atomic_path_tail_active_child_destinations_exhausted_excludes_selected_suffix`.
It accepts a destination-exhaustion child refutation, its empty-cursor suffix,
the selected-child whole-spine equivalence, selected cursor suffix, and child
trace as explicit witnesses. The parent rejection and selected trace are first
refined to the active-transition case, then those witnesses are forwarded to
`atomic_path_active_child_destinations_exhausted_excludes_aligned_trace`, which
uses the canonical cursor alignment and active destination-exhaustion leaf. No
existential child failure tag is inspected as runtime data, and no unchecked
cast or local index reconstruction is introduced. The direct runtime compile
and seven-test refutation regression pass; wiring this consumer into the
arbitrary rejected-child fold, handling the other three child failure kinds,
and proving the final all-kinds selected-trace/refutation correspondence remain
open.

The active-child construction site now has a canonical failure dispatcher,
`atomic_path_tail_active_child_failure_dispatch`. It branches on the relevant
child cursor spine (`Nil()` versus `Cons(...)`) rather than inspecting the
erased `AtomicPathRefutation` kind as runtime data. The empty-spine branch is
indexed to the destination-exhaustion constructor and forwards to the typed
destination consumer; the non-empty branch is indexed to destination rejection,
packages the required non-empty cursor witness, and forwards to the existing
recursive alignment authority. Input-exhausted and exact-accepted cases are
excluded by the input/thread indices. The direct zero-warning runtime compile
and the eight-test refutation regression pass. The dispatcher is a proof-only
construction-site boundary; integrating it into the arbitrary fold and proving
the final all-kinds selected-trace/refutation correspondence remain open.

The active-child destination-exhaustion construction now delegates to that
indexed failure dispatcher instead of duplicating its child-context refinement.
The dispatcher consumes the `Nil()` child-cursor branch directly through
`atomic_path_active_child_destinations_exhausted_excludes_aligned_trace`,
while the wrapper retains the parent rejection and selected-trace indices.
This avoids recursive re-entry through the wrapper and leaves the dispatcher as
the single construction authority for the exhausted-child kind. The direct
`Std.Regex.Runtime` compile is green and the focused path-refutation source
slice passes 9/9. Non-empty rejected-child recursion, arbitrary sibling-tail
folding, start-list correspondence, and the final all-kinds
selected-trace/refutation theorem remain open.

The accepted-sibling construction site now uses the existing arbitrary indexed
fold, `atomic_path_rejected_tail_fold_to_accepted`, instead of a fixed first
tail peel. The selected accepted candidate, its cursor suffix, and its path are
passed directly to the fold; its recursive tail branch therefore preserves the
same erased refutation/path indices for any later sibling. This removes the
duplicated two-sibling accepted-tail proof without adding runtime state or
reconstructing a candidate. The direct zero-warning `Std.Regex.Runtime`
compile is green, and the source regression pins the generic fold call.
Active/rejected child recursion, arbitrary rejected-tail exhaustion folding,
start-list correspondence, and the final all-kinds selected-trace/refutation
theorem remain open.

The active-child rejected-tail construction now has the corresponding generic
fold, `atomic_path_rejected_tail_fold_to_active`. It recursively consumes the
selected active candidate's rejected sibling suffix, matching only the
indexed cursor and parent destination-rejection constructors; each adjacent
candidate is handed to the original construction-site consumer,
`atomic_path_tail_active_child_rejection_excludes_selected_suffix_base`.
The wrapper preserves the public theorem shape while the base's head and
remaining-tail witnesses are explicitly proof-erased, so the fold introduces
no runtime representation or alternate resolver. The direct zero-warning
`Std.Regex.Runtime` compile and the focused dependent path-refutation
regression pass 11/11. Remaining work is to wire the other child-failure kinds
and destination-exhaustion cases through the same fold, complete start-list
correspondence, and prove the final all-kinds selected-trace/refutation
theorem.

The active-child alignment construction now computes the canonical alignment
case once and routes its `Here`/`There`/`Reverse` result through the
proof-only `atomic_path_active_child_rejection_tail_fold` dispatcher. The
later-sibling case is therefore an explicit construction-site continuation,
while the cursor and alignment witnesses remain erased; no runtime branch or
failure-tag inspection is introduced. The direct zero-warning
`Std.Regex.Runtime` compile and the focused dependent path-refutation
regression pass 12/12. This is the typed dispatch/wiring slice, not the final
child-failure-tail consumer: candidate-specific tail refutations, the other
child-failure kinds, destination-exhaustion integration, start-list
correspondence, and the all-kinds selected-trace/refutation theorem remain
open.

The active-child failure dispatcher now enumerates all four constructors of
`AtomicPathFailureKind` at the indexed child boundary. `InputExhausted` and
`ExactAcceptedWithInput` are explicitly discharged as impossible for a
non-empty active child, `DestinationsExhausted` continues through the typed
empty-cursor consumer, and `DestinationRejected` continues through the
non-empty alignment consumer. This makes the failure-kind partition
exhaustive without inspecting an erased tag at runtime. The direct
zero-warning `Std.Regex.Runtime` compile and the focused path-refutation
regression pass 13/13. The recursive child-tail consumers, complete
start-list correspondence, and final all-kinds selected-trace/refutation
theorem remain open.

The active-child selection package consumer no longer takes a zero-argument
lambda continuation. It accepts the already-constructed proof result directly
and returns it after validating the package's selected-whole equivalence and
active origin. The rejected-active construction site now builds that result
before entering the package boundary, so the branch remains proof-only while
the Cure compiler can elaborate it when the path is reachable (Cure does not
support the former lambda shape in this dependent callback context). The
complete `Std.Regex.Runtime` module compiles with zero warnings and the focused
dependent path-refutation regression passes 14/14. Recursive rejected-child
consumers, complete start-list correspondence, and the final all-kinds
selected-trace/refutation theorem remain open.

The indexed `AtomicPathDestinationRejected` branch now has a named
construction-site consumer, `atomic_path_active_child_rejection_excludes_destination_rejected`.
The aligned helper only performs the constructor match and forwards the
already-refined cursor witnesses to that consumer; the named boundary owns the
single call to `atomic_path_active_child_rejection_tail_fold`. This removes the
last duplicated alignment construction at that branch without introducing a
runtime callback, cast, or second failure-kind authority. The complete
`Std.Regex.Runtime` module compiles with zero warnings and the focused
dependent path-refutation regression passes 15/15. Recursive rejected-child
consumers, complete start-list correspondence, and the final all-kinds
selected-trace/refutation theorem remain open.

The singleton active-child head now has its own reducible construction-site
boundary, `atomic_path_active_child_rejection_head_excludes_trace`, and the
aligned dispatcher routes the head case through it. The boundary currently
delegates to the canonical destination-rejection consumer; this preserves the
erased proof shape while isolating the one-character induction leaf for the
next specialized theorem. `Std.Regex.Runtime` compiles with zero warnings and
the focused dependent path-refutation regression passes 16/16. The specialized
head contradiction, recursive rejected-child consumers, complete start-list
correspondence, and the final all-kinds selected-trace/refutation theorem
remain open.

The embedded `cure_regex` package now takes its identity and export surface
from `lib/std_deps/regex/Cure.toml` at the package construction site. The
stdlib bootstrap no longer duplicates `cure_regex`/`Std.Regex` in its stage and
merge options; it derives the package name and normalized export list from the
manifest, records that same map in the merged artifact, and compares it during
the up-to-date short circuit so an export edit cannot reuse a stale generation.
The source bundler preserves the package manifest beside the bundled `.cure`
files under `priv/std_deps/regex`. Manifest-authority and bundling regressions
pass, while the acyclic Core → Runtime → Proof/Language → façade graph and its
selected-trace proof obligations remain as previously recorded.

The active-child head consumer now receives the child's canonical
`AtomicPathOriginWitness` directly from the `AtomicPathDestinationRejected`
construction. Its witness indices carry the child thread state, pushed
history, and derived capture context without requiring a runtime inspection or
an untyped cast; the consumer keeps those values erased and delegates only the
existing cursor-alignment authority. This is typed origin transport, not yet
the final head contradiction. `Std.Regex.Runtime` compiles with zero warnings
and the focused dependent path-refutation regression passes 18/18. The
specialized head contradiction, arbitrary rejected-child recursion, complete
start-list correspondence, and final all-kinds selected-trace/refutation
theorem remain open.

The active-child head slice now includes explicit indexed terminal consumers for
`AtomicPathInputExhausted` and `AtomicPathExactAcceptedWithInput`. Each accepts
the terminal refutation and selected trace only at their constructor indices and
delegates to the existing input-exhaustion or exact-acceptance contradiction;
no erased failure tag or proof path is inspected in a runtime-relevant branch.
The generic `atomic_path_active_child_rejection_head_excludes_trace` bridge
remains the alignment fallback, while wiring these terminal consumers into the
recursive rejected-head dispatcher still requires a construction-site
refinement of the nested failure kind. `Std.Regex.Runtime` compiles with zero
warnings and the focused path-refutation regression passes 19/19. Arbitrary
rejected-child recursion, complete start-list correspondence, and the final
all-kinds selected-trace/refutation theorem remain open.

The terminal consumers now infer their erased machine, cursor, context, and
result indices directly from the supplied trace/refutation pair. This keeps
nested callers from having to re-pass proof-only lists or routines as explicit
arguments, while preserving the same indexed contradiction and relevance
boundary. The direct Runtime compile and the 20-test focused regression remain
green; recursive non-terminal child alignment is unchanged and remains open.

The first specialized active-head consumer is now present at the nested
construction site. For a one-character rejected active head, its indexed
`AtomicPathDestinationRejected` parent and `AtomicSelectedTransitionActive`
trace refine the child refutation to `AtomicPathInputExhausted`; the selected
child trace is then discharged by the erased terminal eliminator. This is a
real head contradiction rather than a runtime failure-tag branch. Runtime
compilation and a typed external construction-site probe pass; arbitrary
non-terminal child rejection, sibling-tail alignment, start-list
correspondence, and the all-kinds theorem remain open.

That specialized leaf is now wired into the existing one-character
`atomic_path_tail_active_child_exhaustion_excludes_selected_suffix`
construction site. After the parent destination rejection, active scope, and
both `Here` cursor refinements have been consumed, the site invokes
`atomic_path_active_child_rejection_head_active_excludes_trace` with the full
parent source/active-state indices and the original parent failure/path. The
consumer therefore derives the child `AtomicPathInputExhausted` index itself
and eliminates the selected child trace through the erased terminal theorem;
the older aligned-child handoff is no longer the authority for this leaf.
`Std.Regex.Runtime` compiles with zero warnings and the focused
path-refutation regression passes 23/23. This closes only the singleton
active-child exhaustion leaf: non-terminal rejected-child recursion, arbitrary
sibling-tail alignment, complete start-list correspondence, and the final
all-kinds selected-trace/refutation theorem remain open.

The corresponding singleton nested-child theorem is now explicit as
`atomic_path_active_child_rejection_singleton_active_excludes_trace`. It fixes
the child input to one character and the selected/refuted candidate to the same
active head, then delegates to the indexed active-head contradiction without
inspecting either erased certificate. Direct Runtime compilation and the
focused path-refutation regression pass 24/24. This theorem is proof groundwork,
not the general dispatcher: selecting the same head from independently
existential failure and trace cursors still requires a construction-site
alignment eliminator before recursive rejected-child and sibling-tail induction
can use it.

The singleton cursor-alignment consumer is now wired at the real rejected-tail
construction boundary. `AtomicPathCursorLocation` compares the relevant
failure and selected cursor spines from their common origin while keeping the
resulting equality erased. Candidate discrimination occurs before equality
transport, so proof evidence cannot choose runtime control. The nested selected
child trace is an explicit index of the base consumer and is threaded unchanged
through `atomic_path_rejected_tail_fold_to_active`; the fold no longer accepts
an unrelated parent trace as evidence for that child cursor. Equal active and
accepted heads are discharged by separate erased terminal eliminators, while
the two directional cursor cases remain the recursive sibling obligations.
Direct Runtime compilation is green. General non-singleton child recursion and
the complete start-list/all-kinds correspondence remain open.

The path failure tree now has a parallel proof-only classification family,
`AtomicPathNoEvidence`, matching the already established start-list evidence
discipline. Its recursive destination-rejection constructor retains both child
and sibling-tail evidence before their failure kinds are erased. Child capture
context is tied to the admitted candidate by the indexed
`LookaroundAdmittedStateCaptureContext` relation rather than forcing the
candidate-context reducer inside a recursive constructor signature. Root,
suffix-search, ordinary-member, and escaped-member negative results now publish
that evidence, and the recursive destination traversal constructs
`AtomicPathNoDestinationRejected` from the exact child and sibling-tail values
at their common construction site. Direct Runtime compilation and the focused
27-test path-refutation gate are green. The general theorem consumer and its
start-list lift remain open.

The recursive proof-only rejection constructor now also retains the failed
child's origin equivalence, canonical origin witness, and exact cursor suffix,
plus the sibling tail's cursor suffix and origin equivalence. These are the
same witnesses already available where the evaluator combines the child and
tail failures; publishing them there means the general correspondence theorem
can recurse over `AtomicPathNoEvidence` without reopening and correlating the
larger runtime `AtomicPathRefutation` GADT. The emitted representation remains
unchanged because every added field is erased. The complete Runtime module and
the focused 27-test path-refutation gate pass. Packaged recursive consumption,
the complete start-list lift, and the final all-kinds theorem remain open.

Escaped child-search failures now preserve their canonical origin witness all
the way from `AtomicPathMembersEscapedNo` through `AtomicPathSearchNo` and
commit-scope unwinding. Previously the member result retained this witness but
the public search projection discarded it and later branches substituted
`AtomicPathOriginWitnessNone`; that made the failed and selected child origins
impossible to align without reopening evaluator internals. The witness is
proof-only and erased, so this strengthens correspondence without changing the
runtime result. Runtime elaboration and the focused construction-site
regressions pass. The next proof slice can now package child-origin equality
directly before recursive rejection consumption.

The canonical origin comparison itself is now discharged independently.
`AtomicPathSearchOriginAlignment` has one proof-only constructor carrying the
equality between two origin lists for the same indexed search, and
`atomic_path_search_origin_alignment` derives it by reducing accepted origins
to the canonical empty list or composing both active-origin equations through
the exact `lookaround_machine_admitted_destinations` computation. This avoids
the rejected alternative of converting erased origin evidence into a present
sum tag. Runtime elaboration and the focused 27-test path-refutation gate pass;
publishing both canonical origin certificates in the recursive failure package
and consuming this alignment remain the next construction-site steps.

Origin publication is now total and indexed rather than optional. Active
searches on empty input publish `AtomicPathSearchOriginActiveEmpty` at the
canonical empty list; accepted searches already publish the same empty origin,
and consuming active searches retain their exact admitted-destination
equation. `AtomicPathRootRefutation`, `AtomicPathSearchNo`, both member-failure
results, `AtomicPathRefutation`, and `AtomicPathNoEvidence` now carry
`AtomicPathSearchOrigin` tied to the explicit origin list. The former
`AtomicPathOriginWitness` family and its unconstrained `None` constructor are
removed. Root origin equality is eliminated before a child failure is handed
to the recursive traversal, so independent existential binders cannot leak
past the construction boundary. All fields remain erased; Runtime elaboration
and the focused 27-test path-refutation gate pass. The remaining task is now a
consumer problem: apply `AtomicPathSearchOriginAlignment` to the failed and
selected child certificates and recurse over the aligned cursors.

That consumer boundary is now implemented as
`atomic_path_failed_selected_child_cursor_alignment`. It accepts the failed
whole-to-origin equation, both canonical origin certificates, and the failed
and selected cursor suffixes. The helper first aligns the two origins, then
eliminates both erased equalities to rewrite the list indices before invoking
the cursor-alignment relation; it does not pass erased equality values through
relevant function arguments. Runtime elaboration is green. The remaining
integration work is to replace the older caller-supplied
`selected_whole_equivalence` assumptions in the recursive active-child fold
with this construction-site bridge, then discharge its directional cases.

The canonical active-child dispatcher is now present as
`atomic_path_active_child_rejection_canonical_dispatch`. It keeps the failed
and selected origins as distinct binders, derives their cursor alignment only
through `atomic_path_failed_selected_child_cursor_alignment`, and separately
transports the selected suffix to the failed whole-list index by eliminating
the same canonical origin equalities locally. This separation is required by
Cure's relevance discipline: an erased alignment payload cannot be projected
into a relevant cursor operation, while the construction-site selected suffix
is still relevant and may safely drive the `Here`/`There`/`Reverse` dispatcher.
The focused 27-test path-refutation gate and the complete Regex module chain
elaborate successfully. The next integration slice is to thread the two origin
certificates through `atomic_path_rejected_tail_fold_to_active`, replace its
older caller-supplied whole-list equality, and discharge the three recursive
branches.

That origin migration is now complete across
`atomic_path_tail_active_child_rejection_excludes_selected_suffix_base`, its
public wrapper, and `atomic_path_rejected_tail_fold_to_active`. The fold carries
the failed whole-to-origin equation and both canonical origin certificates as
separate parameters; the former `child_selected_whole_equivalence` premise is
absent from all three signatures. The singleton branch obtains its common
outer suffix only through `atomic_path_failed_selected_child_suffix`, while
the non-terminal branch invokes
`atomic_path_active_child_rejection_canonical_dispatch` directly. Recursive
sibling peels preserve the same origin and cursor witnesses unchanged. The
complete Regex module chain elaborates, and the focused 27-test path-refutation
gate passes. The remaining proof obligation is no longer origin identity: it
is to replace the fold's externally supplied `Here`/`There`/`Reverse`
contradictions with recursive consumers of the child and sibling failure
evidence, then lift that result through the start list.

The all-child-kind construction boundary now uses the same canonical-origin
discipline. `atomic_path_tail_active_child_failure_dispatch` carries a relevant
proof-only failure kind until its indexed branch has been selected; the child
refutation, selected child trace, and parent trace likewise remain relevant
only inside this theorem boundary and are still erased by the matcher result
constructors. Destination exhaustion transports the selected suffix through
`atomic_path_failed_selected_child_suffix` and reuses the existing exhausted
leaf. Recursive destination rejection uses the new current-relative
`atomic_path_active_child_rejection_canonical_current_dispatch`, which compares
the failed and selected cursors after canonical transport and distinguishes
same child, later sibling, and reverse ordering without projecting an erased
non-empty existential. The old failed-whole/selected-whole equality is removed
from both this dispatcher and its exhausted-child wrapper. The full Regex
module chain elaborates and the focused 27-test gate passes. The remaining
directional callbacks must now be replaced by the recursive child/tail
contradictions themselves before the start-list lift can close Phase 2.

The one-character same-head active-child case is now discharged at that
construction boundary. The dispatcher refines the relevant selected trace
before classifying its canonically transported cursor; this exposes whether
the selected head is active or accepted without inspecting erased candidate
data. The equal-cursor branch invokes the corresponding proof-erased singleton
contradiction, while only the genuinely directional sibling cases retain
callbacks. This ordering is required by relevance: attempting cursor
classification first loses the constructor refinement needed to consume the
erased selected trace. Arbitrary non-empty child recursion, sibling-tail
recursion, and the complete start-list lift remain open.

The remaining reverse-cursor branch has now been traced to its sole legitimate
construction source: `AtomicPathMembersEscapedNo`. When a child commitment
escapes the current atomic scope, `atomic_lookaround_routine_add_skipped_candidate`
prepends the committed candidate while retaining the later tail result. If an
ordinary rejected candidate precedes that escaped result, the tail-after-failure
fold prepends that rejection too. The prefix is therefore a mixed ordered spine,
not merely a list of escaped commits. Cursor ordering alone cannot soundly
declare a selected trace in that prefix impossible.

The required construction-site strengthening is now implemented.
`AtomicPathCommitCause` records local failure-after-close, propagated
active-child commits, and commits preceded by either rejected or escaped
candidates. `AtomicPathSkippedPrefixEvidence` records the corresponding mixed
prefix in exact order. `AtomicPathMembersCommit`, `AtomicPathSearchCommit`,
`AtomicPathMembersEscapedNo`, and `AtomicPathSearchNo` retain those erased
certificates, and every constructor is built from the same
`AtomicCommitBlocks`/`AtomicCommitEscapes` proof used by the runtime branch. The
indices also eliminate the former accepted-child commit branch:
`ThreadAccepted` has no `AtomicPathCommitCause` constructor. The reverse branch
must next consume the mixed prefix against the selected trace; it must not infer
rejection from a suffix relation or add a runtime Boolean/tag.

The cursor side of that obligation is now explicit and checked. Reverse
alignment retains `AtomicPathStrictCursorSuffix`, whose proper-suffix
asymmetry is proved structurally for finite admitted-state lists. A root failure
cannot have a strictly earlier selected cursor, and the canonical current
dispatcher now passes the strict witness to its caller instead of discarding it
behind a zero-argument callback. Every rejected element of the mixed skipped
prefix also retains its own `AtomicPathFailurePrefixEvidence`, so recursive
candidate exclusion no longer loses a nested child cursor. The remaining work
is to consume the rejected and escaped-commit prefix constructors directly
against the selected trace, then delete the final reverse continuation rather
than wrapping it again.

The one-element skipped-prefix tail case is now discharged explicitly:
`atomic_path_skipped_one_tail_excludes_strict_selection` composes the selected
tail suffix with the strict reverse witness and eliminates it through finite
suffix asymmetry. Commit causes created after a failed child, or after an
earlier rejected child, now retain that child's
`AtomicPathFailurePrefixEvidence`, canonical search origin/equality, and exact
cursor suffix alongside the existing refutation and no-evidence tree. The
escaped-commit consumer therefore no longer needs to reconstruct any child
root/suffix fact from evaluator internals. The next slice must match the
relevant skipped-prefix constructor at its proof construction boundary, use
these retained fields to consume an at-head selected child, recurse through the
tail constructor otherwise, and remove the final reverse callback. The focused
27-test refutation gate and the 52-check canonical pipeline are green. The
embedded Regex package itself is already acyclic (all eleven package modules
are singleton dependency components); the canonical stabilization gate now
checks `lib/std_deps/regex` separately so package cycles cannot escape the
ordinary `lib/std` scan.

Commit-result transport is now complete at the same proof boundary.
`AtomicPathMembersCommit` and `AtomicPathSearchCommit` retain the canonical
origin equation/certificate plus the exact whole-to-current cursor witness and
suffix. Rejected-tail and escaped-tail reconstruction preserve those fields at
the parent cursor, while `AtomicPathCommitFromChild` and
`AtomicPathCommitPastEscaped` retain the corresponding child origin and suffix
beside the recursive cause. Consequently all four commit-cause constructors
now expose the child alignment data required by direct selected-trace
consumption; no commit branch needs to reopen the evaluator. The indexed
terminal eliminators also establish that a commit cause cannot exist at empty
input or under `ThreadAccepted`. The remaining implementation is the recursive
non-empty active-thread cause fold, its integration into the mixed skipped-
prefix consumer, and deletion of the reverse continuation.

Escaped-prefix evidence now retains the skipped candidate's capture-context
and scope-alignment proofs together with the committed child origin and cursor
suffix. Both `AtomicPathCommitPastEscaped` and
`AtomicPathCommitPastRejected` also retain the later sibling cause's canonical
origin and tail suffix. Thus the recursive fold has explicit evidence for both
choices at every constructor: consume the selected head through its aligned
child, or recurse into the canonically indexed sibling tail. A standalone
projection from an erased cause to a non-empty witness was deliberately
rejected by E104 and removed; the implementation must match each cause directly
into `Empty` rather than materializing an intermediate proof package. The
focused 27-test refutation gate remains green.

Commit causes are now indexed by the proof-erased
`AtomicPathCommitCauseKind`, with one index for each of the four construction
forms. The result boundaries carry that erased index explicitly so Cure gives
nested causes a fully determined expected type; recursive causes retain their
own erased kind. This does not add runtime control state, but it permits each
next eliminator to select exactly one cause constructor without reopening a
generic erased sum, which is the E104-safe shape required by the recursive
non-empty active-thread fold. The complete Regex module chain and focused
27-test refutation gate pass after the migration.

Each commit-cause kind now has a constructor-specific non-empty projection.
All four projections compile while their cause argument remains erased,
confirming that the new index selects one constructor and avoids the generic
erased-sum inspection rejected by E104. These projections provide the
non-empty cursor premise needed by the per-constructor contradiction folds;
they do not themselves discharge the mixed skipped-prefix correspondence.

Successful atomic destination searches now retain the same indexed skipped-
prefix history as failures. `AtomicPathSkippedPrefixEmpty` marks a selected
head; rejected-child and escaped-commit constructors are prepended whenever
the evaluator continues to a sibling. `AtomicPathSearchYes`, internal member
successes, recursive selected transitions, and the active-child selection
package all preserve that erased certificate. A selected suffix therefore no
longer loses why its preceding candidates were legally skipped. The next
construction-site invariant is the indexed reason a rejected child was
allowed to continue—no local close or an escaping close—so it can be compared
directly with a blocking commit cause.

That continuation invariant is now explicit. `AtomicPathFailureContinuation`
is indexed by the exact close depth computed from the rejected candidate's
routine: it records either canonical `None`, or canonical `Some(depth)` plus
the proof that the close escapes the current scope. Rejected-prefix evidence
and commit causes propagated past a rejected candidate retain the witness;
locally blocking commit causes retain the canonical `Some(depth)` equation.
`atomic_path_failure_continuation_excludes_blocked` eliminates both conflicts:
`None = Some` is impossible, while equal `Some` indices reduce to the existing
finite-order contradiction between `AtomicDepthBelow` and
`AtomicDepthAtLeast`. The complete module chain and focused 27-test gate pass.

The first constructor-specific consumer now uses that invariant directly:
`atomic_path_commit_after_failure_excludes_continuation` proves that a locally
blocking `AfterFailure` cause excludes sibling continuation for the same
candidate. The two propagated cause forms also project an erased
`AtomicPathCommitTailPackage` containing the exact later-sibling cause,
canonical origin, and whole-to-tail suffix. These projections are kind-refined
and compile without reopening the generic cause sum, providing the recursive
step needed by the mixed-prefix fold. The focused 27-test gate remains green.

Skipped-prefix evidence is now indexed by the proof-erased recursive
`AtomicPathSkippedPrefixKind`. Empty, singleton escaped-commit, recursive
escaped-commit, and recursive rejected-child prefixes have distinct indices;
the recursive constructors retain the tail kind explicitly. Search/member
successes and failures, selected child transitions, and the active-child
selection package carry the kind beside the erased evidence. This gives the
mixed-prefix fold a constructor selector at every recursive step without
making proof evidence runtime-relevant or reopening an arbitrary erased sum.
The complete Regex module chain elaborates and the focused 27-test
path-refutation gate passes. Constructor-specific skipped-prefix consumers,
their recursive cause/trace contradiction, and the complete start-list lift
remain open.

The kind-indexed skipped-prefix interface now has constructor-specific erased
eliminators. The empty kind publishes its exact front/current equality; the
singleton escaped kind publishes non-emptiness; and both recursive escaped and
rejected kinds publish their exact tail through a zero-runtime
`AtomicPathSkippedPrefixTailPackage`. Returning the erased tail directly was
correctly rejected by E104, so the package mirrors the established commit-tail
projection and keeps proof evidence out of runtime expressions. The complete
module chain and focused 27-test gate pass. The next slice must combine these
tail projections with the matching commit-cause projections and continuation
contradiction in the recursive mixed-prefix fold.

The first mixed constructor pair is now discharged directly.
`atomic_path_commit_after_failure_excludes_rejected_prefix` consumes an
`AfterFailure` commit at the current candidate together with the
`RejectedCons` evidence that allowed success to continue past that same
candidate. It extracts the retained continuation witness at the construction
site and invokes the finite depth contradiction, with both proof sums fixed by
their erased kinds. This closes the locally blocking rejected-head case; the
propagated escaped/rejected tail recursion and selected-child cause case remain.

Both propagated sibling forms now expose one correlated recursive package.
`AtomicPathCommitSkippedTailPackage` retains the later commit's canonical
origin, whole-to-tail cursor, kind, and cause together with the skipped-prefix
tail kind and evidence at that exact same list suffix. The escaped/escaped and
rejected/rejected constructor pairs each build this package directly from
their kind-refined erased inputs. Recursive consumers therefore cannot combine
a commit cause and success prefix produced at unrelated cursors. The remaining
step is to recurse over this package for every tail-kind/commit-kind pairing,
then connect the resulting fold to selected-child and start-list alignment.

Failure-prefix evidence is now indexed by the proof-erased
`AtomicPathFailurePrefixKind`. Root failures and failures reached after a
mixed skipped prefix have distinct indices, and the latter retains the exact
`AtomicPathSkippedPrefixKind` that produced its current cursor. Every
destination rejection, no-evidence mirror, commit cause, skipped-prefix node,
and evaluator helper threads that index beside the erased evidence from its
single construction site. This removes the last need to inspect the former
unindexed erased `AtRoot`/`AfterSkipped` sum, which Cure correctly rejected
under E104, without adding a runtime tag. The complete Regex module chain
elaborates and the focused 27-test path-refutation gate passes. The next fold
can therefore dispatch root failures to the strict-root contradiction and
after-skipped failures to the recursively correlated skipped-prefix/commit
consumer.

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
Finite PCRE start controls `(*UTF)`, `(*UTF8)`, and `(*NO_JIT)` now normalize
away at the syntax boundary: Cure's subjects are already Unicode-scalar lists,
and the matcher has no host JIT mode whose selection could affect semantics.
The optimizer-only controls `(*NO_START_OPT)` and `(*NO_AUTO_POSSESS)` now
normalize away for the same reason: the Cure lowering has no observable host
start optimizer or automatic-possessification pass. They are accepted only as
leading controls, just like the other start controls, and do not add runtime
control state.
`(*UCP)` normalizes to the existing scoped Unicode modifier, so generic
word/digit/space predicates use the same typed and erased implementation as
the `u` option. `(*UTF16)` and `(*UTF32)` are rejected with the structured
`:UnsupportedRegexEncodingControl` diagnostic because Cure does not model
UTF code-unit subjects. These controls have focused runtime and exact-span
diagnostic regressions.
The finite `(*F)` spelling is now accepted as PCRE's short alias for
`(*FAIL)` and lowers through the same negative-empty assertion, so it adds no
separate runtime or proof state. The label-bearing `(*FAIL:NAME)` and
`(*ACCEPT:NAME)` forms are likewise consumed at the syntax boundary and lower
through the existing finite controls; empty labels retain PCRE's no-label
meaning, and an unclosed label receives the structured `:UnclosedRegexControl`
diagnostic with its exact source span. The finite `(*MARK:NAME)` control is now
accepted anywhere an atom is allowed:
its label is consumed by a fuel-bounded parser, must be non-empty, and the
control normalizes to `LiteralEmpty`. Cure's public match values expose no
MARK channel, so this preserves the observable acceptance and capture result
without introducing runtime state. Missing, empty, and colon-less MARK forms
produce dedicated structured diagnostics with exact source spans.
The search-stack controls `(*THEN)`, `(*PRUNE)`, `(*SKIP)`, and `(*COMMIT)` are
recognized before ordinary group parsing, including their label-bearing forms,
and rejected with the dedicated structured `:UnsupportedRegexBacktrackingControl`
diagnostic. Their PCRE semantics mutate alternative backtracking or the search
cursor; until Cure has an explicit finite control algebra and preservation
proof, treating them as empty atoms would be unsound. Missing closing
parentheses use the structured `:UnclosedRegexControl` diagnostic with the
whole control span. This makes the compatibility divergence explicit rather
than allowing these verbs to fall through to a misleading quantifier error.
The parser also rejects the currently deferred `\G` search anchor and `\K`
match-span reset with dedicated structured diagnostics rather than treating
them as escaped literal letters. `\G` requires an explicit caller-provided
search cursor and `\K` requires additive reported-span semantics; both are
reserved for the runtime search-context work in Phase 4. Raw-byte `\C` is
rejected as `:UnsupportedRegexByteEscape` because the Cure subject model is a
Unicode-scalar sequence, not a byte string. PCRE octal `\o{...}` and control
character `\cX` escapes are likewise rejected as
`:UnsupportedRegexNumericEscape` and `:UnsupportedRegexControlEscape`; their
byte-oriented encodings must not fall through to literal `o` or `c` atoms.
The class parser applies the same boundary: anchor, line-break, numeric, and
other special escapes that have no character-class meaning are rejected with
structured `:UnsupportedRegexClassEscape` or numeric diagnostics instead of
becoming literal class members.
PCRE resource-limit controls (`(*LIMIT_MATCH=...)`, `(*LIMIT_DEPTH=...)`, and
`(*LIMIT_HEAP=...)`) now receive the dedicated structured
`:UnsupportedRegexResourceControl` diagnostic, and the caller-level empty-match
controls `(*NOTEMPTY)`, `(*NOTEMPTY_ATSTART)`, and `(*NOTEMPTY_ATEND)` receive
`:UnsupportedRegexEmptyMatchControl`. Neither family is silently treated as an
empty atom: Cure's resource policy and empty-match policy are explicit in the
typed APIs and cannot be replaced by mutable host controls.
Remaining Phase 3 work is grapheme clusters,
duplicate-name and capture-layout policy, other finite control normalizations,
and the remaining control families below. `(*FAIL)`/`(*F)` and terminal `(*ACCEPT)`
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

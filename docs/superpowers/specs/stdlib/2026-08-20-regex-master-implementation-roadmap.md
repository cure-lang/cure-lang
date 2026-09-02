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

Both failure-prefix constructors now have kind-refined consumer boundaries.
`atomic_path_failure_at_root_excludes_strict_selection` immediately combines
the stored root equality, the selected whole-to-cursor suffix, and the strict
reverse witness through finite suffix asymmetry. The after-skipped constructor
projects its exact skipped-prefix certificate through the zero-runtime
`AtomicPathFailureSkippedPackage`, avoiding the E104-invalid operation of
returning an erased proof as relevant data. These are the two branches needed
by the final reverse-cursor dispatcher; the after-skipped package must next be
fed into the recursive commit/skipped-kind matrix.

The nominally suffix-local branch also closes its empty-prefix base explicitly.
Although `AtomicPathFailureAfterSkippedKind` is structurally closed over every
skipped-prefix kind, `AtomicPathSkippedPrefixEmpty` identifies the failure
cursor with the whole list. The new
`atomic_path_failure_after_empty_skipped_excludes_strict_selection` consumes
that equality and reduces the alleged reverse selection to finite strict-suffix
asymmetry. The proof therefore does not rely on an informal claim that this
publicly constructible index is unreachable. Non-empty escaped and rejected
heads remain the recursive cases.

Both recursive non-empty prefix constructors now publish kind-refined
non-emptiness projections. The escaped-cons and rejected-cons consumers expose
their exact `candidate :: tail` spine only after matching the corresponding
erased evidence constructor; no caller reconstructs that decomposition from an
unindexed list. Together with the existing escaped-one projection and both tail
packages, the recursive cursor fold now has canonical head and tail structure
for every non-empty skipped-prefix kind. Candidate-level commit/refutation
contradictions still have to consume those heads against the selected trace.

Rejected skipped-prefix kinds now retain the rejected child's failure-prefix
kind and path-failure kind in addition to the recursive tail kind. These were
already present as erased constructor fields, but omitting them from
`AtomicPathSkippedPrefixRejectedConsKind` prevented a recursive consumer from
selecting either child proof constructor without an E104-invalid inspection of
an erased sum. Evaluator success/failure construction, nonempty and tail
projections, the blocking-continuation contradiction, and correlated
commit/skipped-tail transport all thread the three-part index. The rejected
head theorem can now dispatch the exact child refutation and its own prefix
recursion entirely from erased indices.

The rejected head now has its own constructor-refined erased package.
`AtomicPathRejectedSkippedHeadPackage` deliberately carries the already
canonical `AtomicPathSkippedPrefixEvidence` family rather than restating the
child prefix/refutation indices in a second constructor: the latter produced
an E093 index drift at interface registration, while the established
single-evidence package shape preserves every existential at its construction
site. `atomic_path_skipped_prefix_rejected_cons_head` fixes the package kind to
`AtomicPathSkippedPrefixRejectedConsKind`, so the contradiction consumer can
open the rejected constructor in an erased match without returning proof data
through a relevant expression. The next slice consumes that package against
the selected child trace and then recurses through its tail package.

The first rejected-head contradiction is now direct rather than callback
driven. `atomic_path_rejected_skipped_head_input_exhausted_excludes_selected_trace`
opens the constructor-refined package for an active skipped candidate whose
child failure is indexed by `AtomicPathFailureInputExhausted`. Selecting that
same candidate necessarily exposes its active child trace, and the existing
input-exhaustion eliminator closes the contradiction after the stored scope
refinement is matched. This establishes the terminal leaf of the rejected
head recursion without a runtime failure tag or a caller-supplied directional
case. Recursive destination rejection and selected-in-tail transport remain.

The accepted terminal dual is closed as well.
`atomic_path_rejected_skipped_head_exact_accepted_excludes_selected_trace`
specializes the same package to an accepted skipped candidate and
`AtomicPathFailureExactAccepted`. Matching its stored accepted-scope
refinement makes the selected parent transition expose the exact child trace;
the accepted-thread/non-empty-input eliminator then discharges it. Rejected
heads therefore have direct consumers for both terminal child-failure kinds,
leaving only destination exhaustion/rejection and tail recursion.

Root-relative destination exhaustion is direct too. The new erased exhaustion
leaf consumes a selected child trace without making its existential routine or
cursor relevant. The rejected-head consumer matches the stored root-prefix
equality, failed-origin equality, and canonical-origin alignment in sequence;
these refine the selected child origin and cursor to `Nil`, after which the
erased destinations-exhausted eliminator closes the contradiction. No reverse
continuation is supplied. Destination exhaustion after a non-empty skipped
child prefix, recursive destination rejection, and outer tail recursion remain.

The recursive active-child dispatcher now retains the failure-prefix kind and
evidence instead of discarding them before cursor classification. Its reverse
branch calls `atomic_path_failure_prefix_reverse_dispatch`: the relevant
proof-only kind selects the construction case, after which the fixed erased
root constructor is safe to consume and finite suffix asymmetry closes that
branch directly. An attempted generic erased-prefix match was rejected by E104
because it would make runtime control depend on erased evidence; the indexed
dispatcher deliberately avoids that shape. Only `AfterSkipped` delegates to
the remaining mixed-prefix recursion, narrowing the final reverse continuation
to its genuine semantic source.

The nominal `AfterSkipped` base is no longer delegated either. The dispatcher
opens the relevant skipped-prefix kind first; when it is `Empty`, the erased
prefix constructor is fixed and
`atomic_path_failure_after_empty_skipped_excludes_strict_selection` closes the
same finite suffix contradiction. The remaining continuation is now reachable
only for `EscapedOne`, `EscapedCons`, or `RejectedCons`, exactly the three
non-empty mixed-prefix constructors that require candidate-level consumption.

Escaped skipped-prefix kinds now retain the head commit-cause kind.
`EscapedOne` is indexed by its `AtomicPathCommitCauseKind`, and `EscapedCons`
retains both that head kind and its recursive tail kind. The evaluator,
successful-prefix reconstruction, non-empty projections, tail projection, and
correlated commit/skipped transport all thread the new index. Without this,
an `EscapedOne` consumer would have to inspect the erased four-constructor
commit cause generically and trigger E104. Candidate-level commit dispatch can
now select the fixed cause constructor from the proof-only kind first.

`EscapedOne` now has a constructor-refined erased head package as well.
`AtomicPathEscapedSkippedHeadPackage` carries the original canonical skipped
evidence rather than duplicating its dependent child/cause indices, and
`atomic_path_skipped_prefix_escaped_one_head` fixes the package kind to the
new cause-indexed `EscapedOne`. The next consumer can therefore match one fixed
escaped constructor and then dispatch its fixed commit-cause kind without
returning any erased payload through a relevant expression.

The commit-cause kind itself is now recursively indexed rather than merely
naming its outer constructor. `AfterFailure` retains the child failure-prefix
and failure kinds, `FromChild` retains the child commit kind, and the two
propagating constructors retain their child and tail kinds. Constructors,
non-empty projections, contradiction projections, correlated skipped-tail
packages, and evaluator result construction all preserve these indices. This
is required for the `EscapedOne` consumer: an outer kind that discarded its
nested proof shape would still force generic inspection of an erased child
cause and reproduce E104 one level lower. The focused 27-test refutation gate
and the complete `Std.Regex.Runtime` → `Std.Regex.Proof` → `Std.Regex` →
`Std.Regex.Language` elaboration chain pass with the recursive algebra.

The first `EscapedOne` terminal eliminators are now explicit. A locally
committing child whose rejected descendant is indexed by input exhaustion
cannot coexist with selection of the same active outer head: the selected
transition exposes an impossible active trace at empty input. The accepted
dual similarly exposes a selected trace at an accepted thread with input still
remaining. The root destinations-exhausted leaf is separated at the exact
same-candidate boundary; its root equality and canonical-origin alignment
transport the nested selected suffix to the empty child cursor before applying
the existing erased exhaustion eliminator. An earlier attempted wrapper
compared the nested commit origin with the selected origin one transition too
early, producing pathological normalization rather than a useful diagnostic;
the corrected theorem makes the required candidate alignment explicit. The
outer `EscapedOne` dispatcher must next derive that alignment (or recurse over
the ordered child cursor) before selecting these leaves.

Commit/search cursor alignment now has a canonical construction authority.
`atomic_path_commit_cause_nonempty` dispatches on the relevant recursive cause
kind and selects exactly one erased constructor projection; the commit suffix
then lifts that non-empty decomposition back to the canonical whole list.
Canonical commit and selected origins feed the existing ordered child-cursor
classifier through `atomic_path_commit_selected_alignment_fold`. Where a leaf
needs the exact equality rather than only the three-way branch,
`atomic_path_commit_selected_cursor_location` preserves `Same`, strictly
later, and strictly earlier witnesses. The canonical whole list is deliberately
relevant at that boundary because `atomic_path_cursor_location` traverses it;
all other origin and cause witnesses remain proof-only. This supplies the
missing alignment layer needed to compose the terminal leaves into
`EscapedOne` without assuming that the commit and selected cursors coincide.

The exhausted-input and exact-accepted terminal contradictions now also exist
at the aligned commit cursor itself, alongside the root destinations-exhausted
leaf. These are the reusable leaves required after a `Same` cursor equality is
consumed. A proposed generic `AfterFailure` dispatcher was deliberately
rejected: matching only its failure-kind parameter attempted to refine generic
erased input/current indices across incompatible `Nil` and `Cons` branches,
which E093 rejects. Dispatch must remain at the full construction site where
the recursive cause kind, candidate shape, input shape, and cursor equality are
simultaneously fixed; this is a stronger and more precise boundary than a
failure-kind-only helper.

The recursive commit tree now has a constructor-directed CPS boundary as
`atomic_path_commit_cause_dispatch`.  It branches only on the relevant
`AtomicPathCommitCauseKind` and hands the corresponding cause to each
continuation inside a one-constructor `AtomicPathCommitCausePackage`; the
cause payload remains erased and can therefore be opened collapsibly once an
outer `EscapedOne` construction has fixed the kind.  This records the sound
alternative to inspecting erased cursor lists: Cure has no separate
proof-function annotation, and allowing arbitrary `Empty`-returning functions
to inspect erased data would be unsound because `Empty` can eliminate into a
runtime result.  The remaining composition must invoke this dispatcher where
the evaluator still has the relevant child `whole`/`current` spines, use the
canonical cursor-location fold there, and then recurse through `FromChild`,
`PastEscaped`, and `PastRejected`.  The full four-module Regex elaboration
chain and the focused 27-test refutation gate pass with this boundary.

Canonical cursor classification and recursive cause dispatch are now composed
by `atomic_path_commit_selected_location_dispatch`.  The combinator receives
the canonical child `whole` spine as relevant data, computes the exact
`Same`/left-after/right-after location once, and threads that location as an
ordinary context through the proof-only cause dispatcher.  Extending the
dispatcher with a generic context also avoids anonymous dependent lambdas:
the first attempted composition reached the full module chain but E093
rejected those lambdas in body checking.  Passing the context explicitly is
both simpler and accepted.  This is the construction-site API the
`EscapedOne` proof can now call before the child lists disappear into erased
evidence; the per-constructor/per-location continuations and recursive cause
consumers remain to be supplied.

The first full construction-site terminal fold is now present for
`AfterFailure(InputExhausted)`. It compares the committing and selected
cursors from their canonical origins while the shared `whole` spine remains
relevant. `Same` transports the selected trace to the exact commit cursor and
immediately invokes the existing exhausted-input contradiction; strictly
later and strictly earlier locations are retained as typed continuations for
sibling recursion. This crosses the former erased-cursor boundary without
recovering a list from proof evidence or adding a runtime witness. The
accepted and root-destination terminal folds remain, followed by the recursive
cause constructors.

The exact-accepted dual is now folded at the same construction boundary.
Canonical cursor equality transports an accepted selected trace to the
committing accepted candidate and closes it with the existing non-empty-input
contradiction; both strict cursor directions remain typed recursion cases.
Together these two folds cover the active empty-input and accepted non-empty
terminal shapes without a generic failure-kind match. Root destination
exhaustion is the remaining `AfterFailure` terminal fold.

Root-relative destination exhaustion now has the same canonical-location
fold. In the `Same` case it reuses the aligned leaf, including the child's
root-prefix equality and canonical-origin transport; both strict locations
are preserved for recursive sibling handling. All three terminal
`AfterFailure` shapes are therefore composed with independently existential
selected cursors. Remaining `AfterFailure` work is recursive destination
rejection rather than another terminal alignment case.

Recursive destination rejection exposed a deeper erased-cursor boundary. An
attempt to derive child-whole non-emptiness by feeding the erased multi-clause
suffix to the ordinary suffix traversal correctly failed with E104: that
traversal chooses control flow, and an `Empty` result is not intrinsically
proof-only because it can eliminate into runtime data. The invalid projection
was removed. The replacement begins with
`LookaroundAdmittedStateCursorSuffixKind` and its constructor-correlated erased
`LookaroundAdmittedStateCursorSuffixEvidence`. `Here` and `Drop` construction
authorities are green. This structural index must now be published with child
failure cursors and consumed kind-first, mirroring the sound recursive
commit-cause design rather than weakening relevance checking.

The suffix evidence now has its first kind-directed consumer:
`lookaround_admitted_cursor_suffix_evidence_nonempty`. `Here` consumes its
fixed erased equality; `Drop` uses the explicitly retained erased prior-outer
spine to construct the non-empty decomposition without traversing erased
evidence. This is the exact invariant the recursive destination-rejection
theorem needs. The remaining plumbing task is to construct and publish the
suffix kind/evidence alongside evaluator cursors, then retain it in commit and
negative-result witnesses.

The publication boundary is now represented explicitly by
`LookaroundAdmittedStateCursorSuffixPackage`. Its `kind` is the only relevant
payload; the constructor-correlated suffix evidence remains erased. Canonical
`Here` construction and recursive `Drop` extension elaborate through the full
Regex module chain, and the focused 27-test refutation gate is green. The next
slice must thread this package through `AtomicPathMembersResult` and
`AtomicPathSearchResult`, starting with a root `Here` package and extending it
exactly once whenever destination traversal drops a head. Recursive commit and
negative witnesses can then retain the published package instead of attempting
to recover a relevant branch from an erased suffix.

`lookaround_admitted_cursor_suffix_package_advance` now supplies that exact
one-head traversal operation. Its worker recurses on the relevant suffix kind
and accepts the correlated evidence through an erased parameter; an earlier
form that repackaged the evidence as a relevant recursive argument was rejected
by E104 and removed. The accepted worker creates the first `Drop` from `Here`
or advances the nested prior suffix under an existing `Drop`, preserving the
original outer spine. The full Regex chain and focused refutation gate remain
green.

Negative destination traversal now publishes the package through both
`AtomicPathMembersNo`/`AtomicPathMembersEscapedNo` and the public
`AtomicPathSearchNo` result. `atomic_lookaround_routine_members_from` starts
with the canonical `Here` package and advances it once with every sibling
drop; ordinary and escaped negative projections preserve the same indexed
package. Root failures construct `Here` directly, while suffix-local child
failures hand their published package to the failure construction boundary.
This is runtime metadata only at the already-tagged negative search boundary,
and its evidence remains erased. The full four-module Regex chain and focused
27-test gate are green. The next slice is to index recursive commit/failure
witnesses by the published suffix kind so the destination-rejection consumer
can dispatch kind-first after those runtime results are erased.

Successful destination selection now publishes the dual cursor packages too.
`AtomicPathMembersYes` retains packages for both its selected-whole suffix and
its current-to-selection suffix; `AtomicPathSearchYes` retains the selected
suffix and canonical-origin suffix packages. Terminal selections construct
`Here`, and escaped/rejected sibling traversal prepends exactly one `Drop` to
both relevant origins. Parent transitions deliberately construct a fresh
`Here` package for their own selected candidate while preserving the child's
packages at the runtime result boundary. The full Regex chain and focused
27-test gate pass. The remaining trace migration must add these package kinds
to `AtomicSelectedPathTrace` indices, allowing recursive commit alignment to
consume both failure and selected suffix evidence without reopening an erased
trace.

The recursive structural index is now declared as
`AtomicSelectedPathTraceKind`. It distinguishes prefix completion, exact
completion, active transition, and accepted transition; each transition node
retains both its canonical child-cursor suffix kind and the suffix trace kind.
This deliberately records the whole recursive trace shape rather than only
the outer cursor: otherwise the next induction step would again hide its
cursor kind behind an erased existential. The declaration compiles through the
full Regex chain and the focused 27-test gate remains green. The next slice is
the constructor-correlated erased evidence relation and its construction in
`AtomicPathSearchYes`.

`AtomicSelectedPathTraceEvidence` now indexes the exact erased trace value as
well as its semantic inputs and structural kind. Prefix and exact completion
are the first correlated base constructors; they cannot be paired with an
arbitrary trace that merely shares the same output indices.
`AtomicSelectedPathTracePackage` exposes only the relevant shape kind and
keeps both the trace and correlation evidence erased. Named prefix/exact
construction authorities elaborate through the full Regex chain, and the
focused 27-test gate remains green. Active and accepted evidence constructors
must extend this exact relation with the published child cursor package and a
recursive suffix-trace package before the package is added to search results.

The active-transition correlation constructor is now complete. It retains all
existential fields of the exact `AtomicSelectedTransitionActive` trace,
correlates the canonical child origin/current spine with erased suffix
evidence, and recursively correlates the exact child trace with its own shape
kind. The resulting outer kind is
`AtomicSelectedPathTraceActiveKind(child_cursor_kind, suffix_kind)`; neither
kind can be substituted independently of the trace it describes. The full
Regex chain and focused 27-test gate pass. A named construction authority must
next consume the already-published child cursor and suffix-trace packages,
followed by the accepted-transition dual.

The accepted-transition dual now completes the four-constructor exact trace
relation. It correlates the accepted admitted-state head, canonical accepted
child origin, child cursor evidence, skipped-prefix evidence, and recursively
indexed suffix trace with the exact `AtomicSelectedTransitionAccepted` value.
Both recursive constructors therefore retain the same proof boundary, with
only their child thread state and admitted-state head differing. The full
Regex chain and focused 27-test gate pass. Construction helpers can now consume
the child cursor package and suffix trace package uniformly for active and
accepted transitions, after which `AtomicPathSearchYes` can publish the exact
trace package.

`atomic_selected_path_trace_active_package` is now the single active
construction authority. It receives the exact ordinary trace fields plus the
relevant child cursor and suffix-trace packages, opens each package kind first,
and feeds only erased correlated evidence into
`AtomicSelectedPathTraceActiveEvidence`. The resulting runtime package carries
the recursive active kind and no list, equality, origin certificate, or trace
payload. The full Regex chain and focused 27-test gate pass. The accepted
construction helper is the remaining dual before evaluator publication.

`atomic_selected_path_trace_accepted_package` now supplies that dual. It opens
the published accepted-child cursor and recursive suffix-trace packages
kind-first, then constructs the exact accepted evidence with the correlated
erased payloads. Active and accepted parent transitions therefore share the
same construction boundary and expose only their finite relevant kind trees.
The complete Regex module chain and focused 27-test refutation gate pass. The
next slice publishes these exact trace packages through
`AtomicPathMembersYes` and `AtomicPathSearchYes` and constructs them at every
terminal and recursive evaluator success site.

Successful evaluator results now publish the exact trace package end to end.
Prefix and exact completion construct the two terminal packages;
active/accepted recursion constructs the parent package from the canonical
child-origin cursor package and the child's exact trace package. Sibling
skipping and the member-to-search projection preserve the package unchanged,
while start selection consumes only the erased trace until its own package is
introduced. Both `AtomicPathMembersYes` and `AtomicPathSearchYes` index their
relevant package by the exact erased trace they return. The complete Regex
chain and focused 27-test gate pass. Recursive commit alignment can now inspect
the published trace kind before opening its correlated erased constructor.

Consumption testing found that the last sentence is too weak as written. The
generic `AtomicSelectedPathTracePacked(kind, erased_evidence)` boundary is
sound to construct, but a consumer still cannot reopen the erased correlation
and repackage or dispatch on fields obtained from it: E104 correctly rejects
both operations. Do not weaken E104 and do not project erased evidence back
into a runtime package. Replace this generic boundary with constructor-
correlated relevant package constructors for prefix completion, exact
completion, active transition, and accepted transition. The active/accepted
constructors must carry the already-existing child-origin cursor package and
recursive suffix-trace package directly; their erased trace remains only an
index. Matching the relevant package constructor then exposes the recursive
packages without inspecting erased data. Migrate evaluator successes to this
representation before implementing recursive destination-rejection alignment,
then delete the generic packed boundary once no consumer remains.

That atomic migration is now complete. `AtomicSelectedPathTracePackage` has
four constructor-correlated cases: prefix completion, exact completion, active
transition, and accepted transition. The recursive cases carry the relevant
canonical child-origin cursor package and exact suffix-trace package directly;
all trace values, cursor proofs, equalities, origin certificates, and skipped
evidence remain erased indices or erased constructor arguments. Construction
helpers no longer inspect either child package. The generic
`AtomicSelectedPathTracePacked`, the redundant trace-kind tree, and its erased
correlation relation have been removed. The complete Regex chain and focused
27-test gate pass. Recursive destination-rejection alignment can now match the
relevant active/accepted package constructor and recurse on its child packages
without any E104-invalid recovery step.

The exhausted-input escaped-head contradiction is the first migrated
consumer. It now receives the exact trace package, refines the relevant active
constructor, and eliminates the active child's suffix package directly. That
suffix is indexed at an active thread with empty input, so none of the four
package constructors can inhabit it. The former erased selected-trace match is
gone from this theorem. The full Regex chain and focused 27-test gate pass,
confirming that recursive package elimination—not erased evidence inspection—
is accepted by the relevance checker. Apply the same pattern to the exact-
accepted leaf and then to nonterminal destination-rejection recursion.

The exact-accepted escaped-head leaf now uses the same package-only
elimination. Its outer accepted package exposes a suffix package indexed at an
accepted thread with non-empty input in exact mode; prefix completion has the
wrong mode, exact completion requires empty input, and recursive packages
require an active thread. The erased selected trace is no longer inspected.
The complete Regex chain and focused 27-test gate pass. Both terminal
escaped-head leaves are now migrated; the next proof slice is the recursive
destination-rejection child/tail alignment.

The rejected-root bridge now has the same package-native form.
`atomic_start_refutation_excludes_selected_package` accepts the root rejection
certificate, relevant selected membership, and the exact relevant
`AtomicSelectedTracePackage`; the erased selected trace appears only as the
package index. It delegates to the package-preserving membership induction, so
the tail callback receives `AtomicStartSelectedTailTracePackage` without
recovering anything from erased evidence. This shape correctly does not trigger
E104: matching or reconstructing relevant data from the erased trace would be
illegal, but eliminating the separately relevant constructor-correlated package
is permitted. The complete focused 27-test Regex refutation gate passes. Next,
migrate the concrete active and accepted rejected-root wrappers to this bridge,
then remove the legacy trace-only root adapter and tail transport once their
callers are gone.

The concrete active rejected-root path is now package-native.
`atomic_start_refutation_rejected_active_excludes_package` owns the dependent
membership split: `Here` refines the selected start to the active head and
eliminates `AtomicSelectedTracePackage` through the empty-input active
contradiction, while `There` constructs
`AtomicStartSelectedTailTracePackage` from the rejected-tail certificate and
preserves the same relevant trace package. The public
`atomic_start_refutation_rejected_active_selected_package` wrapper exposes that
consumer without the legacy erased public witness or trace-only tail callback.
The full Runtime → Proof → Regex → Language chain and focused 27-test
gate pass. Migrate the accepted rejected-root path next, then redirect concrete
callers before deleting the trace-only variants.

The accepted rejected-root dual is now package-native as well.
`atomic_start_refutation_rejected_accepted_excludes_package` performs the same
relevant membership split: `Here` eliminates the accepted selected package at
non-empty exact child input, and `There` preserves that package in
`AtomicStartSelectedTailTracePackage`. Its public selected-package wrapper no
longer needs `AtomicStartAcceptedRejectedTailPackage`, a head-specialized erased
trace, or the erased public start witness. Runtime, Proof, Regex, and Language
all elaborate, and the focused 27-test gate passes. Both concrete active and
accepted rejected-root consumers now have relevant-package forms; redirect the
remaining construction-site callers to these forms, then remove the obsolete
trace-only consumers and recovery packages.

Recursive commit alignment now has package-native terminal leaves for both
local rejection causes. The input-exhausted active leaf and the exact-accepted
leaf each consume `AtomicSelectedPathTracePackage` at the already-aligned outer
candidate, refine its relevant active/accepted constructor, and eliminate the
directly retained child package at its impossible index. Their erased
`AtomicPathCommitCause` values remain certificates only and are never inspected
to recover relevant data. The full Regex chain and focused 27-test gate pass.
Next thread the trace package through the two cursor-location folds so their
same-cursor branches call these leaves, then migrate the strict left/right
recursive continuations.

Both commit cursor-location folds now have package-preserving forms. Their
same-cursor branches call the package-native input-exhausted and exact-accepted
leaves, while both strict directional callbacks receive the cursor location
and exact `AtomicSelectedPathTracePackage` explicitly. No callback must close
over an erased trace or recover its package later. Runtime, Proof, Regex, and
Language elaborate and the focused 27-test gate passes. Next implement the
left/right recursive consumers over these two-argument continuations and
connect them at the escaped/rejected-prefix commit dispatch sites.

Commit cursor-package publication is now complete at the evaluator boundary.
`AtomicPathMembersCommit` and `AtomicPathSearchCommit` retain the relevant
`LookaroundAdmittedStateCursorSuffixPackage` alongside their erased suffix.
Local blocking commits publish the package already owned by destination
traversal; propagated child commits preserve the current parent package; and
escaped/rejected sibling propagation preserves the exact parent package rather
than attempting to derive it from a tail cursor with the same `whole` index.
The members-to-search projection carries it unchanged. The first attempted
tail-derived construction was correctly rejected by E093 because it changed
the package's outer list; using the construction site's existing parent package
is the canonical fix. The full Regex chain and focused 27-test gate pass.
Recursive commit-cause packages can now retain and consume this relevant cursor
authority in the strict directional branches.

`AtomicPathCommitSelectedLocationPackage` now correlates the three authorities
needed by strict recursion: the exact erased commit cause, its relevant commit
cursor package, and the exact relevant selected-trace package. Separate
`Same`, `LeftAfter`, and `RightAfter` constructors retain the cursor relation
that selected the branch; `atomic_path_commit_selected_location_package`
constructs them from the canonical cursor comparison. Recursive callbacks can
therefore no longer pair a cause, cursor, and trace originating at different
search results, and no erased cause projection selects runtime control. The
full Regex chain and focused 27-test gate pass. Next specialize this carrier at
the input-exhausted and exact-accepted location folds, then consume its strict
constructors in sibling recursion.

The correlated carrier now has a single constructor-directed eliminator,
`atomic_path_commit_selected_location_package_fold`. Same, left-after, and
right-after continuations each receive the intact carrier rather than separate
payload arguments. This makes the relevant location constructor the sole
branch authority and prevents recursive consumers from substituting a cause,
commit cursor, or selected trace after dispatch. The complete Regex chain and
focused 27-test gate pass. The next slice specializes the same continuation to
the two terminal package leaves and replaces the left/right continuations with
recursive sibling consumers.

The input-exhausted `AfterFailure` case now consumes the correlated location
carrier directly. `Same` uses its erased equality only to rewrite the selected
cursor index, then invokes the package-native exhausted-child contradiction
with the cause and trace package retained by that same constructor. `LeftAfter`
and `RightAfter` forward the original carrier intact. The complete Regex chain
and focused 27-test gate pass. Apply the identical construction to the
exact-accepted terminal case, then replace both strict callbacks with recursive
commit/sibling consumers.

The exact-accepted `AfterFailure` dual now consumes the same correlated
location carrier. Its `Same` constructor rewrites the selected cursor and
eliminates the retained accepted child package at the non-empty exact index;
strict constructors forward the intact cause/cursor/trace triple. Runtime,
Proof, Regex, and Language elaborate and the focused 27-test gate passes. Both
terminal correlated folds are complete. The remaining work at this layer is
the genuinely recursive `LeftAfter`/`RightAfter` sibling handling and the
root-destinations-exhausted correlated fold.

The missing child-cursor boundary for correlated `AfterFailure` commits is now
explicit as `AtomicPathCommitAfterFailureChildPackage`. It pairs the exact
erased commit cause with the relevant child
`LookaroundAdmittedStateCursorSuffixPackage` already present at evaluator
construction. This is the payload required by root destination exhaustion and
recursive destination rejection; consumers no longer need to project a child
cursor branch from the erased cause. The complete Regex chain and focused
27-test gate pass. Next publish this carrier through the `AfterFailure` branch
of the recursive commit-structure package and consume it in the correlated
root-destinations-exhausted fold.

The initial generic child carrier was deliberately replaced before
publication: pairing an arbitrary cause type with an arbitrary cursor-package
type preserved two values operationally but did not prove that the hidden
child cursor belonged to the cause. The definitive
`AtomicPathCommitAfterFailureChildPackage` is instead indexed by the exact
`AtomicPathCommitAfterFailure(...)` value, its child whole/current cursors, and
both child failure kinds. Its sole constructor mirrors the cause constructor
and carries the relevant cursor package at those same indices. Consumers may
therefore refine the erased cause and obtain its actual child cursor without a
trust convention or E104-invalid projection. The full Regex chain and focused
27-test gate pass.

Do not immediately hide that relation behind one generic outer structure
indexed by both `kind` and `cause`. The attempted sum correctly failed during
interface registration: refining generic `kind` to `AfterFailure(...)` does not
transport the separately dependent `cause` index, and weakening the cause to a
mere type would discard the correlation just established. Keep
`AfterFailure`, `FromChild`, `PastEscaped`, and `PastRejected` as exact
constructor-specific recursive families first; combine them only through a
fully mirrored outer constructor whose result fixes the exact cause value.

That fully mirrored outer family now has its first sound branch.
`AtomicPathCommitStructureAfterFailurePacked` explicitly binds an
`after_cause` whose type is already fixed at
`AtomicPathCommitAfterFailureKind(...)`, then carries the exact indexed child
package for that value. This avoids transporting a generic dependent cause
when the kind refines and elaborates through Runtime, Proof, Regex, and
Language; the focused 27-test gate passes. Add `FromChild` next with its exact
child cause and recursive structure package, followed by the two sibling-tail
constructors.

`AtomicPathCommitStructureFromChildPacked` now mirrors the propagated-child
cause exactly and carries a strictly positive recursive
`AtomicPathCommitStructurePackage` indexed by the exact child cause. The outer
constructor fixes `AtomicPathCommitFromChild(...)` as its result index, so
recursive consumption needs neither an erased kind match nor a separately
recovered child cursor. The complete Regex chain and focused 27-test gate pass.
Implement `PastEscaped` and `PastRejected` with the same exact tail-cause
discipline next.

`AtomicPathCommitStructurePastEscapedPacked` now retains both exact recursive
substructures: the child commitment that escaped the current scope and the
later sibling-tail commitment that determines the outer commit depth. Its
result is indexed by the exact `AtomicPathCommitPastEscaped(...)` cause, so
neither recursive branch can be paired with another cursor or cause. The full
Regex chain and focused 27-test gate pass. `PastRejected` is the remaining
structure constructor before evaluator publication.

`AtomicPathCommitStructurePastRejectedPacked` completes the recursive cause
shape. It retains the rejected child cursor package at the exact child failure
indices and the exact recursive tail commit structure; its result is indexed
by the mirrored `AtomicPathCommitPastRejected(...)` value. All four cause
constructors now have sound structure constructors, and the complete Regex
chain plus focused 27-test gate pass. Next add this structure package to
members/search commit results and build each constructor at its evaluator
construction site.

`AtomicPathMembersCommit` and `AtomicPathSearchCommit` now publish an exact
`AtomicPathCommitStructurePackage` alongside every erased cause. The evaluator
constructs `AfterFailure` from the child cursor package at the blocking site,
wraps recursive child commits with `FromChild`, and combines child/tail
structures for `PastEscaped` and `PastRejected`; the members-to-search boundary
preserves that package unchanged. No later consumer has to inspect an erased
cause to recover its relevant recursive data. The complete Regex chain and
focused 27-test gate pass. Next consume the published structure in the
correlated root-destination exhaustion fold, then implement the strict
left/right recursive destination rejection branches.

The aligned root-destinations-exhausted leaf is now package-native. It matches
the exact `AfterFailure` structure package and the selected-trace package
before refining any erased child scope, failure, origin, cursor, or trace
field; after those relevant constructors have fixed the branch, the existing
canonical-origin contradiction is entirely erased. This ordering is
essential. A discarded prototype aligned two erased origin certificates and
then used that result to inspect a relevant cursor package: E104 correctly
rejected it. A second discarded carrier matched the erased canonical
equalities before the remaining relevant trace package and spent 251.65 s wall
(232.78 s CPU) without finishing `Std.Regex.Runtime`, versus the established
roughly two-minute complete Regex-chain window. Selecting all relevant package
constructors first avoids both the relevance violation and that normalization
blow-up; the complete Regex chain and focused 27-test gate pass. Next extend
the correlated commit/selection location carrier with the exact structure
package and implement the root terminal fold over that intact carrier.

The correlated commit/selection carrier now retains a single relevant
`AtomicPathCommitStructureExistentialPackage` rather than independently typed
cause and structure payloads. Its constructor carries the cause as an explicit
erased field and the structure at that exact cause index: explicitness makes
the witness available for type refinement while erasure still prevents it
from affecting runtime representation. The input-exhausted, exact-accepted,
and root-destinations-exhausted `Same` folds first inspect this relevant
existential and selected-trace package, then refine the erased cursor equality.
The root fold calls the package-native aligned leaf without scrutinizing its
erased cause. `LeftAfter` and `RightAfter` preserve the entire carrier for the
recursive sibling proof. The complete Regex chain and focused 27-test gate
pass. Next implement those two strict recursive destination-rejection branches
from the published `FromChild`, `PastEscaped`, and `PastRejected` structures.

Strict recursion also requires the successful search's explanation for moving
past earlier siblings; a commit structure and a selected trace alone do not
prove that the selected cursor was reachable under ordered search. That
authority is now published as
`AtomicPathSkippedPrefixStructurePackage`. Its four relevant constructors
correlate empty, escaped-one, escaped-cons, and rejected-cons prefixes while
keeping the original evidence erased; both cons constructors retain the exact
recursive tail package. `AtomicPathMembersYes` constructs this structure at
the same escaped/rejected sibling sites as `AtomicPathSkippedPrefixEvidence`,
and `AtomicPathSearchYes` preserves it. Active and accepted selected-path
packages also retain the child's skipped-prefix structure, so it survives
recursive character transitions instead of being recoverable only from an
erased trace. The complete Regex chain and focused 27-test gate pass. Next add
this authority to the commit/selection carrier and consume paired commit/skip
constructors in the strict `LeftAfter` and `RightAfter` induction.

`AtomicPathCommitSelectedLocationPackage` now retains that authority directly.
All three location constructors carry the selected skipped-prefix package
alongside the exact commit structure, commit cursor, and selected trace; the
constructor helper accepts all four values before performing the canonical
cursor comparison. The input-exhausted, exact-accepted, and root-exhaustion
terminal folds are polymorphic over the new package because their `Same`
branches do not inspect it, while strict callbacks receive it intact. This
keeps terminal proofs small and makes the upcoming sibling induction the only
consumer responsible for pairing commit and skip constructors. The complete
Regex chain and focused 27-test gate pass. Next implement that paired strict
induction, starting with the locally blocking `AfterFailure` versus rejected-
head continuation contradiction.

That first strict base contradiction is now package-native.
`atomic_path_commit_after_failure_excludes_selected_rejected_head_package`
accepts the exact local `AfterFailure` cause and a selected skipped-prefix
structure whose head has the same child prefix/failure kinds. It first matches
the relevant `RejectedCons` structure constructor and only then consumes its
erased evidence; the retained continuation contradicts the commit's blocking
close through the existing exact indexed lemma. This proves the fundamental
later-sibling case without inspecting an erased skip-kind sum or accepting an
uncorrelated continuation. The complete Regex chain and focused 27-test gate
pass. Next call this leaf from the strict `RightAfter` branch, then recurse
through paired escaped/rejected cons tails; `LeftAfter` remains the reverse-
cursor induction over the commit structure.

The local blocking case is now connected to the intact location carrier.
`atomic_path_commit_after_failure_excludes_selected_rejected_packages` opens
the relevant commit existential and delegates to the rejected-head leaf;
`atomic_path_commit_after_failure_excludes_selected_rejected_location_package`
consumes `Same`, `LeftAfter`, and `RightAfter` carriers without separating
their commit, skip, cursor, or trace authorities. All three locations close:
once the exact `AfterFailure` commit and corresponding rejected skipped head
are fixed, blocking close versus continuation is contradictory independently
of the cursor comparison. The complete Regex chain and focused 27-test gate
pass. Propagated `PastEscaped`/`PastRejected` cases next need their relevant
tail cursor packages retained in the commit structure so they can construct a
new correlated tail carrier and recurse.

That last proposed duplication was rejected by the next red test before any
commit-structure representation changed. The outer commit cursor package can
already be advanced canonically, while the selected skipped-prefix structure
itself determines the exact front-to-current cursor.
`atomic_path_skipped_prefix_structure_cursor_package` now derives that cursor
by matching the relevant empty/escaped/rejected structure first and rebuilding
the package recursively; erased constructor fields affect only indices.
`AtomicPathCursorLocationRightAfter` and the correlated carrier now retain a
relevant cursor package instead of an erased suffix, and the generic bridge
`lookaround_admitted_cursor_suffix_package` publishes existing relevant suffix
evidence once. The complete Regex chain and focused 27-test gate pass. Tail
recursion can therefore advance existing authorities rather than enlarging
the recursive commit structure.

The selected-tail location is now derived without re-comparing canonical
lists. `atomic_path_skipped_prefix_structure_location` maps the relevant empty
structure to `Same` and every non-empty escaped/rejected structure to
`RightAfter`, reusing the cursor package derived by the previous lemma. Thus a
recursive tail carrier can obtain both its selected suffix and its location
from one constructor-correlated authority; no erased suffix is promoted back
into relevant control and no second traversal can disagree with the selected
skip tree. The complete Regex chain and focused 27-test gate pass. Next extract
the exact `PastEscaped`/`PastRejected` tail commit structure into a relevant
existential, advance the outer commit cursor package, and combine those values
with this location.

Recursive commit-tail extraction now has that authority.
`AtomicPathCommitStructureCursorExistentialPackage` ties an exact erased tail
cause to its relevant recursive structure and the cursor package for the same
tail. Constructor-directed projections for `PastEscaped` and `PastRejected`
first select the relevant commit structure, then retain its already-correlated
tail structure while advancing the relevant outer cursor. An initial compile
correctly raised E104 because the canonical cursor-advance API still declared
its `head` and `tail` indices relevant; those values only index erased suffix
evidence and never select runtime behavior, so both cursor-advance layers now
declare them erased. The projections do not inspect the erased cause at all.
The complete Regex chain and focused 27-test gate pass. Next combine the
extracted commit tail with the selected skipped-prefix tail and its derived
location to construct the recursive correlated carrier.

`atomic_path_commit_selected_tail_location_package` now performs that generic
combination. It opens the relevant commit-tail package only to obtain the
cursor already correlated with its structure, retains the combined commit
authority intact, and derives `Same` or `RightAfter` solely from the relevant
selected skipped-prefix structure. The resulting
`AtomicPathCommitSelectedLocationPackage` cannot pair an unrelated cursor,
commit structure, or selected tail. The complete Regex chain and focused
27-test gate pass. Next add constructor-specific PastEscaped/EscapedCons and
PastRejected/RejectedCons adapters that extract both tails and invoke this
constructor before the recursive RightAfter fold.

Those paired adapters are now implemented.
`atomic_path_commit_past_escaped_selected_tail_location_package` requires the
same child commit-kind index on `PastEscaped` and `EscapedCons`, while
`atomic_path_commit_past_rejected_selected_tail_location_package` requires the
same child prefix/failure-kind indices on `PastRejected` and `RejectedCons`.
Each relevant selected constructor exposes its tail structure, the matching
commit projection supplies the exact tail commit/cursor authority, and the
generic constructor derives the recursive location. There is no generic
erased-kind dispatch and no uncorrelated tail pairing. The complete Regex
chain and focused 27-test gate pass. Next consume these adapters from the
outer RightAfter branch and recursively dispatch on the returned tail
location.

The recursive tail dispatch boundary now preserves its construction
provenance. `AtomicPathRecursiveCommitSelectedPackage` names the exact
commit/cursor/trace/skipped-tail carrier, while
`atomic_path_commit_selected_tail_location_fold` matches the relevant skipped
structure directly: `Empty` constructs `Same`; escaped-one, escaped-cons, and
rejected-cons construct `RightAfter`. It exposes only those two callbacks, so
an artificial `LeftAfter` obligation cannot re-enter after a forward tail
step. The complete Regex chain and focused 27-test gate pass. Next route the
PastEscaped/EscapedCons and PastRejected/RejectedCons outer branches through
this two-way fold, then make its `RightAfter` callback the recursive call.

Both propagated branches now use that interface.
`atomic_path_commit_past_escaped_selected_tail_location_fold` and
`atomic_path_commit_past_rejected_selected_tail_location_fold` first match the
relevant selected head structure, extract the matching commit tail/cursor,
and invoke the two-way fold. Their `Same` and `RightAfter` callbacks receive
the exact recursive carrier, including the unchanged selected trace package;
neither branch reconstructs erased evidence or admits `LeftAfter`. The
complete Regex chain and focused 27-test gate pass. Next implement the common
recursive consumer: `Same` dispatches the tail commit structure against the
selected trace terminal leaves, while `RightAfter` consumes a local blocking
head or invokes one of these propagated folds again.

The recursive branch refinement is now retained in one-constructor authority
types instead of being forgotten at callback entry.
`AtomicPathCommitSelectedSameAuthorityPackage` and
`AtomicPathCommitSelectedRightAuthorityPackage` carry the exact correlated
payloads for their respective cases, and the two-way fold plus both
propagated folds expose those types directly. The three initial `Same`
terminal consumers are complete: active-child input exhaustion, accepted
child with remaining input in exact mode, and active-child root-destination
exhaustion. The first two close from the refined trace package; the third
selects the relevant commit structure before reusing the exact package-native
root contradiction. The complete Regex chain and focused 27-test gate pass.
Next extend `Same` dispatch across recursive commit structures, then implement
the one-constructor `RightAfter` consumer and its recursive call.

The first one-constructor `RightAfter` leaf is now complete.
`atomic_path_recursive_commit_after_failure_right_excludes_selected_rejected_package`
matches the relevant combined commit package, exact `AfterFailure` structure,
and corresponding rejected skipped-prefix structure before consuming any
erased fields. The child package supplies the blocking close and the selected
skip supplies its continuation certificate, which contradict through the
existing depth lemma. No erased cause is projected or reconstructed. The
complete Regex chain and focused 27-test gate pass. Next add the propagated
`PastEscaped` and `PastRejected` right-authority consumers whose recursive
callbacks invoke the common induction again.

Both propagated `RightAfter` consumers are now complete. Direct projections
from `AtomicPathCommitStructureCursorExistentialPackage` advance the retained
cursor and extract the exact `PastEscaped` or `PastRejected` tail structure;
they never rebuild the older explicit-cause existential. The corresponding
right-authority folds match the paired escaped-cons or rejected-cons selected
structure and produce the next one-constructor `Same` or `RightAfter`
authority for their callbacks. The complete Regex chain and focused 27-test
gate pass. Next define the common structurally recursive dispatcher over
commit structure and selected skipped-prefix structure, using the completed
terminal and propagated consumers as its cases.

The terminal escaped-prefix edge is now explicit too.
`atomic_path_recursive_commit_past_escaped_right_selected_one_tail_package`
handles `PastEscaped` paired with `EscapedOne`: after the single escaped head,
the projected tail commit cursor and selected cursor are definitionally the
same `remaining` list. It therefore returns a one-constructor `Same` authority
with an exact empty selected-prefix structure, rather than routing through the
recursive `EscapedCons` fold. The complete Regex chain and focused 27-test
gate pass. The common dispatcher can now treat escaped-one as the base and
escaped-cons/rejected-cons as forward recursion.

`AtomicSelectedTracePackage` now introduces the corresponding selected-start
boundary. Its active and accepted constructors are indexed by the exact erased
`AtomicSelectedTrace` value and retain three relevant recursive packages: the
selected-whole cursor, canonical selected-origin cursor, and selected path
suffix. Start membership, canonical equalities, routines, and trace values
remain erased. The declaration elaborates through the complete Regex chain and
the focused 27-test gate passes. The next slice constructs these packages at
the two start-success sites and publishes them through start and top-level
search results.

Selected-start package publication is now complete. Both active and accepted
start-success branches construct the exact package from the two cursor
packages and child path package already returned by `AtomicPathSearchYes`.
`AtomicStartMembersYes` preserves it through sibling traversal. A one-
constructor existential wrapper hides the exact erased start trace while
`LookaroundRoutineSearchYes` carries the relevant package to its consumers;
the existing erased selected-start witness remains unchanged. The complete
Regex chain, downstream proof module, and focused 27-test gate pass. Recursive
proof entry points can now accept this top-level package and refine down to the
selected path package without inspecting an erased witness.

Package-native active and accepted start-rejection eliminators now establish
the terminal consumer API for that top-level package. The active case refines
an active selected start with empty child input; the accepted case refines an
accepted selected start in exact mode with remaining child input. Each closes
by eliminating the directly retained path suffix package, without matching the
erased start trace or using a child refutation to recover its suffix. The full
Regex chain and focused 27-test gate pass. The remaining migration is to thread
the existential package through the existing start-refutation recursion and
replace its legacy trace-only terminal calls with these package-native leaves.

The selected sibling-tail transport now has a package-preserving authority.
`AtomicStartSelectedTailTracePackage` correlates the recursive tail refutation,
no-evidence witness, later membership, erased selected trace, and its relevant
selected-start package. `atomic_start_rejected_member_induction_selected_package`
returns the head result for `Here` and transports that complete package
unchanged for `There`. The legacy trace-only induction remains temporarily for
unmigrated callers; new recursion must use the package-preserving form. The
complete Regex chain and focused 27-test gate pass. Next migrate the rejected-
root adapters to this induction, then remove the trace-only tail type and fold.

Recursive commit causes are now available at the relevant structure boundary
while remaining quantity-zero. `PastEscaped` and `PastRejected` publish their
exact tail cause explicitly, and
`AtomicPathCommitStructureCursorExistentialPacked` publishes the cause
correlated with its relevant cursor and structure in the same form. A separate
compiler limitation prevented a named bare-variable pattern from binding a
forced erased constructor field: the elaborator treated every forced field as
check-only even when the binding would remain at quantity zero. Named implicit
splitting now binds a bare variable at the telescope slot's actual quantity,
including forced erased slots, while dot and non-variable patterns remain
checks and relevance still rejects runtime use. Regressions cover both the
basic case and a forced erased field following a dependent erased kind. The
four package-native terminal eliminators can consequently select `FromChild`
or `PastEscaped`, bind the exact child kind and cause, and close empty-input or
accepted-child cases through the existing cause-native contradiction. No
proof evidence is promoted into relevant runtime state. The complete Regex
chain, 12-test named-implicit gate, and focused 27-test Regex gate pass. Next
use these leaves in the common recursive dispatcher and complete its remaining
structure/selected-prefix cases.

The recursive child cursor is now retained at its actual construction site.
`FromChild` and `PastEscaped` previously kept an erased child suffix and a
relevant child structure but discarded the corresponding relevant cursor
package returned by `AtomicPathSearchCommit`; that made the common induction
unable to compare the committed child suffix with the independently selected
child suffix without reconstructing relevant data from erased evidence. Both
structure constructors now retain that cursor package. Because the child
capture context, scope, canonical spine, current suffix, commit depth, and kind
are existential from the parent boundary,
`AtomicPathCommitChildCursorExistentialPackage` owns all of those indices with
the exact recursive cursor/structure package. Constructor-directed projections
for `FromChild` and `PastEscaped` return this single authority. The complete
Regex chain and focused 27-test gate pass. Next pair this child existential
with the child cursor/skipped-prefix/trace package exposed by the selected
trace constructor, then invoke the recursive location fold.

The first recursive child/selection pairing boundary is now E104-safe. A
direct dependent match over the child existential and selected trace caused
their erased capture-context, scope, origin, and cursor indices to enter the
runtime match convoy when the two relevant cursor packages were compared.
The compiler correctly rejected that reconstruction as E104. The child cursor
now publishes a finite `Here`/`Drop` runtime shape before its dependent indices
are hidden, while `AtomicPathCommitChildCursorPayloadPackage` retains the exact
dependent cursor/structure authority behind a non-dependent runtime envelope.
The shape comparison is ordinary structural recursion and is intentionally not
`@reducible`; it chooses runtime control but is not itself proof evidence. The
complete Regex module chain and focused 27-test refutation gate pass. Next
thread the selected cursor's construction-time shape alongside its retained
trace package, use the shape tag only to select a branch, and discharge that
branch from the retained cursor/structure authorities before invoking the
recursive location fold.

Both recursive selected-trace constructors now retain the selected child's
finite cursor shape at the same construction site as its canonical cursor
package. Active and accepted transitions derive the shape structurally from
that relevant package; every dependent consumer has been migrated to the new
constructor arity. Attempting to recover the shape later by matching the full
dependent trace package still correctly raises E104, because that match also
opens erased transition and origin indices. Therefore the shape must next be
threaded through a non-dependent outer trace envelope alongside the untouched
dependent package. The envelope, not a projection through erased indices, will
feed `atomic_path_commit_child_selected_location_package` and the recursive
location fold.

`AtomicSelectedPathTraceRuntimeEnvelope` now supplies that non-dependent
boundary. It is parameterized only by the complete dependent trace-package
type and retains `(shape, package)` as ordinary relevant fields, so matching
the envelope introduces no erased transition binders. The recursive child
existential and its location packer now retain this envelope intact and use
only its shape for finite control selection. The dependent package remains the
authority consumed by subsequent proof branches. Next construct and propagate
the envelope at every active/accepted selected-trace publication site, then
replace the legacy trace-only recursive dispatcher inputs with the enveloped
form.

Successful path search now publishes the runtime envelope as part of both
`AtomicPathSearchYes` and `AtomicPathMembersYes`. Empty accepted terminals
construct a `Here` envelope, recursive active and accepted transitions derive
the next envelope from the exact child selection-from-origin package, and
sibling traversal preserves the envelope unchanged while extending only the
outer skipped prefix. Root conversion also forwards the same envelope. This
keeps the selected child shape live from its construction site to every search
consumer without inspecting the dependent trace. Next consume the propagated
envelope in the common commit/selection dispatcher and replace its remaining
trace-only recursive entry points.

The common recursive existential now has a single runtime dispatcher.
`atomic_path_recursive_commit_selected_existential_dispatch` distinguishes the
ordinary correlated carrier from child `Same`, `LeftAfter`, and `RightAfter`
shape cases, but passes the original existential unchanged to every callback.
Consequently the finite tag controls branch selection without reconstructing
erased child indices or masquerading as a cursor proof. Next replace the
legacy entry points one constructor family at a time: terminal same-cursor
leaves first, then rejected-head right branches, then escaped/rejected sibling
tail recursion.

The recursive child payload now also retains its exact erased cursor-suffix
authority beside the canonical child origin and relevant cursor/structure.
Previously `FromChild` and `PastEscaped` preserved the suffix only inside the
structure constructor, then discarded it while publishing the child payload;
that forced any later same-cursor proof either to reopen the wrong abstraction
boundary or to mistake the runtime shape tag for evidence. Both canonical
payload construction sites now forward the original suffix unchanged. The
complete Regex chain and focused 27-test refutation gate pass.

The canonical alignment core now accepts a structure-derived non-emptiness
theorem rather than requiring the erased commit-kind index to be promoted to
runtime data. `atomic_path_commit_structure_nonempty` dispatches on the
relevant structure authority, and
`atomic_path_commit_selected_authority_alignment_fold` contains the shared
origin/suffix alignment calculation. A proposed generic recursive-child fold
was rejected by E104: after erased origin refinement, invoking one of several
relevant continuation callbacks would make erased proof data choose runtime
control, even though every callback returns `Empty`. Therefore the next step
is branch-specific: the existing relevant shape dispatcher first selects
`Same`, `LeftAfter`, or `RightAfter`; each concrete commit/trace consumer then
opens erased authorities only to derive its single fixed contradiction or
recursive theorem. The shape remains a control hint, while each consumer
independently validates the corresponding canonical cursor relation.

The runtime dispatcher now narrows its `Same` branch into
`AtomicPathRecursiveCommitSelectedChildSameExistentialPackage` before handing
control to a consumer. This carrier preserves the exact dependent child commit
and selected trace envelope but no longer includes a location sum: its sole
constructor can only be built from the relevant `AtomicPathCursorShapeSame`
branch. Consequently the eventual same-cursor contradiction has one fixed
runtime control path before it opens any erased context, origin, or suffix
authority. The complete Regex chain and focused 27-test refutation gate pass.
Next add the structure-specific `Same` consumers: begin with the three existing
`AfterFailure` terminal leaves, validate canonical cursor equality directly in
each fixed branch, then recurse through `FromChild`, `PastEscaped`, and
`PastRejected` without rebuilding the legacy broad location package.

The failure side now retains an equally exact runtime discriminator.
`AtomicPathRootRefutation` is indexed by its `AtomicPathFailureKind`, and every
root/no search result publishes that kind as relevant data while keeping the
refutation itself erased. `AtomicPathFailureKindAuthority` is a dependent
singleton family, so an `AfterFailure` child package carries a runtime tag
whose type is definitionally tied to the erased failure index; a loose or
mismatched enum cannot be constructed. The authority is created once from the
relevant search result at the blocking construction site and survives into the
commit structure. This is the control input needed for the three terminal
`Same` consumers without matching erased failure evidence. The complete Regex
chain and focused 27-test refutation gate pass. Next dispatch the narrowed
`Same` carrier by this authority and connect input exhaustion, exact accepted,
and root destination exhaustion to their existing fixed contradiction leaves.

Commit-child cursor shape is now type-correlated too.
`LookaroundAdmittedStateCursorShapedPackage` indexes its recursive runtime spine
by the exact `Here`/`Drop` shape: the `Here` constructor can only inhabit
`ShapeHere`, and every `Drop` constructor extends both the cursor and shape
indices together. `lookaround_admitted_cursor_shaped_package` is the sole
bridge from the existing suffix package. `AtomicPathCommitChildCursorPayloadPackage`
is indexed by that shape and carries the shaped package, while its outer
existential uses the same shape index. A hand-written mismatched commit
`(shape, payload)` is therefore no longer typeable. The complete Regex chain
and focused 27-test refutation gate pass. Next add the same shaped authority to
active/accepted selected-trace constructors and derive their runtime envelope
shape from it, completing both sides of the sound `Same` comparison.

Active and accepted selected traces now retain the same shaped cursor authority
as their final relevant field. Their published `child_cursor_shape` is the
shape computed from the exact `child_cursor_package`, and the dependent
`LookaroundAdmittedStateCursorShapedPackage` field ties that value back to the
cursor spine in the constructor type. Every existing trace consumer was
migrated to the strengthened constructor arity. Thus both inputs to recursive
shape comparison now carry independently checkable, type-correlated runtime
spines; neither side relies on an unchecked parallel tag. The complete Regex
chain and focused 27-test refutation gate pass. Next define the structural
same-shape relation over these two authorities, retain it in the narrowed
`Same` carrier, and use it with canonical-origin equality to reach the fixed
terminal contradictions.

Cursor-shape comparison now returns indexed structural authority rather than
manufacturing the coarse location tag directly. `Same`, `LeftAfter`, and
`RightAfter` each have recursive singleton relations over the two exact shape
indices, and `AtomicPathCursorShapeComparison` is the total three-way result.
The legacy `atomic_path_cursor_shapes_location` API is retained for existing
callers but is now only an erasure through this canonical comparison. Thus a
future narrowed branch can retain the full recursive relation while ordinary
runtime consumers still receive the compact location enum. The complete Regex
chain and focused 27-test refutation gate pass. Next carry the comparison
authority—not merely its erased location—through the recursive child
existential and into the dedicated `Same` carrier.

Recursive pairing no longer trusts the selected trace envelope's parallel
shape hint. `atomic_path_commit_child_selected_location_package` opens the
relevant trace package and obtains `selected_shape` from the active or accepted
constructor whose final shaped authority certifies it. Prefix/exact terminal
constructors are uninhabited at this non-empty outer cursor. The commit shape
is already indexed by its payload, so the coarse location is now computed from
two validated construction authorities. The envelope hint remains only a
propagated optimization and cannot affect proof routing. The complete Regex
chain and focused 27-test refutation gate pass. Next change the recursive
existential to retain the full `AtomicPathCursorShapeComparison` produced from
these validated shapes, then narrow `Same` with its structural authority.

The recursive existential now retains that full comparison. The two hidden
shape indices are packed with `AtomicPathCursorShapeComparison` instead of
being erased to `AtomicPathCursorShapeLocation`, so dispatch can distinguish
the three runtime branches without losing the constructor-derived relation.
The `Same` branch moves its `AtomicPathCursorShapesSameAuthority` into
`AtomicPathRecursiveCommitSelectedChildSameExistentialPackage`; `LeftAfter`
and `RightAfter` continue to forward the original complete carrier. The full
Regex module chain elaborates and the focused 27-test refutation gate passes.
Next open the narrowed `Same` carrier in branch-specific consumers, revalidate
its hidden shapes against the retained shaped cursor packages, and connect the
input-exhausted, exact-accepted, and destination-exhausted cases to their fixed
contradiction leaves.

The structural `Same` witness can now be checked against both exact shaped
cursor packages without reifying canonical proof equality. The local
`lookaround_admitted_cursor_same_shape_inner_equivalent` recursion follows only
the relevant `Here`/`Drop` spines and returns a one-constructor authority whose
inner-cursor equality field is erased. A direct `Equivalent` return was rejected
by E104 because it would have promoted the canonical outer equality into a
runtime value; the authority package preserves the same theorem without that
violation. The complete Regex chain elaborates, and the exact construction-site
regression passes. Next consume this authority inside the fixed input-exhausted
`Same` branch and forward its erased equality to the existing aligned terminal
leaf.

The first direct terminal wiring attempt exposed one remaining carrier
invariant that must be fixed before that forwarding is sound. Although the
private dispatcher constructs `same_authority` from the two validated shapes,
`AtomicPathRecursiveCommitSelectedChildSameExistentialPackage` does not index
that authority to either retained payload. Opening the child existential and
the dependent trace envelope together therefore leaves the authority's hidden
shape metavariables unrelated to the cursor authorities; E093 rejects the
correlated package rather than accepting a construction-time convention. An
attempt to expose only the commit payload inside the existing outer constructor
was also correctly rejected by E104: retaining the relevant trace envelope
after opening the child imports the envelope's erased path index into runtime
construction. The next carrier revision must introduce an opaque
selected-child payload at the trace construction boundary. That payload must
hide the outer path/context indices while exposing a right-shape-indexed cursor,
origin, skipped-prefix, and suffix-trace authority. The recursive carrier can
then pair it with an independently opaque left-shape-indexed commit payload and
an `AtomicPathCursorShapeComparison(left_shape, right_shape)` without opening
either dependent payload. Do not resume the terminal leaves until both shape
indices occur in the carrier's field types.

The selected side now has that opaque construction boundary.
`AtomicPathSelectedChildCursorPayloadPackage` has separate active and accepted
constructors indexed by the parent candidate and by the exact validated cursor
shape. Each constructor retains the child canonical origin, ordinary cursor
package, shaped cursor authority, skipped-prefix structure, and recursive
suffix trace package under shared child-whole/current indices. The extractor
`atomic_selected_path_trace_child_cursor_package` is the only bridge from an
outer active/accepted trace package; prefix and exact terminals are impossible
at this boundary. Consequently later recursive dispatch can consume a compact
right-shape-indexed payload without retaining or reopening the outer erased
trace path. The complete Regex chain elaborates and the exact structural
regression passes. Next replace the trace envelope in the recursive child
carrier with this selected payload, then add the symmetric opaque commit
payload and index the comparison directly by both exposed shapes.

The recursive child boundary is now fully path-free and constructionally
correlated. `AtomicPathCommitSelectedChildCursorPackage` opens the opaque
commit and selected existentials once, retains their left- and
right-shape-indexed payloads, and stores
`AtomicPathCursorShapeComparison(left_shape, right_shape)` over those exact
indices. The recursive carrier retains only this package: the outer selected
trace envelope, routine, and path no longer cross the dispatch boundary. The
`Same` carrier likewise retains both payloads together with
`AtomicPathCursorShapesSameAuthority(left_shape, right_shape)`, so a consumer
cannot receive equality authority for unrelated hidden shapes. The obsolete
unindexed comparison existential and late comparison helper have been removed.
The complete Regex module chain elaborates and the exact construction-site
regression passes. Next open the correlated `Same` payloads in its terminal
consumer, derive the inner-cursor equality through
`lookaround_admitted_cursor_same_shape_inner_equivalent`, and feed that erased
authority to the existing input-exhausted contradiction leaf.

The `Same` branch now has a proof-facing aligned carrier rather than another
shape-only convention. The active and accepted constructors of
`AtomicPathRecursiveCommitSelectedChildSameAlignedPackage` retain the exact
recursive commit structure, selected skipped-prefix structure, recursive
selected suffix package, and a
`LookaroundAdmittedCursorInnerEquivalentAuthority` indexed by their actual
inner cursors. Its sole constructor helper opens both opaque payloads, consumes
the candidate's capture-context and scope alignment, aligns their independently
published canonical origins, and combines that outer equality with the
validated common shape. Candidate metadata that does not occur in the child
proof state is deliberately absent from the aligned existential; retaining it
would leave hidden indices underdetermined. The complete Regex module chain
elaborates and the exact construction-site regression passes. Next match the
aligned commit structure: route `AfterFailure` terminal kinds into the existing
input-exhausted/exact-accepted leaves, and route `FromChild`, `PastEscaped`, and
`PastRejected` through their existing package-preserving recursive projections.

Recursive commit outer structure is now classified at the commit-child
construction boundary. `AtomicPathCommitStructureCursorClassifiedPackage` has
exact `AfterFailure`, `FromChild`, `PastEscaped`, and `PastRejected`
constructors, each retaining the original cursor/structure existential at its
fully indexed cause kind. `AtomicPathCommitChildCursorPayloadPackage` and the
aligned `Same` carrier now require this classified authority; a later consumer
can no longer receive a generic commit structure and speculatively reopen all
four possibilities. Both child projection sites construct the classification
before hiding their dependent indices. The complete Regex chain elaborates in
the established range and the exact structural regression passes. A direct
terminal fold was deliberately rejected: even after classification, combining
the nested failure/input/candidate refinements, inner-cursor equality rewrite,
and the older broad aligned-selected leaf exceeded five CPU minutes in
`Std.Regex.Runtime`. The next step is therefore to publish a narrow
input-exhausted terminal authority from the classified `AfterFailure`
construction itself, so the consumer does not normalize that entire telescope
again.

The empty-input equation is now retained at both relevant construction
boundaries. `AtomicPathSearchRootActiveInputExhaustedNo` specializes the
evaluator result to `Nil()` instead of immediately hiding it behind the generic
active-root rejection constructor. At commit publication,
`AtomicPathCommitAfterFailureTerminalClassifiedPackage` classifies the relevant
child input, candidate, and failure kind before the recursive existential hides
them; its input-exhausted constructor fixes `Nil()`, the exact active candidate,
and `AtomicPathFailureInputExhausted()` together. The generic branch remains
available for the other terminal and recursive cases. This construction never
matches `child_failure`, so no erased evidence is used to manufacture relevant
authority. The complete Regex chain elaborates in the established range and the
exact construction-site regression passes. Next open this retained terminal
classification in the aligned `Same` consumer and use its erased inner-cursor
equality only inside an `Empty`-returning eliminator that forwards the selected
suffix package to the existing aligned input-exhaustion leaf.

The aligned `Same` consumer now performs that narrow elimination.
`atomic_path_recursive_commit_selected_child_same_input_exhausted_fold` opens
only the already-classified outer commit, selects the retained
`AtomicPathCommitAfterFailureInputExhaustedPacked` authority, and forwards the
exact cause and selected suffix package to the existing aligned terminal leaf.
Its erased inner-cursor equality is inspected only on the path that eliminates
to `Empty`; it never constructs relevant state. Every unclassified,
`FromChild`, `PastEscaped`, `PastRejected`, and accepted-child case is returned
unchanged to the recursive callback. The complete Regex chain elaborates in
the established range and the exact construction-site regression passes. Next
install this fold as the `Same` callback of the common recursive dispatcher,
then classify and connect exact-accepted and destinations-exhausted terminals
using the same construction-time pattern.

The common recursive dispatcher now enforces that sequencing. Its `Same`
callback accepts only `AtomicPathRecursiveCommitSelectedChildSameAlignedPackage`;
the dispatcher constructs that alignment from the correlated child payloads and
runs the input-exhausted fold before invoking the callback. A caller therefore
cannot accidentally consume the earlier shape-only existential or bypass the
terminal contradiction. `LeftAfter` and `RightAfter` still receive the original
complete carrier, preserving the recursive evidence they require. The complete
Regex chain elaborates in the established range and the exact structural
regression passes. Next extend the construction-time terminal classifier with
the exact-accepted active/accepted dual and root destinations-exhausted case,
then make the same canonical dispatcher discharge those leaves in order.

The exact-accepted dual is now classified and discharged as the second
canonical `Same` stage. The terminal authority is additionally indexed by
`prefix_mode`; `AtomicPathCommitAfterFailureExactAcceptedPacked` exists only
for `False()`, a non-empty child input, an accepted candidate, and
`AtomicPathFailureExactAccepted()`. The dispatcher runs
`atomic_path_recursive_commit_selected_child_same_exact_accepted_fold` after
the input-exhausted fold and before exposing the aligned recursive callback.
The fold uses the retained inner-cursor equality only to eliminate through the
existing exact-accepted package leaf. The complete Regex chain elaborates in
the established range and the exact structural regression passes. Next retain
root-prefix authority at construction so destinations-exhausted can be
classified without inspecting erased prefix or failure evidence, then add its
third canonical `Same` fold.

Root destinations exhaustion is now the third canonical `Same` terminal.
`AtomicPathFailurePrefixRootAvailability` is published explicitly at each of
the seven child-search result branches: root constructors supply the exact
root witness, while suffix-local results supply an opaque unavailable witness
without inspecting their erased skipped-prefix kind. Combined with non-empty
input, an active candidate, and the destinations-exhausted failure tag, this
constructs `AtomicPathCommitAfterFailureRootDestinationsExhaustedPacked`.
The dispatcher runs the corresponding aligned fold after input exhaustion and
exact acceptance; it forwards the retained structure and selected suffix to
the existing package-native terminal leaf. The complete Regex chain
elaborates in the established range and the exact structural regression
passes. Next route the remaining aligned `Same` cases: unclassified local
failure continues to its rejected-prefix proof, while `FromChild`,
`PastEscaped`, and `PastRejected` recurse through their existing
package-preserving projections.

The first direct `FromChild`/`PastEscaped` routing attempt identified one more
carrier boundary that must be strengthened before recursion is relevantly
typeable. The aligned `Same` package currently retains the two exact current
lists only through `LookaroundAdmittedCursorInnerEquivalentAuthority`; its
equality field is erased. That is sufficient for the three terminal folds,
because they use the equality only while eliminating to `Empty`, but it cannot
reindex a selected trace package to construct a new runtime recursive carrier.
E093 therefore rejects passing the projected commit child and selected suffix
to `AtomicPathRecursiveCommitSelectedChildExistentialPacked`; using the erased
equality to force the construction would violate E104. The failed formulation
has been removed. Next construct a relevant recursive-continuation package
inside `atomic_path_recursive_commit_selected_child_same_aligned_package`,
while both opaque commit and selected payloads are still present. Its
`FromChild` and `PastEscaped` constructors must contain the already-correlated
next `AtomicPathRecursiveCommitSelectedExistentialPackage`; local
`AfterFailure` and `PastRejected` constructors must retain the aligned package
for contradiction. The later dispatcher may select among those relevant
constructors, but must never manufacture a recursive package from the erased
inner equality.

The aligned carrier now retains that construction source explicitly. Both
`AtomicPathRecursiveCommitSelectedChildSameAlignedActivePacked` and its
accepted dual carry the original
`AtomicPathRecursiveCommitSelectedChildSameExistentialPackage` alongside the
classified commit, selected skipped structure, selected suffix, and erased
inner equality. This keeps both opaque payloads and their common outer
candidate available after terminal elimination; no index is reconstructed and
the existing three terminal folds remain unchanged apart from forwarding the
source. The complete Regex chain elaborates in the established range and the
exact structural regression passes. The next continuation carrier must open
this retained source and keep the projected left and right recursive children
heterogeneous until an `Empty`-returning proof consumer can use their erased
canonical alignment. It must not require an already-shared inner candidate as
an input to relevant construction.

The aligned `Same` boundary now has an explicit relevant structural
continuation carrier. `AtomicPathRecursiveCommitSelectedChildSameContinuationPackage`
classifies active aligned packages into `AfterFailure`, `FromChild`,
`PastEscaped`, or `PastRejected`, and preserves accepted-state packages in a
separate impossible branch. Every constructor retains the complete aligned
package, including the original heterogeneous source payloads; classification
therefore makes no use of erased cursor equality and manufactures no reindexed
trace data. The common dispatcher now exposes only this continuation carrier
after running all three terminal folds, preventing later consumers from
bypassing relevant structural classification. The complete Regex chain
elaborates and the exact structural regression passes. Next implement
branch-specific `Empty` consumers for `FromChild` and `PastEscaped` that reopen
the retained source, recurse over its left and right payloads heterogeneously,
and use erased canonical alignment only at the final contradiction boundary.

Those two propagated branches now retain their projected left child before
the proof consumer opens any cursor equality.
`AtomicPathRecursiveCommitSelectedChildSameProjectedPackage` existentially
hides the projected child's candidate, context, scope, history, and cursor
while keeping its relevant commit authority beside the intact aligned package.
The `FromChild` and `PastEscaped` continuation constructors carry this stronger
package; projection occurs only after matching the corresponding relevant
commit-structure constructor, which also exposes the required non-empty input
index. The unused hidden `escaped_depth` parameter was removed from the
`PastEscaped` child projection because it occurred in neither the projection's
input nor result and prevented principled inference. No selected trace is
reindexed, and erased inner equality still does not select runtime control.
The complete Regex chain elaborates and the focused structural regression
passes. Next open the projected package in fixed `Empty`-returning consumers,
retain the selected side independently from the aligned source, and perform
the recursive canonical comparison without first constructing a shared-index
runtime carrier.

The selected side now survives that boundary in the same opaque form.
`AtomicSelectedPathTraceExistentialRuntimeEnvelope` hides the selected suffix's
input, state, contexts, cursor, result, routine, and exact path indices while
retaining the runtime envelope built from its validated right cursor shape and
exact suffix package. Both active and accepted aligned-`Same` constructors
carry this envelope beside the selected suffix and the original source. The
right shape is taken directly from the source comparison that is already
indexed to the selected payload; it is not recovered by reopening the
dependent trace. Consequently the propagated continuation now has an existing
left child projection and an existing right selected-suffix envelope before
any erased inner-cursor equality is consumed. The complete Regex chain
elaborates and the focused structural regression passes. Next define the
fixed `Empty` transport that accepts these two opaque authorities, refines
their hidden current lists only inside proof elimination, and enters recursive
dispatch without returning a reindexed runtime value.

That fixed transport is now implemented as
`atomic_path_recursive_commit_selected_child_same_projected_dispatch`. It
accepts only `Empty`-returning recursive callbacks. In the already-relevant
`FromChild` or `PastEscaped` branch it reopens the exact structure, consumes
the aligned inner-cursor equality, and forwards the existing projected child
commit plus selected suffix into the common recursive dispatcher. The
correlated recursive package exists only as an argument to this
`Empty`-returning call; it cannot escape as relevant state. Structurally
mismatched or accepted packages are delegated to an explicit impossible-case
callback rather than silently assumed uninhabited. This formulation passes
E104 because erased refinement selects no runtime result or continuation—the
four recursive continuations were fixed before the equality was opened. The
complete Regex chain elaborates and the focused structural regression passes.
Next define the common recursive `Empty` consumer supplied to these callbacks:
terminal and local-blocking branches close immediately, while propagated
branches invoke this transport again on their structurally smaller child or
sibling commit.

The relevant continuation dispatcher now enforces that recursive route.
`atomic_path_recursive_commit_selected_child_same_continuation_dispatch`
passes `FromChild` and `PastEscaped` exclusively to the fixed projected
transport with the caller's already-fixed four recursive callbacks. Local
`AfterFailure` and `PastRejected` packages remain distinct exact callbacks,
and the accepted/malformed case remains an explicit impossible obligation.
There is no generic aligned fallback and no second child-pair construction
path. The complete Regex chain elaborates and the focused structural
regression passes. Next supply the concrete common induction callbacks:
connect `AfterFailure` and `PastRejected` to their local contradictions,
connect strict right branches to the existing one-constructor right folds,
and make the recursive callbacks invoke the same theorem on the smaller
commit structure.

Local `AfterFailure` is now narrowed before its erased proof payload is
opened. `atomic_path_recursive_commit_selected_child_same_after_failure_dispatch`
matches the relevant selected skipped-prefix structure and exposes four fixed
`Empty` obligations: empty, escaped-one, escaped-cons, or rejected-cons. A
misclassified commit or accepted aligned package is routed to an explicit
invalid callback. This avoids forcing whole-cursor transport into the broad
aligned carrier prematurely and gives each final contradiction exactly one
selected-prefix constructor. The complete Regex chain elaborates and the
focused structural regression passes. Next close the rejected-cons branch by
retaining its canonical whole alignment at the local construction boundary;
then treat empty and escaped prefixes with their corresponding child or
propagated commit recursion rather than a broad speculative match.

Aligned `PastRejected` now has the same relevant four-way narrowing.
`atomic_path_recursive_commit_selected_child_same_past_rejected_dispatch`
separates empty, escaped-one, escaped-cons, and rejected-cons selected prefixes
while retaining the exact `PastRejected` commit and its recursive tail. Wrong
commit classifications and accepted aligned packages remain explicit invalid
obligations. Thus both remaining local `Same` families reach their proof
callbacks with one fixed selected-prefix constructor and without inspecting
erased failure kinds or causes. The complete Regex chain elaborates and the
focused structural regression passes. Next build the constructor-correlated
local packages needed by the rejected-cons callbacks, then reuse the existing
tail projections for the escaped and recursive sibling callbacks.

The aligned local branches now publish a constructor-correlated skipped-tail
carrier before recursive elimination. The carrier retains the classified
commit, the current relevant skipped-prefix structure, the exact selected
suffix, and the erased equality between the commit and selected final cursors.
It also retains a canonical empty structure constructed while all dependent
indices are still available; this avoids attempting to reconstruct
polymorphic empty evidence after those indices have been existentially hidden.
`atomic_path_recursive_commit_selected_child_same_skipped_tail_fold` then
peels one relevant layer at a time: `EscapedOne` selects that stored empty
tail, while escaped and rejected cons constructors forward their own stored
tail structures. The commit, suffix, and cursor authority are never rebuilt,
and erased evidence does not select a runtime continuation. The complete Regex
chain elaborates and the focused structural regression passes. Next recurse
this fold to its empty terminal, close that exact terminal against the selected
trace, and wire the resulting contradiction into the strict-right recursive
callbacks for `AfterFailure` and `PastRejected`.

The skipped-tail carrier now has a total structural descent to that canonical
empty terminal. `atomic_path_recursive_commit_selected_child_same_skipped_tail_empty_fold`
closes an already-empty structure directly, maps the single escaped head to
the empty structure retained by the carrier, and recursively consumes the
stored tail of either cons constructor. Cure's totality checker accepts both
recursive calls as descent through `tail_structure`; the existential wrapper
does not obscure the decreasing relevant argument. The fixed commit, exact
selected suffix, and erased final-cursor equality survive unchanged to the
empty callback. The complete Regex chain elaborates and the focused structural
regression passes. Next define the empty callback's exact contradiction against
the selected trace, then install it in the `AfterFailure` and `PastRejected`
strict-right recursive routes.

The empty callback now receives an exact terminal authority rather than the
generic traversal carrier. `AtomicPathRecursiveCommitSelectedChildSameSkippedEmptyPackage`
fixes the selected-prefix index to `AtomicPathSkippedPrefixEmptyKind` while
retaining the classified commit, selected suffix, and erased final-cursor
equality. Both the already-empty branch and the terminal escaped-one branch of
the structural descent construct this authority; recursive cons branches
cannot reach the callback without first exposing their stored tails. This
prevents later consumers from rematching or assuming a hidden prefix kind and
makes the next recursive projection boundary explicit in its type. The
complete Regex chain elaborates and the focused structural regression passes.
Next split this exact terminal by its relevant commit classification: project
the nonterminal `AfterFailure` child against the selected child suffix, and
project the `PastRejected` sibling tail into the common recursive dispatcher.

The exact empty authority is now narrowed by its retained relevant commit
classification. `atomic_path_recursive_commit_selected_child_same_skipped_empty_dispatch`
routes `AfterFailure` and `PastRejected` to distinct fixed callbacks and sends
the already-handled propagated forms to an explicit invalid obligation. It
does not open the erased failure, commit cause, or final-cursor equality.
Consequently the next two consumers can project their exact recursive child or
sibling packages without a generic commit-kind recovery path. The complete
Regex chain elaborates and the focused structural regression passes. Next
implement those two projection consumers and feed their results back through
the existing common recursive dispatcher.

The skipped-tail and exact-empty carriers now retain the selected suffix's
existing `AtomicSelectedPathTraceExistentialRuntimeEnvelope`. This envelope
was originally built from the validated selected child cursor shape at the
aligned construction boundary; dropping it would force the `AfterFailure`
consumer to reconstruct relevant child-shape data after opening erased parent
cursor equality. Both structural folds now forward the envelope unchanged,
alongside the exact selected suffix package. The complete Regex chain
elaborates and the focused structural regression passes. Next pair the
`AfterFailure` child's retained cursor package with this envelope, classify
their relevant shapes, and consume each fixed proof branch without returning
transported runtime data.

The traversal and exact-empty carriers also now retain the original
`AtomicPathRecursiveCommitSelectedChildSameExistentialPackage`. That source is
the canonical dependent authority tying the commit payload, selected payload,
their validated cursor shapes, and the `Same` comparison in one constructor.
The selected runtime envelope remains available as an execution convenience,
but later proofs no longer need to assume that independently existential
fields originated from the same child pair. Both skipped-prefix folds forward
the source unchanged. The complete Regex chain elaborates and the focused
structural regression passes. Next open this source only inside the fixed
`AfterFailure` `Empty` consumer, select the already-correlated child payloads,
and dispatch their relevant shape comparison.

The source-native local branch now narrows the child failure kind without
opening erased proof data.
`atomic_path_recursive_commit_selected_child_same_after_failure_empty_kind_dispatch`
opens the original correlated Same source, selects its exact relevant
`AfterFailure` child package, and dispatches on the stored
`AtomicPathFailureKindAuthority`. Input exhaustion, exact acceptance,
destination exhaustion, and recursive destination rejection each receive a
fixed `Empty` callback; malformed propagated commit classifications remain an
explicit invalid obligation. The erased refutation and no-evidence witness are
not inspected. The complete Regex chain elaborates and the focused structural
regression passes. Next connect the first three callbacks to their already
proved terminal/impossible leaves and route destination rejection into the
canonical child-refutation cursor induction.

Local child terminal classification is now published once as
`AtomicPathRecursiveCommitSelectedChildSameAfterFailureTerminalPackage`.
`atomic_path_recursive_commit_selected_child_same_after_failure_terminal_package`
opens the exact relevant `AfterFailure` child package and projects its stored
terminal classifier into five runtime constructors: input exhausted, exact
accepted, root destinations exhausted, unclassified, or malformed. No erased
refutation is inspected. This consolidates the authority previously reopened
independently by three terminal folds and gives the recursive path a dedicated
`TerminalUnclassified` constructor. The complete Regex chain elaborates and
the focused structural regression passes. Next dispatch this package at the
common Same boundary: close the three classified terminals with their existing
package-native leaves, reject malformed input, and allow only unclassified to
enter skipped-prefix and child-failure recursion.

`atomic_path_recursive_commit_selected_child_same_after_failure_terminal_dispatch`
now exposes the consolidated classification through five fixed callbacks. It
forwards the unchanged aligned authority to each legitimate branch and sends
the malformed constructor to a nullary invalid callback. This dispatcher adds
no proof inspection or dependent transport; it is the relevant control
boundary that will replace the three nested terminal reclassification folds.
The complete Regex chain elaborates and the focused structural regression
passes. Next install this dispatcher in the common recursive Same path, reuse
the existing package-native terminal contradictions for its first three
callbacks, and send only `TerminalUnclassified` into skipped-tail descent.

The common recursive `Same` path now performs that consolidated dispatch.
Input exhaustion, exact acceptance, and root-destination exhaustion go
directly to their existing package-native contradiction folds; malformed
classification goes to the caller's explicit invalid obligation. Only the
relevant `TerminalUnclassified` constructor can construct an
`AtomicPathRecursiveCommitSelectedChildSameContinuationPackage` and enter
skipped-prefix or recursive child processing. The two projected recursive
call sites also thread the same invalid callback, so no structural mismatch is
silently converted into a recursive continuation. The complete Regex module
chain elaborates, the focused regression passes, and the full 27-test
structural refutation gate passes. Next consume the unclassified local
`AfterFailure` branch through skipped-tail descent and route its destination-
rejection child into the canonical recursive cursor induction.

The unclassified local `AfterFailure` branch now has one fixed structural
consumer. Child-kind callbacks retain the exact
`AtomicPathRecursiveCommitSelectedChildSameSkippedEmptyPackage` instead of
discarding it, so the selected suffix, runtime envelope, aligned cursor
authority, and original correlated source remain available after relevant
classification. The new
`atomic_path_recursive_commit_selected_child_same_after_failure_unclassified_fold`
descends the skipped-prefix spine to its canonical empty tail, rejects the
three terminal child kinds that the preceding classifier already excluded,
and exposes only destination rejection to its recursive callback. Structural
or classification mismatches remain explicit invalid obligations. The
complete Regex module chain elaborates, the focused regression passes, and the
full 27-test structural refutation gate passes. Next project an exact
destination-rejection child carrier from that retained package and feed its
head/tail cursor decision into the existing destination-rejection induction.

The cursor-package boundary now has the missing proof-facing inverse,
`lookaround_admitted_cursor_suffix_package_evidence`. It reconstructs the
erased indexed `Here`/`Drop` suffix from the relevant runtime package by a
structural fold; heads and equality witnesses remain erased. This is required
to pass a selected cursor into the existing canonical child-rejection theorem
without rebuilding or guessing it. A direct attempt to feed the retained
outer selected payload into
`atomic_path_active_child_rejection_canonical_trace_dispatch` was rejected:
it spent more than five CPU minutes normalizing `Std.Regex.Runtime`, compared
with the established roughly one-minute module check, because the
`AfterFailure` child refutation is one transition below that outer payload.
The attempt was removed rather than accepted as a speculative compatibility
path. The complete Regex chain and full 27-test structural gate pass with the
inverse bridge. Next publish the one-level selected-transition projection
beside the exact destination-rejection child, then call the canonical theorem
with already-aligned indices instead of asking unification to discover that
projection.

The one-level carrier must obey the following construction contract. Do not
reuse `AtomicPathActiveChildSelectionPackage` as a relevant carrier: every
field of that package is erased and its existing consumer is intentionally
only a local refinement barrier. Do not return the selected-child projection
as an independent existential either; that would permit pairing it with a
different `AfterFailure` child having extensionally similar indices. Instead:

1. enter through the destination-rejected callback of
   `atomic_path_recursive_commit_selected_child_same_after_failure_unclassified_fold`;
2. open the retained `AtomicPathRecursiveCommitSelectedChildSameExistentialPackage`
   and its selected suffix package in the same fixed-`Empty` eliminator;
3. match the relevant `AtomicPathFailureDestinationRejectedAuthority` before
   opening the erased child refutation;
4. match exactly one `AtomicSelectedPathTraceActivePacked` transition from the
   selected suffix, retaining its child origin, cursor package, skipped-prefix
   structure, and recursive suffix package together;
5. share the child input, state, history, capture context, policy, scope,
   prefix mode, reversed prefix, and canonical-origin indices between that
   transition and the exact `AtomicPathCommitAfterFailureChildPackage` in one
   constructor or non-escaping eliminator;
6. reconstruct the selected cursor witness only with
   `lookaround_admitted_cursor_suffix_package_evidence`;
7. pass the already-correlated failure origin/cursor and selected origin/cursor
   to `atomic_path_active_child_rejection_canonical_trace_dispatch` with fixed
   head, later-sibling, and reverse `Empty` callbacks; and
8. never ask conversion to infer the intervening transition, never recover a
   runtime branch from erased refutation data, and never retain two unrelated
   existential packages beside one another.

The selected `Accepted` transition is a separate impossible/local terminal
case at this active destination-rejection boundary and must go to the explicit
invalid obligation unless its exact contradiction is established before the
carrier is constructed. This contract is the red-test target for the next
implementation slice.

The first implementation probe refined all of those construction-site indices
and then bisected the remaining elaboration cost. With the final canonical
theorem call replaced by a fixed `Empty` result, the complete Regex chain
returned to its normal elaboration window. Restoring only
`atomic_path_active_child_rejection_canonical_trace_dispatch` again left
`Std.Regex.Runtime` above four CPU minutes. Refining the deeper child capture-
context and scope authorities (rather than the parent authorities) was
necessary but did not remove that cost. The remaining mismatch is the API:
the existing dispatcher accepts nullary branch callbacks and therefore assumes
the branch proofs were constructed before entry, while this boundary first
reveals the exact child refutation and selected child trace inside its
non-escaping eliminator.

Implement a package-native sibling of the canonical dispatcher before wiring
this branch. Its `Here`, later-sibling, and reverse constructors/callbacks must
retain one correlated authority containing the exact destination-rejection
child package, the exact one-transition selected child package, their shared
origin/cursor indices, and the already-consumed parent `Same` authority. Build
that authority only while the relevant destination-rejection and selected-
active constructors are open; consume it only in an `Empty` result. The
package-native dispatcher may reuse
`atomic_path_active_child_alignment_from_canonical`, but must not call the
nullary dispatcher and must not precompute branch proofs outside the carrier.
Add a red construction-site regression requiring the three package-bearing
branches before retrying the final recursive proof connection.

The evidence-preserving canonical alignment layer is now implemented.
`AtomicPathActiveChildAlignmentAuthority` has distinct `Here`, later-sibling,
and reverse constructors that retain their exact erased suffix evidence while
remaining indexed by the failed and selected current spines.
`atomic_path_active_child_alignment_authority_from_canonical` aligns the two
independently certified origins and returns this authority instead of
requiring nullary precomputed branch proofs. E104 established the correct
relevance boundary: the non-empty failure authority is relevant, while its
stored equality and the canonical-origin equality are consumed locally and
replaced by canonical reflexive witnesses before constructing runtime-visible
authority. The complete Regex chain elaborates, the focused regression
passes, and the full 27-test structural gate passes. Next define the correlated
destination-rejection/selected-transition carrier whose three constructors
embed this alignment authority alongside the exact child and selected
packages; then its dispatcher can give each recursive callback both the branch
proof and the construction-site data it needs.

That correlated carrier is now implemented as
`AtomicPathActiveChildAlignmentPackage`. Its `Here`, later-sibling, and reverse
alternatives each contain a distinct one-constructor branch package carrying
the same relevant destination-rejection and selected-transition payloads
together with that branch's exact erased suffix evidence. The generic
`atomic_path_active_child_alignment_package` constructor consumes the canonical
alignment authority once, and
`atomic_path_active_child_alignment_package_dispatch` exposes the correctly
typed branch package to a non-escaping callback. This mirrors the established
selected-location package discipline without duplicating the eventual large
Regex-specific payload signatures. The complete Regex chain elaborates, the
focused red regression is green, and the full 27-test structural gate passes.
Next instantiate the two generic payload parameters with the exact retained
destination-rejection child and one-transition selected-child packages while
their constructors are open, then consume each branch in `Empty` to connect the
recursive rejection theorem. Do not reconstruct either payload from an
independent existential package after dispatch.

Construction-site instantiation exposed a stricter relevance boundary than the
generic list-indexed carrier suggested. The exact canonical-origin and suffix
equalities are erased, so neither an `Active` origin token reconstructed from
those proofs nor the nested suffix package revealed under the selected trace
may escape as a relevant payload; both forms correctly produce E104. Runtime
branch selection is instead determined by the already-relevant cursor-package
shapes. `AtomicPathActiveChildShapeAlignmentAuthority` now classifies equal
`Here`, later/deeper, and reverse shapes, and its three one-constructor branch
packages carry the original retained `SkippedEmpty` package beside the original
exact one-transition selected suffix package. The inner cursor equality and
nested suffix therefore remain correlated inside their owning packages until a
fixed-`Empty` branch opens them.

The three shape alternatives now enter typed package folds rather than
discard-only result helpers. Each fold opens its one-constructor branch and
passes the original failure package, original selected package, and (for the
directional cases) exact shape authority to its callback. This is the final
relevant-data boundary needed by the recursive proof: subsequent work belongs
inside those fixed-`Empty` callbacks and must not add another existential
carrier. The complete Regex chain and all 27 structural regressions remain
green after this change.

The common `Same` continuation dispatcher can no longer bypass this boundary.
Its former raw `AfterFailure(aligned)` callback has been replaced by three
fixed `Here`, later-sibling, and reverse `Empty` callbacks, and the dispatcher
itself routes `AfterFailure` through skipped-tail descent, child-kind
classification, destination-rejection construction, and the typed shape
package folds. Thus the eventual common induction supplies only the three
mathematical branch obligations; it cannot accidentally reopen an earlier,
less-refined carrier. The complete Regex chain and all 27 structural
regressions pass. Next define the common induction over the remaining
correlated, propagated-Same, strict-left, strict-right, and `PastRejected`
callbacks, using these three obligations as its local destination-rejection
case.

The `PastRejected` side of the same dispatcher is now equally constrained.
Instead of returning a broad aligned package to one callback, it invokes the
existing relevant skipped-prefix dispatcher and exposes separate empty,
escaped-one, escaped-cons, and rejected-cons obligations. Both local `Same`
families therefore arrive at the future common induction already split by
their runtime constructors; neither can reclassify erased causes or cursor
evidence. The complete Regex chain elaborates and the 27-test structural gate
passes (the known near-60-second fixture requires the gate's 120-second test
timeout). Next connect each of these four `PastRejected` obligations to its
tail projection or local contradiction while defining the common induction.

That four-way callback surface was still broader than necessary. All four
selected-prefix constructors share the existing structurally recursive
skipped-tail descent, so
`atomic_path_recursive_commit_selected_child_same_past_rejected_empty_fold`
now consumes the entire relevant prefix before any sibling projection. It
then uses the exact-empty commit classifier to admit only `PastRejected` and
passes one `AtomicPathRecursiveCommitSelectedChildSameSkippedEmptyPackage` to
the common induction. This preserves the original correlated source, selected
trace envelope, inner-cursor authority, and classified commit while removing
four duplicate recursive entry points. The complete Regex chain and the full
27-test structural gate pass. Next open this exact package in a fixed-`Empty`
consumer, project the retained `PastRejected` tail structure/cursor, and pair
it with the selected authority from the original correlated source before
recursing.

The `PastRejected` sibling direction is now proved before that recursive
boundary. `atomic_path_cursor_shapes_advance_left_after` establishes by
structural induction that advancing the left member of a `Same` shape pair by
one cursor step is strictly `LeftAfter` the right member. The exact-empty
consumer opens the relevant `PastRejected` classifier and the original
correlated source, applies that theorem to its retained `Same` authority, and
publishes only
`AtomicPathRecursiveCommitSelectedChildSamePastRejectedReversePackage`.
Consequently the common induction cannot speculate about Same or RightAfter
for this tail, and the complete exact-empty authority remains available for
the reverse contradiction. The complete Regex chain and all 27 structural
tests pass. Next consume this reverse package at the common induction boundary
alongside the already-refined `AfterFailure` Here/later/reverse cases, then
connect projected `FromChild` and `PastEscaped` packages recursively.

The three local `AfterFailure` directions now have the same proof-bearing
interface as `PastRejected`. Separate Here, later-sibling, and reverse
one-constructor packages retain the exact destination-rejected skipped-empty
authority selected by the runtime shape comparison. The typed shape folds
construct those packages from their original failure payload; the common
continuation dispatcher no longer accepts nullary obligations that have lost
the child refutation, selected suffix, aligned source, or cursor packages.
This is the final local carrier boundary: the common induction can open each
package in `Empty` and recurse or contradict using its exact data, without
rematching a broad aligned existential. The complete Regex chain and all 27
structural tests pass. Next implement the package consumers, beginning with
Here (recursive child refutation), then later sibling and reverse, and combine
them with the proved `PastRejected` reverse consumer.

`atomic_path_recursive_commit_selected_child_same_destination_rejected_alignment_fold`
constructs that shape carrier only after exposing the exact local
`DestinationRejected` child and selected `Active` transition. The previously
unclassified `AfterFailure` fold now routes its destination-rejected callback
through this construction site and exposes explicit `Here`, later-sibling, and
reverse obligations. The complete Runtime -> Proof -> Regex -> Language chain
elaborates, the focused construction-site regression passes, and the full
27-test structural gate passes. Next implement the three fixed-`Empty` branch
eliminators: each must reopen the original two packages locally, consume the
erased canonical equalities without exporting them, and invoke the recursive
rejection theorem with the branch-specific alignment evidence.

The first fixed-`Empty` consumer probe exposed a stricter prerequisite at this
boundary. The current Here/later/reverse wrappers retain only the exact
`AtomicPathRecursiveCommitSelectedChildSameSkippedEmptyPackage`; their
construction callbacks discard the corresponding
`AtomicPathActiveChildShapeHerePackage`, `...TherePackage`, or
`...ReversePackage`. Reopening the empty package recovers the child origin,
suffix, refutation, and selected trace, but all of those certificates are
erased. Passing them to the older runtime
`atomic_path_active_child_rejection_canonical_trace_dispatch` is correctly
rejected as E104. A proof-only replacement that inspects those erased suffixes
to choose among Here/later/reverse callbacks is also correctly E104: erased
evidence may refine a fixed contradiction, but it may not select relevant
control flow. Therefore the directional wrapper tag is runtime control, not by
itself sufficient logical evidence.

Do not solve this by making canonical equalities relevant, by making the
machine index runtime-visible, or by trusting the wrapper tag. Before writing
the consumers, replace these three wrappers with first-order indexed carriers
constructed directly at
`atomic_path_recursive_commit_selected_child_same_destination_rejected_alignment_fold`.
Each carrier must retain, in one constructor-correlated payload:

1. the exact skipped-empty package and selected active suffix;
2. the failure and selected child cursor packages checked against their
   relevant runtime shapes;
3. the Here, later-sibling, or reverse shape authority selected at that same
   construction site;
4. the erased child-origin equivalence, canonical origins, cursor suffixes,
   destination-rejected refutation, selected child trace, and active scope
   alignment needed by the recursive theorem; and
5. no generic `Type` existential that a callback lambda must infer.

The last restriction is operational as well as stylistic. A prototype that
stored `AtomicPathActiveChildShape*Package(failure_package,
selected_package, ...)` behind an existential `selected_package: Type` hit E093
in both higher-order lambda inference and a named constructor dispatcher; an
explicit-erased version then failed dependent-index refinement. Use a dedicated
constructor signature whose ordinary and erased fields name the concrete
`AtomicSelectedPathTracePackage` and child indices, following the existing
`AtomicSelectedPathTraceActivePacked` and
`AtomicPathCommitAfterFailureChildPacked` pattern. The resulting consumer must
match one relevant directional constructor first, use its shaped cursor
packages to fix the only legal suffix constructors, and only then eliminate
the erased canonical equalities while returning `Empty`. Add the red structural
test against this first-order carrier before implementation; retain the E104
negative lesson in the assertion by forbidding an erased-proof dispatcher that
chooses callbacks.

The first direct implementation probe also rules out one monolithic carrier.
A single Here constructor was given the complete shared child context, both
canonical origins and suffixes, both shaped Here cursor packages, the
destination-rejected refutation, raw selected path, selected trace package,
and exact empty package. Its indices were sound, but constructing it kept the
normalizer CPU-bound beyond the established Runtime-module range; explicitly
annotating the result and generalizing the child input away from `Cons` did not
change that behavior. Do not reproduce this constructor.

Stage the first-order carrier instead. First publish a small canonical child
pair indexed only by the common input/state context, failure and selected
origins/currents, and the two shaped cursor packages. Then publish the
refutation/selected-trace pair in a second package indexed by that canonical
pair. Finally let the directional Here/later/reverse carrier contain those two
already-checked packages plus the exact empty continuation. Each stage must
elaborate within the recorded Runtime-module baseline before the next is
introduced. This mirrors the existing successful split between
`AtomicPathCommitAfterFailureChildPackage`, cursor-shaped packages, and
`AtomicSelectedPathTracePackage`, rather than asking normalization to solve all
three existential boundaries in one constructor application.

A downstream two-stage prototype narrows the required publication point
further. The small canonical Here pair by itself type-checks through a named
factory, but attaching it to the already-built skipped-empty package requires
reopening the outer erased inner-equivalence first. That downstream match again
drives Runtime elaboration outside the established range. Without the equality
the factory call instead reports the expected dependent-index mismatch, because
the failed candidate's state/capture context has not yet been identified with
the selected active candidate. Therefore staging the data types alone is not
enough if all stages are reconstructed at the final existential fold.

The evaluator-flow audit corrects one part of that prescription: no evaluator
branch constructs both `AtomicPathCommitAfterFailureChildPacked` and a
successful `AtomicSelectedPathTraceActivePacked`. A blocking commit and a
successful sibling selection are mutually exclusive results. Their first
common boundary exists only in the correspondence theorem, which is too late
to reconstruct their child identity safely.

The attainable upstream authority is instead the failed-child/selected-trace
pair. When `atomic_lookaround_routine_tail_after_failure` receives an
`AtomicPathMembersYes` from the remaining siblings, it still has the exact
failed-child cursor package and the exact selected trace package. That branch
now constructs `AtomicPathRejectedSelectedTracePairPackage` and retains it in
`AtomicPathSkippedPrefixStructureRejectedConsPacked`. The package remains
inside already-erased successful-search evidence, so it adds no emitted runtime
proof object. Direct Runtime, Proof, facade, and Language compilation passes,
and the construction-site regression is green.

Next align the independently produced commit child with the retained rejected
child, then compare that already-aligned child with the selected trace carried
by the same package. Thread the resulting staged direction carrier through the
Here/later/reverse folds. The final destination-rejection fold must consume
those published authorities; it must not recompute a three-way pair after
matching `inner_equivalence`, re-scan a cursor, or assume a nonexistent common
evaluator outcome.

The first threading slice is now present. The selected active trace's exact
`child_skipped_structure` is traversed relevantly, distinguishing a spine with
no ordinary rejection from one carrying an
`AtomicPathRejectedSelectedTracePairPackage`; escaped commits are not
misclassified as rejected children. The result is hidden behind the indexed
`AtomicPathRejectedSelectedTracePairAvailability` authority and retained by
each AfterFailure Here/There/Reverse package. All dependent indices remain
inside the existential pair, while the relevant availability constructor can
guide the next proof fold without inspecting erased evidence. The next slice
must consume this authority: Here should discharge the structurally empty
selected-child prefix, while later/reverse recurse through the retained
rejected child or the separately classified escaped-commit path.

The child direction is now tied to the skipped-prefix structure itself rather
than to a separately recomputed cursor shape. An exact recursive helper returns
`Sigma(shape, payload)` while all front/current/kind indices remain visible;
only the completed payload is existentialized. Its four payload constructors
mirror Empty, EscapedOne, EscapedCons, and RejectedCons and fix the corresponding
Here/Drop shape in their result. The direction split retains that shape-indexed
payload and the There/Reverse authority. Consequently the Here consumer has
only the Empty payload constructor and publishes
`AtomicPathRecursiveCommitSelectedChildSameAfterFailureHereEmptyPackage`
without inspecting an erased equality or accepting an invalid callback. Direct
Runtime/Proof/facade/Language compilation and the construction-site regression
pass. The next leaf must open this fixed Empty package together with the local
destination refutation and selected trace, then invoke the recursive child
refutation contradiction; There/Reverse still require their retained pair and
tail directions.

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

# `Std.Versioned`: gapless evolution with support windows

**Date:** 2026-08-02  
**Status:** Proposed design  
**Owner:** Standard library  
**Consumers:** Protocols, serialization formats, schemas, public APIs, configuration, and persistent state

## 1. Summary

`Std.Versioned` is a general standard-library abstraction for evolving an
artifact without accidentally skipping or forgetting its history.

Release numbers are not user-provided values. They are `Nat` indices computed
by the constructors of an opaque lineage:

- the first release has index `S(Z)`;
- evolving release `n` produces release `S(n)`; and
- there is no operation that accepts an arbitrary `Nat` and manufactures a
  release at that index.

Every published release also carries a decision for every historical release.
The most recent releases fall inside a statically enforced support window. The
smallest possible window is two, so from V2 onward the current and immediately
previous versions must be supported simultaneously. A project may select a
larger window. Historical versions outside the window must still be explicitly
marked supported or unsupported.

The mechanism is deliberately domain-neutral. `Std.Versioned` defines lineage,
membership, decision alignment, and support-window proofs. A consumer defines
what evidence counts as support. For an OTP protocol that evidence might include
wire codecs, adapters, and a trace-refinement proof. For stored data it might be
a decoder and migration proof.

## 2. Motivation

Ordinary version declarations are unrelated values:

```cure
type Version = V1 | V2 | V3
```

Nothing prevents a program from deleting `V1`, constructing `V3` directly, or
claiming compatibility without retaining an implementation of the older
surface.

Semantic versions do not solve that problem. They are useful names, but their
ordering and compatibility meaning exist only by convention.

The desired guarantee is structural:

> Given the source presented to the compiler, every inhabitable release at
> version `n` contains an uninterrupted construction history from V1 through
> Vn, explicitly classifies every historical version, and supports every
> version inside its declared support window.

This prevents accidental gaps and accidental retirement. It does not attempt to
stop a user from deliberately rewriting the source, replacing the standard
library, or modifying the compiler.

## 3. Locked design decisions

1. The authoritative version is a one-based `Nat` index maintained by the
   library, not a user argument.
2. The lineage is opaque. Its constructors are available only through `first`
   and `evolve`.
3. User-facing names and semantic versions are optional labels. They do not
   determine ordering or identity.
4. Every release classifies every version in its history as `Supported` or
   `Unsupported`.
5. The support window includes the current release and has a minimum size of
   two.
6. At V1, the effective window contains only V1. At V2 and later, the complete
   minimum window must be inhabited.
7. `Unsupported` is forbidden inside the active support window.
8. Versions outside the window may remain supported or may carry explicit
   non-support evidence.
9. A support window may remain fixed or widen. It cannot silently shrink.
10. “Supported” is domain evidence, not a boolean and not merely the continued
    presence of an old type definition.
11. Artifact hashes, signed histories, registry enforcement, and protection
    against deliberate environment modification are out of scope.

## 4. Version indices

The internal numbering is one-based:

```text
V1 = S(Z)
V2 = S(S(Z))
V3 = S(S(S(Z)))
```

`Z` represents an empty lineage, not a publishable version.

The public API never accepts a version number:

```cure
fn first(
  window: SupportWindow(window_size),
  draft: Draft(family, artifact),
  native: decision(artifact, artifact, Supported)
) -> Release(family, artifact, decision, S(Z), window_size)

fn evolve(
  {n: Nat},
  {window_size: Nat},
  previous: Release(family, artifact, decision, n, window_size),
  draft: Draft(family, artifact),
  plan: EvolutionPlan(previous, draft)
) -> Release(family, artifact, decision, S(n), window_size)
```

These signatures are illustrative; the implementation may expose additional
history indices needed by the kernel. The important API fact is that `n` is
implicit and inferred from `previous`. There is no `version(number, draft)` or
`release_at(number, draft)` escape hatch.

A draft is deliberately unversioned. Only `first` and `evolve` seal it into a
lineage position. A user therefore cannot annotate a draft as V17 and use that
annotation to manufacture the required lineage evidence.

## 5. Optional labels

Labels are presentation metadata:

```cure
type VersionLabel =
  Named(String)
  | Semantic(Nat, Nat, Nat)
```

A release may have no label:

```cure
type ReleaseMetadata = ReleaseMetadata(Option(VersionLabel))
```

The following do not affect the structural version:

- naming V2 `"Aurora"`;
- attaching `Semantic(4, 0, 0)` to V2;
- changing or omitting a label; or
- using the same label in two independent protocol families.

Tooling should display both when available, for example `V3 (2.1.0)`, but all
proofs and lookups use the lineage index.

## 6. Protocol-family separation

The lineage carries a nominal `family` parameter:

```cure
opaque type Lineage(
  family: Type,
  artifact: Type,
  decision: (artifact, artifact, SupportStatus) -> Type
) indices (count: Nat)
```

Users define an uninhabited or otherwise nominal marker for each family. This
prevents two histories over the same artifact representation from being mixed
accidentally.

For example, two protocols may both use a `ProtocolSpec` representation while
remaining distinct lineages:

```cure
type AccountsProtocol
type InventoryProtocol
```

Creating two independent V1 lineages is valid. The guarantee is gaplessness
within a family, not global uniqueness of version numbers.

## 7. Support windows

The support-window witness is opaque:

```cure
opaque type SupportWindow indices (size: Nat)

fn minimum_window() -> SupportWindow(S(S(Z)))

fn extend_window(
  {size: Nat},
  window: SupportWindow(size)
) -> SupportWindow(S(size))
```

There is no constructor for `SupportWindow(Z)` or
`SupportWindow(S(Z))`. Passing an arbitrary `Nat` cannot create a window.

The window size counts the current release. When fewer releases exist than the
window requests, every existing release must be supported.

### Minimum window

| Current release | Required simultaneous support |
| --- | --- |
| V1 | V1 |
| V2 | V2 and V1 |
| V3 | V3 and V2 |
| V4 | V4 and V3 |

At V3 with the minimum window, V1 remains in the history and still requires an
explicit decision, but it may be unsupported.

### Extended window

For a three-version window:

| Current release | Required simultaneous support |
| --- | --- |
| V1 | V1 |
| V2 | V2 and V1 |
| V3 | V3, V2, and V1 |
| V4 | V4, V3, and V2 |

The initial window is selected when the family is created. `evolve` preserves
it. A separate `widen_window` operation may increase it after receiving fresh
support evidence for every version newly brought into the active window. No
operation decreases it.

Shrinking a published compatibility commitment is not ordinary evolution. A
future design may model it as an explicit policy break, but it must not be an
unremarkable argument to `evolve`.

## 8. Decisions and domain evidence

The standard library defines only the status:

```cure
type SupportStatus = Supported | Unsupported
```

The consumer supplies an indexed evidence family of the form:

```cure
(old: artifact, current: artifact, status: SupportStatus) -> Type
```

This lets the support claim mean something appropriate for the artifact.

An OTP consumer could define:

```cure
type ProtocolDecision indices (
  old: Protocol,
  current: Protocol,
  status: SupportStatus
)
  Supports :
    Decoder(old) ->
    Encoder(old) ->
    Adapter(old, current) ->
    PreservesProtocol(old, current) ->
    ProtocolDecision(old, current, Supported)

  DoesNotSupport :
    Reason ->
    RejectsDuringHandshake(old, current) ->
    ProtocolDecision(old, current, Unsupported)
```

A persistence consumer could instead require:

- an old-format decoder;
- a migration into the current schema;
- a proof that migrated values satisfy the current invariant; and
- an explicit recognition-and-rejection path for retired formats.

The standard library must not provide a universal `Supported` constructor. It
aligns and checks evidence supplied by the domain.

## 9. Complete historical classification

Every current release carries a decision table aligned with the complete
lineage. Its shape is an indexed list, not a map keyed by user-provided numbers.
Consequently:

- no historical entry can be omitted;
- no decision can target a version outside the lineage;
- no version can receive two contradictory statuses; and
- the table order is the lineage order.

Conceptually:

```cure
type Decisions indices (history: History(artifact), current: artifact)
  NoDecisions : Decisions(NoHistory, current)

  MoreDecisions :
    decision(old, current, status) ->
    Decisions(rest, current) ->
    Decisions(MoreHistory(old, rest), current)
```

The concrete implementation will also index the corresponding status list so
the support-window proof can inspect it without examining domain evidence.

An explicit `Unsupported` decision is required outside the window when support
has ended. Merely dropping the old decoder, adapter, module, or decision makes
the release fail to elaborate.

## 10. Window satisfaction

`RecentVersionsSupported` relates:

- the selected window size;
- the complete newest-first history;
- the aligned decision statuses; and
- the current release.

It requires `Supported` for the first `min(window, history_length)` entries.
There is no constructor that consumes `Unsupported` while the window still has
positions remaining.

The current version also requires native support evidence. Its presence in the
source is insufficient: a domain must provide the implementation evidence its
decision family demands.

The key negative case is therefore uninhabitable:

```cure
fn invalid_v2(
  v1: Release(family, artifact, decision, S(Z), S(S(Z))),
  v2: Draft(family, artifact),
  retired_v1: decision(v1_artifact, v2_artifact, Unsupported)
) -> Release(family, artifact, decision, S(S(Z)), S(S(Z))) =
  evolve(v1, v2, plan_with(retired_v1))
```

The history is valid, but the minimum-window proof cannot be constructed because
V1 is the immediately previous release.

At V3 under the same window, an explicit unsupported decision for V1 is valid
provided V3 and V2 have `Supported` evidence.

## 11. Observation and lookup

Callers may observe the compiler-maintained number:

```cure
fn version_number(
  {n: Nat},
  release: Release(family, artifact, decision, n, window)
) -> Nat = n
```

Historical lookup requires membership evidence or a bounded index such as
`Fin(n)`. A plain `Nat` lookup must return `Option`; it cannot manufacture a
proof that a requested release exists.

The library should expose:

- `latest`;
- `version_number`;
- `latest_label`;
- `history` as a safe fold or indexed view;
- `member` or `lookup`;
- `decision_for`; and
- `supports` for evidence-bearing queries.

It must not expose the underlying lineage constructor.

## 12. Evolution rules

Publishing V1 requires:

1. a window witness of size at least two;
2. an unversioned draft;
3. optional metadata; and
4. native `Supported` evidence for V1.

Publishing `S(n)` requires:

1. the complete release at `n`;
2. a new unversioned draft;
3. optional metadata;
4. native support evidence for the new release;
5. one domain decision for every member of the previous lineage; and
6. a proof that the current support window contains only `Supported` statuses.

The returned release embeds the previous lineage. The version index and history
length advance together.

## 13. Trust boundary

The guarantee is relative to the source and compiler environment the user chose
to build.

In scope:

- accidental skipped numbers;
- deleting an older version still needed to construct the lineage;
- omitting a historical support decision;
- retiring the immediately previous version;
- claiming a larger support window without the necessary evidence; and
- confusing a semantic-version label with structural lineage position.

Out of scope:

- deliberately rewriting the entire lineage from V1;
- modifying the standard library or compiler;
- replacing proof definitions with different source;
- cryptographic artifact identity;
- signed release histories;
- registry policy enforcement; and
- defending users from a deliberately hostile build environment.

No artifact hashing is required by this design.

## 14. Standard-library and consumer responsibilities

### `Std.Versioned`

The standard library owns:

- `SupportStatus`;
- `VersionLabel` and release metadata;
- opaque `SupportWindow` construction;
- opaque gapless lineage construction;
- aligned history membership;
- exhaustive decision tables;
- recent-window satisfaction;
- safe observation and lookup; and
- the generic gaplessness and window theorems.

### Consumer libraries

A consumer owns:

- the artifact representation;
- its nominal family marker;
- the indexed decision evidence;
- adapters, migrations, codecs, or implementations;
- the meaning of explicit non-support;
- runtime negotiation or dispatch; and
- domain-specific preservation theorems.

OTP must consume this abstraction rather than define a private version-lineage
system.

## 15. Required theorems

The initial implementation must prove in Cure:

1. **Non-zero releases:** no `Release(..., Z, ...)` is constructible.
2. **Gaplessness:** every release at `S(n)` contains a release at `n`.
3. **Exact length:** a release indexed by `n` contains exactly `n` entries.
4. **Latest membership:** the current artifact is a member of its lineage.
5. **Historical retention:** evolving preserves membership of every previous
   entry.
6. **Complete classification:** every member has exactly one current decision.
7. **Minimum window:** every `SupportWindow(w)` proves `2 ≤ w`.
8. **Recent support:** every member inside the effective window has status
   `Supported`.
9. **V2 overlap:** every V2 release supports both V2 and V1.
10. **No shrink:** window transitions preserve or increase the window size.

These are library theorems. Consumer-specific compatibility and migration
theorems remain parameters to the generic structure.

## 16. Diagnostics

Elaboration errors should explain the policy obligation, not merely report an
opaque index mismatch. Required diagnostic situations include:

- “V2 must continue to support V1 because the support window is 2.”
- “Version V1 has no support or explicit non-support decision.”
- “This support window has size 1; the minimum is 2.”
- “The requested window would shrink from 4 to 2.”
- “Semantic label 3.0.0 is metadata; the structural release is V2.”
- “Support for V1 lacks the domain evidence required by this family.”

The implementation should first express these failures through ordinary indexed
types. Dedicated diagnostics are justified only after the generic representation
is stable.

## 17. Testing requirements

### Positive tests

- Construct V1 with the minimum window.
- Construct V2 while supporting V1 and V2.
- Construct V3 with window two while explicitly retiring V1.
- Construct V3 with window three while supporting all three versions.
- Keep an older version supported outside the mandatory window.
- Widen an existing window after supplying newly required evidence.
- Retrieve every retained version with membership evidence.
- Show that labels do not affect structural numbering.
- Instantiate the abstraction for at least two unrelated domains.

### Negative tests

- Attempt to construct V2 without V1.
- Attempt to construct a release at a user-provided `Nat`.
- Attempt to use a size-zero or size-one window.
- Mark V1 unsupported at V2.
- Mark V2 unsupported at V3 under the minimum window.
- Mark V1 unsupported at V3 under a three-version window.
- Omit a decision for an older version.
- Reuse a decision from another family.
- Shrink a support window.
- Claim support without the consumer’s required evidence.

### Properties

- `version_number(first(...)) == 1`.
- `version_number(evolve(previous, ...)) == 1 + version_number(previous)`.
- Evolution preserves every prior membership proof.
- The number of decisions equals the history length.
- Widening never removes a previously required supported version.
- `RecentVersionsSupported` agrees with a reference `take(window, history)`
  implementation after erasure.

## 18. Implementation phases

### Phase 1: feasibility probe

- Confirm an opaque indexed lineage can hide its constructors while exporting
  eliminators.
- Confirm a multi-argument dependent evidence-family parameter elaborates:
  `(artifact, artifact, SupportStatus) -> Type`.
- Confirm indexed decision lists can retain existential statuses.
- Confirm the window relation normalizes on newest-first histories.

No compiler special case should be introduced for `Std.Versioned`.

### Phase 2: structural lineage

- Implement labels, drafts, entries, lineage, `first`, and `evolve`.
- Prove non-zero releases, exact length, latest membership, and historical
  retention.
- Add negative construction tests.

### Phase 3: decisions and minimum window

- Implement domain evidence parameters and exhaustive decision alignment.
- Implement opaque windows with minimum size two.
- Implement recent-window satisfaction.
- Prove the V2-overlap theorem.

### Phase 4: observation and widening

- Add lookup, folds, decision queries, and labels.
- Add widening with fresh evidence.
- Prove that widening cannot remove mandatory support.

### Phase 5: domain integrations

- Integrate the distributed-protocol work through an OTP-specific decision
  family.
- Add a second integration, preferably serialized-data migration, to prevent
  OTP assumptions from leaking into the generic API.
- Add executable documentation and generated stdlib API documentation.

## 19. Scope boundaries

### In scope

- One-based, gapless, compiler-derived release indices.
- Optional names and semantic-version labels.
- Complete historical decisions.
- Minimum two-version support overlap.
- User-selected larger support windows.
- Non-shrinking window policy.
- Generic domain evidence.
- Explicit non-support outside the active window.

### Out of scope

- Branching or merging lineages.
- Multiple simultaneously current heads.
- Semantic-version ordering rules.
- Automatically synthesizing migrations or adapters.
- Runtime version negotiation as a generic effect.
- Package-manager or registry compatibility policy.
- Content hashes, signatures, or tamper resistance.
- Protection against deliberately rewritten source histories.

Branching histories require a different algebra and must not weaken the linear
successor guarantee of this first design.

## 20. Acceptance criteria

The design is implemented when:

1. `Std.Versioned` exists without compiler-specific version-name handling.
2. No public API can construct a release from an arbitrary `Nat`.
3. No public API can construct a support window smaller than two.
4. V2 fails to elaborate unless both V2 and V1 have `Supported` evidence.
5. Larger windows enforce the corresponding number of recent versions.
6. Every historical version has exactly one supported-or-unsupported decision.
7. Window shrinking is impossible through the ordinary API.
8. The generic theorems in section 15 are machine-checked in Cure.
9. OTP and one non-OTP domain instantiate the same generic mechanism.
10. Focused, full-suite, documentation, and clean-rebuild tests pass.


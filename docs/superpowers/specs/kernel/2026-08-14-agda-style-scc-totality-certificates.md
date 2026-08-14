# Agda-Style SCC Totality Certificates

**Date:** 2026-08-14  
**Status:** implementation specification  
**Layer:** K/E boundary (`Cure.Core.Kernel`, `Cure.Core.Certificate`, and the totality driver)  
**Primary reference:** Agda's termination pipeline in `Agda.Termination.TermCheck`, `Agda.Termination.CallGraph`, `Agda.Termination.CallMatrix`, `Agda.Termination.SparseMatrix`, and `Agda.Utils.Favorites`  
**Secondary implementation reference:** Idris 2's `Core.Termination.SizeChange` and `Core.Termination.CallGraph`

## Outcome

Move recursive-component discovery, call-graph scheduling, and eventually
size-change closure construction out of Cure's trusted computing base (TCB).
The compiler proposes a totality certificate for an entire strongly connected
component (SCC). The kernel checks bounded, explicit evidence against trusted
per-definition call summaries and either certifies every member atomically or
certifies none of them.

This is not a change to Cure's termination criterion. Cure continues to accept
exactly the programs justified by its current Lee-Jones-Ben-Amram size-change
criterion. The first migration must preserve acceptance and rejection bit for
bit. The change is where work happens, what is cached, and what the kernel must
trust.

The end state is:

```text
checked Core bodies
       │
       │ trusted, local, one-pass extraction
       ▼
canonical direct-call summaries ───────────────┐
       │                                       │
       │ untrusted compiler                    │ trusted inputs
       ▼                                       │
SCC partition + size-change candidate          │
       │                                       │
       └──────────────► kernel verifier ◄──────┘
                              │
                              ▼
                  atomic SCC totality certificate
```

The kernel no longer discovers an SCC by repeatedly scanning bodies or by
running reachability from the declaration being certified. It verifies a
proposed partition using direct-edge completeness, topological ranks, and
strong-connectivity witnesses.

## Why this change

The current implementation places global graph analysis inside
`Cure.Core.Certificate.terminating?/3`:

1. `mutual_group/3` discovers recursive peers from Core bodies.
2. `mutual_group_total?/4` walks every member body again to construct direct
   size-change edges.
3. `group_closure/1` computes the transitive matrix closure.
4. `Cure.Core.Kernel.validate_certificate/2` then asks for `total_group/3`,
   repeating group discovery to decide which definitions to mark total.
5. `Cure.Elab.TotalityClosure` may submit several members of the same group,
   causing the same graph and matrix work to be requested more than once.

Profiling on the dependent-regex workload established that recursive totality
checking, especially `mutual_group_total?/4`, dominates rebuild time. The recent
source/target-indexed worklist reduced a synthetic three-member closure from 126
composition attempts to 27, but it did not remove repeated SCC discovery, body
walks, or repeated certification attempts.

The current arrangement is sound, but it gives the TCB responsibility for an
expensive search problem. A trusted kernel should check a compact claim; it
should not have to discover that claim.

## Exact relationship to Agda

This design follows Agda's separation of responsibilities rather than copying
its Haskell modules mechanically.

### Mutual blocks versus actual recursive components

In `Agda.Termination.TermCheck`, `termMutual` starts with the declarations in a
mutual block, constructs their call information, computes the actual recursive
SCCs, and invokes `termMutual'` once per SCC. `termMutual'` collects the calls for
all definitions in that component and records one shared termination result for
the members.

Cure must adopt the same semantic unit:

- a source/module group is only a scheduling region;
- the definition SCC is the certification unit;
- every member of that SCC receives the same result atomically;
- a second request for another member reuses that result instead of rediscovering
  the SCC.

Unlike Agda, Cure has an explicit small kernel boundary. Therefore Cure treats
Agda's SCC calculation as an **untrusted proposal** and adds a checkable SCC
partition certificate.

### Incremental completion

`Agda.Termination.Termination` completes a call graph incrementally, composing
new information against existing information and checking newly exposed loops.
`Agda.Termination.CallGraph.completionStep` composes only edges whose endpoints
match. Idris 2 represents the same idea as source/target-indexed maps in
`Core.Termination.SizeChange`.

Cure must retain endpoint indexing and must never return to an all-pairs scan.
The compiler-side closure engine will distinguish `new` and `old` edges so each
useful composition is scheduled once per newly admitted representative.

### Sparse matrices and favorites

Agda stores matrices sparsely (`Agda.Termination.SparseMatrix`) and uses
`Agda.Utils.Favorites` to retain an antichain of relevant call matrices rather
than every equivalent or dominated matrix. Cure currently uses dense nested
lists and `Enum.at/2` in a triple loop.

Cure should adopt sparse storage once the certificate boundary is in place.
It must **not** adopt matrix dominance as an undocumented optimization. The
replacement relation must have a proved conservative direction and executable
properties before it affects kernel acceptance. Phase 1 therefore uses exact
matrix equality. Favorites are a later, independently gated phase.

### Cutoff

Agda uses a configurable termination depth (`CutOff`, with its normal default)
to keep the abstract domain finite and useful. Cure's present three-value
domain, `smaller | equal | unknown`, is already finite. This migration does not
add a cutoff or change relation precision. A richer bounded domain may be
considered later without changing the SCC certificate format.

## Locked trust boundary

### Trusted

The following remain in the TCB:

1. Core validation and canonical global identity.
2. A local traversal that extracts or verifies the complete direct-call summary
   of one checked definition.
3. Structural comparison of a call argument against the caller's parameters,
   including the existing `smaller`, `equal`, and exact reconstruct-equal rules.
4. Hashing/identifying the checked body and the extracted summary.
5. Verification of an SCC partition certificate.
6. The size-change certificate condition used in the current implementation.
7. Atomic publication of a totality result for all members of a verified SCC.

### Untrusted

The following move to the elaborator/compiler side:

1. Selection of the graph universe to submit.
2. SCC discovery (Tarjan, Kosaraju, or an equivalent algorithm).
3. Scheduling SCCs in dependency order.
4. Assembly of direct edges from trusted summaries.
5. Matrix closure search.
6. Deduplication, sparse indexing, favorites/antichain selection, and caching.
7. Construction of spanning-tree and topological-rank witnesses.

An incorrect untrusted result may cause a diagnostic or rejection. It must not
cause an unsound totality certificate.

### Important qualification

"Move SCC out of the TCB" does not mean trusting a list labelled `members`.
The kernel must verify that list without independently running an SCC algorithm.
That verification is linear in the submitted direct graph plus the witness
trees. Graph **search** is untrusted; finite witness checking is trusted.

## Canonical direct-call summaries

### Data model

Add a versioned trusted summary associated with each checked definition:

```elixir
%Cure.Core.DirectCallSummary{
  version: non_neg_integer(),
  caller: canonical_definition_key(),
  body_hash: binary(),
  caller_arity: non_neg_integer(),
  calls: [
    %Cure.Core.DirectCall{
      id: binary(),
      callee: canonical_definition_key(),
      callee_arity: non_neg_integer(),
      matrix: Cure.Core.SizeChangeMatrix.t(),
      provenance: Cure.Core.Provenance.t()
    }
  ],
  summary_hash: binary()
}
```

`calls` is sorted by a stable key before hashing. Duplicate syntactic call sites
may share a matrix, but their provenance remains available for diagnostics.
The summary hash covers the version, caller, body hash, arities, canonical
callees, matrices, and semantic provenance identifier. It does not cover raw
source spans whose movement cannot alter meaning.

### Construction rule

The summary is produced exactly once for a changed checked body:

1. Start from the canonical caller key and its leading-lambda parameters.
2. Walk every Core branch using the same binder shifting, root, smaller-set, and
   reconstruction tracking used by today's `Certificate` implementation.
3. Record every direct global call after application spines are recovered.
4. Resolve the callee to a canonical key. A bare unresolved key is a kernel
   validation error; it is never repaired by alias guessing.
5. Build the non-square `callee_arity × caller_arity` matrix.
6. Include self-calls, calls to mutual peers, ordinary acyclic calls, total
   dependencies, partial dependencies, and externs. Completeness is required for
   SCC verification even when an edge later becomes a terminal boundary.

The initial implementation may extract the summary inside
`Kernel.validate_certificate/2` and cache it in the environment. The desired
implementation extracts it as part of checked-definition publication so later
totality passes never rescan the body.

### Validation rule

The kernel accepts a cached summary only when all of these match:

- summary format/checker version;
- canonical definition key;
- checked Core body hash;
- caller arity;
- hashes of any trusted type/constructor information used for structural
  refinement;
- canonical callee identity and callee arity.

A stale or mismatched summary is ignored and reconstructed. It is never patched
in place.

## SCC partition certificate

### Why a partition certificate is necessary

Checking only that the proposed members call one another is insufficient: the
compiler could omit a third member on a return path. Checking that a set is
closed under all outgoing edges is also wrong: an SCC may call ordinary
downstream helpers which do not call back.

The kernel instead verifies a graph decomposition certificate. This is the
checkable analogue of the SCC result computed by Agda's `termMutual`.

### Certificate form

For a finite graph universe, submit:

```elixir
%Cure.Core.SCCPartitionCertificate{
  version: non_neg_integer(),
  universe: [canonical_definition_key()],
  summary_hashes: %{canonical_definition_key() => binary()},
  component_of: %{canonical_definition_key() => component_id()},
  rank: %{component_id() => non_neg_integer()},
  components: %{
    component_id() => %{
      members: [canonical_definition_key()],
      root: canonical_definition_key(),
      forward_tree: [edge_id()],
      reverse_tree: [edge_id()]
    }
  },
  sealed_boundaries: %{canonical_definition_key() => interface_certificate_hash()}
}
```

The certificate covers one canonical compilation component: the definitions
whose bodies are being published together, plus any visible definition that can
participate in a return path. A previously published definition may be a sealed
boundary only when its interface contains a valid totality/dependency
certificate tied to the same source and dependency hashes.

Legal module-import cycles are not rejected. The canonical module pipeline
already schedules module SCCs; all definitions from a module SCC that can call
one another belong to the same certificate universe.

### Kernel verification

The verifier performs the following checks in order:

1. **Universe identity.** Every submitted node exists canonically and its trusted
   direct-summary hash matches. No node appears twice.
2. **Edge completeness.** For every direct call in every submitted summary, the
   callee is either in `universe`, a recognized primitive/extern terminal, or a
   valid sealed boundary. Unknown callees fail with a structured diagnostic.
3. **Partition totality.** Every universe node has exactly one component and
   every component member maps back to that component.
4. **Condensation order.** For every direct edge `u -> v`, either
   `component_of[u] == component_of[v]`, or the target component has a strictly
   lower rank than the source component. Equal ranks across different
   components are rejected. This proves that no path leaving a component can
   return to it.
5. **Forward connectivity.** Within each component, the listed forward-tree
   edges are real direct edges and reach every member from `root`.
6. **Reverse connectivity.** Within each component, the listed reverse-tree
   edges are real direct edges viewed in reverse and reach every member from
   `root`. Together the two trees prove strong connectivity.
7. **Singleton rule.** A singleton with no self-edge is acyclic and does not need
   size-change closure. A singleton with a self-edge is a recursive SCC.

These checks prove that the proposed components are exactly SCCs of the verified
direct graph. They do so without Tarjan, repeated reachability, or Core body
rescans in the kernel.

### Boundary rule

A sealed boundary must include enough dependency information to prove that it
cannot call back into the current unpublished universe. In the first migration,
the conservative rule is:

- include every definition in the current module compilation SCC;
- permit as boundaries only definitions from already published interfaces whose
  dependency certificate predates and does not mention the current source-hash
  component;
- if that cannot be established, expand the universe rather than guessing.

This rule preserves Cure's legal import-cycle semantics while preventing an
omitted cross-module return edge.

## SCC totality certificate

After the partition is verified, the compiler submits one totality candidate per
recursive component:

```elixir
%Cure.Core.SCCTotalityCertificate{
  version: non_neg_integer(),
  component_id: component_id(),
  members: [canonical_definition_key()],
  member_body_hashes: %{canonical_definition_key() => binary()},
  direct_summary_hashes: %{canonical_definition_key() => binary()},
  closure: [Cure.Core.SizeChangeEdge.t()],
  derivations: [Cure.Core.SizeChangeDerivation.t()]
}
```

Member ordering is canonical and irrelevant to the result. The certificate hash
covers all member body hashes and direct-summary hashes, so changing any member
invalidates the whole SCC result.

### Phase 1 verification: preserve the current criterion

The first implementation moves SCC discovery out but deliberately retains the
current trusted closure calculation:

1. Verify the SCC partition certificate.
2. Fetch direct matrices from the trusted summaries for the exact component.
3. Run the existing endpoint-indexed `group_closure` over this explicit edge set.
4. Apply the existing idempotent-endo condition.
5. Publish the result once for the entire component.

This phase removes trusted SCC discovery, repeated body traversal, and repeated
member certification without changing matrix closure semantics.

### Phase 2 verification: proof-carrying closure

The compiler then takes over closure construction. Every submitted derived edge
has one of two forms:

```text
Base(direct_call_id)
Compose(left_edge_id, right_edge_id)
```

The kernel checks endpoints, dimensions, and matrix composition for each
derivation. It also checks a saturation witness: every compatible retained pair
is either represented by its exact composition or is covered by an explicitly
validated conservative representative.

Initially, `covered` means exact matrix equality. This makes the proof simple
and preserves the current finite domain. Only after the dominance lemma below is
implemented and property-tested may `covered` use an antichain.

For every idempotent endo edge in the verified saturated set, the kernel requires
at least one `smaller` diagonal entry. Failure rejects the entire SCC and reports
the shortest available derivation path.

### Phase 3: Agda-style favorites

Adopt Agda's `Favorites` idea only after defining and proving Cure's replacement
order. The required theorem is:

> If matrix `A` covers matrix `B`, removing `B` cannot hide an idempotent
> non-decreasing loop obtainable by any compatible prefix or suffix.

The proof must cover rectangular cross-function matrices and both left and right
composition. The implementation gate is:

- an executable exhaustive property over all matrices through at least arity 3;
- a direct mathematical argument in the spec/code documentation;
- differential comparison of exact closure and favorites closure on generated
  SCCs;
- an Antigen control containing a divergent mutual cycle whose weaker matrix
  must not be discarded.

Until this gate passes, exact equality is the only allowed deduplication rule.

## API and ownership changes

### `Cure.Core.Certificate`

Split the present module by responsibility:

- `Cure.Core.DirectCalls`: trusted local extraction/verification;
- `Cure.Core.SizeChange`: trusted relation and matrix primitives;
- `Cure.Core.TotalityCertificate`: trusted finite certificate verifier;
- `Cure.Elab.Totality`: untrusted SCC discovery and candidate construction.

Names may vary, but the ownership boundary must not.

Delete from the trusted certificate path:

- `mutual_group/3`;
- recursive `reaches?`-style SCC discovery;
- repeated `called_globals` walks used only to rediscover the group;
- per-member calls to `total_group/3` after a successful check.

### Kernel API

Replace member-oriented validation:

```elixir
Kernel.validate_certificate(env, name)
```

with component-oriented validation:

```elixir
Kernel.validate_scc_certificate(
  env,
  partition_certificate,
  totality_certificate
)
```

The successful result returns the updated environment and the complete sorted
member list. Publication is transactional: no member is marked total until all
checks succeed.

An acyclic singleton may use a smaller
`Kernel.validate_acyclic_definition/3` path, but it must still be tied to the
trusted direct-summary hash.

### Environment and interfaces

Store:

- direct-call summaries by canonical definition key and body hash;
- SCC result by component certificate hash;
- member-to-component index for constant-time reuse;
- totality certificate digest in the published module interface.

Interface hashing must include semantic certificate data but exclude diagnostic
spans. Loading the same interface twice remains idempotent. A source or
dependency hash change invalidates only affected summaries/components and their
reverse dependants.

### Totality driver

`Cure.Elab.TotalityClosure` becomes a batch driver:

1. Ensure every checked body in the compilation component has a trusted direct
   summary.
2. Build the definition graph once.
3. Compute SCCs once.
4. Topologically schedule components once.
5. Skip components whose certificate hash is already valid.
6. Submit each unresolved component once.
7. Attach a single failure to the component and contextualize it at each
   declaration only when rendering diagnostics.

`certify_deferred` remains a phase distinction for incomplete bodies, not a
license to repeat already valid SCC work.

## Diagnostics

New failures are structured diagnostics, never exceptions or bare strings.

Required cases:

- `E_TOTALITY_SUMMARY_STALE`: definition, old/new body hashes, checker version;
- `E_TOTALITY_UNKNOWN_CALLEE`: caller, canonical/unresolved callee, call-site
  provenance, source span, Core call term;
- `E_TOTALITY_SCC_INCOMPLETE`: proposed component, omitted node, and verified
  path witnessing the omission;
- `E_TOTALITY_SCC_INVALID`: invalid tree/rank edge and both component ids;
- `E_TOTALITY_MATRIX_INVALID`: caller, callee, call site, expected dimensions,
  submitted matrix, and derived trusted relation;
- `E_TOTALITY_DERIVATION_INVALID`: edge id, parent ids, endpoints, expected and
  submitted composition;
- `E_TOTALITY_NOT_DECREASING`: SCC members, offending idempotent matrix,
  diagonal, and a source-call path reconstructed from derivations.

Macro expansion provenance must survive into direct-call provenance. Diagnostic
fingerprints include the semantic call/derivation identity, so two distinct
failing paths are not collapsed merely because they end at the same global.

## Implementation sequence

Every stage starts with the smallest failing regression and lands separately.

### Stage 0 — Characterize current behavior

Add golden tests that record current accept/reject outcomes for:

- self recursion;
- well-founded two- and three-member mutual recursion;
- a divergent mutual cycle;
- a mutual block containing two independent SCCs;
- an SCC with an outgoing acyclic helper;
- legal cross-module recursion inside a module compilation SCC;
- declaration-order permutations of all of the above.

Record closure edge count, composition attempts, body-walk count, SCC-discovery
count, and certificate submissions. The new path must preserve outcomes while
reducing repeated work.

### Stage 1 — Trusted direct summaries

Extract the current call-site/matrix walker behind a single summary API. Cache by
body hash. Add properties that cached and uncached extraction are identical and
that metadata-only source movement does not change the semantic hash.

No SCC behavior changes in this stage.

### Stage 2 — Batch untrusted SCC discovery

Build the direct definition graph from summaries in `Cure.Elab.TotalityClosure`.
Compute SCCs once and demonstrate via counters that each body is summarized once
and each component is submitted once.

The old kernel SCC discovery remains temporarily as a differential oracle.

### Stage 3 — Partition certificate verifier

Implement ranks plus forward/reverse spanning-tree witnesses. Differentially
compare proposed components with the old trusted discovery, then switch kernel
validation to the verified proposal.

After the full gate is green, delete the old discovery code. It must not remain
as fallback recovery.

### Stage 4 — Atomic SCC publication and cache

Key results by member body/summary hashes, publish all members atomically, and
skip already valid components. Update serialized interfaces and incremental
invalidation.

### Stage 5 — Sparse closure engine outside the kernel

Port Agda/Idris endpoint-indexed completion using sparse matrices and `new`
versus `old` work sets. Submit exact derivations and compare against the trusted
closure on generated examples.

### Stage 6 — Proof-carrying closure

Enable kernel verification of externally built exact closure, then remove
trusted closure search. The kernel retains matrix primitives and finite proof
checking.

### Stage 7 — Favorites, only if justified

Implement the conservative replacement theorem and gates described above. This
stage is optional: sparse exact closure may already meet the performance target.

## Required properties

### Graph properties

- SCC result is invariant under declaration and map iteration order.
- Every verified direct edge is intra-component or strictly rank-decreasing.
- Forward/reverse trees accept exactly strongly connected proposed components.
- Removing any genuine SCC member makes verification fail.
- Merging two distinct SCCs makes rank/connectivity verification fail unless
  they are genuinely mutually reachable.
- Interface reload is idempotent and preserves component identity.

### Summary properties

- Every Core global call appears in the direct summary.
- No summary edge uses a bare or alias-dependent identity.
- Summary hashes ignore diagnostic metadata and change for semantic call/matrix
  changes.
- Cached and freshly extracted summaries are equal.
- Macro-generated and authored equivalent calls produce equal semantic entries.

### Totality properties

- Old and new paths agree on every generated graph/matrix fixture during
  migration.
- Every accepted exact closure satisfies the current idempotent-loop criterion.
- Every rejected SCC remains wholly uncertified.
- Certification is invariant under member and edge ordering.
- Revalidating the same certificate is idempotent and performs no body walks or
  closure compositions.

### Adversarial certificates

Tests must reject certificates with:

- an omitted direct call;
- an omitted mutual member;
- a forged canonical key;
- a stale body or dependency hash;
- a false topological rank;
- a forward or reverse tree using a nonexistent edge;
- a matrix with the right dimensions but an overstated relation;
- an invalid composition derivation;
- a missing bad idempotent loop;
- partial publication after a later member fails.

## Performance requirements

Performance is measured, not inferred from asymptotic claims.

For a cold and warm dependent-regex build, record:

- time in direct-summary extraction;
- time in SCC proposal and witness construction;
- time in kernel partition verification;
- time in closure generation and verification;
- number of Core body traversals;
- number of SCC submissions;
- direct and closure edge counts per SCC;
- matrix composition attempts and admitted matrices;
- cache hits/misses and invalidation reasons.

Hard invariants:

- one direct-summary body traversal per changed definition;
- one SCC proposal per graph build;
- one kernel totality submission per changed recursive SCC;
- zero closure compositions for a valid warm SCC cache hit;
- focused tests do not rebuild unrelated stdlib summaries;
- no dense `Enum.at/2` matrix inner loop after the sparse phase lands.

Wall-time acceptance is relative to the recorded Stage 0 baseline because host
and BEAM scheduling variance is material. Each later stage must report median
and range over at least three serialized runs. A stage that increases median
cold time by more than 5% must explain the regression before landing; warm
rebuilds must show a material reduction for unchanged SCCs.

## Full verification gate

Before deleting the old SCC path:

1. Current totality unit tests and new SCC-certificate tests pass.
2. Exact old/new differential property passes for generated small graphs.
3. TCB and totality suites pass.
4. Relevant Antigen assays, including divergent mutual recursion, pass.
5. Canonical module pipeline full gate passes.
6. Complete `MIX_ENV=test mix test` passes with Mix invocations serialized.
7. Clean dependency-ordered stdlib build passes.
8. Incremental rebuild tests prove cache invalidation by body and dependency
   hash.
9. Escript/Unix smoke test passes.
10. The dependent-regex build has recorded cold and warm profiles.

## Superseded specifications

This specification supersedes only the ownership and scheduling portions of:

- `docs/superpowers/specs/antigen/2026-07-04-mutual-size-change-design.md`,
  specifically its instruction to compute the SCC with
  `called_globals/reaches?` inside `Cure.Core.Certificate`;
- `docs/superpowers/specs/antigen/2026-07-03-antigen-totality-closure-design.md`,
  where it requires the kernel to re-derive the complete group through global
  search for every submitted member.

The size-change relations, reconstruct-equal rule, cross-function matrix shape,
and idempotent-loop acceptance condition in the 2026-07-04 size-change specs
remain normative until explicitly replaced by a separately verified design.

## Non-goals

- No `assert_total` or `assert_smaller` escape hatch.
- No weakening of quantity-zero checking or proof closure.
- No change to which recursive programs are accepted in the first migration.
- No rejection of legal module import cycles.
- No whole-program requirement for ordinary incremental compilation.
- No move to Lean-style explicit well-founded recursion terms in this change.
  That remains a valuable future path for user-supplied proofs, but Agda's
  call-graph/SCC architecture is the closer fit for Cure's existing automatic
  size-change checker.
- No unproved matrix antichain optimization.

## Completion criterion

The change is complete when the trusted kernel performs only local direct-call
summary validation, finite SCC-witness verification, finite size-change proof
verification, and atomic certificate publication. It must not discover SCCs,
scan unrelated bodies, guess canonical identities, or repeat certification for
another member of an already decided component.

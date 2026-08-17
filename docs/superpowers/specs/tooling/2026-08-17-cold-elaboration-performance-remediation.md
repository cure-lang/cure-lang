# Cold dependent-elaboration performance remediation

**Status:** structural implementation complete; stabilization gates pass, but
the 15% cold-build target remains open for a further optimization pass

**Date:** 2026-08-17

**Scope:** reduce clean-build time for the dependent regular-expression
stdlib while preserving the kernel's soundness boundary, canonical module
identity, structured diagnostics, and incremental-build semantics.

**Prerequisite:** the implementation must start from a red regression or a
newly added performance assertion. This document is not permission to make an
unmeasured cache or a proof-specific workaround.

## 1. Executive decision

The measured cold-build bottleneck is typed elaboration of the dependent Regex
proofs, not SCC proposal, sparse closure generation, or kernel partition
checking. The remediation therefore has two primary tracks, in this order:

1. Remove the `Std.Regex`/`Std.Regex.Proof` body-elaboration cycle by creating
   a one-way Regex module graph and a compatibility façade.
2. Complete the canonical dependent-constructor retry algorithm so blocked
   fields wake only when one of their blockers changes and de-Bruijn field
   prefixes are maintained incrementally rather than rebuilt on every attempt.

Only after those tracks are measured should a narrow normalization or
elaboration memo be considered. The rejected whole-environment cache prototype
must remain stashed and must not be restored as part of this work.

The target graph is:

```text
                         +----------------------+
                         | Std.Regex (façade)   |
                         | public compatibility |
                         +----------+-----------+
                                    |
                         +----------v-----------+
                         | Std.Regex.Proof     |
                         | verified theorems   |
                         +----------+-----------+
                                    |
              +---------------------+---------------------+
              |                                           |
   +----------v-----------+                     +-----------v----------+
   | Std.Regex.Runtime    |                     | Std.Regex.Language   |
   | executable engine    |                     | denotation/language  |
   +----------+-----------+                     +-----------+----------+
              |                                             |
              +---------------------+-----------------------+
                                    |
                         +----------v-----------+
                         | Std.Regex.Core      |
                         | shared indexed data |
                         +----------------------+
```

The arrows mean “imports”. The façade may import every lower layer needed for
its public wrappers. No lower layer may import the façade. In particular:

```text
Std.Regex.Core      -> no Regex/Proof/Language module
Std.Regex.Runtime   -> Std.Regex.Core
Std.Regex.Proof     -> Std.Regex.Core, Std.Regex.Runtime
Std.Regex.Language  -> Std.Regex.Core, Std.Regex.Runtime, Std.Regex.Proof
Std.Regex           -> Std.Regex.Core, Std.Regex.Runtime, Std.Regex.Proof
```

There must be no `Std.Regex -> Std.Regex.Proof` edge from a module that
`Std.Regex.Proof` imports, and no `Std.Regex.Proof -> Std.Regex` edge after the
migration. The public façade is the only module that may have the old name.

## 2. Evidence and baseline

The current clean baseline was obtained after stashing the revision-aware
exposure-cache prototype, at commit `d67ad8b0`, with one serialized invocation
of:

```sh
MIX_ENV=test CURE_SKIP_DOC_FENCES=1 \
  mix cure.bench.interfaces --warm-iterations 1 --top 20
```

The run rebuilt 77 modules:

| Measurement | Baseline |
|---|---:|
| cold total | 175.688 s |
| cold rebuilt modules | 77 |
| warm total | 8.234 s |
| warm rebuilt modules | 0 |
| warm module check | 2.127 s |
| `Std.Regex` + `Std.Regex.Proof` | 120.195 s |
| `Std.Regex.Language` | 34.825 s |

The two Regex components consumed approximately 88% of the cold run. The
largest declaration stages were typed elaboration:

| Declaration | Typed elaboration |
|---|---:|
| `Std.Regex.Proof#thompson_alternate_acceptance_captures` | 28.167 s |
| `Std.Regex.Proof#thompson_evidence_acceptance_from_encodes_explicit` | 21.917 s |
| `Std.Regex.Proof#certified_alternate_acceptance_captures` | 16.889 s |
| `Std.Regex.Language#alternate_compilation_is_sound` | 14.566 s |
| `Std.Regex.Proof#thompson_repeat_acceptance_captures` | 13.932 s |
| `Std.Regex.Proof#thompson_repeat_acceptance_from_encodes` | 10.766 s |
| `Std.Regex.Language#complete_repeat_mode_continuation_view_from` | 8.791 s |

The totality/SCC verifier is not the cold bottleneck. In the same run its
aggregate timings were approximately:

| Operation | Total |
|---|---:|
| closure generation | 1.903 s |
| closure verification | 0.913 s |
| direct summaries | 3.423 s |
| partition verification | 0.084 s |
| SCC proposal | 0.060 s |
| component certificates | 0.002 s |

Historical three-sample cold totals for the same 77-module universe ranged
from 149.305 s to 177.370 s, with a median of 167.339 s. The current 175.688 s
sample is therefore a valid current baseline but not evidence of a regression
by itself. Every comparison in this specification uses serialized samples and
reports both the total and the Regex-component medians.

The prior exposure-cache prototype is explicitly excluded. It serialized and
retained whole environments, caused swap pressure, and produced cold samples
of 168.526 s, 198.540 s, and 190.011 s. It may inform rejected-design notes,
but it is not an implementation option.

The benchmark harness now runs each cold/warm pair in a fresh monitored Erlang
worker and waits for that worker before starting the next pair. This prevents
the old same-process `run_repeated/3` path from retaining all sample-local
elaborator state (which reached approximately 2.5 GB RSS). The workers share
one BEAM, so this is a reclamation boundary rather than an OS-level memory
reset; RSS still oscillated below 1 GB during the final run. A future harness
change may use subprocesses if memory isolation itself becomes an acceptance
criterion, but it is not a reason to add a semantic cache.

### 2.1 Implementation checkpoint (2026-08-17)

The first structural and retry changes are now in the working tree:

- `Std.Regex.Core` and `Std.Regex.Runtime` own the shared indexed data and
  executable engine; `Std.Regex` is a thin public façade, and lower layers no
  longer import that façade.
- Canonical visibility carries a manifest-derived root-to-reexport table, so a
  qualified compatibility spelling such as `Std.Regex.configured` resolves to
  the canonical `Std.Regex.Runtime#configured` key without source-driven alias
  discovery in the canonical pipeline. The classic source loader retains its
  compatibility alias construction for unmigrated callers.
- Declaration preparation is reused between the canonical type-skeleton and
  interface-registration passes, and the timing regression asserts one
  preparation event per module.
- Constructor field retries use blocker/fingerprint queues. The old global
  constructor-failure cache is not reused for a partially refined field goal;
  refined nullary constructor fields propagate their result template through
  the parent metavariable context. This fixes the `AStar` simultaneous-
  unification regression without changing the kernel or adding a Regex branch.

Observed serialized benchmark samples after the split/preparation work were
`191.872 s`, `179.595 s`, and `168.219 s` cold (median `179.595 s`) and
`10.525 s`, `8.641 s`, and `8.612 s` warm (median `8.641 s`). The combined
Regex component median was approximately `149.4 s` versus the `155.0 s`
baseline (about a 3.6% improvement), while total cold time remains noisy and
does not yet meet the 15% target. The warm median is within the 5% guardrail.
The latest constructor profile recorded 1,576 field attempts, 797 blocked
attempts, 808 retries, 144 wakeups, and 15 hard failures; contextual
normalization recorded 1,890 calls (232 hits, 1,658 misses). Those hit rates do
not justify adding a speculative normalization cache, so none has been added.

The current declaration profile confirms that the remaining cost is still
typed elaboration rather than kernel certificates or SCC work. In a serialized
diagnostic sample, `Std.Regex.Proof` consumed about 113.8 s and
`Std.Regex.Language` about 27.7 s; the largest declaration stages were
`thompson_alternate_acceptance_captures` (25.85 s),
`thompson_evidence_acceptance_from_encodes_explicit` (18.39 s),
`certified_alternate_acceptance_captures` (13.29 s),
`thompson_repeat_acceptance_captures` (12.91 s), and
`thompson_repeat_acceptance_from_encodes` (10.41 s). The corresponding
totality/SCC work remained in the low single-digit seconds.

One measured optimization experiment attempted to pass the already-certified
Thompson package through the four Language alternate-completeness branches and
replace the Pattern-shaped capture helper with a compilation/proof-shaped
helper. It compiled and preserved the accepting-path tests, but increased the
Language component from roughly 27.7 s to 42.4 s because the caller-side
dependent package matches became more expensive. The experiment was reverted.
Future work must first isolate the recursive normalizer/unifier cost inside
the named Proof declarations; no further source-level theorem reshaping is
accepted without a before/after declaration profile.

Focused verification now passes the simultaneous-unification antibody (4/4),
constructor retry controls (11/11), Regex split/acceptance/evidence/bounded
tests (20/20), and the canonical pipeline gate. The final serialized
no-skip suite passes 6,533 tests with 0 failures and 6 exclusions; the 329
documentation fences pass, and the post-change canonical gate passes 52/52
(2 properties, 50 tests). The structural remediation is therefore complete;
the remaining work is a separate optimization pass to pursue the unmet 15%
cold-build target.

### 2.2 Current hot-path source map

This is the source map an implementer must verify before editing. The
function names are canonical construction sites; fixing a caller or adding a
Regex-only branch is not an acceptable substitute.

#### Module pipeline

`lib/cure/compiler/module_pipeline.ex` is the component authority:

- `check_component/8` classifies the component and times
  `component_register`, `component_merge`, `component_bodies`, and
  `component_freeze`;
- `register_component_type_skeletons/5` calls
  `Program.canonical_type_skeleton/3` for every member;
- `register_component_interfaces/8` calls
  `Program.canonical_register_interface/3` for every member and merges the
  resulting interfaces;
- `check_component_bodies/6` installs the component environment and calls
  `Program.canonical_check_bodies/2`;
- `component_check_order/2` orders lexical `use` and prelude edges inside a
  component. It must not acquire a Regex-specific exception.

The implementation must use Chiasmus on this focused absolute-path set before
changing the pipeline:

```text
/Users/ch/Develop/esp32-beam/cure-lang/lib/cure/compiler/module_pipeline.ex
/Users/ch/Develop/esp32-beam/cure-lang/lib/cure/elab/program.ex
/Users/ch/Develop/esp32-beam/cure-lang/lib/cure/elab/declarations.ex
/Users/ch/Develop/esp32-beam/cure-lang/lib/cure/elab/elaborator.ex
/Users/ch/Develop/esp32-beam/cure-lang/lib/cure/elab/attempt_cache.ex
```

Use `chiasmus_map` for symbol locations and focused `callers`/`callees`/
`path` queries for the functions above. Treat dynamic dispatch, generated
modules, and process-global state as invisible to the graph until confirmed by
direct source inspection.

#### Program and declaration pipeline

`lib/cure/elab/program.ex` is the canonical registration/checking authority:

- `canonical_type_skeleton/3` prepares declarations and declares type headers;
- `canonical_register_interface/3` prepares declarations, registers the
  interface, and checks overload legality;
- `canonical_check_bodies/2` runs the strict body pass, deferred totality,
  macro validation, type-level certification, and equation generation;
- `canonical_install_component_environment/2` installs the merged component
  environment without changing canonical owners.

`lib/cure/elab/declarations.ex`, chiefly `elaborate_real_body/4`, is the
per-declaration hot path. Its stage order is part of the benchmark contract:

```text
macro expansion -> signature -> induction -> typed elaboration -> relevance
-> Core packaging -> environment publication -> totality -> equations
```

`typed_elaboration` invokes `elaborate_body_typed/4` and the kernel's branch
checking. The remediation must not move type checking into Runtime or bypass
the kernel check to make the timing smaller.

#### Constructor retry authority

`lib/cure/elab/elaborator.ex` is the only constructor retry authority:

- `resolve_ctor_argument_values/13` builds the field problem;
- `resolve_ctor_fields/13` runs the pending-field fixpoint;
- `retry_deferred/3` retries result-index equations;
- `frame_prefix/5` currently rebuilds prior field values and is the identified
  prefix-work hotspot;
- `try_infer_field/6` and `try_infer_field_uncached/6` perform isolated field
  inference;
- `field_blockers/2` extracts metavariable dependencies;
- `AttemptCache.scope/1` bounds the existing operation-local retry cache.

The implementation must keep all semantic changes in this path. Do not add a
special constructor case to `Std.Regex.Proof` or to a test helper.

#### Regex source set

The source files to classify and graph are:

```text
/Users/ch/Develop/esp32-beam/cure-lang/lib/std/regex.cure
/Users/ch/Develop/esp32-beam/cure-lang/lib/std/regex_proof.cure
/Users/ch/Develop/esp32-beam/cure-lang/lib/std/regex_language.cure
```

The current edges that create the expensive body SCC are:

- `Std.Regex` makes qualified calls to
  `Std.Regex.Proof.parse_pattern_full_verified/2`,
  `parse_program_full_verified/2`,
  `parse_program_prefix_verified_at/7`, and
  `parse_program_prefix_chars_verified_at/8`;
- `Std.Regex.Proof` lexically imports `Std.Regex`;
- `Std.Regex.Language` lexically imports both `Std.Regex` and
  `Std.Regex.Proof`.

The four façade calls must be preserved semantically, but their dependency
must move to the façade after the Core/Runtime/Proof split. The source map is
not permission to delete those verification calls.

## 3. Goals

### 3.1 Correctness goals

The implementation must:

1. Preserve the exact typed semantics of `Std.Regex`, `Std.Regex.Proof`, and
   `Std.Regex.Language`.
2. Preserve the existing canonical definition identity rules. Moving a
   declaration must not reintroduce bare-name closure entries or alias-based
   recovery.
3. Preserve full structured diagnostics, including source span, declaration,
   failing Core term, expected/inferred types, unresolved global, and macro
   provenance when available.
4. Preserve proof erasure and totality certification. A successful benchmark
   is invalid if it succeeds by making a proof opaque, weakening checking, or
   adding a runtime interpreter.
5. Preserve source compatibility for the public Regex API, or document and
   test an intentional versioned break before changing it.
6. Preserve legal W086 behavior. The Regex/Proof cycle must disappear from the
   dependency graph; the reviewed `Std.Char`/`Std.Literal`/`Std.String` SCC
   remains legal. No new W086 component is accepted.

### 3.2 Performance goals

The structural split and retry work are successful only if they produce a
repeatable improvement, not merely a single fast machine sample. The first
release target is:

- at least a **15% reduction in the median cold time of the combined Regex
  components** (`Std.Regex`, `Std.Regex.Core`, `Std.Regex.Runtime`,
  `Std.Regex.Proof`, and `Std.Regex.Language`, counted by component once); and
- no more than a **5% regression in median warm total time**; and
- no increase in the number of declarations elaborated on a clean build;
  movement from one component to another must be visible in the stage report.

These are engineering targets, not permission to change semantics to meet a
number. If the split alone does not meet the target, the report must identify
the remaining dominant declaration before the retry optimization proceeds.

The target remains open after the current serialized acceptance run. The
current source universe contains 79 modules and has source hash
`84515496281c31f4b1550086c9a5e5714afb6952ae47c893bba1b3b53a9206ab`. With
`CURE_SKIP_DOC_FENCES=1`, three cold/warm pairs produced:

| Sample | Cold total | Warm total | Regex components |
|---:|---:|---:|---:|
| 1 | 193.251 s | 8.060 s | 170.161 s |
| 2 | 154.341 s | 10.087 s | 131.356 s |
| 3 | 183.380 s | 11.561 s | 151.805 s |
| Median | **183.380 s** | **10.087 s** | **151.805 s** |

The Regex-component median is only about 2% below the historical ~155 s
component baseline, not the required 15%. The total and warm medians are noisy
and are not a passing stabilization claim. The report is nevertheless valid:
all pairs were serial, the source hash and doc-fence setting matched, and the
machine-readable report included the component median directly.

### 3.3 Observability goals

Every cold benchmark must answer all of these questions without a debugger:

- Which module component was checked?
- Which pipeline phase consumed its time?
- Which declaration and body stage consumed the time?
- How many constructor attempts were made, blocked, retried, and reused?
- Which metavariable revisions woke a blocked field?
- How much time was spent in typed elaboration versus kernel checking,
  totality, equations, and interface publication?
- Did a cache entry hit, miss, or get rejected as stale, and what was its
  compact key? No complete environment may be printed or retained for this.

## 4. Non-goals and prohibited shortcuts

This work does **not**:

- build the MetaM-like reflective tier;
- add a general proof tactic language;
- move proof checking out of the trusted kernel;
- make all `@reducible` definitions transparent;
- restore a catch-all constructor deferral rule;
- add a Regex-specific runtime path or unchecked cast;
- serialize complete `Env`, `Context`, `MetaCtx`, or AST values into a
  process-global cache;
- cache failed elaboration results across independent declarations;
- treat the persistent publication cache as a cold-build optimization;
- suppress W086 or downgrade it to a generic warning to make the graph look
  acyclic;
- change the theorem statements merely to make them elaborate faster;
- introduce a special import in `Std.Regex.Proof` that exists only to work
  around a source cycle.

The cache boundary is an elaborator implementation detail. It may retain a
small normalized term or a constructor-attempt summary only when its complete
validity key is explicit and testable. It may never retain an environment
snapshot or a term whose meaning depends on an unrecorded imported interface.

## 5. Phase 0 — red regressions and measurement harness

No implementation phase starts until these tests and reports exist.

### 5.1 Dependency-graph regression

Add a compiler test that loads the stdlib manifest and asserts:

```text
Std.Regex        does not depend on Std.Regex.Proof
Std.Regex.Proof  does not depend on Std.Regex
Std.Regex.Core   has no dependency on any Regex proof/language module
Std.Regex.Runtime depends only on Std.Regex.Core and its ordinary prelude
Std.Regex.Language depends on Core, Runtime, Proof, and no façade
```

The test must inspect canonical manifest edges, not source text alone. A
qualified reference, a `use` import, a macro home, and a generated declaration
must be represented separately. A future implementation that reintroduces the
cycle through a macro or generated declaration must fail this test.

### 5.2 API inventory regression

Before moving declarations, generate or record an API inventory for the
current `Std.Regex` interface:

- exported type and typealias names, including parameter arities;
- exported constructors and their arities;
- exported function names and arities;
- reducibility, inline, extern, and visibility metadata;
- canonical owner and source span for each entry;
- the normalized type of each entry.

The inventory is a test fixture, not an unreviewed golden. Internal proof
helpers must be marked intentionally non-public rather than copied into the
façade.

### 5.3 Semantic red tests

Pin representative behavior before the split:

1. Empty, literal, predicate, group, concat, alternate, optional, repeat,
   lazy repeat, anchors, and configured patterns.
2. Full parse, prefix parse, search, split, and typed result extraction.
3. The bounded-regex fixture that previously reached emission with a bare
   `:same` key.
4. Concat, alternate, group, and repeat proof certificates.
5. The exact nested-constructor sibling-refinement regression.
6. Type-alias and canonical-owner checks for `Pattern`, `ShapeCode`,
   `MachineState`, `Evidence`, and the indexed certificate families.

The tests must check successful compilation and selected runtime results. A
test that checks only that an interface contains a name is insufficient.

### 5.4 Benchmark harness

Extend `mix cure.bench.interfaces` (or the existing trace sink) so one run
emits a machine-readable record containing:

```text
source_universe_hash
stdlib_source_hashes
component_members
component_edges
component_stage_us
declaration_stage_us
constructor_counters
normalization_counters
totality_counters
warm_or_cold
rebuilt_modules
```

Human-readable output may remain, but the acceptance script must consume the
structured record. The benchmark runner must:

1. run one cold publication in an isolated generation;
2. run one warm no-rebuild check;
3. repeat that pair three times, serially;
4. report median, minimum, and maximum;
5. refuse to compare runs with different source-universe hashes or different
   doc-fence settings.

The runner must never invoke two Mix processes concurrently. It must not use a
destructive broad cleanup command. The existing immutable publication root and
its generation mechanism should be reused.

## 6. Phase 1 — pipeline timing and duplicated-preparation audit

This phase does not change semantics. It makes the expensive work attributable
and removes only environment-independent duplication.

### 6.1 Component timing schema

Keep the existing timing boundaries in
`lib/cure/compiler/module_pipeline.ex`:

- `component_register`;
- `component_merge`;
- `component_bodies`;
- `component_freeze`.

Make each event carry:

```elixir
%{
  component: canonical_sorted_member_list,
  module: canonical_module_identity,
  phase: phase,
  source_hash: source_hash,
  imported_interface_hashes: sorted_hash_list
}
```

Do not use a source filename as the identity. The canonical identity is the
module key used by the manifest and emission closure.

### 6.2 Declaration-stage timing

`lib/cure/elab/declarations.ex` already times:

```text
macro_expansion
signature
induction
typed_elaboration
relevance
core_packaging
environment_publication
totality
equations
```

Add the declaration's canonical owner/name, arity, source span, and a stable
declaration fingerprint to the event. The fingerprint must exclude transient
metavariable IDs and source-path-only metadata. It must not expose full source
text in ordinary output.

Inside `typed_elaboration`, record counters rather than nested wall-clock
events for every recursive expression. The counters must include:

- constructor field attempts;
- blocked attempts;
- hard failures;
- retries skipped because the same revision/fingerprint was attempted;
- retries woken by a blocker;
- prefix cells materialized and reused;
- deferred result-index equations attempted and discharged;
- contextual normalization calls, hits, misses, and stale rejections.

The default compiler path may keep counters disabled; the benchmark path must
enable them. The instrumentation must not alter elaboration order.

### 6.3 Shared declaration preparation

`Program.canonical_type_skeleton/3` and
`Program.canonical_register_interface/3` currently repeat the following
preparation:

1. `check_declarations/1`;
2. owner seeding and telescope support;
3. imported-environment merge;
4. module-visibility installation;
5. induction lifting;
6. `where` expansion;
7. overload ordinal annotation.

Introduce an explicit `PreparedDeclarations` value, scoped to one canonical
pipeline request, containing:

```text
owner
source_hash
validated_ast_shape
lifted_declarations
expanded_where_declarations
overload_ordinals
source/provenance table
```

The preparation is reusable only if each operation is proven independent of
the imported environment. If any macro, where expansion, hygiene decision, or
overload operation reads an imported binding, split the operation into:

- an environment-independent preparation step cached in the request; and
- an environment-dependent registration step executed for each environment.

Do not make this value a persistent cache entry until its dependency hash is
part of the key. `canonical_type_skeleton/3` and
`canonical_register_interface/3` must consume the same prepared declaration
list, but retain their separate environment construction and error labels.

Add a regression asserting that preparation occurs once per module per
request, while registration still occurs once per component pass. A failure in
preparation must report the original source span and never leak a partial
prepared value into another module.

## 7. Phase 2 — canonical Regex module split

This is the main graph-level optimization. It must be implemented as a source
migration, not as a pipeline special case.

### 7.1 Inventory and classification

Parse the current three files with Chiasmus and inspect the source directly.
The Chiasmus adapter is a navigation aid; it is not the authority for Cure's
dynamic module visibility or generated declarations. For every declaration in
`lib/std/regex.cure`, classify it into exactly one of:

1. **Core data:** indexed data families, aliases, constructors, and values
   that appear in the types of both runtime and proof declarations.
2. **Core computation:** small total functions whose normal forms occur in
   shared indices (for example `Sem`, shape simplifiers, index arithmetic, or
   canonical injections). These must remain terminating and must not import a
   proof module.
3. **Runtime:** parser/compiler ASTs, machine construction, stepping, evidence
   execution, search, conversion, and public non-proof operations.
4. **Proof-only:** theorem families, existential views, acceptance certificates,
   completeness/soundness lemmas, and proof-directed extraction routines.
5. **Façade:** compatibility aliases and public wrappers only.

The classification table must be reviewed before files are moved. A
declaration may not be put in Core merely because Proof mentions it; Core must
remain a small foundational interface.

### 7.2 `Std.Regex.Core`

Create `lib/std/regex_core.cure` with module name `Std.Regex.Core`.

It owns the shared indexed vocabulary required by multiple layers, including
the final reviewed set of:

- `ShapeCode`, `Choice`, and `Sem`;
- the public `Pattern` family and its constructors;
- machine and state families (`PatternMachine`, `MachineState`, `ThreadState`
  and their indexed companions);
- evidence, capture, instruction, routine, and execution index families;
- boundary and position data needed in shared signatures;
- `Encodes`, `EncodesMany`, extraction, and other certificate *data families*
  that are inputs or outputs of both Runtime and Proof;
- definitionally relevant total helpers such as canonical state injections and
  shape simplifiers.

The exact list comes from the classification table and type-use graph. Core
must not contain a theorem whose only purpose is to establish a law about a
Runtime function. It must not call `Std.Regex.Proof`, `Std.Regex.Language`, or
the public façade.

Core's interface is to be frozen before Proof is checked. Any function moved
into Core must be benchmarked independently because a large recursive helper
in Core merely moves the cold cost rather than removing it.

### 7.3 `Std.Regex.Runtime`

Create `lib/std/regex_runtime.cure` with module name `Std.Regex.Runtime`.

Move executable behavior that depends on Core but has no theorem dependency:

- regex/program compilation;
- pattern machine construction and stepping;
- boundary filtering and search;
- evidence and capture execution;
- parser-facing conversion and runtime result assembly;
- ordinary public helpers whose bodies do not call Proof.

Runtime imports Core only (plus ordinary prelude modules). It must not import
the public façade or Proof. If a runtime function currently calls a verified
Proof parser, split it into:

- an unverified-but-typed Runtime primitive that returns the shared certificate
  input required by Proof; and
- a verified façade wrapper that calls Proof.

This is not permission to weaken the public verified API: the façade must call
the Proof routine where the old public function did. It only moves the
dependency edge out of the foundational runtime module.

### 7.4 `Std.Regex.Proof`

Change `lib/std/regex_proof.cure` to import `Std.Regex.Core` and
`Std.Regex.Runtime`, never `Std.Regex`.

All theorem declarations remain semantically unchanged unless a moved owner
requires a qualified name update. Proof owns:

- execution views and uniqueness laws;
- acceptance path projections and embeddings;
- concat, group, alternate, and repeat certificates;
- verified full/prefix parsers;
- proof-directed extraction and soundness lemmas.

Proof must use explicit qualified Core/Runtime names where ambiguity would
otherwise make canonical ownership unclear. Do not add a `use Std.Regex`
bridge to retain old names.

### 7.5 `Std.Regex.Language`

Change `lib/std/regex_language.cure` to import Core, Runtime, and Proof.
It must not import the façade. Its denotation and completeness declarations
must refer to Core's canonical type families and Runtime's canonical execution
functions. Proof calls remain explicit and are not replaced with unchecked
runtime calls.

### 7.6 `Std.Regex` compatibility façade

Retain `lib/std/regex.cure` as module `Std.Regex`, but reduce it to:

- explicitly reviewed typealiases to Core families;
- explicitly reviewed constructor/function wrappers for the existing public
  surface;
- verified parse/search/split entry points that delegate to Runtime and Proof;
- compatibility metadata, docs, and source provenance.

The façade must not be imported by Core, Runtime, Proof, or Language. Do not
assume that a lexical `use` re-exports a name. For each inventory entry, either
write an explicit alias/wrapper or mark it intentionally removed with a
diagnostic and migration note.

Wrappers must preserve:

- argument order and plicity;
- erased versus relevant quantities;
- return indices and reducibility metadata;
- source-level constructor names where supported;
- totality and purity classification;
- BEAM-visible exports for runtime functions.

The façade is allowed to be thin even when it has many declarations. Its
purpose is API compatibility, not to be a second implementation.

### 7.7 Canonical owner migration

Moving an inductive family changes its canonical owner from, for example,
`Std.Regex#Pattern` to `Std.Regex.Core#Pattern`. This is a semantic identity
change unless Cure's transparent typealias mechanism proves otherwise. It
must not be hidden behind a passing surface test.

Before implementation, add a compiler test that records the normalized owner
of a typealias target and checks the behavior of `Equivalent`, conversion,
constructor lookup, interface loading, and emission. Then choose one of these
reviewed outcomes:

1. **Transparent migration (preferred if verified):**
   `Std.Regex.Pattern(shape)` is a transparent alias for
   `Std.Regex.Core.Pattern(shape)`, and all internal references canonicalize to
   Core. The test must prove no duplicate nominal family is registered.
2. **Owner-preserving migration:** retain the family in `Std.Regex` and move
   only the proof-independent implementation behind another module. This is
   acceptable only if the resulting graph is still one-way and the public
   owner remains canonical.
3. **Versioned break:** if neither is sound, stop the split, document the
   owner change, update every dependent interface and fixture deliberately,
   and do not claim source compatibility.

The implementation must not copy an inductive into Core and leave a second
same-named inductive in the façade. Duplicate families are a correctness bug,
not a compatibility technique.

### 7.8 Graph and W086 acceptance

After the split:

- the manifest must produce separate components for Core, Runtime, Proof, and
  Language unless another independently justified cycle exists;
- the Regex/Proof W086 must disappear;
- the reviewed Char/Literal/String W086 remains exactly as specified by the
  stabilization gate;
- the pipeline must not use an SCC-specific ordering exception to hide a new
  edge;
- clean builds with filenames reversed must still follow graph order;
- qualified availability must remain distinct from lexical `use` imports.

## 8. Phase 3 — dependent-constructor retry algorithm

This phase addresses the repeated nested constructor work left after the
revision-aware attempt cache. The canonical implementation authority is
`Cure.Elab.Elaborator.resolve_ctor_fields/13` and its direct helpers.

### 8.1 Existing behavior to preserve

The current algorithm correctly:

- separates explicit fields from implicit/erased slots;
- seeds implicit slots from the goal-pinned metavariables;
- instantiates field types against `params ++ fields`;
- defers fields whose types contain unresolved metavariables;
- retries deferred result-index equations;
- distinguishes rigid constructor clashes from solving-order failures;
- uses revision-aware attempt fingerprints;
- keeps the retry cache operation-local.

The new algorithm must preserve all of those semantics. It must not turn a
rigid mismatch into a blocked attempt or silently accept an unsolved field.

### 8.2 Explicit state

Replace the loose tuple arguments of the inner fixpoint with a private state
record containing:

```text
pending_fields       ordered queue of field positions
resolved_fields      position -> elaborated term
seed_fields          position -> original implicit metavariable/seed
field_types          position -> declared field type
prefix_view          persistent prefix representation
deferred_equations   ordered result-index equations
blocker_index        metavariable id -> waiting field positions
attempts             compact attempt key -> outcome
mctx                 current metavariable context
revision             current MetaCtx revision
progress             whether this round changed a solution
```

The state must be private to one constructor application. Never put it in a
process-global table.

### 8.3 Persistent prefix representation

`frame_prefix/5` currently rebuilds positions `0..i-1` with a comprehension,
`Map.get`, and `Enum.at` on every pending field and every sweep. Replace it
with a representation supporting:

- O(1) lookup of a prior field by position;
- O(1) append/update when a field resolves;
- O(i) materialization only when the final de-Bruijn frame is actually passed
  to `Subst.instantiate`, or an equivalent amortized bound;
- explicit preservation of seed placeholders for unresolved siblings;
- zonking under the current `mctx` without mutating a prior revision.

A tuple/array plus a resolved-bitset, or a persistent vector, is acceptable.
A mutable ETS table, process dictionary, or copied whole `Env` is not. The
implementation must document its complexity and include a counter for prefix
cells read and materialized.

### 8.4 Blocker-indexed wake list

When `try_infer_field_uncached/6` returns `:blocked`, record the exact
metavariable IDs returned by `field_blockers/2`. Add the field position to
`blocker_index[id]` and do not retry it during unrelated sweeps.

After any operation that changes `mctx`:

1. obtain the set of metavariables whose assignments changed, using a
   revision-delta API or a compact binding-change log;
2. union the waiting field positions for those IDs;
3. remove those positions from the wake index;
4. enqueue them in deterministic field-position order;
5. recompute their instantiated types and retry them at the new revision.

If the unifier cannot expose a binding delta, implement a local conservative
delta by comparing the compact meta assignment spine, not by rerunning every
field. A global revision increment alone is insufficient: it tells us that
something changed but not which blocked fields can benefit.

A field with no discoverable blocker remains on a bounded fallback queue. The
fallback must be counted and diagnosed; it cannot silently become a catch-all
retry loop. If the fallback queue exceeds the configured threshold, return a
structured elaboration diagnostic naming the constructor, field, and blocking
term rather than looping indefinitely.

### 8.5 Attempt key and stale-result rules

The compact attempt key must include:

```text
canonical constructor identity
field position
argument syntax fingerprint
instantiated field-type fingerprint after zonk
blocker metavariable IDs
MetaCtx revision (or an equivalent dependency revision)
local context fingerprint
```

A cached `blocked` result is reusable only when all dependency fields match.
A cached success may be reused only if its term and inferred type are valid in
the current context and no relevant meta assignment changed. A rigid failure
is never generalized into a reusable blocked result.

The cache stores compact terms and blocker metadata only. It does not store:

- `Env`;
- `Context` copies containing complete declaration tables;
- source ASTs unrelated to the attempt;
- serialized BEAM terms from a previous process;
- a result whose source interface hash is absent.

### 8.6 Fixpoint termination

The work-list terminates when one of these holds:

1. all explicit fields are resolved;
2. a rigid error is returned;
3. the pending queue is empty and deferred equations cannot discharge;
4. no assignment, deferred-equation discharge, or blocker wake occurred in a
   complete round.

Case 4 returns the existing structured `unsolved_field_type` or
`unsolved_index` error with enhanced context. It must not retry indefinitely.

The deterministic order is:

1. fields woken by changed blockers, ascending position;
2. newly concrete fields, ascending position;
3. deferred result-index equations, source/declaration order;
4. conservative fallback fields, ascending position.

This order is part of reproducibility and must be pinned by a test that runs
the same constructor with different source declaration orderings.

### 8.7 Diagnostics

When the fixpoint fails, include:

- canonical constructor owner/name and arity;
- field position and source span;
- the surface argument and its span;
- instantiated field type before and after zonk;
- expected constructor result family/index;
- inferred argument type when available;
- blocker metavariable IDs and their current assignments;
- revision and attempt count;
- the originating declaration and macro provenance.

Do not report only “invalid constructor” or “unsolved index”. The new fields
are additive diagnostic context and must pass the existing fingerprint
deduplication rules.

### 8.8 Constructor regressions and properties

Add focused red/green tests for:

- a nested `Witnessed` constructor whose second field solves the first field's
  index;
- the same constructor with fields reversed;
- a field blocked on one metavariable while an unrelated sibling changes;
- a rigid constructor-family mismatch;
- a computed index such as `add(m1, m2) = S(Z)`;
- recursive constructor arguments;
- erased and relevant implicit fields together;
- repeated attempts at the same revision;
- a new revision invalidating a blocked result;
- declaration-order independence.

At least one test must assert the semantic result and another must assert the
counter relationship: after blocker indexing, unrelated revisions do not
increase the blocked field's attempt count.

## 9. Phase 4 — narrow normalization and elaboration reuse (conditional)

This phase is allowed only if the post-split, post-retry profile still shows
one normalization operation dominating a named declaration. It must not be
implemented speculatively.

### 9.1 Candidate cache boundary

The only initially permitted candidates are:

- contextual WHNF/NF of a single Core term;
- a single constructor field-type instantiation;
- a single immutable type-level reducer result.

Every entry must be keyed by:

```text
term fingerprint
reduction mode and fuel
local context fingerprint
relevant interface/source hash
MetaCtx dependency revision
transparency/reducibility policy
```

The result must be a compact Core term plus the dependency set that justified
it. Reuse is rejected if any dependency revision changed.

### 9.2 Scope and lifetime

The first implementation is request-local and bounded. It is cleared after
the declaration or component request. A persistent cache is a separate future
design requiring source/dependency hash invalidation and a published artifact
format; it is not part of this spec.

### 9.3 Measurement gate

Before and after adding the cache, collect three serialized cold samples and
three warm samples. The cache is rejected if any of these occur:

- cold median increases by more than 3%;
- resident memory or swap activity materially increases;
- a cache hit changes a diagnostic, source span, canonical identity, or
  totality result;
- the cache's hit rate is below the threshold that explains its overhead;
- the cache requires serializing a complete environment or context.

If the profile does not justify the cache, remove it rather than keeping a
complexity debt “for future builds.”

## 10. Tests and verification gates

Every implementation phase must pass the focused gate before the next phase.

### 10.1 Focused compiler tests

- canonical module manifest/dependency-edge tests;
- interface idempotence and source-hash invalidation tests;
- transparent typealias/canonical-owner tests;
- constructor retry and blocker wake-list tests;
- structured diagnostics tests;
- emission closure tests proving every reachable key resolves to a body or
  legitimate extern;
- incremental build tests with unchanged Core/Runtime and changed Proof;
- declaration-order independence tests.

### 10.2 Regex tests

- all existing dependent Regex tests;
- full/prefix/search/split behavior tests;
- bounded NFA property tests;
- proof extraction and erasure tests;
- language soundness/completeness tests;
- generated BEAM smoke tests for façade wrappers;
- API inventory compatibility tests.

### 10.3 Pipeline gates

Run serially, in this order:

1. focused Elixir tests for the changed subsystem;
2. focused Cure Regex fixtures;
3. `./scripts/check-canonical-module-pipeline --full`;
4. `MIX_ENV=test mix cure.check.stdlib`;
5. TCB, totality, erasure, and relevant Antigen assays;
6. `MIX_ENV=test mix cure.check.examples`;
7. doc-fence tests with `CURE_SKIP_DOC_FENCES` unset;
8. full `MIX_ENV=test mix test`;
9. Unix/escript smoke tests.

The full gate must report no E101, no bare unresolved closure key, no
unexpected W086, and no compiler warnings beyond the two reviewed SCCs.

## 11. Benchmark acceptance report

For each phase, record:

```text
commit or working-tree revision
source-universe hash
three cold totals and median/range
three warm totals and median/range
Regex component medians
largest ten declaration stages
constructor counters
normalization counters
totality/SCC counters
memory/swap observation
W086 membership
test-gate result
```

The report must distinguish:

- total wall time;
- module-check wall time;
- typed-elaboration time;
- kernel-check time;
- totality/certificate time;
- manifest, expansion, and publication time.

A speedup claim is invalid if only a single declaration gets faster while
component or total cold time remains within host noise. Conversely, a
component split is still useful if the total is noisy but the dependency graph
and declaration-stage report prove that the expensive SCC body re-elaboration
has been removed; the report must state that result without overstating the
wall-clock gain.

## 12. Implementation order and commit boundaries

The eventual implementation should be split into independently revertible
changes:

1. benchmark/event schema and red performance assertions;
2. request-local prepared-declaration reuse;
3. Core/Runtime source extraction with no Proof changes;
4. Proof and Language import migration;
5. façade wrappers and canonical-owner compatibility tests;
6. graph/W086 and incremental-build fixes;
7. constructor persistent-prefix state;
8. blocker-indexed wake list;
9. optional narrow normalization cache, only if justified;
10. baseline/report updates and final stabilization gate.

Each boundary must compile and test on its own. Do not combine a source split,
an elaborator algorithm change, and a proof rewrite in one unreviewable patch.
The user, not the agent, performs commits.

## 13. Rollback and failure handling

Rollback the current phase if any of the following occurs:

- a public Regex type acquires a second nominal owner;
- a proof or runtime function becomes opaque or unchecked;
- an emission closure contains a bare key;
- an existing structured diagnostic loses context;
- a new W086 component appears;
- clean-build semantics differ from warm-build semantics;
- the retry work changes which declaration succeeds without a corresponding
  kernel-checked term;
- cold memory pressure or swap activity increases materially;
- the benchmark target is missed and the profile does not identify a concrete
  next bottleneck.

The stashed whole-environment cache remains available only as a recoverable
historical artifact. Do not apply it during rollback or use it as a baseline.

## 14. Definition of done

This remediation is complete when all of the following are true:

1. The Regex module graph is one-way and the old Regex/Proof W086 is gone.
2. `Std.Regex` remains a tested compatibility façade, or an intentional API
   break is documented and accepted.
3. Canonical owners, aliases, constructor identities, and emission roots are
   stable and tested.
4. Constructor field resolution uses revision-aware blocker wake-ups and an
   incremental prefix representation, with no catch-all deferral.
5. Any normalization cache is narrow, request-local, dependency-keyed, and
   supported by measurements; otherwise it is absent.
6. The full diagnostic payload is present for constructor and emission
   failures.
7. The full compiler, Regex, TCB, totality, Antigen, doc-fence, and smoke gates
   pass.
8. Three serialized cold samples show the target reduction in the combined
   Regex components, while three warm samples show no more than the allowed
   regression.
9. The performance baseline document records the new measurements, operation
   counts, W086 policy, and any remaining dominant declaration.

Only after this definition of done should further Regex theorem work or a
MetaM-like reflective tier be scheduled.

# Unified Artifact Integrity Sweep

**Status:** implemented  
**Date:** 2026-07-30  
**Scope:** all Cure-generated BEAM artifacts: standard library, projects,
dependencies, bundled `priv/ebin`, `$CURE_HOME`, tests, documentation examples,
examples, escripts, and releases.

## Summary

Cure must never load, link, copy, publish, or treat a generated BEAM as fresh
unless the BEAM belongs to a completely verified artifact set.

The current incremental compiler hashes source, interfaces, the compiler
toolchain, and an external stdlib fingerprint. It still considers an output
fresh when the expected BEAM filename merely exists. The preload layer then
loads matching BEAMs without consulting the build manifest. Consequently, a
valid but old BEAM, a corrupt BEAM, or a BEAM produced by an interrupted build
can survive under the expected filename and reach runtime.

This specification replaces those partial checks with one content-addressed
artifact sweep shared by compilation, preload, testing, bundling, and
deployment.

## Relationship to the incremental compilation design

This specification extends and partially supersedes
`2026-07-18-incremental-compilation-design.md`.

The earlier design remains authoritative for:

- source-content hashing;
- interface-level dependency invalidation;
- dependency-first compilation order;
- ambient prelude dependency propagation;
- removal of deleted modules;
- fail-safe handling of malformed manifests.

This specification supersedes its assumptions that:

- BEAM existence is sufficient output validation;
- preload completeness checks are an adequate integration backstop;
- bundling may retain an independent mtime-based freshness policy;
- stdlib artifact integrity is outside project incremental compilation;
- an atomic manifest write alone makes the output set atomic.

## Motivating failure

`Cure.Std.Semigroup.beam` existed at the expected path and therefore passed the
incremental compiler's output-presence check. The BEAM did not contain the
current generated List implementation:

```text
__impl_Semigroup_Std.List#List_combine/2
```

A consumer compiled successfully and emitted a remote call to that function.
Runtime then failed with `UndefinedFunctionError`.

A fresh isolated compilation of `Std.Semigroup` produced the function and made
the same program return `[1, 2, 3, 4]`. The source and code generator were
correct; artifact freshness was not.

This class of failure must be rejected or repaired before code loading. It must
never surface as an undefined function in a consumer.

## Goals

1. Verify every generated artifact by content, identity, and provenance.
2. Compute freshness for an entire artifact set in one sweep.
3. Use the same verifier in every producer and consumer.
4. Preserve interface-level incremental recompilation.
5. Publish builds atomically.
6. Detect missing, corrupt, swapped, copied, obsolete, and orphaned BEAMs.
7. Make every rebuild or rejection explainable with a structured reason.
8. Make a no-change sweep fast enough to run before every load.
9. Eliminate mtime and filename presence as correctness signals.
10. Fail closed when verification cannot be completed.

## Non-goals

- Authenticating releases against a remote publisher. This design provides
  local integrity, not package signing.
- Per-consumed-symbol invalidation.
- Reproducible BEAM bytes across different OTP releases.
- Preserving manifest version 1. Version 1 is treated as stale and rebuilt.
- Loading arbitrary unmanifested Cure BEAMs by default.

## Core invariant

> A Cure-generated BEAM may be used only after the artifact sweep proves that
> its bytes, module identity, provenance, build context, and manifest entry all
> agree.

The invariant applies before:

- `:code.load_binary/3`;
- `:code.ensure_loaded/1` for Cure-generated modules;
- code generation links to a dependency;
- a BEAM is copied into a bundle;
- a test marks stdlib modules sticky;
- an escript or release is published.

## Terminology

### Artifact set

A complete collection of outputs produced together for one purpose, such as:

- the standard library;
- one project;
- one dependency package;
- a bundled standard library;
- a packaged release.

An artifact set has one manifest and one generation identity.

### Generation

A generation is a complete, immutable artifact set identified by a Merkle-style
root hash derived from its build context, module records, and artifact hashes.

### Build context

Every non-source input capable of changing emitted interfaces or BEAMs:

- compiler bytecode;
- language edition;
- target backend;
- code-generation options;
- OTP and Elixir versions;
- feature flags;
- dependency generations.

### Sweep

The single operation that discovers inputs and outputs, validates them, derives
the dirty set, repairs it when allowed, revalidates the result, and publishes a
complete generation.

## Architecture

Add one subsystem:

```text
Cure.Compiler.Artifacts
Cure.Compiler.Artifacts.Manifest
Cure.Compiler.Artifacts.Sweep
Cure.Compiler.Artifacts.Provenance
Cure.Compiler.Artifacts.Writer
Cure.Compiler.Artifacts.Lock
```

Responsibilities:

- `Artifacts`: public API and policy selection;
- `Manifest`: schema, deterministic encoding, decoding, and root hashing;
- `Sweep`: discovery, verification, dirtiness, and dependency propagation;
- `Provenance`: reads and writes Cure metadata in BEAM files;
- `Writer`: staging and atomic publication;
- `Lock`: serializes writers for an output set.

No other module decides freshness independently.

## Public API

```elixir
Artifacts.sweep(
  kind: :stdlib,
  source_roots: ["lib/std"],
  output_dir: "_build/cure/ebin",
  repair: true
)
```

Result:

```elixir
{:ok,
 %Artifacts.Result{
   generation: <<...>>,
   fresh: ["Std.List"],
   rebuilt: %{
     "Std.Semigroup" => [:artifact_hash_mismatch]
   },
   removed: %{
     "Cure.Std.Obsolete.beam" => :orphan
   },
   manifest_path: "_build/cure/ebin/.cure_manifest"
 }}
```

Read-only validation:

```elixir
Artifacts.open_verified_set(
  kind: :stdlib,
  candidates: Cure.Stdlib.Paths.beam_dirs()
)
```

Packaged validation:

```elixir
Artifacts.verify!(manifest_path, source_roots: :unavailable)
```

## Manifest version 3

The manifest is deterministic data encoded with
`:erlang.term_to_binary(term, [:deterministic])`.

```elixir
%{
  version: 3,
  kind: :stdlib,
  workspace_key: <<sha256>>,
  input_snapshot: <<sha256>>,
  artifact_digest: <<sha256>>,
  validated_at: 1_785_000_000,
  context: %{
    compiler_hash: <<sha256>>,
    language_edition: "0.34",
    otp_release: "29",
    elixir_version: "1.20.1",
    target: :beam,
    codegen_options_hash: <<sha256>>,
    source_roots_hash: <<sha256>>
  },
  dependencies: %{
    stdlib: nil,
    packages: %{}
  },
  expected_modules: ["Std.Core", "Std.Semigroup", ...],
  modules: %{
    "Std.Semigroup" => %{
      source: %{
        path: "lib/std/semigroup.cure",
        sha256: <<sha256>>,
        stat: %{device: {1, 0}, inode: 42, size: 900, mtime: 1, ctime: 1}
      },
      interface_hash: <<sha256>>,
      edges: %{
        compile_order: ["Std.Core"],
        interface: ["Std.Core", "Std.List"],
        runtime: ["Std.Core", "Std.List"]
      },
      artifacts: [
        %{
          path: "Cure.Std.Semigroup.beam",
          module: "Cure.Std.Semigroup",
          sha256: <<sha256>>,
          size: 4824,
          stat: %{device: {1, 0}, inode: 43, size: 4824, mtime: 1, ctime: 1},
          exports_hash: <<sha256>>,
          provenance_hash: <<sha256>>,
          producer_snapshot: <<sha256>>
        }
      ]
    }
  }
}
```

The identities have one job each:

- `workspace_key` hashes configuration that cannot change within an
  incremental workspace;
- `input_snapshot` hashes exact source content and dependency artifact digests;
- `artifact_digest` seals the semantic final manifest and names the immutable
  artifact directory. It deliberately excludes `validated_at` and nested
  `stat` records: those are verification memoization metadata, not content
  identity.

An interface-stable reused BEAM retains the `producer_snapshot` that produced
its bytes. Version-2 manifests are stale and rebuilt, not migrated.

## Compiler fingerprint

The compiler hash must cover every compiled Cure application module capable of
affecting parsing, elaboration, interfaces, erasure, or code generation.

The implementation embeds a deterministic hash of every Cure compiler source
file plus `mix.exs` and `mix.lock`. Those paths are compiler external resources,
so changing any of them recompiles the fingerprint owner. This works identically
under Mix and in the standalone escript, where `Mix.Project` and ordinary paths
to embedded BEAMs are unavailable. It does not use a curated semantic allowlist;
over-invalidation is acceptable, while missing a compiler input is not.

Generated Cure stdlib BEAMs are not inputs and therefore cannot make the
compiler fingerprint self-referential.

The context also separately records:

- language edition;
- target backend;
- normalized compiler options;
- OTP release;
- Elixir version.

An incompatible context mismatch dirties the complete artifact set.

## BEAM provenance

Every Cure-generated BEAM carries a custom attribute or chunk:

```elixir
%{
  format: 1,
  module: "Std.Semigroup",
  source_hash: <<sha256>>,
  interface_hash: <<sha256>>,
  compiler_hash: <<sha256>>,
  producer_snapshot: <<sha256>>
}
```

The BEAM does not contain its own final SHA-256 because that would be recursive.
The external manifest records the final content hash.

Verification requires:

1. the BEAM can be decoded by `:beam_lib`;
2. its declared module equals the manifest's module;
3. its content hash equals the manifest hash;
4. its size equals the manifest size;
5. its provenance equals the manifest provenance;
6. its embedded producer snapshot equals its artifact record (reused artifacts
   may predate the enclosing input snapshot);
7. its export table hash equals the manifest export hash.

The export check produces a precise diagnostic for failures such as the missing
Semigroup implementation. It is not a substitute for the full content hash.

## Unified sweep algorithm

### Phase 1: discovery

1. Normalize source roots and output directory.
2. Acquire the artifact-set writer lock when `repair: true`.
3. Discover all source modules through `DepGraph`.
4. Discover every generated BEAM in the artifact-set directory.
5. Load manifest version 3.
6. Treat missing, corrupt, or older manifests as an empty manifest.

### Phase 2: hash inputs once

Compute and memoize for this sweep:

- compiler context hash;
- each source content hash;
- each dependency artifact digest;
- each existing BEAM content hash;
- each BEAM identity, exports, and provenance.

No later subsystem repeats this work. The sweep result is passed to compilation,
preload, bundling, or testing.

### Phase 3: classify artifacts

Each module receives zero or more reasons:

```elixir
:new_module
:source_hash_mismatch
:compiler_context_mismatch
:dependency_artifact_digest_mismatch
:beam_missing
:beam_unreadable
:beam_module_mismatch
:artifact_hash_mismatch
:artifact_size_mismatch
:exports_hash_mismatch
:provenance_mismatch
:producer_snapshot_mismatch
:manifest_entry_invalid
```

Every discovered BEAM absent from the expected manifest and source graph is an
orphan.

### Phase 4: derive dirty closure

Separate validation from invalidation:

- Any invalid artifact dirties its producer.
- A source change dirties its producer.
- A compiler context change dirties the complete set.
- A dependency interface change dirties compile-time consumers.
- A runtime-only dependency implementation change rebuilds the producer but
  does not rebuild consumers when their linked ABI is unchanged.
- A missing dependency generation rejects or repairs the dependency before
  consumers are considered.

Dependency propagation uses the existing closure dependency graph, including
ambient prelude providers.

### Phase 5: repair

When `repair: true`:

1. compile dirty modules in dependency order into staging;
2. copy or hard-link verified fresh artifacts into staging;
3. recompute interfaces for rebuilt modules;
4. propagate actual interface changes;
5. compile newly dirtied dependants;
6. omit orphaned artifacts;
7. construct the candidate manifest.

When `repair: false`, return all validation failures without changing disk.

### Phase 6: complete-set verification

Before publication, repeat artifact verification against the candidate manifest.
Publication is forbidden unless:

- every expected source has a module record;
- every module record has every expected artifact;
- every artifact passes all integrity checks;
- there are no unclaimed Cure-generated BEAMs;
- every dependency generation is available and verified;
- the manifest root recomputes exactly.

### Phase 7: publication

Publish the complete generation atomically, then release the lock.

## Atomic publication

The target layout becomes:

```text
_build/cure/
  generations/
    <artifact-root-id>/
      .cure_manifest
      Cure.Std.Core.beam
      Cure.Std.List.beam
      ...
  current
```

`current` is an atomically replaced pointer or symlink to one immutable
generation.

Publication:

1. create a uniquely named staging generation;
2. populate it completely;
3. verify it;
4. write its manifest;
5. atomically rename staging to its final generation name;
6. atomically replace `current`.

An interrupted build leaves an unpublished staging directory. Readers continue
using the previous verified generation.

If generation directories cannot land in the first implementation, the
temporary compatibility path writes every BEAM atomically and writes the
manifest last. The generation layout remains the required end state.

## Locking

Only one process may publish to an artifact set.

The lock records:

- PID;
- host;
- start time;
- output directory;
- intended generation.

A competing writer waits, then reruns the sweep after the first writer
publishes. It does not trust the first writer's planned result.

A stale lock may be reclaimed only after proving that its owner no longer
exists. Lock timeout produces a structured operational diagnostic.

## Standard-library compilation

`mix cure.compile_stdlib` becomes:

```elixir
Artifacts.sweep(
  kind: :stdlib,
  source_roots: ["lib/std"],
  output_dir: configured_output,
  repair: true
)
```

The task no longer has an independent definition of freshness.

The stdlib manifest records:

- all stdlib source hashes;
- all stdlib interface hashes;
- every generated BEAM and lifted module;
- compiler context;
- complete stdlib generation.

## Project compilation

Project manifests record:

- project module records;
- verified stdlib generation;
- verified dependency-package generations;
- exact imported interface hashes.

A changed stdlib generation does not blindly rebuild the project. The sweep
compares imported interface hashes:

- unchanged interfaces: validate runtime dependencies, retain consumers;
- changed interfaces: rebuild affected consumers and their dependants.

The first implementation may conservatively rebuild all project modules on any
stdlib generation change. It must not skip validation.

## Preload and module lookup

`Cure.Stdlib.Preload` must stop selecting and loading individual BEAMs directly.

It asks the artifact subsystem for a verified set:

```elixir
Artifacts.open_verified_set(
  kind: :stdlib,
  candidates: Cure.Stdlib.Paths.beam_dirs()
)
```

Candidate selection rules:

1. validate candidates in configured priority order;
2. choose the first complete verified set;
3. never combine BEAMs from different directories;
4. never silently fall through from one corrupt module to another directory;
5. report why rejected candidates were invalid.

Development and tests may use `repair: true` when sources are available.
Packaged installations without sources fail with a corruption diagnostic.

There is no default unverified fallback.

## Test integration

`test/test_helper.exs` performs one stdlib sweep:

```elixir
Artifacts.sweep(kind: :stdlib, repair: true)
```

It then loads and sticks modules from the returned verified generation.

The current unconditional task invocation, declared-versus-loaded scan, and
filename-presence checks are replaced by the sweep result. Stickiness remains a
runtime isolation mechanism after verification.

Focused `mix test path/to/test.exs` should pay:

- one fast content sweep on a clean tree;
- compilation only for dirty modules;
- no repeated stdlib compilation during the same invocation.

## Bundles, escripts, and releases

Bundling consumes a verified artifact set rather than scanning a directory.

It:

1. opens the verified source generation;
2. copies exactly the manifest-listed files;
3. recomputes content hashes after copying;
4. emits a bundle manifest;
5. verifies the destination;
6. publishes only the verified bundle.

The existing mtime-based `cure.bundle_stdlib_beams` freshness path is removed.

Packaged `priv/ebin`, escripts, releases, and `$CURE_HOME` installations carry
the same manifest format.

## Orphan handling

An artifact under the artifact-set namespace is an orphan when:

- no current source owns it;
- no current manifest record claims it;
- it belongs to an obsolete lifted module;
- a module was renamed.

Repair mode excludes orphans from the next generation. It may delete old
orphans only after the new generation is published.

Read-only mode rejects an artifact set containing orphans. It never loads them.

## Performance and verification modes

Content hashes remain authoritative. Stat metadata is only a memoization key.

`verification: :cached` may reuse a recorded hash when canonical path, device,
inode, size, mtime, and ctime all match and both timestamps are strictly older
than the manifest's filesystem timestamp fence. The fence comes from a sentinel
file on the artifact filesystem, never the wall clock. Ambiguous or newly
written timestamps force hashing.

`verification: :full` always reads and hashes every artifact. Full verification
is mandatory before publication, copying, bundling, escript creation, and
release packaging. Results report computed and reused hash counts.

## Diagnostics

Freshness failures use structured reasons.

Example:

```text
-- STALE STANDARD LIBRARY ------------------------------------------------------

Cure.Std.Semigroup.beam does not match the current standard-library manifest.

Expected generation: 7a31…
Found provenance:    29bc…
Reason:              BEAM content hash differs

Cure will rebuild Std.Semigroup before loading it.
```

Packaged corruption:

```text
The installed Cure standard library is incomplete or corrupted.
Reinstall Cure from a verified distribution.
```

Verbose builds print one or more machine-readable reasons for every rebuilt
module.

## Security properties

This design provides integrity against accidental staleness, corruption, and
artifact mixing.

It does not establish publisher authenticity. A malicious actor able to replace
both the manifest and every BEAM can produce a self-consistent artifact set.
Package signing is a separate feature.

## Adversarial test matrix

Every scenario below must begin as a failing regression.

### Artifact corruption

- missing BEAM;
- zero-byte BEAM;
- random bytes;
- truncated valid BEAM;
- valid BEAM for another module;
- valid old BEAM under the expected filename;
- modified BEAM with preserved size and mtime;
- current BEAM paired with an old manifest;
- current manifest paired with an old BEAM;
- missing generated export;
- mismatched provenance chunk.

### Input and context changes

- source changed;
- compiler parser changed;
- compiler elaborator changed;
- erasure changed;
- code generator changed;
- language edition changed;
- codegen option changed;
- OTP release changed;
- stdlib generation changed;
- dependency generation changed.

### Dependency propagation

- dependency interface changed;
- dependency implementation changed but interface stayed stable;
- ambient prelude provider changed;
- qualified runtime dependency artifact became corrupt;
- dependency generation missing;
- dependency artifact set partially valid.

### Manifest failures

- absent manifest;
- corrupt binary;
- unsupported version;
- false artifact hash;
- false root hash;
- duplicated artifact ownership;
- module record missing an expected lifted BEAM;
- manifest contains a path outside its artifact root.

### Publication and concurrency

- interrupted before any staged output;
- interrupted after one staged BEAM;
- interrupted after candidate manifest write;
- interrupted before replacing `current`;
- two simultaneous sweeps;
- stale writer lock;
- reader during publication;
- failed rebuild preserves the previous generation.

### Discovery and packaging

- orphan from a renamed module;
- first candidate directory is incomplete;
- second candidate directory is valid;
- two candidates contain different generations;
- packaged release has no source tree;
- bundled copy is corrupted after copying;
- `$CURE_HOME` contains an old valid generation.

### Named regression

```elixir
test "a stale Semigroup beam cannot be loaded as fresh" do
  # Install a valid older Cure.Std.Semigroup BEAM that lacks:
  # __impl_Semigroup_Std.List#List_combine/2
  #
  # The sweep must rebuild it when sources are available, or reject the
  # artifact set before preload when they are not.
end
```

## Rollout

### Phase 1: manifest version 2

- Add schema and deterministic root hashing.
- Add per-BEAM hashes, identities, export hashes, and provenance.
- Treat version 1 as stale.
- Add read-only verification.

### Phase 2: unified sweep

- Move dirty classification into `Artifacts.Sweep`.
- Reuse existing interface invalidation and dependency ordering.
- Add structured reasons and orphan detection.
- Route incremental compilation through the sweep.

### Phase 3: standard library

- Route `mix cure.compile_stdlib` through the sweep.
- Add the Semigroup stale-BEAM regression.
- Replace test startup freshness logic.

### Phase 4: atomic generations

- Add staging generations.
- Add output locks.
- Publish via atomic `current` replacement.
- Preserve the last verified generation on failure.

### Phase 5: preload and paths

- Validate whole candidates.
- Stop loading individual unmanifested BEAMs.
- Stop combining directories.
- Add packaged corruption diagnostics.

### Phase 6: projects and dependencies

- Record stdlib and package generations.
- Validate imported interfaces.
- Propagate interface changes precisely.

### Phase 7: bundles and releases

- Remove mtime-based bundle freshness.
- Copy verified generations.
- Ship manifests in every distribution layout.

### Phase 8: delete legacy paths

Remove:

- filename-presence freshness checks;
- mtime-only freshness decisions;
- direct preload directory scans;
- independent stdlib and bundle hash policies;
- unverified fallback loading;
- manifest version 1 writers.

## Acceptance criteria

The work is complete when:

1. No Cure-generated BEAM is loaded without artifact-set verification.
2. Every source, compiler, option, dependency, and output-byte change is
   detected.
3. A same-name stale BEAM is never considered fresh.
4. An invalid build is never published.
5. A failed repair leaves the previous verified generation usable.
6. Tests perform one clean sweep and compile only dirty modules.
7. Preload chooses one complete generation and never mixes directories.
8. Bundles use the same manifest and verifier as development.
9. Repeated no-change sweeps perform no compilation.
10. Every rebuild and rejection has a structured reason.
11. The Semigroup failure is caught before runtime.
12. All adversarial tests above pass.

## Verification gates

Focused:

```sh
MIX_ENV=test mix test test/cure/compiler/artifacts
MIX_ENV=test mix test test/mix/tasks/cure.compile_stdlib_incremental_test.exs
MIX_ENV=test mix test test/cure/stdlib/preload_test.exs
MIX_ENV=test mix test test/mix/tasks/cure.bundle_stdlib_beams_test.exs
```

Integration:

```sh
MIX_ENV=test mix compile --warnings-as-errors
MIX_ENV=test mix test test/cure/elab/semigroup_concat_test.exs
MIX_ENV=test mix test
mix cure.compile_stdlib
mix cure.compile_stdlib
git diff --check
```

The second `mix cure.compile_stdlib` must report zero compiled modules and a
verified unchanged generation.

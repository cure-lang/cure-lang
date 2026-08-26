# Incremental Cure Compilation

**Status:** design approved, pending implementation
**Date:** 2026-07-18
**Scope:** a general compiler feature (stdlib builds, project builds, and the
test harness that drives them), not a test-only optimization.

## Problem

Every multi-file Cure compile recompiles all modules unconditionally.
`mix cure.compile_stdlib` rebuilds all 81 stdlib modules (~7.5s including the
escript step) on every invocation regardless of what changed, and
`mix cure.compile <dir>` (project builds) does the same over a project's
sources. Because `test/test_helper.exs` runs the stdlib task at the start of
every `mix test`, this fixed cost is also paid on every single-file test run.

The previous "optimization" was a presence check on a sentinel beam. It was
removed because presence cannot notice that a *source changed* since its beam
was built, so it produced ordering-dependent test flakes from stale beams
(`test_helper.exs:17`). Correctness — never serving a stale beam — is the
non-negotiable constraint; speed must not reintroduce that hole.

## Goal

Recompile a module only when its output could actually differ from what is on
disk. Concretely, recompile module `M` iff:

1. `M`'s **source content** changed, or
2. any of `M`'s **output beams is missing**, or
3. any **direct dependency's interface** changed in this build, or
4. the **compiler itself** changed (invalidates everything).

This is interface-level (Swift-style) invalidation: a change confined to a
module's private internals recompiles that module alone; only a change to what
consumers actually elaborate against cascades to dependents.

## Why interface-level is both cheap and sound here

The elaborator already produces, per module, the exact artifact consumers
compile against. `Cure.Elab.Program.compute_module_interface/2`
(`program.ex:1500`) returns a map that already contains a `source_hash` and an
`export_env` — the elaborated environment a consumer merges in when it imports
the module (`load_dependency_env` → `merge_env`, `program.ex:1508-1511`).

Two facts make `export_env` the *complete* channel by which a dependency
affects a consumer's compilation:

- **Cross-module inlining travels inside it.** Inline hints are registered into
  the env via `Env.register_inline_hint` (`mark_inline_hints/2`,
  `program.ex:1740`), so they are part of `export_env`, not a side channel. (This
  is a fixed, compiler-owned hint table for two prelude modules — `Std.Bool`'s
  connectives and `Std.Sigma`'s projections, `@inline_hints`, `program.ex:1725` —
  not a general user-facing inlining feature; any change to the table itself is
  a compiler change and is caught by the `toolchain` hash below.)
- **Codegen does not read dependency beam *content* for compilation decisions.**
  There is no `:code.get_object_code`, `:beam_lib`, or beam-content inspection
  anywhere in the compiler; codegen works from the elaborated environment
  (`dependent_codegen/1` → `check_ast_with_locals/1` + `Emit.compile_forms/3`,
  `compiler.ex:408-420`). Two beam-*existence* (not content) interactions exist
  and are deliberately narrower than a content dependency: (1)
  `Cure.Elab.Program.validate_stdlib_imports/1`, run immediately before
  `dependent_codegen` (`compiler.ex:324`), calls `:code.ensure_loaded/1` per
  `use`d **stdlib** import as an existence gate, not a content read — its only
  failure mode (beam missing/unloadable) is already covered by invariant #2
  below. (2) `Cure.Compiler.load_emitted/2` reads a `.beam` file to register it
  in the VM's code table for later execution, but it is called only from
  `Cure.Project.compile_all_files/6` and the `cure` CLI's build command —
  **not** from `Mix.Tasks.Cure.CompileStdlib` or `Mix.Tasks.Cure.Compile`, the
  two entry points this design routes through (`cure.compile_stdlib.ex` only
  adds `output_dir` to the code path once, up front, and relies on the code
  server's ordinary lazy load-by-path; `cure.compile.ex` calls neither).
  Neither interaction feeds beam content back into a codegen decision, so
  hashing `export_env` remains the complete channel for the two mix tasks this
  design changes.

Therefore hashing `export_env` is sound **by construction**: if two versions of
a dependency produce a byte-identical `export_env`, every consumer's compilation
input is provably identical, whatever the consumer used from it.

### A module's dependency set is bigger than its `use` imports

`export_env` is not limited to what a module explicitly `use`s. Every module
outside the prelude-bootstrap closure ambiently merges the *entire*
`@prelude`-marked manifest into its base env before its own declarations are
elaborated (`module_prelude_env` → `prelude_slice_env`, `program.ex:1547-1548`,
`624-641`) — that is the whole point of `@prelude`: a consumer gets the names
without writing `use`. `compute_module_interface`'s own dependency set reflects
this: `module_dependency_sources(ast) = prelude_sources_for(ast) ++ imports(ast)`
(`program.ex:1543-1546`), not `imports(ast)` alone.

`Cure.Compiler.DepGraph` already models exactly this distinction as two edge
kinds (see its moduledoc): **order-edges** — `use` only, exposed via
`order_deps_map/1` — and **closure-edges** — `use` + qualified-call targets +
`@prelude` providers, exposed via `closure_deps_map/1` (`finalize_node/4`
appends every scanned `@prelude`-provider module to every node's closure deps,
`dep_graph.ex:225-232`, detected via `prelude_decorated?/1`, `dep_graph.ex:210,
242-253`). The driver below must build its dirty-propagation graph from
`closure_deps_map/1`, not `order_deps_map/1` — the latter is `use`-only and
would silently fail to invalidate the (common) case of a module that consumes a
changed `@prelude` provider ambiently, which is exactly the stale-beam failure
this design exists to prevent.

`closure_deps_map/1` is a safe *superset* for this purpose, not a precise
match: it also includes qualified-call targets (e.g. a bare `Std.Foo.bar()`
call), which do not actually appear in `module_dependency_sources` and do not
flow into `export_env` (qualified calls lower syntactically, order-free, per
`DepGraph`'s own moduledoc). Treating them as dependency edges anyway only
over-invalidates — safe, never a missed change. Likewise, `closure_deps_map/1`
does not exempt prelude-bootstrap modules from listing other prelude providers
as dependencies the way the elaborator's `prelude_bootstrap?/1` check does (to
avoid manufacturing a cycle), so it can report edges among that small set of
bootstrap modules that elaboration itself never creates; because these are
*extra*, not missing, edges, and `DepGraph.toposort/2` is SCC-tolerant, this
can only coarsen invalidation within that small set, never miss a real change.

This sidesteps the trap that makes signature-based interface hashing *unsound*
in a dependently-typed language: a consumer's *types* can depend on a
dependency's *value/body* (e.g. `Vec(n)` where `n` is an exported definition),
so a signature hash would miss body changes that matter. An env hash cannot miss
them — the reduced/elaborated value is in the env.

### What is explicitly out of scope: per-consumed-symbol invalidation

Recompiling a consumer only when the *specific* symbols it uses from a
dependency change would require the elaborator to record a per-module *use-set*
(which env entries each module actually touched) and persist it. In a dependent
setting a single type-level reduction can transitively touch many definitions,
so a *complete* use-set is hard to capture without risking a missed dependency
(a stale beam). That is a separate elaborator-instrumentation project. This
design does not attempt it; the interface hash is per-module, not per-symbol.

## Design

### Fingerprints

- **`source_hash`** = `:crypto.hash(:sha256, source_bytes)`. Content-based, so it
  is stable across `git checkout`, `touch`, and mtime granularity, and changes
  only on a real edit. Already computed in `compute_module_interface`.

- **`interface_hash`** = `:crypto.hash(:sha256, :erlang.term_to_binary(export_env,
  [:deterministic]))`. The `:deterministic` flag gives a canonical encoding with
  stable map-key ordering. Computed only for modules actually (re)compiled this
  build; skipped modules reuse their stored hash.

  The `export_env` is obtained from the loader's interface computation, exposed
  as a new public `Cure.Elab.Program.module_interface/2`. This is **not** a
  second elaboration pass on the common paths: the loader already computes and
  caches each stdlib module's interface in `:persistent_term`
  (`cached_module_interface/2`, key `{Cure.Elab.Program, :module_interface,
  path}`) as a side effect of compiling that module's dependents. Computing
  `interface_hash(M)` immediately after M is recompiled primes exactly that
  cache, which M's dependents' compiles then hit — so the interface is elaborated
  once, not twice. The only genuinely extra elaboration is for a changed module
  whose dependents turn out *not* to need recompiling (interface unchanged);
  that is bounded by the number of changed modules and is the very case where
  incremental avoids a full dependent recompile, so it is a net win. Non-stdlib
  (project) sources are not `:persistent_term`-cached (they can change between
  runs), so a project build may elaborate a changed module's interface twice;
  project builds are smaller and less frequent, so this is accepted.

  **Serializability caveat.** `:erlang.term_to_binary` requires `export_env` to
  be a pure data term (no live closures/pids/refs). Cure Core terms are
  tuples/atoms/maps, so this is expected to hold, but the first implementation
  task must verify it on a real stdlib `export_env`. If it does not hold, the
  fallback is to hash a structural projection of the env (its def/family/ctor
  tables) rather than the whole struct — same soundness argument, narrower term.

- **`toolchain`** = an embedded content hash of the compiler's Elixir sources
  plus `mix.exs` and `mix.lock`, with paths and bytes encoded deterministically.
  Every input is an external resource of the fingerprint-owning module, so Mix
  recompiles it when an input changes. This representation is also available
  inside the standalone escript, where `Mix.Project` and filesystem paths to
  embedded BEAMs do not exist. Any real source or build-definition change
  changes the hash; a no-op touch does not.

The `toolchain` hash is stored once at the top of the manifest. A mismatch
against the current toolchain marks **every** module dirty (case 4 above),
because a compiler change can alter any beam. This matches the reality that
editing the elaborator invalidates the whole stdlib — correctly — and it is the
honest limit of the speedup: interface-level invalidation only avoids work
*within a fixed toolchain*.

The hash deliberately covers the **whole `:cure` application**, not a curated
"compiler-relevant" subset. That over-invalidates — editing an unrelated part of
the app (e.g. the REPL) also bumps the toolchain and rebuilds the stdlib — but
it is safe and needs no maintenance. A curated subset would be a fragile
allow-list that is easy to leave incomplete (a missed transitive dependency
would ship a stale beam), so the coarse-but-safe hash is the deliberate choice.

### Manifest

Stored alongside the output beams as `<output_dir>/.cure_manifest`, encoded with
`:erlang.term_to_binary/1` (no parser needed, fast). Shape:

```elixir
%{
  version: 1,                       # manifest schema version
  toolchain: <sha256 binary>,
  modules: %{
    "Std.List" => %{
      source_path: "lib/std/list.cure",
      source_hash: <sha256 binary>,
      interface_hash: <sha256 binary>,
      deps: ["Std.Core", ...],      # direct deps (use imports + ambient @prelude
                                     # providers), from DepGraph.closure_deps_map/1
      beams: ["Cure.Std.List.beam"] # every output file this source produced
    },
    ...
  }
}
```

Writes are **atomic**: serialize to `<output_dir>/.cure_manifest.tmp`, then
`File.rename/2` over the real path, so an interrupted build cannot leave a
half-written manifest. A manifest that is absent, unreadable, or fails to decode
to the expected shape/version is treated as empty → full rebuild (fail-safe:
the failure mode is *rebuild everything*, never *serve stale*).

### The incremental driver: `Cure.Compiler.Incremental`

A new module, the single place both mix tasks route through.

`compile_dir(source_paths, output_dir, opts) :: {:ok, summary} | {:error, ...}`

Steps:

1. **Scan** the sources with `Cure.Compiler.DepGraph.scan/1` + `order/1`, used
   only to report import cycles exactly as the current task does today (a real
   `use` cycle stays a reported error; it is unrelated to the synthetic
   `@prelude`-provider cycles noted in step 5 below, which are not errors) —
   and `closure_deps_map/1` (module → full dependency set: `use` imports +
   ambient `@prelude` providers), which step 5 walks via `toposort/2` for both
   the dirty-decision order and the compile order. Use `closure_deps_map/1`,
   **not** `order_deps_map/1`, for the dirty-propagation graph — see "A
   module's dependency set is bigger than its `use` imports" above for why the
   latter would miss ambient `@prelude` edges.

   **Unparseable sources are not silently dropped.** `closure_deps_map/1` (like
   `order_deps_map/1`) is keyed by resolved module name and skips any scanned
   node whose module could not be determined (`is_binary(m)` filter,
   `dep_graph.ex:108-120,156-162`) — which includes a file with a genuine parse
   error (`scan_file/1` leaves `module: nil` on a parse failure,
   `dep_graph.ex:181-194`). Module-name-keyed walking would therefore silently
   skip a broken `.cure` file rather than reporting it, unlike today's task,
   which iterates `order/1`'s *path*-keyed list and lets `compile_file` hit
   (and report) the same parse error again. The driver must keep every scanned
   path with an unresolved module as a forced compile target alongside the
   `closure_deps_map/1` walk (it has no interface/dependency tracking since it
   has no module name — it is not part of the dirty graph, only of the
   "must still attempt and report" set) and fail the build precisely when
   `compile_file` fails on it, matching today's behavior.
2. **Load** the manifest (or empty on miss/corruption).
3. **Toolchain check.** If `manifest.toolchain != current_toolchain`, every
   module is dirty; set `all_dirty = true` and continue to step 4, then step 5
   (every module still walked in the order below, so compilation itself stays
   ordered). Step 4 (deletions) is **not** skipped on a toolchain mismatch — a
   source deleted in the same build a compiler change lands must still have its
   stale beam and manifest entry removed, not left orphaned until some later
   build happens to reach step 4 again.
4. **Deletions, scoped to this run's source roots.** `Mix.Tasks.Cure.CompileStdlib`
   and `Mix.Tasks.Cure.Compile` **default to the same `output_dir`**
   (`_build/cure/ebin` — `cure.compile_stdlib.ex:27`, `cure.compile.ex:27`), so a
   project build's manifest can be the *same file* stdlib's manifest lives in.
   A project build's `source_paths` cover only the project's own tree, never
   `lib/std/*.cure` — so "no longer exists among the scanned sources," read
   literally, would delete every stdlib module's beam the first time someone
   runs `mix cure.compile <project_dir>` against the default output dir (stdlib
   entries would look exactly like removed files). To avoid this, a module is
   only a deletion candidate if its manifest `source_path` falls under one of
   *this run's* `source_paths` roots; a manifest entry whose `source_path` is
   outside those roots (e.g. a stdlib entry during a project build) is left
   untouched, deleted or not. Within a run's own roots, a module in the
   manifest whose `source_path` no longer exists on disk: delete its `beams`,
   drop it from the manifest. (A removed stdlib module, compiled via
   `cure.compile_stdlib` itself — whose source_paths root *is* `lib/std/` —
   must still not leave an orphaned beam; only a *foreign* run must not treat
   it as removed.)
5. **Single interleaved walk, in `DepGraph.toposort/2` order over this build's
   freshly-scanned `closure_deps_map/1`**, that decides dirtiness *and*
   compiles in the same pass — deciding dirtiness for `M` requires already
   knowing each visited dependency's *actual new* `interface_hash`, which only
   exists once that dependency has been compiled, so the dirty-check and the
   compile cannot be separate sequential phases over the whole module set; they
   are one step per module, repeated in walk order (`order/1`'s order is not
   usable here — see step 1). Dependencies for the
   dirtiness check are read from `closure_deps_map/1` (not the manifest's
   stored `deps`), so a changed dependency set — explicit or ambient — is
   always honoured, though a module whose imports changed also has a changed
   `source_hash` and is dirty anyway.

   For each module `M`, in walk order:
   - Mark `M` dirty iff `all_dirty`, or `source_hash(M)` differs from the
     manifest, or `M` is new (absent from the manifest), or any beam in
     `manifest[M].beams` is missing on disk, or any direct dependency of `M`
     (per `closure_deps_map/1`) was marked dirty earlier in *this* walk and its
     freshly-recomputed `interface_hash` (from that dependency's own visit,
     below) differs from its stored one. A dependency with no stored
     `interface_hash` (new, or previously errored) counts as changed.
   - If `M` is dirty, compile it immediately via the existing
     `Cure.Compiler.compile_file/2`. On success, recompute its `interface_hash`
     (from the same interface computation the elaborator already runs) and
     stage the updated manifest entry — this is what step 5's dependents read
     when they are visited later in the walk. On a compile **error**, do
     **not** stage an entry for that module — it stays dirty next run — and
     propagate the error the way the current task does (report + non-zero
     exit); dependents visited afterward still see it as "no stored
     `interface_hash`" (changed), so they stay dirty too rather than building
     on a broken dependency.
   - If `M` is not dirty, its stored manifest entry (`source_hash`,
     `interface_hash`, `beams`) carries forward unchanged.

   Because deps precede dependents in this topological order, each dependency's
   new `interface_hash` is known — because it was just computed — before its
   dependents are visited: no fixpoint loop is needed. `toposort/2` is
   SCC-tolerant: a cycle in `closure_deps_map/1` (which can only arise among
   the small prelude-bootstrap set that DepGraph does not exempt, per the note
   above) is emitted as an alphabetical group with no guaranteed internal
   order, so within such a group this build may not fully propagate a same-pass
   change from one cycle member to another; because these are synthetic edges
   among a handful of always-co-resident bootstrap modules (not a real
   elaboration dependency), and a missed propagation only means that specific
   member's `interface_hash` re-check happens on the *next* build (still safe —
   never a stale beam) rather than this one, this is an accepted, narrow
   precision loss, not a correctness gap.
6. **Write** the updated manifest atomically (only if no module errored this
   build, so a failed build never records partial freshness as complete).
7. Return a summary: counts of `compiled`, `skipped_fresh`, `deleted`, and any
   errors, for the task to print.

`opts`:
- `:force` (also `CURE_FULL_REBUILD=1` env) → skip steps 2-4 (manifest load,
  toolchain check, deletions), set `all_dirty = true`, and run step 5 as
  normal (every module is then compiled, since every module is dirty) — a
  clean rebuild. The escape hatch for a suspicious build.
- `:output_dir` default `_build/cure/ebin` (unchanged).

Interface-hash recomputation reuses the loader's existing interface computation
via `Cure.Elab.Program.module_interface/2` (see the fingerprint section for the
cache-sharing argument that keeps this off the second-elaboration path on full
builds).

### Mix task integration

- `Mix.Tasks.Cure.CompileStdlib` calls `Incremental.compile_dir` over
  `lib/std/*.cure`. Its output messages change from "Compiling … (81 modules)"
  to reporting compiled/skipped counts.
- `Mix.Tasks.Cure.Compile` (project builds) calls the same driver over the
  supplied sources.

  **Known limitation.** A project build's `closure_deps_map/1` is scanned only
  from its own `source_paths` (never `lib/std/*.cure`), so a project module's
  edges to the stdlib modules it `use`s or ambiently preludes never appear in
  *its* graph — the deletion-scoping fix above stops a project build from
  destroying stdlib beams, but a project module can still be left marked clean
  after a stdlib interface change that should have invalidated it, until the
  project module's own source changes or `:force` is used. The stdlib-only
  case (`cure.compile_stdlib`) is unaffected — there, every Std↔Std edge,
  including ambient `@prelude` ones, is within the single scanned universe.
  The safe, minimal mitigation, consistent with this design's existing
  coarse-but-safe compiler hash: add a stdlib artifact digest for project
  builds only — the same pattern as `toolchain` (sorted, concatenated,
  SHA-256'd `Cure.Std.*.beam` content in the stdlib's own `output_dir`),
  stored once at the top of a project's manifest; a mismatch marks every
  project module dirty, the same way a `toolchain` mismatch does. This is
  coarse (whole-stdlib granularity, not per-module) but safe, and is deferred
  to implementation rather than specified in full here — a project build that
  never mixes with a changing stdlib (the common case once both are stable)
  pays nothing extra.
- `test/test_helper.exs` is **unchanged** — it invokes the task and inherits the
  speedup. Its post-compile stickiness + declared-vs-loaded completeness checks
  (`test_helper.exs:35-120`) stay in place as an integration backstop: if the
  driver ever wrongly skipped a module, those checks raise loudly rather than
  letting a consumer flake. (They guard *presence*, not staleness, so they are a
  backstop, not the primary correctness mechanism — the fingerprints are.)

The `compile` alias in `mix.exs:135`
(`compile → cure.bundle_stdlib → cure.compile_stdlib → cure.bundle_stdlib_beams
→ cure.escript`) is left as-is; `cure.compile_stdlib` simply becomes cheap on a
no-op build. (The escript rebuild is a separate cost; not addressed here.)
`cure.bundle_stdlib_beams` (`cure.bundle_stdlib_beams.ex`) is also left as-is:
it independently recompiles the same `lib/std/*.cure` sources a second time,
into `priv/ebin/` rather than `_build/cure/ebin`, using its own pre-existing
per-module **mtime** comparison — `should_compile?/2`, `cure.bundle_stdlib_beams.ex:221-226`,
true when the beam is missing or its mtime is older than the source's — not
this design's content hash. That mechanism is unchanged by this spec and
not made incremental *by* this spec — it already has its own (weaker, coarser)
incrementality — so it is a second, separate fixed cost alongside the escript
step, not eliminated by making `cure.compile_stdlib` cheap.

### In-process `compile_and_load`

`Cure.Compiler.compile_and_load/2` (ad-hoc single-source compiles used directly
by tests) is **not** made incremental — there is nothing to cache for a
one-shot in-memory source. Incrementality applies to directory/project builds
only. This is the natural boundary of the feature.

## Correctness invariants (the part that must not regress)

1. **Never serve a stale beam.** Every channel by which a change reaches a
   module's output is a fingerprint input: its own source (`source_hash`), its
   dependencies' interfaces (`interface_hash`), and the compiler (`toolchain`).
2. **Beam presence is part of dirtiness** — a matching hash with a missing beam
   still recompiles.
3. **Only successful compiles update the manifest**, and the manifest is only
   written when the whole build succeeded — a failed or interrupted build never
   records partial freshness.
4. **Fail-safe on any manifest problem** — absent/corrupt/old-version manifest →
   full rebuild, never a skip.
5. **Determinism affects precision, not correctness.** If `export_env` carries
   run-varying data (fresh metavar/gensym counters), an identical recompile can
   yield a different `interface_hash`. That only over-invalidates dependents
   (safe, degrades toward module-level) and can never make two different envs
   collide. Skipped modules reuse their stored hash, so they are never affected.
   If over-invalidation proves noticeable in practice, a follow-up can normalize
   `export_env` before hashing; it is not required for correctness.
6. **Deletion is scoped and unconditional.** A manifest entry is only ever a
   deletion candidate when its `source_path` falls under *this run's own*
   `source_paths` roots (never a foreign entry, e.g. a stdlib entry seen during
   a project build sharing the default output dir) — and, within those roots,
   deletion runs on every build, including an `all_dirty` (toolchain-mismatch)
   build, not only a normal incremental one.

## Testing (red-green)

Unit tests for `Cure.Compiler.Incremental` over a temp-dir fixture of small
inter-dependent `.cure` modules (`A ← B ← C`, plus a private-helper module):

- **No change** → 0 recompiles.
- **Edit a leaf's source** → only that module recompiles.
- **Edit a dependency's exported definition** → the dependency *and* its
  transitive dependents recompile.
- **Edit a dependency's private/non-exported helper** (interface hash unchanged)
  → only that dependency recompiles; **no dependent rebuilds**. This is the test
  that proves interface-level actually buys something over module-level.
- **Edit an ambient `@prelude`-provider's exported definition, consumed by a
  fixture module with no explicit `use` of it** → the provider *and* its
  ambient (non-`use`-declared) consumer both recompile. This is the test that
  proves the dirty-propagation graph is sourced from `closure_deps_map/1`
  (ambient edges included), not `order_deps_map/1` (`use`-only) — the gap this
  spec's soundness section exists to close.
- **A dependency fails to compile, with a dependent that would otherwise be
  clean** → the dependent is also treated as dirty this build (per step 5's
  "no stored `interface_hash` counts as changed" rule for a broken dependency),
  not silently compiled against a stale/absent interface.
- **A source file with a genuine parse error** (no resolvable module name) →
  still attempted and reported as a build error, not silently absent from the
  build; proves unresolved-module paths aren't dropped by the module-name-keyed
  `closure_deps_map/1` walk.
- **A manifest containing an entry whose `source_path` is outside this run's
  `source_paths` roots** (simulating a project build sharing the default
  `_build/cure/ebin` output dir with a prior stdlib build) **→ that entry and
  its beam file are left untouched**, not deleted. This is the test that
  proves the deletion-scoping fix in step 4; without it, a project build would
  delete every stdlib beam the manifest already recorded.
- **Toolchain hash bump** → all modules recompile.
- **Toolchain hash bump in the same build as a deleted source** → every
  remaining module recompiles *and* the deleted module's stale beam and
  manifest entry are still removed — proves step 4 (deletions) is not skipped
  on the `all_dirty` path.
- **Delete a source** → its beams are removed and it leaves the manifest.
- **Missing beam with matching source hash** → recompiles.
- **Corrupt / absent / wrong-version manifest** → full rebuild.
- **A module fails to compile** → it is not recorded fresh; the next build still
  treats it as dirty; the manifest is not advanced past the failure.
- **`force` / `CURE_FULL_REBUILD`** → rebuilds everything regardless of manifest.

Integration: the existing `test_helper.exs` stickiness + completeness checks and
`mix cure.check.stdlib` remain and must stay green. The full gate (this touches
the compile pipeline) runs with Antigen.

**Discipline.** Each scenario above is a red test, written and run *before* any
`Cure.Compiler.Incremental` code exists, confirmed failing (or erroring, since
the module doesn't exist yet) for the reason the scenario states — then only
enough of the driver is written to turn it green, one scenario at a time,
re-running the full set after each addition so earlier scenarios stay green.
Every assertion is on `compile_dir`'s public return value (the `compiled` /
`skipped_fresh` / `deleted` / error summary from step 7) and on-disk state
(which beams exist, the manifest's recorded hashes) — never on internal call
counts or private functions — so the tests survive an internal refactor of the
driver. Once a scenario's test is green and correctly encodes the behavior
above, it is not weakened, skipped, or rewritten to match different code; the
only valid reason to touch a written test is a proof that the test itself
encodes the wrong behavior, stated explicitly before changing it.

## Follow-ups (not in this spec)

- **Per-consumed-symbol invalidation** — finer than per-module interface;
  requires elaborator use-set instrumentation. Deferred (see scope note above).
- **`export_env` normalization** — only if determinism-driven over-invalidation
  is measured to matter.
- **Escript rebuild staleness** — the `cure.escript` step in the compile alias
  is a separate fixed cost not addressed here.
- **`cure.bundle_stdlib_beams` mtime-vs-content staleness** — this task
  redundantly recompiles `lib/std/*.cure` into `priv/ebin/` using its own
  pre-existing mtime-based check, independent of (and weaker than) this
  design's content-hash manifest. Folding it into `Cure.Compiler.Incremental`
  (or having it read this design's manifest instead of comparing mtimes) would
  remove both the redundant compile and the mtime-staleness risk class this
  spec's `source_hash` approach was chosen specifically to avoid elsewhere. Not
  addressed here.

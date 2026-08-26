# Canonical module pipeline switch catalogue

**Date:** 2026-08-03

**Status:** Gating inventory

**Gate:** `module_pipeline: :canonical`

## 1. Purpose

This catalogue is the migration checklist for routing every Cure semantic
compilation path through `Cure.Compiler.ModulePipeline`. It complements the
interface-first design: that document defines semantics; this document names
the concrete call sites and competing authorities that must be consolidated.

The gate selects the complete semantic pipeline, never an individual resolver,
loader, graph, prelude builder, or emitter. A compilation invocation is either
canonical from discovery through checked artifacts or it follows the existing
path. Mixing stages across the gate is forbidden.

The public option is:

```elixir
module_pipeline: :canonical
```

The default remains the existing path during shadowing. There is no second
boolean flag, environment-specific spelling, or fallback from the canonical
selection. An unsupported entry point must return
`{:error, {:canonical_pipeline_not_routed, entry_point}}`, not silently use a
different path.

## 2. Single routing boundary

Every adapter builds one `Cure.Compiler.ModulePipeline.Request` and calls one of
these operations:

```text
ModulePipeline.check(request)
ModulePipeline.compile(request)
ModulePipeline.compile_and_load(request)
ModulePipeline.interfaces(request)
```

All four operations share discovery, manifest construction, expansion,
interface checking, body checking, semantic graph construction, closure
validation, and artifact identity. The operation only chooses the requested
terminal product.

`Request` owns all invocation inputs currently passed independently or stored
in process state:

```text
entry_point
package identity and package dependencies
source files, virtual sources, and source roots
interface and artifact roots
stdlib/prelude selection
compiler-owned providers
edition and compiler options
macro execution policy
requested roots and output products
output root and publication policy
diagnostic/event sinks
incremental cache inputs
```

The request is immutable. Adapters may not install source roots, module indexes,
or environments in the process dictionary.

## 3. Public compiler facade

These functions are the primary gate. They SHALL inspect
`module_pipeline: :canonical` once and construct a request. Internal callees do
not inspect the option again.

| Existing entry | Canonical terminal operation | Notes |
| --- | --- | --- |
| `Cure.Compiler.compile_file/2` | `compile` | One physical source plus its universe. |
| `compile_file_with_artifact/2` | `compile` | Returns the checked-module and interface products from the same run. |
| `compile_string/2` | `compile` | Uses a virtual source with explicit provenance. |
| `compile_string_with_artifact/2` | `compile` | Must not recheck to obtain its interface. |
| `compile_files/2` | `compile` | One manifest and graph for the entire set. |
| `compile_and_load/2` | `compile_and_load` | Loading happens only after verified artifact publication. |
| `Cure.Elab.Program.elaborate/2` | `check` | Compatibility facade returning the checked environment projection. |
| `check_ast/1,2` | `check` | AST input becomes a virtual-source request; it cannot invoke an independent loader. |
| `check_ast_artifact/2` | `check` | Returns the canonical checked-module product. |
| `check_ast_with_locals/1` | `check` | Local-definition information is a projection of the same result. |
| `module_interface/2` | `interfaces` | No separate source elaboration or cache. |

The facade must preserve current return shapes while migration is in progress.
The canonical result itself remains richer and is not reduced internally to an
`Env` and reconstructed later.

## 4. Bulk build and artifact drivers

These are separate orchestration paths today and must become request builders
over the same pipeline.

| Owner | Existing path to consolidate | Canonical responsibility |
| --- | --- | --- |
| `Cure.Compiler.Incremental.compile_dir/3` | Scans `DepGraph`, chooses order/components, threads `qualified_envs`, calls compiler per file, computes interface dirtiness. | Supply previous manifest/cache state to one canonical compile request and publish its returned generation. |
| `Cure.Compiler.Artifacts.Sweep.run/1` | Calls incremental compilation and constructs/seals build manifests. | Validate inputs, call canonical compile, atomically publish the returned artifact set. |
| `Cure.Compiler.Artifacts` | Opens, verifies, loads, copies, and prunes artifact generations. | Remains artifact storage, but semantic validity and dependency closure come from canonical interface results. |
| `Cure.Compiler.Artifacts.Writer` | Stages and swaps generations. | Remains the single atomic publisher; never chooses semantic dependencies. |
| `Cure.Compiler.BuildManifest` | Independently records modules, source hashes, dependencies, and compiler context. | Serialize the canonical manifest/interface/component hashes rather than reconstructing them. |
| `Cure.Project.compile_project/2` | Preloads stdlib, constructs roots, and sweeps project files. | Construct package-aware request; no extra dependency graph. |
| project dependency compilation in `Cure.Project` | Sweeps dependency source roots independently. | Produce/load package interface sets through the same request format. |
| `Cure.Release.build/2` and project publisher | Consume project artifacts after project compilation. | Consume only a verified canonical generation. |

## 5. Standard library and prelude paths

The stdlib currently has several authorities over availability. All semantic
parts move into the canonical manifest and checked prelude interface set.

| Existing mechanism | Location/owner | Consolidation |
| --- | --- | --- |
| Source scanning and compile repair | `Cure.Stdlib.Preload.preload/1`, `compile_missing_from_sources/1,2` | Preload may load a verified set. It may not compile sources or decide missing semantic providers. Repair becomes an explicit canonical compile request owned by the caller. |
| Stdlib dependency scan | `Cure.Stdlib.Preload` module initialization and `DepGraph.scan/1` | Remove; use the serialized stdlib canonical manifest. |
| Injected prelude `use` AST nodes | `Cure.Compiler.inject_prelude_uses/2` | Remove; ambient scope is a projection of checked prelude interfaces. |
| Prelude provider propagation | `prelude_provider_names/1`, `:prelude_providers` parser/compiler options | Replace with `Request.prelude_set`. |
| Source-scanned prelude manifest | `Cure.Elab.Program.prelude_manifest/0`, invalidation, scanning and slicing helpers | Replace with the checked prelude interface set. |
| Recursive provider elaboration | `prelude_entry_env/2`, prelude slice and import closure helpers | Remove. Loading ambient scope never checks provider bodies. |
| Parser prelude macro caches | parser `:persistent_term` caches and `:cure_loading_prelude` recursion guard | Populate parser/expander inputs from the request's verified macro interfaces. Cache only by canonical interface hash. |
| Compile-time built-in fixity scan | `Parser.BuiltinFixity` scans stdlib source while compiling Elixir | Replace with a generated compiler-owned interface resource or bootstrap manifest produced by the canonical stdlib build. |
| On-demand fixity source resolution | `Parser.FixityResolver` and `FixityScan` use/prelude closure | Resolve fixity imports through manifest skeletons/interfaces. |

The Mix tasks `cure.compile_stdlib`, `cure.check.stdlib`,
`cure.bundle_stdlib_beams`, `cure.check.examples`, and `cure.check.docs` all
construct canonical requests. None may call stdlib repair as an implicit side
effect.

## 6. Discovery, graph, and source resolution authorities

| Existing authority | Current role | Canonical destination |
| --- | --- | --- |
| `Cure.Compiler.ModuleIndex` | Maps module names to paths/providers and direct edges. | Replaced by the immutable `ModuleManifest`; useful parsing code may be moved, but there is one stored authority. |
| `Cure.Compiler.DepGraph` | Scans sources; maintains order and closure dependency maps; computes SCCs and prelude providers. | Bootstrap and semantic graphs owned by `ModulePipeline`; no standalone compilation ordering API. |
| `Cure.Compiler.SourceResolver` | Reads `:cure_module_index` and `:cure_source_roots` from process state and probes paths. | Pure manifest lookup receiving the request/universe explicitly. |
| `Cure.Compiler.plan_files/2` | Separately scans and orders file compilation. | Manifest discovery plus phase/component planning. |
| CLI source-root and module-index helpers | Reconstruct roots/index for commands. | Package/request builder shared by all CLI commands. |
| Incremental `compile_order/1` and component scheduling | Uses a graph variant selected for compilation. | Canonical phase planner over bootstrap/interface/body component graphs. |
| Build-manifest dependency maps | Reconstruct invalidation edges after compilation. | Checked semantic graph serialization. |

The following process keys are removed from semantic compilation:

```text
:cure_source_roots
:cure_module_index
Program's loader-session state
```

Observer and telemetry process keys may remain only as sinks; they cannot carry
semantic state.

## 7. Elaboration and interface construction

The largest consolidation occurs inside `Cure.Elab.Program`.

| Existing mechanism | Canonical replacement |
| --- | --- |
| `with_loader_session` and its mutable module/path/prelude state | Immutable request, manifest, interface cache, and explicit phase state. |
| Recursive `load_module_interface`/source compilation | Component interface checking driven by the phase planner. |
| Source-hash-only loader cache | Interface/component cache keyed by all semantic inputs. |
| `qualified_envs` threaded from incremental and lifted-module compilation | Checked interface table in the request result. |
| Import-source recursion and transitive import-module reconstruction | Resolver records lexical and semantic edges at lookup time. |
| `canonical_export_env` built by slicing a cumulative mutable `Env` | Immutable checked `ModuleInterface` constructed from declarations owned by that module. |
| Repeated environment merge helpers | One law-tested interface-environment merge. |
| Coherence recovery over cumulative instances | Owner-local conformance publication plus deterministic selection. |
| `macro_home_source` dependency lookup | Hygiene/provenance only; macro dependency availability comes from the manifest. |

`Cure.Elab.Resolution.resolve_bare/2` and `resolve_qualified/3`, overload
resolution, constructor lookup, equation/member lookup, proof search, macro
reflection, and generated syntax all receive one resolver view backed by the
same manifest and interfaces. They may add type-directed selection but may not
invent module or definition identity.

## 8. Macro and lifting paths

| Existing path | Consolidation |
| --- | --- |
| Parser prelude/builtin macro loading | Macro skeletons and verified expanders from canonical interfaces. |
| `MacroExpand` compiled-module probing and fallback selection | Execution strategy selected by request; both consume and publish through the same expansion state. Host loading may execute a verified expander but cannot resolve Cure names. |
| Macro validation helpers calling `Program.check_ast` | Submit virtual-source child requests sharing the parent universe and phase policy. |
| Macro fuzz/example compilation | Same child-request API, explicitly marked test/compile-time. |
| `LiftModule` checking and emitting lifted units independently | Publish lifted declarations into the owner module's checked result; no separate `qualified_envs`. |
| Generated-dependency AST scans | Resolver-recorded graph edges during expansion/checking. |

## 9. Reachability, totality, and emission

| Existing mechanism | Consolidation |
| --- | --- |
| `Program.reachable_def_names/2` returns atom names and independently walks Core. | Canonical typed closure entries from the checked semantic graph. |
| Audit ledger performs a second reachability walk. | Consume the canonical closure and unresolved-edge diagnostics. |
| Totality/proof closure reconstruct dependencies from environments/Core. | Consume canonical definition keys and semantic edges. |
| `Emit.compile_forms` receives an `Env`, name list, origins, aliases, and process-local state. | Receive a checked module plus validated typed closure. |
| Emission suffix/alias recovery and missing-definition guessing | Remove; unresolved closure entries fail before emission with predecessor paths. |
| `dependent_codegen` rechecks AST with `qualified_envs`. | Emit the checked Core returned by the same canonical run. |
| `LiftModule` performs its own `Program.check_ast_with_locals` and emission. | Emit owner-published lifted definitions from the canonical result. |
| `BeamWriter` | Remains a host backend accepting complete forms; it performs no Cure resolution. |

## 10. User-facing and tooling adapters

Every direct call below must propagate the gate and identify its entry point.

### Command-line and build tooling

- `Cure.CLI`: compile, run/eval, check, stdlib, dependency, and script paths;
- `Cure.Project`: project and dependency compilation;
- `Cure.Watch`: compile and check actions;
- `Cure.Release` and project publishing;
- Mix tasks for project compile, stdlib compile/check/bundle, docs, and examples;
- `test/test_helper.exs` stdlib sweep.

### Interactive and service tooling

- `Cure.REPL` and `Cure.REPL.Session`, including expression checking, definition
  accumulation, file loading, reload, type queries, and execution;
- `Cure.LSP.Server` document elaboration;
- `Cure.MCP.Server` checking and execution;
- documentation snippets and doctests;
- profiler, developer trace, oracle, audit/Antigen elaboration adapters;
- the Phoenix site application preload, playground, evaluator, and terminal
  command wrappers.

REPL state stores canonical checked declarations/interfaces and constructs a
new immutable request generation after each accepted declaration. It does not
concatenate source and invoke a smaller elaborator model.

## 11. What the gate does not control

The following remain downstream or host concerns and must not be mistaken for
alternate semantic pipelines:

- Erlang compilation in `BeamWriter`;
- loading a completely verified BEAM generation in `Artifacts`;
- host extern validation and explicit dynamic FFI calls;
- diagnostic rendering, CLI command discovery, telemetry, and doctor checks;
- package solving, lockfiles, signing, archive creation, and publication;
- migration tools that only transform syntax and do not claim to check it.

Host `Code.ensure_loaded?`, `module_info`, or `:code.is_loaded` calls in those
areas are not automatically violations. They are violations only when used to
answer a Cure semantic question: whether a Cure module/declaration exists, its
type, its exports, its conformance, or its dependency closure.

## 12. Gate propagation and enforcement

The gate is normalized once at the public facade:

```text
nil              -> configured default during shadow period
:canonical       -> canonical request
anything else    -> invalid compiler option
```

Configuration sources use the same key and value:

- API keyword: `module_pipeline: :canonical`;
- project compiler options: `module_pipeline = "canonical"`;
- CLI development switch: `--module-pipeline canonical`.

Environment variables are deliberately not a semantic configuration source;
they make concurrent tests and embedded callers disagree invisibly. A test or
CI job may set the project/API option explicitly.

Propagation rules:

1. A parent request passes the normalized selection to every child request.
2. A child cannot downgrade or choose a different pipeline.
3. Artifact manifests record the pipeline schema, not the temporary gate name.
4. Cache keys include the semantic schema/toolchain, so outputs from different
   pipelines cannot be mistaken as equivalent during shadowing.
5. Every adapter emits an event containing its `entry_point` and selected
   pipeline; the entry-point parity test asserts full coverage.

## 13. Switch checklist

The gate cannot become default until each row is green in canonical mode.

| Area | Routed | Shadow-compared | Existing path deleted |
| --- | --- | --- | --- |
| compiler file/string/AST facades | no | no | no |
| bulk and incremental compilation | no | no | no |
| interface-only checking | no | no | no |
| stdlib bootstrap/check/bundle/preload | no | no | no |
| project and dependency compilation | no | no | no |
| macros and lifted declarations | no | no | no |
| totality, reachability, audit, emission | no | no | no |
| CLI run/check/eval and watch | no | no | no |
| REPL | no | no | no |
| docs/examples/doctests | no | no | no |
| LSP/MCP/profiler/oracle/Antigen | no | no | no |
| release/bundle/escript | no | no | no |
| Phoenix site preload/playground/eval | no | no | no |
| test harness and isolated builds | no | no | no |

## 14. Catalogue enforcement tests

Before implementing semantics, add tests that:

- enumerate every adapter above and assert it recognizes
  `module_pipeline: :canonical`;
- assert a selected canonical request never calls existing `DepGraph` ordering,
  recursive source loading, injected prelude imports, `qualified_envs`, or
  emission rechecking;
- assert child requests inherit the normalized selection;
- assert unknown values fail rather than fall back;
- assert every canonical invocation emits one entry-point event; and
- scan for new direct calls to `Program.check_ast`, `compile_and_load`,
  `Incremental.compile_dir`, and stdlib repair outside approved adapters.

This catalogue is updated whenever an enforcement test discovers another call
site. A discovered call site is not patched locally; it is added to the routing
table and migrated through the single boundary.

## Appendix A. Audited direct-call files

The 2026-08-03 audit found direct semantic compilation calls in the following
files. This is the concrete allow-list that the architectural test initially
freezes; adding another file requires updating this catalogue.

### Compiler and elaborator owners

```text
lib/cure/compiler.ex
lib/cure/compiler/incremental.ex
lib/cure/compiler/artifacts/sweep.ex
lib/cure/compiler/lift_module.ex
lib/cure/compiler/macro_fuzz.ex
lib/cure/elab/program.ex
lib/cure/elab/emit.ex
lib/cure/stdlib/preload.ex
```

### Product and command adapters

```text
lib/cure/cli.ex
lib/cure/project.ex
lib/cure/project/proof.ex
lib/cure/release.ex
lib/cure/watch.ex
lib/cure/repl.ex
lib/cure/repl/session.ex
lib/cure/lsp/server.ex
lib/cure/mcp/server.ex
lib/cure/doc/snippets.ex
lib/cure/doc/doctests.ex
lib/cure/profiler.ex
lib/cure/dev/trace.ex
lib/cure/oracle.ex
lib/antigen/assays/elab.ex
```

### Mix and test-build adapters

```text
lib/mix/tasks/cure.compile.ex
lib/mix/tasks/cure.compile_stdlib.ex
lib/mix/tasks/cure.check.stdlib.ex
lib/mix/tasks/cure.bundle_stdlib_beams.ex
lib/mix/tasks/cure.check.examples.ex
lib/mix/tasks/cure.check.docs.ex
test/test_helper.exs
```

### Phoenix site adapters

```text
site/lib/cure_site/application.ex
site/lib/cure_site_web/commands/cure_eval.ex
site/lib/cure_site_web/eval.ex
site/lib/cure_site_web/live/playground_live.ex
```

The audit also found semantic state or alternate authority in these modules,
even where they do not directly invoke a public compile facade:

```text
lib/cure/compiler/module_index.ex
lib/cure/compiler/dep_graph.ex
lib/cure/compiler/source_resolver.ex
lib/cure/compiler/build_manifest.ex
lib/cure/compiler/artifacts.ex
lib/cure/compiler/artifacts/writer.ex
lib/cure/compiler/parser.ex
lib/cure/compiler/parser/builtin_fixity.ex
lib/cure/compiler/parser/fixity_scan.ex
lib/cure/compiler/parser/fixity_resolver.ex
lib/cure/compiler/macro_expand.ex
lib/cure/compiler/macro_reflection.ex
lib/cure/elab/resolution.ex
lib/cure/elab/overload.ex
lib/cure/elab/equation.ex
lib/cure/elab/proof_search.ex
lib/cure/audit/ledger.ex
```

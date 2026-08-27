# Automatic dependency-ordered compilation (DepGraph) — Design

**Date:** 2026-07-08
**Status:** Approved (operator design gate, autopilot run)
**Topic:** auto-import-order

## 1. Problem

Cure's build entry points maintain module ordering by hand or by accident:

- `Mix.Tasks.Cure.CompileStage1.stage1_group/1` is a hand-numbered 0–10 table
  ordering the self-hosted kernel sources (`lib/mix/tasks/cure.compile_stage1.ex:106-118`).
  It is load-bearing: stage1 modules import each other via
  `use Compiler.Kernel.Core.X` and call each other **unqualified**, and codegen
  resolves those calls by probing **loaded** beams
  (`resolve_import`/`module_exports?`, `lib/cure/compiler/codegen.ex:2050-2069`).
  Because non-`Std.*` imports are never validated, a wrong order does not fail —
  it silently emits **local** calls (`codegen.ex:1204-1213`), producing broken
  beams that `:undef` at runtime.
- `mix cure.compile_stdlib` compiles `lib/std/*.cure` alphabetically.
- Multi-file user compiles (`Cure.CLI.cmd_compile`, `Cure.Project.compile_project`)
  never load compiled beams between files, so a user module that `use`s a
  sibling module and calls it unqualified is silently miscompiled (local-call
  fallback) **regardless of argument order**. (`Cure.CLI.cmd_run` is single-file
  only — it has no multi-file variant of this problem; see §3.2 item 3.)
- `Cure.Stdlib.Preload`'s source-JIT fallback (`compile_missing_from_sources/1`)
  iterates alphabetically; a classic (non-dependent) module with `use Std.X` can
  hard-fail (`missing_stdlib_module`, `codegen.ex:2020-2046`) if X is not yet
  loadable.
- Selective preload (`preload(kind: :collections)`) loads a group without its
  cross-group runtime dependencies (e.g. beams that remote-call `:core`-group
  modules), because groups are a selection filter with no dependency knowledge.

The operator's directive: replace manual ordering with real compiler machinery —
automatic dependency-graph sorting so modules Just Work, like every serious
language.

## 2. Verified ground truth (fresh-VM experiments, 2026-07-08)

These facts bound the design. Each was verified empirically on this checkout,
not inferred from reading code:

1. **Two codegen pipelines.** `Cure.Compiler.compile_file/2` routes a module
   through the dependent pipeline (`Cure.Elab.Program` → Core →
   `Cure.Elab.Emit`) when `Elab.Program.dependent?/1` holds
   (`lib/cure/compiler.ex:259-280`); otherwise through classic codegen
   (`compile_module_container`). The dependent pipeline re-elaborates imported
   **source files** (`import_source_env`, `lib/cure/elab/program.ex:592-630`) and
   never probes beams: `vector.cure` (`use Std.Nat`, `use Std.Bounded`) compiles
   correctly in a fresh VM with `Cure.Std.Nat` unloadable.
2. **Qualified calls are order-free.** `Std.Map.get(...)`-style calls lower
   syntactically to remote calls (`compile_qualified_call`,
   `codegen.ex:1222-1229`) with no load probe. `access.cure` (no `use` lines,
   all cross-module calls qualified) compiled in a fresh VM with
   `Cure.Std.List` unloadable produces a beam whose import table correctly
   references `Cure.Std.List`, `Cure.Std.Map`, `Cure.Std.Pair`.
3. **Implicit no-`use` references are not cross-module edges at compile time.**
   References like `Equivalent`/`reflexive`/`True` in `decision.cure` resolve
   from the builtin-inductive seed (`Cure.Core.Builtins.seed`,
   `program.ex:133`) and the auto-prelude (`Std.Bool`, `Std.Nat`;
   `program.ex:240`), all source-based.
4. **The only load-sensitive machinery** is classic codegen's
   `validate_stdlib_imports/1` (hard error, `Cure.Std.*` only — confirmed live
   with a `use Std.Nonexistent` probe → `{:codegen_error,
   {:missing_stdlib_module, ...}}`) and `resolve_import/3` (silent local-call
   fallback, all imports). Both probe `:code.ensure_loaded` +
   `module_info(:exports)`.
5. **Runtime cross-module call graph** (beam import tables): stdlib —
   Access→{List,Map,Pair}, Functor→List, Gen→List, NonEmpty→List,
   Set→{List,Map}, Signal→{Eq,Ord}, Signal.Event→Eq,
   Signal.Flow.Graph→{Clock,Fsm,List,Signal.Flow,String}; stage1 — the full
   kernel-core mesh (TypeChecker→{Declaration,Environment,Expr,Level,
   LocalContext,Name}, Environment→{...,TypeChecker}, etc.) plus Std.{List,
   String,Test}.
6. **The stdlib `use` graph is a DAG; the stage1 graph no longer is.** At the
   time of the original experiments both graphs were acyclic. Commit `5ef6d80`
   ("Bootstrap Lean-style stage1 kernel") later introduced a genuine `use`
   cycle `Environment ↔ Exception` (`environment.cure:6` /
   `exception.cure:6`) — type-level mutual recursion faithful to the Lean
   kernel being ported, with no runtime calls across the edge. This drift is
   what forced the §3.1 cycle-policy amendment from hard-error to
   SCC-condensation-with-warning. (Only 2 of 39 stdlib modules declare `use`
   at all; stage1 kernel modules declare `use` comprehensively.)
7. **`__group__` is selection, not ordering.** It drives `preload(kind:)`
   filtering (`lib/cure/stdlib/preload.ex:309-320`); order within a selection is
   `Enum.sort()`. Live consumers of the kind API: `cure run`,
   `mix cure.check.examples`, the test suite, and `Cure.REPL.Config`
   (validates against `known_groups/0`). The sources-absent release fallback
   `discover_from_beams/1` calls the exported `__group__/0` on packaged beams
   (`preload.ex:345-376`).

## 3. Design overview

Build-orchestration machinery only. **No kernel/TCB changes, no elaborator
changes, no new surface syntax, no manifest/package system.** Codegen's
qualified-call and dependent-pipeline paths are already order-free and are left
alone; we make every build entry point feed them files in dependency order and
keep compiled output loadable as the pass proceeds.

### 3.1 `Cure.Compiler.DepGraph` (new, `lib/cure/compiler/dep_graph.ex`)

Pure Elixir module (no process state). Input: a list of `.cure` paths — a
*compile set*.

**Per-file scan** via the headless front-end `Cure.Compiler.parse_source/2`
(commit `eacfdfa`; lex+parse only, no app boot):

- **Declared module name**: from the AST container node, covering all container
  kinds (`mod|proof|actor|fsm|sup|app`) — semantics matching Preload's
  `@mod_regex` but AST-based, not regex.
- **Order-edges**: targets of `use` declarations (`{:import, meta, _}` nodes,
  `meta[:source]`), restricted to modules declared **within the compile set**.
  Out-of-set targets (e.g. `Std.*` from a stage1 file) impose no intra-set
  ordering; their availability is already handled by preload/validate.
- **Closure-edges** (superset, for load/JIT closure — not ordering): `use`
  targets + qualified-call targets (AST walk for dotted callee names, module
  part per `compile_qualified_call` semantics, filtered to the known module
  universe so Erlang externs are never edges) + auto-prelude modules
  (`Std.Bool`, `Std.Nat`, minus the self/declared-type exclusions mirroring
  `auto_prelude_imports/1`).
- A file that fails to parse contributes no edges and is reported
  (`{:error, {:parse, path, reason}}`) — the build task decides whether to
  proceed (existing per-file error handling) — except placeholder (blank)
  sources, which are skipped exactly as `cure.compile_stage1` does today.
- Two in-set files declaring the same module name is an error
  (`{:duplicate_module, name, [path1, path2]}`).

**API** (shapes indicative):

```elixir
@spec scan([Path.t()]) :: {:ok, graph} | {:error, reason}
@spec order(graph) :: {:ok, [Path.t()], [cycle]}   # cycle = closed hop walk of one multi-member SCC
@spec closure(graph_or_baked_map, [module_atom]) :: [module_atom]
```

`order/1`: SCC condensation ordering — compute strongly-connected components
of the in-set order-edge graph (Tarjan), topologically sort the condensation
with **alphabetical tie-break** (an SCC is keyed by its alphabetically
smallest path), and expand each multi-member SCC in alphabetical path order.
Fully deterministic, so repeated builds compile in identical order. Every
multi-member SCC is additionally reported as a closed cycle walk
(`A (a.cure:3) -> B (b.cure:2) -> A`) in the third tuple element.

**Cycle policy: warn and proceed (SCC condensation).** A `use` cycle among
in-set modules is NOT an error: the members are compiled as a group in
deterministic (alphabetical) order and a new **warning** code reports the
cycle. Rationale — this policy was amended on 2026-07-08 during
implementation, superseding the original hard-error policy, for two reasons:
(a) *the DAG premise broke*: commit `5ef6d80` ("Bootstrap Lean-style stage1
kernel", post-dating this spec's experiments) introduced a genuine
`use` cycle `Compiler.Kernel.Core.Environment ↔ Compiler.Kernel.Core.Exception`
— type-level mutual recursion faithful to the Lean kernel it ports
(`KernelException` constructors carry `Environment`; `Environment` functions
return `Result(Environment, KernelException)`), with zero runtime calls
across the edge (verified via beam import tables); (b) *the operator's
briefing explicitly mandated it*: "Cure supports mutual recursion;
cross-module cycles likely exist … the agent needs a defined behavior
(compile an SCC together / arbitrary intra-SCC order), not a crash." Cure's
compile-set model matches Rust's crate-internal modules (cycles legal), not
OCaml's compilation units. Cycles stay *observable* in the artifact result (the
optional W086 diagnostic names the full walk), and any genuinely order-unsatisfiable unqualified call inside an
SCC is caught by the separate unresolved-import warning (§3.2 item 4).
Error/warning codes: the registry's `E`/`W`/`H` codes share one numeric
sequence (e.g. `W081`/`W082`/`H083`/`H084` sit between `E080` and `E085`);
as of this writing the lowest free number is 086 — the cycle warning takes
**W086**, duplicate-module takes **E087**; implementation verifies against
the registry and takes the actual next free numbers.

### 3.2 Build entry-point integration

1. **`mix cure.compile_stage1`**: delete `stage1_group/1` and
   `stage1_sort_key/1`; order via `DepGraph.order/1`. Keep: placeholder skip,
   `--include-tests` filtering (test files sort naturally after their deps;
   the flag continues to include/exclude them), `Code.prepend_path` before
   compiling (already present — this is what lets the ordered pass resolve
   earlier beams).
2. **`mix cure.compile_stdlib`**: order via DepGraph instead of `Enum.sort()`,
   and move the output-dir code-path registration to **before** the compile
   loop (mirroring stage1). Today this changes nothing observable (fact 2/6) —
   it makes the pass principled and future-proofs classic `use` inside the
   stdlib.
3. **`Cure.CLI.cmd_compile`** (`cli.ex:439`, the only CLI entry that is
   actually multi-file — it accepts a list of file/directory paths) **and
   `Cure.Project.compile_project`** (`project.ex:522`, used by
   `Cure.Release`, `release.ex:88`, over `cure_files` derived from the
   project's source paths): order the file list via DepGraph and **load
   each emitted beam immediately after compiling it** (the
   `Preload.load_if_present/2` pattern — `:code.load_binary`, no global path
   pollution). This makes user→user `use` + unqualified calls link
   correctly. Single-file invocations are unaffected (a one-node graph).
   `cmd_compile` resolves multiple top-level `paths` arguments (each
   independently directory-wildcarded, `cli.ex:488-497`); the compile set
   for ordering purposes is the union of every file resolved from every
   given path, not each path ordered in isolation — otherwise a dependency
   spanning two path arguments (`cure compile b_dir a_dir` where a file in
   `b_dir` `use`s one in `a_dir`) would not be caught.
   **`Cure.CLI.cmd_run` is out of scope for this item**: despite the name
   resemblance, `cmd_run` (`cli.ex:522`) takes exactly one file
   (`["run" | [path]]`, `cli.ex:93-94`) and compiles it via
   `Cure.Compiler.compile_and_load/2`, which loads straight into the VM and
   never writes a `.beam` to disk — there is no file list to order and no
   emitted beam to load. It already benefits transitively once stdlib
   preload (§3.3) gains closure-awareness, and needs no direct change here.
4. **`resolve_import` silent fallback → warning.** When a `use`-imported
   unqualified call resolves to no import and falls back to a local call
   (`codegen.ex:1208-1213`), emit a compiler warning naming the function and
   the modules probed. This is new plumbing, not reuse of an existing
   channel: `%Cure.Compiler.Codegen{}` (`codegen.ex:29-45`) carries no
   `:warnings` field today, `compile_module_container/4` returns bare
   `{:ok, forms}`, and the `warnings` element of `compile_file`'s
   `{:ok, module, warnings}` result currently comes only from
   `BeamWriter.compile_forms/2` (the Erlang compiler's own diagnostics,
   `lib/cure/compiler.ex:117-131`) — codegen itself has no warnings sink to
   emit into (contrast the type checker's W081/W082 pickup warnings, which
   are collected in `Cure.Types.Checker`, a separate pipeline phase). This
   item therefore requires adding a warnings accumulator to codegen state,
   threading it through `compile_module_container` and `compile_module`'s
   return value, and merging it with `BeamWriter`'s warnings before
   `compile_file` returns. Behavior is otherwise unchanged (no new hard
   error — existing workflows that rely on late loading keep working, but
   silence is removed).

### 3.3 `Cure.Stdlib.Preload` — closure-aware selection

- Extend the existing compile-time scan (same `@external_resource` baking
  pattern) to bake **two** maps, keeping the order-edges/closure-edges
  distinction from §3.1 rather than flattening it away:
  `%{module => [order_dep_module]}` (`use`-only, mirroring `DepGraph.order/1`'s
  edge set) and `%{module => [closure_dep_module]}` (the full superset —
  `use` + qualified-call targets + auto-prelude — mirroring
  `DepGraph.closure/2`). A single flattened map would not suffice: bullet
  below needs the order-only subset specifically, because ordering by the
  full closure could over-constrain or spuriously cycle on qualified-call
  edges that are legitimately order-free (fact 2) and were never meant to
  gate load sequencing. Groups and `@mod_regex`/`@group_regex` stay; the new
  maps are additive. (The scan may reuse DepGraph's parser-based extraction;
  if parsing at Elixir compile time is unacceptable there — e.g. parser not
  yet compiled in the same pass — a documented regex fallback for `use` +
  qualified-call heads is acceptable, since stdlib style is enforced
  in-repo. The implementation plan decides with evidence; behavior, not
  mechanism, is normative here.)
- `preload(kind:)` expands the selected module set to its **closure** over the
  baked dep map before loading (e.g. any selection pulling `Std.Signal` also
  loads `Std.Eq`/`Std.Ord`). Selection *semantics* (which groups the user asked
  for) are unchanged; closure only adds modules needed for the selection to
  actually run.
- `compile_missing_from_sources/1` (source-JIT) iterates its module list in
  dependency order using the baked **order-only** map (not the closure map;
  alphabetical tie-break).
- **Unchanged and explicitly preserved**: `__group__` convention in sources,
  `known_groups/0`, the `kind` API and its validation in `Cure.REPL.Config`,
  and the `discover_from_beams/1` release fallback. In the beams-only fallback
  the dep map is empty → closure degrades to plain selection (status quo).
- `docs/STDLIB.md` gains a paragraph: groups are selection tags; ordering and
  load closure are automatic (DepGraph).

### 3.4 What `__group__` becomes

Nothing changes in sources. `__group__` was never an ordering mechanism
(fact 7); it remains the selection tag for REPL/preload kinds. The *manual
ordering* being retired is the stage1 numeric table plus the alphabetical
accidents; DepGraph replaces those.

## 4. Error handling summary

| Condition | Behavior |
|---|---|
| `use` cycle within a compile set | Proceed silently by default: SCC is compiled as a group in deterministic order; `--warn-import-cycles` (or `warn_import_cycles: true`) emits W086 with the closed cycle path and file:line |
| Duplicate module name in a compile set | Hard error naming both files |
| In-set file fails to parse | Per-file error via existing channel; ordering proceeds for the rest (parse failure will also fail that file's own compile) |
| `use` target not in set and not loadable (classic module) | Existing `missing_stdlib_module` for `Std.*` (unchanged); **new warning** for the silent local fallback on any import |
| Release / sources-absent preload | Closure degrades to selection; groups still work via `__group__/0` beam export |

## 5. Testing

TDD throughout: for each item below, write the test first, watch it fail for
the stated reason, then write the minimal implementation to turn it green,
then refactor with the suite staying green. Once a test correctly encodes the
behavior below, it is immutable — a red test goes green by changing
implementation code, never by weakening, skipping, or rewriting the test. The
sole exception is a test later proven to be itself wrong (misencodes the
intended behavior), and that must be argued explicitly before the test is
touched, not asserted as the fast path to green.

1. **DepGraph unit tests** (`test/cure/compiler/dep_graph_test.exs`): ordering
   respects order-edges; deterministic output (same input → same order, ready
   set tie-broken alphabetically); cycle → ordering still succeeds, SCC members
   grouped deterministically, and the closed cycle walk is reported in
   `order/1`'s third element; duplicate module error; out-of-set `use` ignored
   for ordering; closure includes qualified-call targets (fixture mirroring
   Access→List/Map/Pair) and auto-prelude edges with the self-exclusions.
2. **Stage1 parity** (red first): property test on the real `lib/compiler`
   tree — for every in-set `use` edge A→B where A and B are in different
   SCCs, `index(B) < index(A)` in `DepGraph.order` (intra-SCC edges are
   exempt: the real tree contains the Environment↔Exception cycle, which must
   be reported in the cycles element); the hardcoded table is deleted only
   after this passes, and `mix cure.compile_stage1` output stays `0 errors`
   with identical module set.
3. **User multi-file linkage** (red first — fails today): two-file fixture
   where `b.cure` `use`s `A` and calls it unqualified; compile via the
   Project/CLI path into a fresh output dir; assert `b`'s beam import table
   contains the remote call to `Cure.A`. Also assert the adversarial file
   order (B listed first) produces the same result.
4. **Fallback warning**: a classic module whose imported call resolves nowhere
   emits the new warning (and still compiles).
5. **Preload closure**: with a controlled fixture (or the baked map directly),
   selecting a group whose member has a cross-group closure dep loads the dep;
   beams-only fallback degrades to selection.
6. **Full `mix test` suite green**; `mix cure.check.examples` and the stage1 +
   stdlib build tasks run clean. One build/test run at a time (hard
   constraint).

## 6. Out of scope

- Kernel/TCB, elaborator, unification, or any dependent-types semantics.
- New surface syntax (no `import` keyword changes, no manifests).
- Rewriting classic codegen's resolution (qualified + dependent paths already
  order-free); the loaded-beam probe stays, now fed by ordered+loaded builds.
- AtomVM/esp32-beam scripts (they benefit transitively via the CLI).
- Renaming `__group__` or restructuring stdlib groups.
- The `Registry`-based protocol cross-module dispatch (`resolve_protocol_call`)
  — separate concern, unchanged.

## 7. Constraints for implementation

- Compile Cure with OTP 26–28 (AtomVM constraint, repo-wide).
- Never run two full build/test passes concurrently.
- `Cure.Compiler.parse_source/2` is the only front-end entry DepGraph may use
  (headless; degrades gracefully without the started app).
- Preload's compile-time baking must keep the `@external_resource`
  invalidation property for every scanned source.
- Deterministic ordering is a hard requirement (reproducible builds).

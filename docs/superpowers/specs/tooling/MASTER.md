# Tooling Specs — Condensed Master

**Date:** 2026-07-21

**Scope.** This document condenses the 15 design specs in `docs/superpowers/specs/tooling/` into one reference
covering: the module system (import surface, cross-module resolution, canonical loading), build orchestration
(dependency-ordered and incremental compilation), the migration facility and lossless printing (including the
Metastatic meta-slot blind spot), elaborator/kernel tooling changes (neutral-application sort inference, Lean-bridge
removal, the proof-authoring ergonomics catalog), macro/staged-execution architecture (Tier-3 `computed by`, the
`Generator` typeclass), and test/docs infrastructure (stdlib test isolation, Markdown example type-checking). It
preserves every locked decision, invariant, constraint, and status marker; implementation step-by-steps and long
examples are dropped. Where a later spec supersedes an earlier one, only the final design is kept, with a one-line
supersession note.

**2026-07-22 execution amendment.**
`2026-07-22-compiler-identity-and-regex-stabilization-plan.md` is the active
implementation plan for canonical module and definition identity, the unified
dependency/emission closure, macro hygiene, dependent-language stabilization,
properties, diagnostics, test isolation, and the bounded-regex resumption gate.
It is grounded in the local Lean 4, Agda, Idris 2, and Racket implementations.
Where it conflicts with the older must-import wording below, the amendment
controls: dependency/interface availability permits canonical qualified access;
`use` controls bare lexical exposure.

**2026-07-30 artifact-integrity amendment.**
`2026-07-30-unified-artifact-integrity-sweep.md` extends and partially
supersedes the incremental-compilation design. Source, interface, and toolchain
hashes remain authoritative for invalidation, but BEAM existence is no longer
sufficient freshness evidence. Compilation, preload, tests, bundling, and
deployment must share one content-addressed artifact-set sweep with per-BEAM
hashes and provenance, complete-set validation, and atomic generation
publication.

**2026-08-03 interface-first amendment.**
`2026-08-03-interface-first-module-pipeline-design.md` supersedes the remaining
loaded-BEAM and order-edge assumptions in the auto-import-order design. `use`
controls lexical exposure only. Qualified access, ambient Prelude selection,
macro output, checking, reachability, and emission resolve through immutable
canonical module interfaces and a checked semantic graph. BEAM availability is
an artifact concern and never a semantic resolver.

---

## 1. Import surface & name visibility (must-import) — PARTIALLY LANDED / remainder PARKED

Source: `2026-07-12-import-surface-must-import-design.md`.

**Superseded availability rule (2026-07-22).** The original design required
`use M` before either bare or qualified access. The compiler-identity plan now
separates the concerns: a module present in the canonical dependency/interface
closure is qualified-available, while `use M` controls bare lexical exposure.
There is still no load-by-mention global namespace: a qualified module must be
present in the dependency graph. This removes macro-generated synthetic imports
without allowing transitive bare-name leakage.

**Consumer surface** (keyword stays `use`):

```cure
use Std.List                         -- all of List's own names, unqualified
use Std.List exposing (map, filter)  -- only these, unqualified
use Std.{List, Core}                 -- grouping sugar
```

- **No `as`, no qualified-only import mode** (operator decision: aliases hurt cross-person readability; one canonical
  way to reach a name).
- Author-side privacy already exists via `local`; do not rebuild it.
- **`exposing` is Elm-style**: unlisted names stay qualified-reachable (`M.other`); the list governs the unqualified
  shortcut, not membership. Chosen over Haskell's "unlisted names entirely gone."
- **Constructors follow the type**: exposing a type does not drag its constructors in; `Type(..)` exposes type + all
  ctors; bare ctor names may be listed. Constructor collisions become opt-in-avoidable.
- **Auto-import explicitly rejected**; instead a targeted "did you mean to expose this?" diagnostic when an unresolved
  bare name is provided-but-not-exposed by an imported module.

**Qualifier resolution — last segment OR full path, nothing partial.** A module has exactly two qualifiers: its last
path segment (`Flow.connect`) and its full path (`Std.Signal.Graph.Flow.connect`). Partial suffixes are NOT
qualifiers. On last-segment ambiguity the only disambiguator is the full path. Bare `Flow` is a type; `Flow.connect`
is module access (parser splits on the trailing `.member`).

**Landed (`d65cf2f`):** brace grouping (`imports/1` expands `:items`) and direct-owner-wins (inert
`Env.import_modules` MapSet of direct imports; `Resolution.prefer_direct/2`; kernel never reads the field).

**Landed-work TRAP:** do NOT gate `resolve_qualified(:value)`'s bare fallback on `import_modules` — tried, regressed 4
tests (instance-delegate resolution contexts lack the set). The latent gap (`Std.String.length` with only `Std.List`
imported falls back to `List.length`) stays reach-pinned.

**Parked build queue:** `exposing` parser + semantics (qualified-only `Mod#name` keys for non-exposed names via
`rekey_module_env`; needs per-source exposing lists threaded), the expose diagnostic, last-segment qualifier
resolution. **Not adopted:** an explicit `unqualified M` keyword (Rust-style leaf binding) — higher-ceremony; revisit
only if deep namespaces proliferate, then with the canonical last-segment rule, never arbitrary aliases.

## 2. User-module import resolution — designed PARKED, since FIXED

Source: `2026-07-12-user-module-import-resolution-design.md` (superseded in practice: resolution landed 2026-07-18 via
`user_source_path` against `:cure_source_roots`; see also catalog entry E3 in §8.3).

**Problem.** The dependent pipeline resolved `use` only for `Std.*`; `use SomeUserModule` + unqualified call →
`:unknown_global`. Fails **closed** (completeness gap, not soundness). Root cause: the classic pipeline resolved
imports untyped from loaded-beam exports (deleted in `07b65ed`); the dependent pipeline needs the callee's type
signatures and recovers them by re-elaborating source — and `import_source_path/1` only knew Std's source dir.

**Design (as executed):** generalize `import_source_path` to an ordered list of source roots (stdlib first, then
project roots); a module resolving nowhere is an explicit `{:error, {:unresolved_module_source, …}}` — the silent
fail-open-to-`Env.empty()` leniency is removed (`use Std.Nonexistent` stops "compiling"). `:source_roots` threaded
through `check_ast/2` (default `[]` preserves Std-only behavior). Cycle guard keys the `seen` set on resolved source
path; determinism follows import-BFS so resolver and `import_origins/1` agree on a name's owner (a mismatch would
type-check against one module and call another). Constraint: E/P layers only, no TCB change. The real E3 root cause
was the module→file mapping for multi-word segments — snake_case each segment via `Macro.underscore`, legacy
all-downcase kept as fallback.

## 3. Canonical module loader — IMPLEMENTATION SPEC (2026-07-17)

Source: `2026-07-17-canonical-module-loader-design.md`. Supersedes the ad-hoc loader paths (`import_source_env/2`,
`module_slice_env/1`, `shadow_resolved_imports/1`, `transitive_import_modules/1`, prelude/macro-home wrappers), which
produced import-order-dependent typing, duplicate diamond elaboration, empty envs from visited modules, and path-keyed
cache identity.

**Prior art adopted:** Lean's `ImportState.moduleNameMap`, Agda's `getInterface`/`VisitedModules`, Idris's
`readModule`/TTC — one interface per canonical name, assembled from interfaces, never per-caller re-elaboration. First
implementation keeps interfaces in memory; persistent `.curei` files are a later optimization.

**Invariants (all ten):**
1. One canonical source path per declared module name per load.
2. A module is parsed/elaborated at most once per loader instance.
3. Elaboration happens in an isolated env determined solely by the module's own source, synthetic prelude edges, and
   declared imports.
4. Direct, transitive, diamond, macro-home, and prelude-entry loads reuse the same interface.
5. Prelude inclusion = dependency edges derived from declaration-site `@prelude` markers; no separate compiler-owned
   auto-prelude list.
6. Repeated imports affect visibility only; they never rebuild declarations.
7. The active load stack rejects cycles with the complete canonical cycle path.
8. Failed interfaces are never treated as successful empty environments.
9. Module identity = declared module name; paths are validated attributes, not cache keys.
10. Kernel/trusted Core unchanged.

**Data model:** loader state map keyed by canonical name: `loading(stack) | loaded(ModuleInterface)
| failed(reason)`. `ModuleInterface` = module_name, source_path, source_hash,
dependency_names/hashes, `owned_env`, `export_env` (the importable portion — the owned/export distinction is
**mandatory** even while equal, pending private declarations), direct_import_names.

**Load algorithm:** resolve (one declared identity + path; reject duplicates and name mismatches) → collect edges
(direct imports + synthetic `@prelude` edges with export filters; providers elaborate from declared imports only,
making the prelude bootstrap graph explicit and acyclic; item-level markers export only that declaration plus a type's
ctors) → recursive load with cycle detection → merge dependency exports once in deterministic edge order → seed
builtins, set owner, elaborate once → totality closure + certification → store. No visited module ever returns
`Env.empty()`. Unqualified visibility derives from direct import edges only; transitive interfaces stay available for
canonical references but never become unqualified merely by being loaded.

**Cache policy:** key = canonical identity + loader generation; failures memoized only within one top-level load;
tests changing source roots get a fresh generation; no `:persistent_term` entry may leak a previous project's
interface. The old recursive loader and path-keyed slice cache are deleted once all callers (Program.elaborate
imports, stdlib compilation, project imports, `@prelude` entry, macro definition-site envs, import-origin discovery)
migrate.

**Non-goals:** `.curei` format, name-resolution/export syntax changes, kernel changes, parallel elaboration (only
after the sequential loader is deterministic and fully tested).

## 4. Dependency-ordered compilation (DepGraph) — APPROVED, LANDED

Source: `2026-07-08-auto-import-order-design.md`.

Replaces hand-maintained ordering (stage1's numeric table, alphabetical accidents) with `Cure.Compiler.DepGraph`
(`lib/cure/compiler/dep_graph.ex`), pure Elixir, fed by the headless `Cure.Compiler.parse_source/2` (the only
front-end entry DepGraph may use). Build-orchestration only: no kernel/elaborator/surface-syntax/manifest changes.

**Two edge kinds (load-bearing, kept separate):**
- **Order-edges** — `use` targets within the compile set only; drive compile order (`order_deps_map/1`).
- **Closure-edges** — superset: `use` + qualified-call targets + auto-prelude providers; drive load/JIT closure
  (`closure_deps_map/1`), never ordering (qualified calls are order-free by construction).

**Ordering:** Tarjan SCC condensation, topological sort, alphabetical tie-break, deterministic (reproducible builds
are a hard requirement).

**Cycle policy — warn and proceed (W086), not error.** Amended 2026-07-08 from the original hard-error policy because
(a) the DAG premise broke — commit `5ef6d80` introduced a genuine `use` cycle `Environment ↔ Exception` in the stage1
Lean-kernel port (type-level mutual recursion, zero runtime calls), and (b) the operator mandated defined SCC
behavior. Cure's compile-set model matches Rust crate-internal modules (cycles legal), not OCaml units. Cycles stay
observable (warning names the closed walk with file:line). Duplicate module name in a set = hard error (E087).

**Integration:** stage1's hand-numbered table deleted; stdlib compile ordered by DepGraph; `Cure.CLI.cmd_compile` and
`Cure.Project.compile_project` order the *union* of all resolved paths and load each emitted beam immediately after
compiling (fixes silently-miscompiled unqualified sibling calls). `cmd_run` out of scope (single-file, no beam on
disk). The classic-codegen silent local-call fallback became a warning (warnings accumulator threaded through codegen
state). `Preload` bakes both maps (order-only for source-JIT ordering; closure for `preload(kind:)` expansion);
`__group__` remains a selection tag only, never ordering; the beams-only release fallback degrades closure to plain
selection.

## 5. Incremental compilation — DESIGN APPROVED (2026-07-18), landed unmerged

Source: `2026-07-18-incremental-compilation-design.md`. A general compiler feature (stdlib + project builds + the test
harness), not test-only.

**Goal.** Recompile `M` iff: (1) its source content changed, (2) any output beam is missing, (3) any direct
dependency's **interface** changed this build, or (4) the compiler itself changed. Interface-level (Swift-style)
invalidation: private-internals changes recompile one module; only consumer-visible changes cascade.

**Soundness argument (why hashing `export_env` is complete):** inline hints travel inside `export_env`, and codegen
never reads dependency beam *content* (only two existence checks, both covered by invariant 2). Hashing the elaborated
env also sidesteps the dependent-types trap that makes *signature* hashing unsound — a consumer's types can depend on
a dependency's value/body (`Vec(n)` with `n` an exported def); the reduced value is in the env. Per-consumed-symbol
invalidation is explicitly out of scope (complete use-sets are hard to capture dependently; a miss = stale beam).

**Fingerprints:** `source_hash` = SHA-256 of source bytes (content, not mtime); `interface_hash` = SHA-256 of
`term_to_binary(export_env, [:deterministic])` (serializability must be verified; fallback = hash a structural
projection); `toolchain` = an embedded content hash of all Cure compiler sources plus `mix.exs` and `mix.lock` —
deliberately coarse-but-safe over a curated subset, and available both under Mix and inside the standalone escript.
Mismatch ⇒ all dirty.

**Dirty-propagation graph MUST use `closure_deps_map/1`, not `order_deps_map/1`** — modules consume `@prelude`
providers ambiently with no `use` edge; order-edges alone would silently miss that invalidation (the exact stale-beam
failure class this design exists to prevent). Closure is a safe superset (qualified-call edges only over-invalidate).

**Mechanics:** manifest v3 separates `workspace_key`, `input_snapshot`, and
`artifact_digest`. It records typed compile-order/interface/runtime edges,
module interfaces, exact BEAM hashes, stat signatures, exports, and provenance.
The artifact digest names an immutable generation published only after full
whole-set verification by atomically replacing `<output_dir>/current`.
`Cure.Compiler.Incremental.compile_dir/3` processes the interface graph as
dependency-first SCCs. Cyclic members are one invalidation unit, eliminating
visit-order prediction. Unparseable sources stay forced compile targets.
Standard-library and project builds use distinct artifact roots:
`_build/cure/ebin` and `_build/cure/project/ebin`. Deletions remain scoped to
the current source roots and run even on `all_dirty` builds. Failed compiles
never publish a candidate generation; dependents see "no stored hash" = changed.
`:force`/`CURE_FULL_REBUILD=1` = clean rebuild.

**Correctness invariants:** never serve a stale beam; beam presence is part of dirtiness; only successful compiles
update the manifest; any manifest absence/corruption/version mismatch ⇒ full rebuild (fail-safe is rebuild, never
skip); hash nondeterminism only over-invalidates, never collides; deletion scoped and unconditional.

Project manifests record and verify the selected stdlib and package artifact digests.
Bundles, escripts, releases, preload, and tests consume the same verified-set
format. Cached verification may reuse a content hash only for an unchanged
device/inode/size/mtime/ctime signature older than a filesystem timestamp
fence; publication and packaging always perform full hashing.
`test_helper.exs` stickiness/completeness checks stay as backstop.

Memory note: landed UNMERGED on `core-let-binder`; traps — compile inside `order_deps`, and invalidate the
`:persistent_term` stdlib cache per recompile.

## 6. Migration facility + `cure migrate` — IMPLEMENTATION-READY, LANDED (unmerged)

Source: `2026-07-10-migration-facility-implementation-design.md`, which **supersedes** the parked capture
`2026-07-09-migration-facility-design.md` (its open lossless-model fork was resolved 2026-07-10; its operator-decided
constraints carry forward).

**Locked constraints:**
1. Migration MUST be lossless — every comment survives; no lossy v0.
2. One rule registry, two consumers: `cure migrate`'s rule set === the set `cure build` warns on.
3. `--strict` promotes migration warnings to errors (warn-now → error-later lifecycle).
4. **Approach A — whole-file canonical reprint** (gofmt/elm-format style), also the engine behind `cure fmt`. Chosen
   over minimal-diff surgical splice (B) as a goal/preference decision — the measured Printer bugs don't discriminate
   A vs B (B needs the same total Printer + trivia model); A also retires the standing Printer/`cure fmt` fidelity
   debt.
5. Keep the hand-rolled Pratt parser — no NimbleParsec (precedence in a compact table; indentation solved in the
   lexer; backtracking/recovery diagnostics NimbleParsec can't match; the trivia model is parser-agnostic anyway).
6. **Git guard:** `cure migrate` refuses unless target files are git-tracked AND clean — per-target `git ls-files
   --error-unmatch` + empty `git status --porcelain -- <path>` (full porcelain deliberately: worktree-only checks miss
   staged-only changes); preflight over the whole target set before any write; read-only modes exempt.

**Empirical grounding (2026-07-10):** round-trip on the comment-heavy corpus lost most comments (e.g. `access.cure`
142 → 11) and one file failed to reparse. Bug 1 — Printer non-total (no `:pin` clause, fell through to `inspect`). Bug
2 — comment capture positional and partial (comments inside constructs dropped).

**Architecture:**
- **Trivia model** (Go `ast.CommentMap`-style): lexer lossless mode collects every comment/blank-run as positioned
  trivia; a single post-parse `Cure.Compiler.Trivia` pass attaches each item to exactly one owning node
  (`meta[:leading]`/`meta[:trailing]`; per-container `meta[:trailer]` buckets for after-last-statement comments in
  *every* statement-list container — load-bearing for totality). Total by construction: an unplaced item is a hard
  error, never a silent drop. Attachment on nodes (not a line-keyed map) so trivia travels through restructuring
  rewrites; `Trivia.carry/2` moves trivia across relocations. AST stays Metastatic 3-tuples; trivia in `meta` — no
  shape change.
- **Printer totality:** every node kind handled; the catch-all **raises** (never `inspect`s); two gates — the corpus
  round-trip/fixpoint test AND a static exhaustiveness cross-check (every parser-constructible node-kind atom has a
  Printer clause), the latter being the falsifiable "total" claim.
- **Blank-line policy** (elm-format style, statement lists only): 0 at top of file, exactly 1 at bottom, exactly 1
  between top-level defs, runs capped at 1 inside blocks, trimmed adjacent to open/close. Rule 5 (multi-line
  expression spans) is documented but **VACUOUS** — Cure has no multi-line collection-literal syntax (verified:
  spanning literals fail to reparse).
- **Rule registry:** `%Cure.Migrate.Rule{id (W-code), description, phase (:syntactic | :needs_resolution),
  detect_and_rewrite (ast, ctx → {:rewrite, ast} | :no_change), warning_template}`. `ctx` = per-file declared+imported
  type-name set, built identically by both consumers (what makes warn/rewrite parity true). Rules run **once each, in
  declaration order, as an ordered fold — no fixpoint**; any future ordering-dependent rule must document it.
- **Three seed rules:** `if/elif → pickup` (syntactic; must resolve its known parenthesised-context reparse limitation
  — skip-and-warn or fix indent-in-parens, or it fails its own gate); uppercase-type-var → lowercase
  (needs-resolution; freshen `T`+`t` collisions with smallest unused numeric suffix, NEVER silently merge); `@group`
  hoist (syntactic; first *relocation* rule — exercises `Trivia.carry/2` and the blank-line policy; idempotent).
- **CLI:** `cure migrate` beside `cure fmt`; in-place default, `--check` (non-zero exit on pending), `--print`,
  `--strict`. Default target discovery mirrors `cure fmt` (`lib/**/*.cure` + `test/**/*.cure`). `--check`/`--print`
  must distinguish "pending migrations" from "failed to migrate cleanly."
- **Batch atomicity:** full pipeline (including a runtime reparse-and-comment-diff check per file) runs in memory for
  all targets first; write only if every file passes — a mid-run failure leaves zero files written.
- **v1 out of scope:** per-rule warn→error maturity (one global `--strict`), rules beyond the three seeds, a full CST
  (trivia-on-meta suffices).
- **Future (post-v1):** repoint `cure fmt` onto the trivia Printer + a conservative Algebra layout layer. The git
  guard is migration-only — pure formatting can't lose information once verify is **comment-aware** (today's
  `verify_algebra` strips comments before comparing; that flip is the one required semantic change).

Memory note: LANDED unmerged — Trivia+Printer, `Cure.Migrate` registry, 3 seed rules.

## 7. Metastatic meta-slot blind spot & migrator rework — DESIGN (2026-07-15)

Source: `2026-07-15-metastatic-meta-blind-spot-design.md`.

**The blind spot.** Metastatic traversal (`prewalk`/`postwalk`/`traverse`) descends only the children slot of `{type,
meta, children}`; the meta slot is copied through unwalked. Cure parks a huge fraction of structure in meta — `param
:type` (999), `function_def :params` (535) / `:return_type` (526), `match_arm :pattern` (366), container `:decorator`
(54), … ≈ **2,600 hidden nodes across the 48-module stdlib**. Every stock-Metastatic consumer (RAG/MCP index,
migrator, future tools) is blind to the entire signature/type/pattern layer.

**Distinct, smaller gap:** six irregular tuple *shapes* (262 occurrences → 6 producer edits; `gadt_ctor` bare child,
`group`/`builtin` 2-tuples, `named_implicit_pat` 4-tuple, `named_dom`, `forced_pattern`), tracked by the
`Cure.MetaAST.Conformance` detector's shrinking allowlist (allowlist reaching `[]` = done). Orthogonal to the meta
gap; both needed for full conformance.

**Why dangerous:** moving a subtree out of meta has **no compiler safety net** — `Keyword.get(meta, :type)` silently
returns `nil` at every stale read site. Hence the detector as green gate.

**Options & decisions:**
- **A** — Cure-side meta-aware traversal wrapper (serves internal tools; leaves the walker-drift trap: anyone reaching
  for stock `prewalk` silently regresses).
- **B** — boundary canonicalization `to_conformant/1` for external consumers. B and C converge (B is C applied at the
  boundary).
- **C** — representation refactor, the principled end-state. Invariant: **no canonical node may appear inside a meta
  value**; every subterm lives in children, scalar annotations stay in meta. Rationale: in a dependent language types
  are terms, so a type annotation is a subterm — filing it in metadata is a category error. **Sub-fork decided: C2 —
  wrapper-node children** (`{:return_type, m, [T]}`, `{:params, m, […]}`) over positional (C1) and
  labeled-children-in-Metastatic (C3, rejected: destabilizes the shared traversal contract). C executes incrementally,
  node type by node type, rewriter-assisted (Sourceror handles construction sites mechanically; read sites
  rewriter-assisted + manual), gated by a `:node_in_meta` detector predicate with a shrinking allowlist. Big-bang
  explicitly not advised.
- **D** (make Metastatic walk meta, opt-in) — contrast only, out of scope.
- **Rejected outright:** a per-key registry of node-bearing meta keys — it IS the walker-drift pattern (fails open);
  all adopted options are structural.

**Recommendation:** ship A+B now (two functions, zero representation risk); file C as the end-state whose
justification is eliminating the standing walker-drift trap; the do-C decision is the owner's one genuine fork.
(Memory note: the conformance detector later took Decision D-variant "nodes STAY in meta" with INV-A/B/C allowlist
gating.)

**§8 phase — rework `Cure.Migrate` onto MetaAST traversal (HARD-ordered downstream of C).** Motivating defect
(verified): rules hand-roll their own walkers; `UppercaseTypeVar` was hand-taught the meta layout (five same-day
fixes); `ModuleRename` was NOT — it renames body calls but leaves both signature occurrences (in meta) pointing at the
renamed-away module while reporting success (half-migrated file, clean bill of health). Principle: **handwrite the
transformation, never the traversal.** Ordering: rebuilding rules on generic traversal *before* C makes them MORE
broken (stock walk never enters meta) — C moves subterms first; C and the rule rebuild advance in lockstep per node
type via the allowlist. Rules rebuild on **Metastatic's own** traversal, not a Cure-only walker (one traversal, one
guarantee, one tripwire). Exit criteria: no rule hand-codes meta descent; rename rules rewrite signature positions
(pinned by the `fn f(x: Std.Eq.T) -> Std.Eq.T = Std.Eq.eq(x)` regression, all three occurrences rewritten);
`:node_in_meta` allowlist empty for every rule-touched node type.

## 8. Elaborator/kernel tooling changes

### 8.1 Neutral-application sort inference (Sigma D1) + D1b — APPROVED, TCB

Source: `2026-07-08-neutral-app-sort-design.md`. Layer K under the Agda/Lean-alignment blanket approval; full
verification gate mandatory.

**Gap.** `infer_type_value_sort/2` had no clause for a neutral application `{:vneutral, {:napp, …}}`, so any dependent
eliminator whose motive applies a type-family variable (canonically Sigma's `second : (p: MySigma(a,b)) ->
b(first(p))`) failed `:bad_motive`. Load-bearing fact: the `:case` rule never term-checks the motive — the sort walk
is its only validation, so the new clause must fully validate, trusting nothing from the elaborator.

**Design — reify + infer, not a head-codomain spine walk.** Reify the neutral via public `Quote.reify/3` **passing
`Context.signature(ctx)`** (required, not optional — the sig-aware form recovers the param/index split of `vdata`
values; without it an `:arg_arity` false rejection reappears) and run the kernel's own trusted `infer/2`; accept only
`{:vtype, l}`. The lighter spine-walk design is rejected because it would not validate arguments, which flow into the
case's result type. Mirrors Lean `inferType` on `App` / Agda sort inference on applied neutrals. **Companion defensive
clause (same TCB change):** `infer(_ctx, {:pair, _, _}) → {:error, :pair_not_inferable}` — the reify+infer path is the
first that can route a pair literal into `infer` at a non-Σ domain, which would otherwise crash with
`FunctionClauseError`. Exactly two new kernel clauses; gate = red-green + new Antigen accept/reject antibodies + full
Antigen + differential-oracle `sg` cluster (Cure/Idris both accept).

**D1b amendment (2026-07-09).** With both kernel clauses in place, the canonical implicit-param probe still failed —
the elaborator's type-position lowering (`idx_to_core` function-call fallthrough) never inserts implicit arguments,
handing the kernel an under-applied spine. Parity defect vs Idris/Agda/Lean (types are terms; one elaborator inserts
implicits everywhere). Fix (E-layer only): thread the params' kernel context into the **return-type lowering only**;
when a term-level global with an `:erased` slot is applied there, delegate the whole application to
`elaborate_implicit_app_bidirectional/6`; NULL the ctx under binder-introducing forms. Blast radius strictly
failure→success. **Residual (documented non-goals):** ctor-signature/index-telescope positions, parameter-type
annotations, and under-binder subexpressions keep today's bare spine. Test-plan correction: the pair-literal negative
must use a *function-typed* head (a Nat-typed head fails `ensure_pi` first and proves nothing).

### 8.2 Lean4lean bridge removal (task #17) — EXECUTED

Source: `2026-07-09-lean-bridge-removal-design.md`. Operator-ordered rip-out of the Lean backend (artifact set of
commit `3d6f739` + encoder hunks of `ae02ba5`/`ccbe2d0`). **Mechanism deviation, empirically justified:** `git revert`
conflicts in 4 files and would silently re-privatize `local_def_names/1` (three later non-bridge call sites — it MUST
stay public) and resurrect a deleted README — so one manual deletion commit citing the reverted material, not a
dishonest "Revert" commit. Deleted: `lib/cure/lean/`, `lib/cure/kernel/backend*`, `lean_bridge/`, their tests, five
bridge functions in `program.ex`/`declarations.ex`; dependent checking rewired directly to the elixir-core path (the
`:elixir_core`/`:lean` selection layer removed — no live caller ever selected `:lean`). Kept: `local_def_names/1`
public; `check_ast/2` opts arity; checker opts-threading; all prose-only Lean mentions (historical specs are records —
supersession lives in the commit message, docs are not edited). Supersedes cleanup-strategy decision 6 ("second
backend is a long-term goal"). Zero surviving-test changes; behavior byte-identical.

### 8.3 Proof-authoring elaborator ergonomics — LIVING CATALOG

Source: `2026-07-17-proof-authoring-elaborator-ergonomics-design.md`. Opened while dogfooding the OTP metatheory
(`Std.Otp.*`). None are soundness holes — they are the gap between the proof an author reaches for and what Cure
accepts. **Standing rule:** when a proof only goes through via a structural trick or confusing rejection a smarter
elaborator would avoid, add an entry; do not silently absorb the tax. Landed entries stay (history). Cross-reference:
the Lean-shape matching spec's full context-refinement closes most of E1/E2/E8 at once.

| Entry | Gap | Status |
|---|---|---|
| E1 | `match` refined the motive but not sibling context binders → nested matches couldn't prune impossible ctors | ✅ FIXED — branch substitutions refine context types AND NbE values; kernel independently re-checks |
| E2 | Index existentials not bindable by name in patterns | ✅ FIXED for erased slots (distinct names). **Residual:** a *relevant* index existential still can't be named — workaround: explicit ctor FIELD + congruence helper; full fix = named-implicit binders on ctor patterns |
| E3 | `use` of implicit-carrying stdlib fn → `:unknown_global` | ✅ FIXED — real cause was module→file mapping (multi-word segments); `Macro.underscore` per segment, legacy fallback kept |
| E4 | Partial application of explicit-arg fn type-checked but emitted wrong arity | ✅ FIXED — `emit.ex` `lower_app_spine` eta-expands under-saturated globals into the curried 1-arg ABI |
| E5 | `##` comments between GADT constructors were a parse error | ✅ FIXED — parser skips comment tokens in `parse_gadt_ctors` |
| E6 | Nullary GADT ctor whose indices come only via a sibling's existential → `:unsolved_metavariables` | ✅ FIXED (Idris2-style postpone-and-fixpoint in `check_ctor_args`, mirroring `checkRestApp`/checkRtoL). **Residuals OPEN:** (a) index via an *enclosing function's* implicit — nested `finish_ctor_app` finalizes metavars eagerly in an isolated metacontext; architectural fix = one shared metacontext through the whole application tree; workaround: typed helper fn pinning the index. (b) wrapped step relations with floating OUTPUT indices — fix is REFORMULATION: index families whose indices are all determined by scrutinee/goal head (proof-authoring lesson) |
| E7 | `_` in a call argument parsed as a global | ✅ FIXED — placeholder-bearing calls route to bidirectional Π-telescope solving; `_` is goal-directed only in direct call-arg slots, must solve before Core |
| E8 | Sequential-match refinement doesn't compose across independent scrutinees (each `match` has its own motive; later substitutions aren't back-propagated) | OPEN — workaround: helper-delegation (move the evidence match into a function taking the evidence as parameter). Same fix family as E1/E2 — simultaneous matching |
| E9 | Stuck-index equation not retained as a proof term on GADT match; no ctor injectivity for the identity type | OPEN — fix sketch: reflect the residual constraint as a branch hypothesis `Equivalent(…)` (Agda/Idris `with`-style) + derived injectivity eliminator |
| E10 | Higher-order fn argument not β/δ-reduced in a dependent index position (free-monad `bind` laws blocked) | OPEN — workaround: first-order monoid reformulation; fix: normalise applied functions inside conversion at index positions |
| E11 | Ambiguous applied def head in type position silently degraded to an unresolvable bare key | ✅ FIXED Stage 1 (`applied_def_key/3`: qualified resolves via VALUE namespace; ambiguous bare = clean `:ambiguous_name`). Stage 2 OPEN: type-directed tie-breaking |
| K1 | Inconsistent A6 freeze in `Normalise.reduce_unfolded` — `f(<ctor>,x)` froze but `f(<reducible-global>,x)` reduced → equal terms got different NFs (conversion incompleteness) | ✅ FIXED (`dee86c0b`) — recurse on the ι-result so a residual stuck `ncase` propagates `:stuck`; the fix only ever freezes MORE. Preserved warning: the "obvious" self-recursion-only freeze is WRONG (breaks mutual-recursion NF termination — needs an unfold *stack*) |

**Confirmed non-gaps (do NOT chase):** sibling refinement into the motive works; explicit relevant siblings are
refined for type computation; empty `match` on an uninhabited indexed type is accepted and total.

## 9. Macro facility & staged execution

### 9.1 Tier-3 `computed by` execution — DESIGN, locks the approach

Source: `2026-07-12-tier3-computed-by-execution-design.md`.

- **Decision A — execute by ELABORATE + NORMALISE, not compile-and-load.** An elab function runs by elaborating it to
  Core, applying it to the quoted input, and normalising with the kernel — the NF *is* the expansion. Terminates
  (elabs are size-change-certified total). **TCB delta ZERO**: calling the trusted normaliser is not a kernel edit;
  the elab's output is re-elaborated + kernel-checked (K3 firewall). Rejected: compile-to-BEAM + load (heavier,
  mutates the code server, duplicates kernel evaluation).
- **Decision B — generic `Std.Syntax` value as substrate; typed records as the API.** A single `Std.Syntax` ADT
  (`Node(tag, children) | Leaf(tag, SynLit)`) mirrors the parser shape, with an Elixir reflection bridge
  `to_syntax`/`from_syntax`. **Operator steer:** the elab-*author*-facing API MUST be the typed derived record (`rec
  RuleSyntax { <hole>: Syntax(<Kind>) }` synthesised from the rule's holes; authors write `a.name`, compile-checked) —
  a generic stringly `field("name")` accessor is explicitly rejected as the shipped API; the record slice lands with
  or immediately after execution.
- **Decision C — `:computed` expands at ELABORATION time, not parse time.** Parser harvests uses and emits a deferred
  `{:computed_use, meta, [elab_ref, bound_input]}` node; an elaboration-time pass (in `lib/cure/elab/*`, untrusted)
  builds the Syntax value, normalises `app(elab, input)`, `from_syntax`es, splices, and re-elaborates. Genuine phase
  distinction from Tier-1/2 (parse-time).
- Slices: 1 parse ✅ DONE (`ce62b17`); 2 Syntax + bridge; 3 execution pass (the big one); 4 `quote`/`$()` sugar; 5
  `check…else fail`; 6 typed records. Open items pinned pre-execution: hook point, elab-ref-to-Core application,
  Syntax as a normaliser-reducible inductive, purity (elab signature is `Syntax -> Syntax`, never `Effect(Syntax)`),
  bounded-depth fuel for macro-emitting macros. Tier-3 execution gates the `actor`/`sup`/`fsm` container macros (macro
  design §14.6).

### 9.2 `Generator` typeclass + PBT engine — DESIGN, phased, not scheduled

Source: `2026-07-12-generator-typeclass-pbt-architecture.md`.

**One-sentence decision:** ship a `Generator(a)` typeclass (stdlib instances + `deriving`) as the single source of
"how to generate an `a`," shared by user property tests and SP3's macro fuzzer; keep the *engine* separate from the
*domain* (the Hegel pattern) — `Std.Test.forall` at runtime for users, Antigen on the host for the compile-time
fuzzer; later port Hypothesis's choice-sequence "conjecture" model underneath so shrinking becomes internal and free,
and re-base both runners on it.

Key points: users never run on Antigen (two runners, two audiences — choosing Antigen for SP3 costs users nothing);
dependent/indexed types take the index (`Generator(Vector(n,a))` draws exactly `n` — well-typed by construction, a
differentiator over QuickCheck); the hard instance is `Code`/`Block` (needs the reflection API, written once as a
`Generator` instance); an external Python Hypothesis process is explicitly rejected (breaks the self-contained
toolchain and deterministic builds). Phase 1 = typeclass + instances + `deriving` over `Std.Gen`'s explicit-shrinker
model; Phase 2 = conjecture core + example database (unifies with Antigen's `corpus.sexp` replay store); the
`Generator` interface is designed to survive the re-base unchanged. SP3's compile-time use rests on Tier-3 staged
execution (SP2) + reflection (SP4). TCB delta zero.

## 10. Test & docs infrastructure

### 10.1 Stdlib test isolation (sticky + namespacing) — APPROVED (2026-07-17)

Source: `2026-07-17-stdlib-test-isolation-design.md`.

**Problem.** One global BEAM code table; producer tests emitted their own (pared-down or differently-lowered) versions
of stdlib modules under canonical names, clobbering the canonical for later consumers → order-dependent contamination;
~44 files serialized with `async: false` as a band-aid. Structural root: `Emit.remote_target/2` hardcodes canonical
remote targets into callers. Rejected alternative: partitioning the suite into multiple OS processes.

**Architecture — two mechanisms + carve-outs:**
- **C1 — stick the canonical stdlib at suite startup:** load every compiled canonical beam and `:code.stick_mod` it
  (scope: `Cure.Std.*` only, never test-emitted modules). Completeness asserted against an independently-derived
  expected set built by re-running the `@mod_regex` source-declaration scan freshly at suite startup — NOT by
  inverting the basename transform (**not invertible**: `non_empty.cure` declares `Std.NonEmpty` whose forward
  transform gives "nonempty", a live counter-example) and NOT by reading the possibly-stale baked
  `@std_module_groups`. **Sticky blocks reload, not purge+delete** — the two audited `preload_test.exs` sites that
  legitimately purge a sentinel must re-stick in their `after` blocks with `:code.is_sticky/1` assertions; any future
  eviction must do the same. `preload_test.exs` stays `async: false`.
- **C2 — namespace the producers:** thread an optional module-name `prefix` + `local_owners` (owner strings exactly as
  `Name.owner/1` returns them) through `Emit.compile_and_load/compile_forms/remote_target`; intra-group calls get the
  prefix, extra-group calls stay canonical (hit the sticky stdlib). **Invariant:** `prefix: ""` is byte-identical to
  today (guards golden/production). Multi-call groups MUST pass explicit whole-group `local_owners` (the per-call
  default is single-owner only). C2 lives in `Cure.Elab.Emit` only — it does not reach
  `Cure.Compiler.compile_and_load/2`.
- **C3 — simplify pure consumers** (emit only for historical safety) to call the sticky canonical directly
  (`stdlib_test.exs` is C3, not C2; `iter_test.exs` needs nothing — pure consumer-side victim, fixed by C1 alone).
- **C4 — golden carve-out:** `actor_quote_golden_test.exs` byte-hashes beams (never loads them); verify unchanged,
  don't migrate. "All async" is honestly ~95% due to this file.
- **C5 — flip clobber-serialized files to `async: true`**; files with genuine non-clobber global state
  (telemetry/otel/observe/profiler, most antigen) stay serial.

A missed producer becomes a loud deterministic `:sticky_directory` failure — the forcing function; never resolved by
loosening sticky. Gate: full suite green twice at two fixed seeds; timing ≤ the ~6-min Path B elaboration-cache
baseline (`0c36c631`, orthogonal, stays).

### 10.2 Markdown example type-checking — APPROVED DESIGN (2026-07-12)

Source: `2026-07-12-markdown-example-typechecking-design.md`.

Every ` ```cure ` fenced block in `.md` files is extracted and **type-checked** (not evaluated — `# =>` comments stay
illustrative; evaluation doctests are the separate existing `cure>`/`=>` Doctests facility). First consumer:
`docs/GLOSSARY.md` (its 100 examples made self-contained as part of the work, asserted by a test).

- **Directive grammar** on the fence info-string: bare/`check` (must type-check, default), `ignore`, `fail`,
  `fail=<reason>` (case-insensitive substring of error text/kind). Any other suffix is a **hard extraction error** —
  typos must not silently become unchecked blocks. Unterminated fences are errors too. Extractor: new
  `Cure.Doc.MdExamples` (block = `%{directive, code, line}`).
- **Hybrid assembly** in `example_runner`: (1) block with its own `mod` compiles verbatim, no prelude injected; (2)
  declarations without `mod` get a synthetic module + configurable default prelude
  (Std.Show/Option/Result/List/String/Semigroup/Comparable/Map/Set); (3) expression-only blocks wrap as a synthetic
  zero-arg fn body. Comment-only blocks intentionally fail (the nudge to mark them `ignore`).
- **Full `compile_string` path deliberately** (not check-only): fsm/actor/sup/app containers validate during codegen.
  Throwaway output dir.
- **Delivery:** `cure check <file>.md` (extension dispatch on the existing verb) and `mix cure.check.docs` (default
  glob `docs/**/*.md`, added to the `mix cure.check` aggregator); per-block output + summary; exit 0/1.
- **Deferred:** harvesting blocks from `.cure` doc-comments (36 stdlib files), an evaluation mode, inner-line error
  mapping.

---

## Source specs

- `2026-08-03-interface-first-module-pipeline-design.md` — interface-first
  compilation universe; lexical `use` versus qualified/interface availability;
  bootstrap and checked semantic graphs; interface SCCs; canonical resolution;
  BEAM-independent emission; incremental/component hashing; migration and
  stabilization gates. Supersedes the 2026-07-08 loaded-BEAM/order assumptions.
- `2026-07-08-auto-import-order-design.md` — DepGraph dependency-ordered compilation; order- vs closure-edges; W086
  SCC cycle policy; entry-point and Preload integration.
- `2026-07-08-neutral-app-sort-design.md` — kernel neutral-application sort inference via reify+infer (two TCB
  clauses) plus the D1b elaborator implicit-insertion-in-return-types amendment.
- `2026-07-09-lean-bridge-removal-design.md` — exact-scope manual removal of the lean4lean backend and its selection
  layer; why a git revert was unsafe.
- `2026-07-09-migration-facility-design.md` — parked design capture for `cure migrate`; recorded the operator-locked
  lossless/one-registry/`--strict` constraints. Superseded by the 2026-07-10 implementation design.
- `2026-07-10-migration-facility-implementation-design.md` — the implementation-ready migration facility: Approach A
  whole-file reprint, trivia model, Printer totality, rule registry, three seed rules, git guard, batch atomicity,
  `cure fmt` convergence plan.
- `2026-07-12-generator-typeclass-pbt-architecture.md` — `Generator(a)` typeclass as the single generation source;
  engine/domain split; two-phase plan toward a ported Hypothesis conjecture core.
- `2026-07-12-import-surface-must-import-design.md` — must-import model, Elm-style `exposing`, constructor visibility,
  last-segment-or-full-path qualifiers; landed grouping + direct-owner-wins; parked remainder.
- `2026-07-12-markdown-example-typechecking-design.md` — ` ```cure ` fenced-block extraction, directive grammar,
  hybrid assembly, `cure check *.md` / `mix cure.check.docs`, the GLOSSARY fixing pass.
- `2026-07-12-tier3-computed-by-execution-design.md` — Tier-3 macro execution by elaborate+normalise, generic
  `Std.Syntax` substrate with typed derived-record API, elaboration-time expansion pass, slice decomposition.
- `2026-07-12-user-module-import-resolution-design.md` — generalizing `import_source_path` to project source roots;
  fail-closed unresolved modules; cycle/ordering rules (since executed; "parked" status stale).
- `2026-07-15-metastatic-meta-blind-spot-design.md` — the ~2,600-node meta-slot traversal blind spot; options
  A/B/C(/D); the C2 wrapper-children decision; detector-gated incremental refactor; the migrator→MetaAST rework phase
  and its lockstep dependency on C.
- `2026-07-17-canonical-module-loader-design.md` — one-interface-per-module loader (Lean/Agda/Idris model); the ten
  loading invariants; ModuleInterface data model; cache/generation policy.
- `2026-07-17-proof-authoring-elaborator-ergonomics-design.md` — living catalog E1–E11 + K1 of proof-authoring gaps
  with statuses, residuals, and confirmed non-gaps.
- `2026-07-17-stdlib-test-isolation-design.md` — sticky canonical stdlib + producer namespacing (C1–C5) for a
  deterministic, parallel-safe test suite.
- `2026-07-18-incremental-compilation-design.md` — interface-level incremental compile driver:
  source/interface/toolchain fingerprints, manifest, closure-edge dirty propagation, scoped deletions, correctness
  invariants.
- `2026-07-22-compiler-identity-and-regex-stabilization-plan.md` — canonical module/declaration identity from
  resolution through emission (one `CompilationWorld` shared by resolution, elaboration, normalization, conversion,
  totality, reachability, and emission); the dependent-language stabilization sequence (local functions, matches,
  literals, `Char`/`String`, `Bounded`) gating the bounded-regex fixture's resumption.
- `2026-07-30-unified-artifact-integrity-sweep.md` — content-addressed artifact sweep shared by compilation, preload,
  testing, bundling, and release; replaces BEAM-existence freshness with per-BEAM hashing, provenance, and atomic
  generation publication; extends and partially supersedes the incremental-compilation design above.

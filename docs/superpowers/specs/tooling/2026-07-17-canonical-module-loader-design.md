# Canonical Module Loader

**Status:** implementation specification

**Date:** 2026-07-17

**Applies to:** source imports, standard-library imports, automatic preludes,
project modules, macro definition-site environments, interface caching, import
cycles, and import visibility

## 1. Problem

Cure currently discovers and elaborates imported modules through several paths:

- `import_source_env/2` recursively elaborates source;
- `module_slice_env/1` separately elaborates and caches source by path;
- `shadow_resolved_imports/1` constructs another merged import environment;
- `transitive_import_modules/1` independently walks the dependency graph;
- prelude contributors and macro homes enter through additional wrappers.

These paths do not construct identical module environments. In particular, a
module can see automatic-prelude definitions when imported directly but lose
them when elaborated transitively. Diamonds can elaborate the same source more
than once, a visited module may contribute an empty environment, and cache
identity is a path rather than the declared module identity.

The result is import-order-dependent typing. Adding an explicit dependency can
hide an individual failure, but it cannot make the loader coherent.

## 2. Prior art

Lean, Agda, and Idris use the same essential model.

- Lean's `ImportState.moduleNameMap` stores one `ImportedModule` per canonical
  name. Repeated visits reuse or upgrade that entry. Environments are assembled
  from serialized `.olean` interfaces, not by elaborating source in each caller.
- Agda's `getInterface` consults `VisitedModules`, detects cycles through an
  active import stack, creates an interface in isolation when necessary, stores
  it, and reuses it thereafter.
- Idris' `readModule` loads a `.ttc` once, tracks `allImported`, and treats the
  prelude as an ordinary synthetic import. Visibility can change without
  reloading the module.

Cure adopts this shared architecture without copying their artifact formats.
The first implementation may keep interfaces in memory and continue using the
existing `Env`; persistent `.curei` files are a later optimization.

## 3. Invariants

1. A declared module name has exactly one canonical source path in a load.
2. A module is parsed and elaborated at most once per loader instance.
3. A module is elaborated in an isolated environment determined solely by its
   own source, synthetic prelude edges, and declared imports.
4. Direct, transitive, diamond, macro-home, and prelude-entry loads reuse the
   same interface.
5. Prelude inclusion is represented as dependency edges before graph loading.
   Every edge is derived from a declaration-site `@prelude` marker; there is no
   separate compiler-owned auto-prelude list.
6. Repeated imports affect visibility only; they do not rebuild declarations.
7. The active load stack rejects cycles with the complete canonical cycle path.
8. Failed interfaces are not treated as successful empty environments.
9. Module identity is the declared module name. Paths are validated attributes,
   not cache keys.
10. The kernel and trusted Core are unchanged. Imported declarations have
    already passed the same elaboration, totality, and certification gates as
    local declarations.

## 4. Data model

The loader owns a state map keyed by canonical module name:

```text
ModuleState = loading(stack) | loaded(ModuleInterface) | failed(reason)
```

`ModuleInterface` contains:

```text
module_name
source_path
source_hash
dependency_names
dependency_hashes
owned_env
export_env
direct_import_names
```

`owned_env` is the module's certified environment including canonical owned
identities. `export_env` is the portion importers may merge. Initially these may
be equal because Cure does not yet have private module declarations, but the
distinction is mandatory.

## 5. Loading algorithm

### 5.1 Resolve

Resolve an import spelling to one declared module identity and source path.
Reject missing modules, duplicate declarations of the same identity, and a
declared name that does not match the requested identity.

### 5.2 Dependency edges

Parse the source header and collect direct imports. Scan the standard library
for module- and item-level `@prelude` markers and add their providers as
synthetic edges with export filters. A provider module is elaborated from its
declared imports only, which makes the prelude bootstrap graph explicit and
acyclic. A whole-module marker exports the complete interface; an item marker
exports only that declaration (and a type's constructors).

### 5.3 Load

For `load(name)`:

1. return the stored interface when state is `loaded`;
2. return the stored error when state is `failed`;
3. report the active cycle when state is `loading`;
4. mark the module `loading`;
5. recursively load every dependency;
6. merge dependency export environments once, in deterministic edge order;
7. seed builtins and set the module owner;
8. elaborate local declarations once;
9. run totality closure and certification;
10. store and return the interface.

No visited module returns `Env.empty()`. It returns its interface.

### 5.4 Scope assembly

The caller's unqualified visibility is derived from its direct import edges.
Transitive interfaces remain available for canonical global references and
certification, but do not become unqualified merely because they are loaded.
Existing ambiguity and `exposing` rules remain authoritative.

## 6. Cache policy

The in-memory cache key is canonical module identity plus a loader generation.
The interface records source and dependency hashes so a later persistent cache
can validate artifacts exactly as Idris validates TTC import hashes. Failures may
be memoized only within one top-level load and must be cleared for a new source
generation.

Tests that change source roots receive a fresh loader generation. No
`:persistent_term` entry may make a temporary project observe a previous
project's interface.

## 7. Integration

The following paths must delegate to the canonical loader:

- ordinary `Program.elaborate` imports;
- standard-library compilation;
- project module imports;
- `@prelude` entry loading;
- macro definition-site environment loading;
- import-origin and transitive-family ownership discovery.

The old recursive source loader and path-keyed slice cache are deleted after
all callers migrate. Compatibility wrappers may exist during implementation but
must not retain independent recursion or caching.

## 8. Verification

Required regressions:

- direct import;
- transitive import whose dependency uses automatic-prelude functions;
- diamond import, with the shared module elaborated once;
- duplicate direct import is idempotent;
- explicit plus transitive import is order-independent;
- cycle reports every module in the cycle;
- two files declaring one module identity are rejected;
- macro-home loading reuses the ordinary interface;
- temporary project roots do not reuse stale interfaces;
- imported coherence, builtins, certification, and inline hints survive.

Required gates are focused loader tests, all elaborator tests, all stdlib tests,
Antigen shape coverage, and the full suite.

## 9. Non-goals

- No `.curei` persistent artifact format in this phase.
- No change to name-resolution or export syntax.
- No kernel, conversion, or coverage-checker change.
- No parallel module elaboration until the canonical sequential loader is
  deterministic and fully tested.

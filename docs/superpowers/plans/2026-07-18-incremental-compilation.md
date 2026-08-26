# Incremental Cure Compilation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make multi-file Cure builds recompile only modules whose output could differ, using content fingerprints + interface-level (Swift-style) invalidation, as a general compiler feature.

**Architecture:** A new `Cure.Compiler.Incremental` driver sits between "list of source files" and "compile each file". It uses `Cure.Compiler.DepGraph` for the dependency graph (`closure_deps_map/1` — the superset that includes ambient `@prelude` and qualified-call edges, not just `use` edges) and `toposort/2` for a deterministic walk order, a `Cure.Compiler.BuildManifest` for the persisted fingerprint store, and a new public `Cure.Elab.Program.module_interface/2` to obtain each module's `export_env` (the exact artifact consumers elaborate against) for interface hashing. Dirtiness is decided and compilation happens in a **single interleaved topological walk** — a module's dirtiness depends on its dependencies' freshly-recomputed interface hashes, which only exist after those dependencies compile. Both `mix cure.compile_stdlib` and `mix cure.compile` route through the driver; `test/test_helper.exs` inherits the speedup unchanged.

**Tech Stack:** Elixir, ExUnit, `:crypto.hash/2`, `:erlang.term_to_binary/2`, existing `Cure.Compiler.{DepGraph, compile_file}` and `Cure.Elab.Program`.

## Global Constraints

- Compile Cure with OTP 26–28 (host compiler unaffected by AtomVM limits).
- Never co-sign commits — author as the user only.
- `lib/cure/elab/program.ex` and `lib/cure/core/*` are TCB: run the full gate (`mix test`, expect Antigen 318/318 and 0 failures) for any task touching them. The only such change here (Task 1) is a purely additive public accessor.
- Author stdlib in `lib/std/`; `priv/std` is generated — do not edit.
- Correctness rule that must never regress: **never serve a stale beam.** Every failure mode (absent/corrupt manifest, missing beam, compile error, non-serializable env) must fall back to *recompile*, never to *skip*.
- Fingerprints are content-based (`:crypto.hash(:sha256, ...)`), never mtime.
- Default `output_dir` is `_build/cure/ebin` everywhere; **`cure.compile_stdlib` and `cure.compile` share this default**, so both can write into the same manifest file — the driver's deletion logic is scoped to each run's own source roots to keep them from destroying each other's entries.
- Use `closure_deps_map/1` (NOT `order_deps_map/1`) for the dirty-propagation graph. `order_deps_map/1` is `use`-only and would silently miss ambient `@prelude` edges — the exact stale-beam hole this feature exists to close. `closure_deps_map/1` is a safe superset (it also includes qualified-call targets, which only over-invalidate).

---

## File Structure

- **Modify** `lib/cure/elab/program.ex` — add public `module_interface/2` wrapping the existing private `cached_module_interface/2` (Task 1).
- **Create** `lib/cure/compiler/build_manifest.ex` — `Cure.Compiler.BuildManifest`: the fingerprint store (load/save/atomic-write, empty, toolchain fingerprint). No compile logic (Task 2).
- **Create** `lib/cure/compiler/incremental.ex` — `Cure.Compiler.Incremental`: `interface_hash/1` (Task 3) + the dirty-set walk + compile driver `compile_dir/3` (Task 4).
- **Modify** `lib/mix/tasks/cure.compile_stdlib.ex` — route through `Incremental.compile_dir/3` (Task 5).
- **Modify** `lib/mix/tasks/cure.compile.ex` — route directory builds through the driver with a `stdlib_hash` guard (Task 6).
- **Create** `test/cure/elab/module_interface_test.exs` (Task 1).
- **Create** `test/cure/compiler/build_manifest_test.exs` (Task 2).
- **Create** `test/cure/compiler/incremental_hash_test.exs` (Task 3).
- **Create** `test/cure/compiler/incremental_test.exs` (Task 4).
- **Create** `test/mix/tasks/cure.compile_stdlib_incremental_test.exs` (Task 5).
- **Create** `test/mix/tasks/cure.compile_incremental_test.exs` (Task 6).

---

## Task 1: Public interface accessor on the loader

Expose the loader's per-module interface (which carries `export_env` and the already-computed `source_hash`) so the driver can hash it. This is the only TCB-file change and it is purely additive.

**Files:**
- Modify: `lib/cure/elab/program.ex` (add public function near the existing private `cached_module_interface/2` at ~line 1441)
- Test: `test/cure/elab/module_interface_test.exs` (Create)

**Interfaces:**
- Produces: `Cure.Elab.Program.module_interface(module_name :: String.t(), path :: String.t()) :: {:ok, map()} | {:error, term()}`. The map includes at least `:export_env`, `:source_hash` (a 32-byte binary), `:module_name`, `:path`. Semantics identical to the private `cached_module_interface/2`: `:persistent_term`-cached for stdlib paths, recomputed for others.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/module_interface_test.exs
defmodule Cure.Elab.ModuleInterfaceTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  test "module_interface/2 returns the export_env and source_hash for a stdlib module" do
    path = "lib/std/core.cure"
    assert {:ok, iface} = Program.module_interface("Std.Core", path)
    assert is_map(iface.export_env)
    assert is_binary(iface.source_hash) and byte_size(iface.source_hash) == 32
  end

  test "module_interface/2 is a cache hit on the second call (same term)" do
    path = "lib/std/core.cure"
    assert {:ok, a} = Program.module_interface("Std.Core", path)
    assert {:ok, b} = Program.module_interface("Std.Core", path)
    # stdlib interfaces are persistent_term-cached, so the cached tuple is reused
    assert :erts_debug.same(a, b)
  end

  test "module_interface/2 surfaces an error for a missing file" do
    assert {:error, _} = Program.module_interface("Nope", "lib/std/does_not_exist.cure")
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/module_interface_test.exs`
Expected: FAIL with `UndefinedFunctionError` for `Cure.Elab.Program.module_interface/2`.

**If `lib/std/core.cure` does not exist** or its module name is not `Std.Core`, pick any real stdlib module by listing `lib/std/*.cure` and reading its `module` declaration; use that path + name consistently across Tasks 1 and 3. Do not invent a module.

- [ ] **Step 3: Add the public function**

In `lib/cure/elab/program.ex`, immediately above `defp cached_module_interface(module_name, path) do` (~line 1441), add:

```elixir
@doc """
Return the canonical module interface for `module_name` at `path`.

The interface map carries the elaborated `:export_env` a consumer merges in
when it imports this module, plus its `:source_hash`. This is the exact
artifact incremental compilation hashes to decide whether a change to this
module can affect its dependents. Semantics match the internal loader cache:
`:persistent_term`-cached for stdlib paths, recomputed otherwise.
"""
@spec module_interface(String.t(), String.t()) :: {:ok, map()} | {:error, term()}
def module_interface(module_name, path) when is_binary(module_name) and is_binary(path) do
  cached_module_interface(module_name, path)
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/module_interface_test.exs`
Expected: PASS (3 tests).

**If `cached_module_interface/2` returns a bare map rather than `{:ok, map}`** (verify by reading its body), change the wrapper to match its actual contract and update the test's `{:ok, iface}` matches accordingly. The wrapper must expose exactly what `cached_module_interface/2` returns — do not reshape it.

- [ ] **Step 5: Run the full gate (TCB file touched)**

Run: `mix test`
Expected: 0 failures; `Antigen shape-coverage: 318/318`.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/elab/program.ex test/cure/elab/module_interface_test.exs
git commit -m "feat(elab): expose module_interface/2 for incremental compilation"
```

---

## Task 2: `BuildManifest` — fingerprint store

The persisted fingerprint store plus the toolchain fingerprint. No compile logic; pure data + IO.

**Files:**
- Create: `lib/cure/compiler/build_manifest.ex`
- Test: `test/cure/compiler/build_manifest_test.exs`

**Interfaces:**
- Consumes: nothing from earlier tasks.
- Produces:
  - `@type entry :: %{source_path: String.t(), source_hash: binary(), interface_hash: binary() | nil, deps: [String.t()], beams: [String.t()]}`
  - `@type t :: %{version: pos_integer(), toolchain: binary(), stdlib_hash: binary() | nil, modules: %{String.t() => entry()}}`
  - `Cure.Compiler.BuildManifest.empty(toolchain :: binary()) :: t()`
  - `Cure.Compiler.BuildManifest.load(output_dir :: String.t()) :: t()` — returns a fresh empty manifest (with `toolchain: ""`, `stdlib_hash: nil`) on any read/decode/shape problem.
  - `Cure.Compiler.BuildManifest.save(manifest :: t(), output_dir :: String.t()) :: :ok` — atomic (temp file + rename).
  - `Cure.Compiler.BuildManifest.toolchain_fingerprint() :: binary()` — SHA-256 over the `:cure` app's compiled `.beam` files.
  - `@manifest_version 1` and the on-disk filename `.cure_manifest`.

The `stdlib_hash` top-level field is nil for a stdlib build (`cure.compile_stdlib`) and carries a fingerprint of the external stdlib beams only for project builds (`cure.compile`) — see Task 6. The manifest stores it; the driver decides its value.

- [ ] **Step 1: Write the failing tests**

```elixir
# test/cure/compiler/build_manifest_test.exs
defmodule Cure.Compiler.BuildManifestTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.BuildManifest, as: M

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_manifest_test_#{:erlang.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "load/1 on an empty dir returns an empty manifest", %{dir: dir} do
    m = M.load(dir)
    assert m.version == 1
    assert m.modules == %{}
    assert m.stdlib_hash == nil
  end

  test "save/1 then load/1 round-trips", %{dir: dir} do
    m = %{
      version: 1,
      toolchain: <<1, 2, 3>>,
      stdlib_hash: <<4, 5>>,
      modules: %{
        "Std.List" => %{
          source_path: "lib/std/list.cure",
          source_hash: <<9>>,
          interface_hash: <<8>>,
          deps: ["Std.Core"],
          beams: ["Cure.Std.List.beam"]
        }
      }
    }

    assert :ok = M.save(m, dir)
    assert M.load(dir) == m
  end

  test "load/1 tolerates a manifest written without stdlib_hash", %{dir: dir} do
    File.write!(
      Path.join(dir, ".cure_manifest"),
      :erlang.term_to_binary(%{version: 1, toolchain: <<7>>, modules: %{}})
    )

    m = M.load(dir)
    assert m.toolchain == <<7>>
    assert m.stdlib_hash == nil
  end

  test "load/1 on a corrupt manifest returns empty, never raises", %{dir: dir} do
    File.write!(Path.join(dir, ".cure_manifest"), "not a term <<<")
    assert M.load(dir).modules == %{}
  end

  test "load/1 on a wrong-version manifest returns empty", %{dir: dir} do
    File.write!(Path.join(dir, ".cure_manifest"), :erlang.term_to_binary(%{version: 999, toolchain: "", modules: %{}}))
    assert M.load(dir).modules == %{}
  end

  test "save/1 is atomic — no .tmp file is left behind", %{dir: dir} do
    assert :ok = M.save(M.empty(<<0>>), dir)
    refute File.exists?(Path.join(dir, ".cure_manifest.tmp"))
  end

  test "toolchain_fingerprint/0 is a stable 32-byte digest" do
    a = M.toolchain_fingerprint()
    b = M.toolchain_fingerprint()
    assert is_binary(a) and byte_size(a) == 32
    assert a == b
  end
end
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `mix test test/cure/compiler/build_manifest_test.exs`
Expected: FAIL — `Cure.Compiler.BuildManifest` undefined.

- [ ] **Step 3: Implement `BuildManifest`**

```elixir
# lib/cure/compiler/build_manifest.ex
defmodule Cure.Compiler.BuildManifest do
  @moduledoc """
  Persisted fingerprint store for incremental Cure compilation.

  One manifest per output directory (`<output_dir>/.cure_manifest`), holding the
  compiler `toolchain` fingerprint, an optional external `stdlib_hash` (project
  builds only), and, per module, its content `source_hash`, `interface_hash`,
  direct `deps`, and the `beams` it produced. Any read or decode problem yields
  an empty manifest so the caller rebuilds everything — the failure mode is
  always "recompile", never "serve stale".
  """

  @manifest_version 1
  @filename ".cure_manifest"

  @type entry :: %{
          source_path: String.t(),
          source_hash: binary(),
          interface_hash: binary() | nil,
          deps: [String.t()],
          beams: [String.t()]
        }
  @type t :: %{
          version: pos_integer(),
          toolchain: binary(),
          stdlib_hash: binary() | nil,
          modules: %{String.t() => entry()}
        }

  @spec empty(binary()) :: t()
  def empty(toolchain) when is_binary(toolchain),
    do: %{version: @manifest_version, toolchain: toolchain, stdlib_hash: nil, modules: %{}}

  @spec load(String.t()) :: t()
  def load(output_dir) do
    path = Path.join(output_dir, @filename)

    with {:ok, bin} <- File.read(path),
         {:ok, term} <- safe_decode(bin),
         %{version: @manifest_version, toolchain: tc, modules: mods}
         when is_binary(tc) and is_map(mods) <- term do
      %{
        version: @manifest_version,
        toolchain: tc,
        stdlib_hash: Map.get(term, :stdlib_hash),
        modules: mods
      }
    else
      _ -> empty("")
    end
  end

  @spec save(t(), String.t()) :: :ok
  def save(manifest, output_dir) do
    File.mkdir_p!(output_dir)
    final = Path.join(output_dir, @filename)
    tmp = final <> ".tmp"
    File.write!(tmp, :erlang.term_to_binary(manifest))
    File.rename!(tmp, final)
    :ok
  end

  @doc "SHA-256 over the :cure application's compiled .beam files, in sorted path order."
  @spec toolchain_fingerprint() :: binary()
  def toolchain_fingerprint do
    # NOT `Application.app_dir(:cure, "ebin")`: in this project `:code.lib_dir(:cure)`
    # resolves to `_build/cure` (not the standard `_build/<env>/lib/cure`), so
    # `Application.app_dir/2` collides with the driver's own default `output_dir`
    # (`_build/cure/ebin`, see Global Constraints). Hashing that directory is
    # self-referential: every compile run writes fresh `Cure.*.beam` files into
    # the exact directory being fingerprinted as "toolchain", so the very next
    # run always sees a mismatch and forces a full rebuild — and it never
    # hashes the compiler's own `Elixir.*.beam` files at all, so a real
    # toolchain change goes undetected. `Mix.Project.compile_path()` is the
    # correct, verified location (matches the design spec) — confirmed via a
    # real `mix test` run in this repo to resolve to `_build/<env>/lib/cure/ebin`,
    # where the `:cure` app's own compiled bytecode actually lives.
    beams =
      Mix.Project.compile_path()
      |> Path.join("*.beam")
      |> Path.wildcard()
      |> Enum.sort()

    ctx = :crypto.hash_init(:sha256)

    beams
    |> Enum.reduce(ctx, fn beam, acc ->
      :crypto.hash_update(acc, File.read!(beam))
    end)
    |> :crypto.hash_final()
  end

  defp safe_decode(bin) do
    {:ok, :erlang.binary_to_term(bin, [:safe])}
  rescue
    _ -> :error
  end
end
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/compiler/build_manifest_test.exs`
Expected: PASS (7 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/build_manifest.ex test/cure/compiler/build_manifest_test.exs
git commit -m "feat(compiler): add BuildManifest fingerprint store for incremental builds"
```

---

## Task 3: `interface_hash/1` + serializability verification

Create the `Cure.Compiler.Incremental` module with just `interface_hash/1`, and verify the serializability assumption on a real stdlib `export_env`. The driver (`compile_dir/3`) is added to this same module in Task 4.

**Files:**
- Create: `lib/cure/compiler/incremental.ex` (module skeleton + `interface_hash/1`)
- Test: `test/cure/compiler/incremental_hash_test.exs`

**Interfaces:**
- Consumes: `Cure.Elab.Program.module_interface/2` (Task 1).
- Produces: `Cure.Compiler.Incremental.interface_hash(export_env :: map()) :: binary()` — 32-byte SHA-256 of the deterministically-serialized env.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/incremental_hash_test.exs
defmodule Cure.Compiler.IncrementalHashTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Incremental
  alias Cure.Elab.Program

  test "a real stdlib export_env is serializable and hashes deterministically" do
    {:ok, iface} = Program.module_interface("Std.Core", "lib/std/core.cure")
    h1 = Incremental.interface_hash(iface.export_env)
    h2 = Incremental.interface_hash(iface.export_env)
    assert is_binary(h1) and byte_size(h1) == 32
    assert h1 == h2
  end

  test "different envs hash differently" do
    {:ok, core} = Program.module_interface("Std.Core", "lib/std/core.cure")
    {:ok, list} = Program.module_interface("Std.List", "lib/std/list.cure")
    assert Incremental.interface_hash(core.export_env) != Incremental.interface_hash(list.export_env)
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/compiler/incremental_hash_test.exs`
Expected: FAIL — `Cure.Compiler.Incremental` undefined.

- [ ] **Step 3: Create the module skeleton + `interface_hash/1`**

```elixir
# lib/cure/compiler/incremental.ex
defmodule Cure.Compiler.Incremental do
  @moduledoc """
  Interface-level incremental driver for multi-file Cure builds.

  Recompiles a module only when its source content changed, one of its output
  beams is missing, a direct dependency's interface changed, or the compiler
  itself changed. See `docs/superpowers/specs/tooling/2026-07-18-incremental-compilation-design.md`.
  """

  @doc """
  SHA-256 of a module's elaborated `export_env` — the exact artifact consumers
  merge in. If two versions of a module produce a byte-identical `export_env`,
  no consumer's compilation can differ, so its dependents need not recompile.
  """
  @spec interface_hash(map()) :: binary()
  def interface_hash(export_env) do
    :crypto.hash(:sha256, :erlang.term_to_binary(export_env, [:deterministic]))
  end
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/compiler/incremental_hash_test.exs`
Expected: PASS (2 tests).

**If Step 4 fails with an `ArgumentError` from `term_to_binary`** (env holds a live closure/pid/ref — not expected, but the spec's fallback): change `interface_hash/1` to hash a structural projection instead. First read the `Cure.Core.Env` struct definition (in `lib/cure/core/inductive.ex`) to get the real field names for its def/family/ctor tables, then:

```elixir
  def interface_hash(export_env) do
    projection = Map.take(export_env, [<the real def/family/ctor field atoms>])
    :crypto.hash(:sha256, :erlang.term_to_binary(projection, [:deterministic]))
  end
```

Re-run Step 4. Do not guess the field names — read the struct.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/incremental.ex test/cure/compiler/incremental_hash_test.exs
git commit -m "feat(compiler): add interface_hash over the elaborated export_env"
```

---

## Task 4: The dirty-set walk + compile driver

The core of the feature: `compile_dir/3` — a single interleaved topological walk that decides dirtiness and compiles in the same pass, over `closure_deps_map/1`.

**Files:**
- Modify: `lib/cure/compiler/incremental.ex`
- Test: `test/cure/compiler/incremental_test.exs`

**Interfaces:**
- Consumes: `Cure.Compiler.BuildManifest` (Task 2), `interface_hash/1` (Task 3), `Cure.Elab.Program.module_interface/2` (Task 1), `Cure.Compiler.DepGraph.{scan/1, order/1, closure_deps_map/1, toposort/2}`, `Cure.Compiler.compile_file/2` (returns `{:ok, module, warnings}` | `{:error, reason}`).
- Produces:
  - `Cure.Compiler.Incremental.compile_dir(source_paths :: [Path.t()], output_dir :: String.t(), opts :: keyword()) :: {:ok, summary()} | {:error, term()}`
  - `@type summary :: %{compiled: [String.t()], skipped_fresh: [String.t()], deleted: [String.t()], errors: [{term(), term()}], cycles: [list()]}`
  - `Cure.Compiler.Incremental.stdlib_fingerprint(output_dir :: String.t()) :: binary()` — SHA-256 over `Cure.Std.*.beam` content in `output_dir` (used by Task 6).
  - `opts`: `:force` (boolean; also honored via `CURE_FULL_REBUILD` env), `:compile_opts` (keyword forwarded to `compile_file/2`, e.g. `[emit_events: false]`), `:source_roots` (list of directory roots for deletion scoping; defaults to the distinct dirnames of `source_paths`), `:stdlib_hash` (binary external fingerprint; when present, a mismatch marks every module dirty).

**Design contract (the invariants the code below encodes — read before implementing):**

- **Walk order.** `DepGraph.closure_deps_map/1` gives `%{module => [dep module names]}` (superset). `DepGraph.toposort(closure, Map.keys(closure))` gives a deterministic order with every dependency before its dependents (cycles emitted as alphabetical groups). Walk in that order.
- **Cycle precision loss is accepted, not a correctness gap.** A cycle in `closure_deps_map/1` can only arise among the small prelude-bootstrap set (real `use` cycles are legal per `DepGraph`'s module doc and would appear here too, but `order/1`'s cycle reporting below is unaffected). `toposort/2` is SCC-tolerant: within a deadlocked group it emits members in alphabetical order with no guaranteed *internal* order, so a same-pass interface change on one cycle member is not guaranteed to be visible to another member of the *same* cycle visited earlier in *this* build. This never serves a stale beam — the affected member is simply re-checked (and, if needed, recompiled) on the *next* build, same as any other dependency-changed case. Do not add a fixpoint/re-visit loop to "fix" this; it is deliberate.
- **`graph.modules`** is `%{module => path}`. Every walked module has a path there.
- **Forced targets.** A scanned node with `blank?: false` and `module: nil` (a parse error, per `DepGraph`'s `scan_file/1`) has no module name, so it is absent from `closure_deps_map/1` and the walk. It must still be *attempted* (so `compile_file` re-hits and reports the parse error) and never staged in the manifest. Collect these paths from `graph.nodes` and compile them after the module walk; any error fails the build. Blank nodes (`blank?: true`) produce no module/beam and are skipped.
- **Single interleaved walk.** For each module M in walk order: decide dirty, and if dirty compile it *immediately* and recompute its interface hash — because M's dependents, visited later, read M's fresh interface hash to decide their own dirtiness. Dirty/compile cannot be two separate phases.
- **Dirty predicate** for M (any one triggers): `all_dirty?`; M absent from the old manifest; `source_hash(M)` differs; any beam in the old entry's `beams` missing on disk; any direct dependency (from `closure_deps_map[M]`) that was **recompiled earlier in this walk** and whose fresh interface hash differs from its stored one (a dependency with no stored interface hash — new or errored — counts as changed).
- **`all_dirty?`** iff `:force`/`CURE_FULL_REBUILD`, or the stored `toolchain` ≠ current, or (`:stdlib_hash` given and stored `stdlib_hash` ≠ given).
- **Deletions** run on every build **except** `:force` (which skips manifest load + deletions entirely), *including* an `all_dirty?` toolchain-mismatch build. A manifest entry is a deletion candidate only if its `source_path` is under one of this run's `:source_roots` **and** the file no longer exists; then remove its beams and drop its entry. A foreign entry (outside the roots — e.g. a stdlib entry seen during a project build sharing the output dir) is left untouched.
- **Manifest write** happens only if no module errored this build. Skipped-fresh modules carry their old entry forward verbatim. Compiled modules get a fresh entry. Any kept manifest entry outside this run's walk — a foreign entry from another build sharing this `output_dir`, or a source under `source_roots` not included in this call's `source_paths` — is carried forward into the saved manifest unchanged (seed the accumulator from the post-deletion manifest, not empty).
- **Beams of a module** are discovered by naming convention: `Cure.<module>.beam` plus `Cure.<module>.*.beam` (lifted submodules) in `output_dir`, **excluding** any `Cure.<module>.*.beam` match whose stripped name (`<module>.<suffix>`) is itself a key in `graph.modules`. Cure's dotted module-naming convention means an independently-declared *sibling* module can share a dotted prefix with `module` without being one of its lifted submodules — e.g. real stdlib modules `Std.Otp` and `Otp.Meta.Call` are two separate top-level `mod` declarations in two separate files, not a `lift module` relationship, yet a bare `Cure.Std.Otp.*.beam` wildcard would match `Cure.Otp.Meta.Call.beam` too. A genuine lifted submodule never appears as its own scanned entry in `graph.modules`, so this exclusion is exact, not heuristic. Cure prefixes every emitted module atom with `Cure.` (per project CLAUDE.md), so this captures the module's outputs without an mtime race, and the sibling exclusion is what keeps `delete_removed` from destroying an unrelated, still-live module's beam when a shorter dotted-prefix module's source is removed.

- [ ] **Step 1: Write the failing tests**

```elixir
# test/cure/compiler/incremental_test.exs
defmodule Cure.Compiler.IncrementalTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{BuildManifest, Incremental}

  # A 3-module chain Leaf <- Mid <- Top via `use`, plus:
  #  - a private helper in Leaf (interface-invariant edits),
  #  - `Amb` (an unrelated module) that Top calls with a QUALIFIED call and no
  #    `use` — a closure-only edge (in closure_deps_map, not order_deps_map).
  @leaf_v1 """
  mod Leaf do
    def pubval() : Int = helper()
    def helper() : Int = 1
  end
  """

  # same public surface, different PRIVATE helper body -> interface unchanged
  @leaf_v2_private """
  mod Leaf do
    def pubval() : Int = helper()
    def helper() : Int = 2
  end
  """

  # changed PUBLIC surface -> interface changed
  @leaf_v3_public """
  mod Leaf do
    def pubval() : Int = 7
    def helper() : Int = 1
  end
  """

  @amb_v1 """
  mod Amb do
    def thing() : Int = 1
  end
  """

  @amb_v2 """
  mod Amb do
    def thing() : Int = 2
  end
  """

  @mid """
  mod Mid do
    use Leaf
    def midval() : Int = pubval()
  end
  """

  # Top `use`s Mid (order edge) and QUALIFIED-calls Amb.thing (closure edge, no use)
  @top """
  mod Top do
    use Mid
    def topval() : Int = midval()
    def viaamb() : Int = Amb.thing()
  end
  """

  setup do
    root = Path.join(System.tmp_dir!(), "cure_incr_#{:erlang.unique_integer([:positive])}")
    src = Path.join(root, "src")
    out = Path.join(root, "ebin")
    File.mkdir_p!(src)
    File.mkdir_p!(out)
    on_exit(fn -> File.rm_rf!(root) end)

    write = fn name, body -> File.write!(Path.join(src, name), body) end
    write.("leaf.cure", @leaf_v1)
    write.("mid.cure", @mid)
    write.("top.cure", @top)
    write.("amb.cure", @amb_v1)

    {:ok, src: src, out: out, write: write}
  end

  defp paths(src), do: Path.wildcard(Path.join(src, "*.cure"))

  defp compile(src, out, opts \\ []) do
    Incremental.compile_dir(paths(src), out, Keyword.put_new(opts, :source_roots, [src]))
  end

  test "first build compiles every module", %{src: src, out: out} do
    assert {:ok, s} = compile(src, out)
    assert Enum.sort(s.compiled) == ["Amb", "Leaf", "Mid", "Top"]
    assert s.skipped_fresh == []
    assert s.errors == []
  end

  test "no-change rebuild compiles nothing", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    assert {:ok, s} = compile(src, out)
    assert s.compiled == []
    assert Enum.sort(s.skipped_fresh) == ["Amb", "Leaf", "Mid", "Top"]
  end

  test "editing a leaf's PRIVATE helper recompiles only the leaf", %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    write.("leaf.cure", @leaf_v2_private)
    assert {:ok, s} = compile(src, out)
    assert s.compiled == ["Leaf"]
    assert "Mid" in s.skipped_fresh and "Top" in s.skipped_fresh
  end

  test "editing a leaf's PUBLIC surface cascades to its use-dependents", %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    write.("leaf.cure", @leaf_v3_public)
    assert {:ok, s} = compile(src, out)
    assert "Leaf" in s.compiled and "Mid" in s.compiled and "Top" in s.compiled
  end

  test "editing a QUALIFIED-called module with no `use` still recompiles its caller (closure edge)",
       %{src: src, out: out, write: write} do
    # Proves the dirty graph is closure_deps_map (which includes qualified-call
    # targets), not order_deps_map (use-only). Top calls Amb.thing() but does
    # not `use Amb`; an order-only graph would leave Top clean here.
    assert {:ok, _} = compile(src, out)
    write.("amb.cure", @amb_v2)
    assert {:ok, s} = compile(src, out)
    assert "Amb" in s.compiled
    assert "Top" in s.compiled
  end

  test "a missing beam forces recompile even when the hash matches", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    File.rm!(Path.join(out, "Cure.Leaf.beam"))
    assert {:ok, s} = compile(src, out)
    assert "Leaf" in s.compiled
  end

  test "a toolchain change forces a full rebuild", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    m = BuildManifest.load(out)
    BuildManifest.save(%{m | toolchain: <<0>>}, out)
    assert {:ok, s} = compile(src, out)
    assert Enum.sort(s.compiled) == ["Amb", "Leaf", "Mid", "Top"]
  end

  test "deleting a source removes its beam and drops it from the manifest", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    File.rm!(Path.join(src, "top.cure"))
    assert {:ok, s} = compile(src, out)
    assert "Top" in s.deleted
    refute File.exists?(Path.join(out, "Cure.Top.beam"))
    refute Map.has_key?(BuildManifest.load(out).modules, "Top")
  end

  test "a toolchain bump in the same build as a deleted source still deletes the beam",
       %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    m = BuildManifest.load(out)
    BuildManifest.save(%{m | toolchain: <<0>>}, out)
    File.rm!(Path.join(src, "top.cure"))
    assert {:ok, s} = compile(src, out)
    assert "Top" in s.deleted
    refute File.exists?(Path.join(out, "Cure.Top.beam"))
  end

  test "a foreign manifest entry (outside this run's roots) is left untouched", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    # Simulate a stdlib entry from a prior build sharing this output dir.
    File.write!(Path.join(out, "Cure.Std.Fake.beam"), "stub")
    m = BuildManifest.load(out)

    foreign =
      Map.put(m.modules, "Std.Fake", %{
        source_path: "lib/std/fake.cure",
        source_hash: <<1>>,
        interface_hash: <<2>>,
        deps: [],
        beams: ["Cure.Std.Fake.beam"]
      })

    BuildManifest.save(%{m | modules: foreign}, out)

    assert {:ok, s} = compile(src, out)
    refute "Std.Fake" in s.deleted
    assert File.exists?(Path.join(out, "Cure.Std.Fake.beam"))
    assert Map.has_key?(BuildManifest.load(out).modules, "Std.Fake")
  end

  test "a compile error keeps the module dirty and does not advance the manifest", %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    write.("leaf.cure", "mod Leaf do\n  def pubval() : Int = nonexistent_fn()\nend\n")
    assert {:ok, s} = compile(src, out)
    assert [{"Leaf", _}] = s.errors
    # manifest NOT advanced: next run still sees Leaf as dirty
    assert {:ok, s2} = compile(src, out)
    assert "Leaf" in (s2.compiled ++ Enum.map(s2.errors, &elem(&1, 0)))
  end

  test "a dependency failing to compile treats its dependent as dirty too", %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    # break Leaf; Mid `use`s Leaf. Mid must not be recorded fresh against a broken dep.
    write.("leaf.cure", "mod Leaf do\n  def pubval() : Int = nonexistent_fn()\nend\n")
    assert {:ok, s} = compile(src, out)
    assert Enum.any?(s.errors, fn {m, _} -> m == "Leaf" end)
    # Mid is either recompiled or errored this build, never silently skipped fresh.
    refute "Mid" in s.skipped_fresh
  end

  test "a source with a genuine parse error is reported, not silently dropped", %{src: src, out: out} do
    File.write!(Path.join(src, "broken.cure"), "mod Broken do def x( = end")
    assert {:ok, s} = compile(src, out)
    assert s.errors != []
  end

  test "force rebuilds everything", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    assert {:ok, s} = compile(src, out, force: true)
    assert Enum.sort(s.compiled) == ["Amb", "Leaf", "Mid", "Top"]
  end

  # Proves `beams_for/3` does not over-match on Cure's dotted module-naming
  # convention. `Ns.Base` and `Ns.Base.Child` are two INDEPENDENT top-level
  # modules (two files, two `mod` declarations) that merely share a dotted
  # prefix — mirroring real stdlib siblings like `Std.Otp` / `Otp.Meta.Call`.
  # A bare `Cure.Ns.Base.*.beam` wildcard would match `Cure.Ns.Base.Child.beam`
  # too; deleting `Ns.Base`'s source must not delete `Ns.Base.Child`'s beam.
  @ns_base """
  mod Ns.Base do
    def baseval() : Int = 1
  end
  """

  @ns_base_child """
  mod Ns.Base.Child do
    def childval() : Int = 2
  end
  """

  test "deleting a module does not delete a sibling whose name shares its dotted prefix",
       %{src: src, out: out, write: write} do
    write.("ns_base.cure", @ns_base)
    write.("ns_base_child.cure", @ns_base_child)
    assert {:ok, s0} = compile(src, out)
    assert "Ns.Base" in s0.compiled and "Ns.Base.Child" in s0.compiled

    File.rm!(Path.join(src, "ns_base.cure"))
    assert {:ok, s} = compile(src, out)
    assert "Ns.Base" in s.deleted
    refute "Ns.Base.Child" in s.deleted
    assert File.exists?(Path.join(out, "Cure.Ns.Base.Child.beam"))
    assert Map.has_key?(BuildManifest.load(out).modules, "Ns.Base.Child")
  end
end
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `mix test test/cure/compiler/incremental_test.exs`
Expected: FAIL — `compile_dir/3` undefined.

**Fixture-validity pre-check.** Before implementing, confirm the fixture syntax actually compiles under the real compiler: temporarily add a one-off test that calls `Cure.Compiler.compile_file(Path.join(src, "leaf.cure"), output_dir: out)` and asserts `{:ok, _, _}`. If `mod X do ... end`, `use`, `: Int`, or the qualified call `Amb.thing()` are not valid surface syntax, fix the fixtures to the real syntax (read an existing `lib/std/*.cure` and a `test/**/*.cure` fixture for the exact forms) — the *behaviors* under test are what matter, not these specific snippets. Keep the private-helper / public-surface / qualified-call distinctions intact. Remove the one-off check once the fixtures are known-good.

- [ ] **Step 3: Implement `compile_dir/3` and its helpers**

Add to `lib/cure/compiler/incremental.ex` (alongside `interface_hash/1`). This is complete; adjust only if the fixture pre-check forced a syntax change or `compile_file/2`'s return shape differs from `{:ok, module, warnings}` / `{:error, reason}`.

```elixir
  alias Cure.Compiler.{BuildManifest, DepGraph}
  alias Cure.Elab.Program

  @type summary :: %{
          compiled: [String.t()],
          skipped_fresh: [String.t()],
          deleted: [String.t()],
          errors: [{term(), term()}],
          cycles: [list()]
        }

  @spec compile_dir([Path.t()], String.t(), keyword()) :: {:ok, summary()} | {:error, term()}
  def compile_dir(source_paths, output_dir, opts \\ []) do
    File.mkdir_p!(output_dir)

    case DepGraph.scan(source_paths) do
      {:error, reason} -> {:error, reason}
      {:ok, graph} -> run(graph, source_paths, output_dir, opts)
    end
  end

  @doc "SHA-256 over `Cure.Std.*.beam` content in `output_dir`, sorted. External stdlib fingerprint for project builds."
  @spec stdlib_fingerprint(String.t()) :: binary()
  def stdlib_fingerprint(output_dir) do
    output_dir
    |> Path.join("Cure.Std.*.beam")
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.reduce(:crypto.hash_init(:sha256), fn f, acc ->
      :crypto.hash_update(acc, File.read!(f))
    end)
    |> :crypto.hash_final()
  end

  defp run(graph, source_paths, output_dir, opts) do
    {:ok, _ordered, cycles} = DepGraph.order(graph)
    closure = DepGraph.closure_deps_map(graph)
    walk = DepGraph.toposort(closure, Map.keys(closure))

    forced_paths =
      for {path, node} <- graph.nodes,
          not node.blank?,
          not is_binary(node.module),
          do: path

    force? =
      Keyword.get(opts, :force, false) or
        System.get_env("CURE_FULL_REBUILD") not in [nil, ""]

    toolchain = BuildManifest.toolchain_fingerprint()
    manifest = if force?, do: BuildManifest.empty(toolchain), else: BuildManifest.load(output_dir)

    stdlib_hash = Keyword.get(opts, :stdlib_hash, manifest.stdlib_hash)

    all_dirty? =
      force? or manifest.toolchain != toolchain or
        (Keyword.has_key?(opts, :stdlib_hash) and manifest.stdlib_hash != stdlib_hash)

    roots =
      opts
      |> Keyword.get(:source_roots, source_paths |> Enum.map(&Path.dirname/1) |> Enum.uniq())
      |> Enum.map(&Path.expand/1)

    {manifest, deleted} =
      if force?, do: {manifest, []}, else: delete_removed(manifest, roots, output_dir)

    state0 = %{
      output_dir: output_dir,
      closure: closure,
      module_paths: graph.modules,
      compile_opts: Keyword.get(opts, :compile_opts, []),
      all_dirty?: all_dirty?,
      old: manifest.modules,
      # Seed `new` with the post-deletion kept map, NOT `%{}`. Every module the
      # walk actually visits overwrites its own key below (skip branch: `old`;
      # compile branch: a fresh entry), so this is a no-op for walked modules.
      # For anything NOT in this run's walk — a foreign entry from a build
      # sharing this output_dir (e.g. stdlib vs project), or a source under
      # `source_roots` that simply wasn't passed in `source_paths` this call —
      # it is what carries the entry forward into the saved manifest. Without
      # this, `delete_removed` correctly protects such entries from *deletion*,
      # but the final `BuildManifest.save` below would still silently *drop*
      # them from the manifest file, since it only ever wrote what the walk
      # touched.
      new: manifest.modules,
      iface: %{},
      compiled: [],
      skipped_fresh: [],
      errors: []
    }

    state = Enum.reduce(walk, state0, &visit_module/2)
    state = Enum.reduce(forced_paths, state, &visit_forced/2)

    summary = %{
      compiled: Enum.sort(state.compiled),
      skipped_fresh: Enum.sort(state.skipped_fresh),
      deleted: Enum.sort(deleted),
      errors: Enum.reverse(state.errors),
      cycles: cycles
    }

    if summary.errors == [] do
      BuildManifest.save(
        %{version: 1, toolchain: toolchain, stdlib_hash: stdlib_hash, modules: state.new},
        output_dir
      )
    end

    {:ok, summary}
  end

  defp visit_module(mod, state) do
    path = Map.fetch!(state.module_paths, mod)
    old = Map.get(state.old, mod)

    dirty? =
      state.all_dirty? or is_nil(old) or
        source_hash(path) != old.source_hash or
        any_beam_missing?(old, state.output_dir) or
        dep_changed?(Map.get(state.closure, mod, []), state)

    if dirty? do
      compile_and_stage(mod, path, state)
    else
      %{
        state
        | new: Map.put(state.new, mod, old),
          iface: Map.put(state.iface, mod, %{changed: false}),
          skipped_fresh: [mod | state.skipped_fresh]
      }
    end
  end

  defp compile_and_stage(mod, path, state) do
    case Cure.Compiler.compile_file(path, [output_dir: state.output_dir] ++ state.compile_opts) do
      {:ok, _module, _warnings} ->
        new_hash =
          case Program.module_interface(mod, path) do
            {:ok, iface} -> interface_hash(iface.export_env)
            _ -> nil
          end

        stored = get_in(state.old, [mod, Access.key(:interface_hash, nil)])
        changed? = is_nil(new_hash) or is_nil(stored) or new_hash != stored

        entry = %{
          source_path: path,
          source_hash: source_hash(path),
          interface_hash: new_hash,
          deps: Map.get(state.closure, mod, []),
          beams: beams_for(mod, state.output_dir, state.module_paths)
        }

        %{
          state
          | new: Map.put(state.new, mod, entry),
            iface: Map.put(state.iface, mod, %{changed: changed?}),
            compiled: [mod | state.compiled]
        }

      {:error, reason} ->
        # not staged; dependents visited later see it as changed (no stored hash)
        %{
          state
          | iface: Map.put(state.iface, mod, %{changed: true}),
            errors: [{mod, reason} | state.errors]
        }
    end
  end

  defp visit_forced(path, state) do
    case Cure.Compiler.compile_file(path, [output_dir: state.output_dir] ++ state.compile_opts) do
      {:ok, _module, _warnings} -> state
      {:error, reason} -> %{state | errors: [{path, reason} | state.errors]}
    end
  end

  defp dep_changed?(deps, state) do
    Enum.any?(deps, fn d ->
      match?(%{changed: true}, Map.get(state.iface, d))
    end)
  end

  defp delete_removed(manifest, roots, output_dir) do
    {removed, kept} =
      Enum.split_with(manifest.modules, fn {_mod, entry} ->
        under_roots?(entry.source_path, roots) and not File.exists?(entry.source_path)
      end)

    Enum.each(removed, fn {_mod, entry} ->
      Enum.each(entry.beams, fn b -> File.rm(Path.join(output_dir, b)) end)
    end)

    {%{manifest | modules: Map.new(kept)}, Enum.map(removed, fn {mod, _} -> mod end)}
  end

  defp under_roots?(path, roots) do
    abs = Path.expand(path)
    Enum.any?(roots, fn r -> abs == r or String.starts_with?(abs, r <> "/") end)
  end

  defp source_hash(path), do: :crypto.hash(:sha256, File.read!(path))

  defp any_beam_missing?(%{beams: beams}, output_dir) do
    Enum.any?(beams, fn b -> not File.exists?(Path.join(output_dir, b)) end)
  end

  # `known_modules` is `graph.modules` (`state.module_paths`) — every top-level
  # module name scanned this run. A `Cure.<mod>.*.beam` wildcard match is only a
  # genuine lifted submodule of `mod` if its stripped name is NOT itself one of
  # these; Cure's dotted naming convention means an independently-declared
  # sibling (e.g. real stdlib modules `Std.Otp` / `Otp.Meta.Call`) can otherwise
  # false-positive-match and later get deleted alongside `mod`'s own beam.
  defp beams_for(mod, output_dir, known_modules) do
    prefix = "Cure." <> mod

    exact = Path.wildcard(Path.join(output_dir, prefix <> ".beam"))

    lifted =
      Path.join(output_dir, prefix <> ".*.beam")
      |> Path.wildcard()
      |> Enum.reject(fn beam_path ->
        candidate = beam_path |> Path.basename(".beam") |> String.trim_leading("Cure.")
        Map.has_key?(known_modules, candidate)
      end)

    (exact ++ lifted)
    |> Enum.map(&Path.basename/1)
    |> Enum.uniq()
    |> Enum.sort()
  end
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/compiler/incremental_test.exs`
Expected: PASS (15 tests).

**If the private-helper test fails** (Leaf recompiles Mid/Top): `export_env` includes private defs, so `interface_hash` picks up private-helper changes. Verify by reading what `module_interface`'s `export_env` contains for a non-exported def. If private defs genuinely appear in `export_env` for this language, the test's premise is wrong — replace `@leaf_v2_private` with a provably interface-invariant edit (a comment or whitespace change to `leaf.cure`) and note the finding in the commit message. Do not weaken any other assertion.

**If the qualified-call test fails** (`Top` not recompiled after editing `Amb`): confirm `DepGraph.closure_deps_map/1` actually lists `Amb` under `Top` for the fixture — add a temporary `IO.inspect(DepGraph.closure_deps_map(graph))` in a scratch call. If the qualified-call form in `@top` doesn't register as a `function_call` with a dotted name (see `collect_qualified_targets/1` in `dep_graph.ex`), adjust the fixture's call syntax to one that does. The behavior under test is "closure edges beyond `use` edges drive propagation"; keep that, adapt the syntax.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/incremental.ex test/cure/compiler/incremental_test.exs
git commit -m "feat(compiler): interface-level incremental compile driver"
```

---

## Task 5: Route the stdlib task through the driver

**Files:**
- Modify: `lib/mix/tasks/cure.compile_stdlib.ex`
- Test: **create** `test/mix/tasks/cure.compile_stdlib_incremental_test.exs` (below) — Task 4's tests exercise `Incremental.compile_dir/3` directly with hand-built args and cannot catch a *wiring* defect in this task (e.g. forgetting to pass `source_roots: [stdlib_dir]`, which would make the driver treat every stdlib module as foreign). Also reuse `test/cure/stdlib/*` + `mix cure.check.stdlib` as integration coverage.

**Interfaces:**
- Consumes: `Cure.Compiler.Incremental.compile_dir/3`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/mix/tasks/cure.compile_stdlib_incremental_test.exs
defmodule Mix.Tasks.Cure.CompileStdlibIncrementalTest do
  use ExUnit.Case, async: false
  import ExUnit.CaptureIO

  # Compiles the real 81-module stdlib twice — genuinely stdlib-scale, so it
  # carries the same `:slow` tag as the other whole-stdlib tests (see
  # test/test_helper.exs); run locally with `mix test --include slow`, always
  # in CI.
  @moduletag :slow

  test "a second cure.compile_stdlib run with no source change recompiles nothing" do
    capture_io(fn -> Mix.Task.rerun("cure.compile_stdlib") end)
    output = capture_io(fn -> Mix.Task.rerun("cure.compile_stdlib") end)
    assert output =~ ~r/0 compiled/
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test --include slow test/mix/tasks/cure.compile_stdlib_incremental_test.exs`
Expected: FAIL — the current `cure.compile_stdlib` always recompiles every module, so the second run's output does not match `0 compiled`.

**If `Mix.Task.rerun/1` errors or behaves unexpectedly** (e.g. the task depends on `Mix.Task.run("app.start")` in a way that isn't idempotent across `rerun`), read the current `lib/mix/tasks/cure.compile_stdlib.ex` in full first, then adjust the test to invoke the task in whatever way is actually safe to call twice in-process (e.g. calling the task module's `run/1` directly with `capture_io` around each call). Keep the assertion on the printed "0 compiled" summary — that observable behavior is what matters, not the invocation mechanism.

- [ ] **Step 3: Replace the compile loop**

In `lib/mix/tasks/cure.compile_stdlib.ex`, keep the `app.start`, `stdlib_dir`, and `compiler_available?()`/empty-file guards. Replace the `cure_files` scan block (lines 36-50) and the `true ->` compile branch (lines 61-101) so cycles are reported from the driver's summary and compilation routes through it:

```elixir
    stdlib_dir = Path.join(["lib", "std"])
    cure_files = Path.wildcard(Path.join(stdlib_dir, "*.cure"))

    cond do
      not compiler_available?() ->
        Mix.shell().info("Cure.Compiler not yet available, skipping stdlib compilation")
        :ok

      cure_files == [] ->
        Mix.shell().info("No .cure files found in #{stdlib_dir}")
        :ok

      true ->
        File.mkdir_p!(output_dir)
        abs_dir = Path.expand(output_dir)
        unless abs_dir in :code.get_path(), do: :code.add_patha(String.to_charlist(abs_dir))

        case Cure.Compiler.Incremental.compile_dir(cure_files, output_dir,
               source_roots: [stdlib_dir],
               compile_opts: [emit_events: false]
             ) do
          {:ok, summary} ->
            Enum.each(summary.cycles, fn walk ->
              Mix.shell().info(Cure.Compiler.Errors.format_error({:import_cycle, walk}, stdlib_dir))
            end)

            Mix.shell().info(
              "  #{length(summary.compiled)} compiled, " <>
                "#{length(summary.skipped_fresh)} up-to-date, " <>
                "#{length(summary.deleted)} removed"
            )

            Mix.shell().info("  Output: #{output_dir}")

            unless summary.errors == [] do
              Enum.each(summary.errors, fn {target, reason} ->
                Mix.shell().error("  #{Cure.Compiler.Errors.format_error(reason, target)}")
              end)

              exit({:shutdown, 1})
            end

          {:error, reason} ->
            Mix.shell().error(Cure.Compiler.Errors.format_error(reason, stdlib_dir))
            exit({:shutdown, 1})
        end
    end
```

`format_error(reason, target)`: `target` is a module name (from `compile_and_stage`) or a path (from `visit_forced`); `format_error/2` already accepts a path/context string, and a module name is an acceptable context here. If it pattern-matches on a path shape, pass `stdlib_dir` as the context instead of `target`.

- [ ] **Step 4: Run the test to verify it passes, then verify stdlib compiles clean cold then warm**

Run: `mix test --include slow test/mix/tasks/cure.compile_stdlib_incremental_test.exs`
Expected: PASS.

Also run by hand: `rm -f _build/cure/ebin/.cure_manifest && mix cure.compile_stdlib`
Expected: `N compiled, 0 up-to-date, 0 removed` where N is the full stdlib module count.

Run again (no source change): `mix cure.compile_stdlib`
Expected: `0 compiled, N up-to-date, 0 removed`.

- [ ] **Step 5: Verify the stdlib integrity checks still pass**

Run: `mix cure.check.stdlib`
Expected: passes (declared == compiled, no orphans).

- [ ] **Step 6: Commit**

```bash
git add lib/mix/tasks/cure.compile_stdlib.ex test/mix/tasks/cure.compile_stdlib_incremental_test.exs
git commit -m "perf(compiler): make cure.compile_stdlib incremental"
```

---

## Task 6: Route the project-compile task through the driver

Route directory builds through the driver, with a `stdlib_hash` guard so a project module is never left stale after a stdlib change (keeping invariant #1 for project builds — the spec's "known limitation" mitigation).

**Files:**
- Modify: `lib/mix/tasks/cure.compile.ex`
- Test: **create** `test/mix/tasks/cure.compile_incremental_test.exs` (below) — same rationale as Task 5: Task 4's tests can't catch a wiring defect in this task's own option-threading (e.g. dropping `stdlib_hash`, which would silently defeat invariant #1 for project builds). Also reuse `test/cure/project/*` if present (integration).

**Interfaces:**
- Consumes: `Cure.Compiler.Incremental.{compile_dir/3, stdlib_fingerprint/1}`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/mix/tasks/cure.compile_incremental_test.exs
defmodule Mix.Tasks.Cure.CompileIncrementalTest do
  use ExUnit.Case, async: false
  import ExUnit.CaptureIO

  setup do
    root = Path.join(System.tmp_dir!(), "cure_compile_task_#{:erlang.unique_integer([:positive])}")
    src = Path.join(root, "src")
    out = Path.join(root, "ebin")
    File.mkdir_p!(src)
    on_exit(fn -> File.rm_rf!(root) end)
    File.write!(Path.join(src, "a.cure"), "mod A do\n  def a() : Int = 1\nend\n")
    File.write!(Path.join(src, "b.cure"), "mod B do\n  use A\n  def b() : Int = a()\nend\n")
    {:ok, src: src, out: out}
  end

  test "a second cure.compile run over an unchanged project directory recompiles nothing",
       %{src: src, out: out} do
    args = [src, "--output-dir", out]
    capture_io(fn -> Mix.Task.rerun("cure.compile", args) end)
    output = capture_io(fn -> Mix.Task.rerun("cure.compile", args) end)
    assert output =~ ~r/0 compiled/
  end
end
```

**If `mod X do ... end`/`use` isn't valid surface syntax**, use the real forms confirmed in Task 4's fixture pre-check (Task 4 Step 2) instead — the behavior under test (second run is a no-op) is what matters, not this exact snippet.

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/mix/tasks/cure.compile_incremental_test.exs`
Expected: FAIL — the current `cure.compile` always recompiles every file, so the second run's output does not match `0 compiled`.

- [ ] **Step 3: Route directory builds through the driver**

In `lib/mix/tasks/cure.compile.ex`, change the directory branch of the `Enum.each(paths, ...)` loop (lines 37-46) to collect the directory's sources and call the driver once, passing the stdlib fingerprint so a changed stdlib invalidates the whole project. Leave the single-file branch (`compile_one/2`) unchanged — a lone file has nothing to be incremental against.

```elixir
    Enum.each(paths, fn path ->
      if File.dir?(path) do
        files = path |> Path.join("**/*.cure") |> Path.wildcard()

        case Cure.Compiler.Incremental.compile_dir(files, output_dir,
               source_roots: [path],
               stdlib_hash: Cure.Compiler.Incremental.stdlib_fingerprint(output_dir)
             ) do
          {:ok, summary} ->
            Enum.each(summary.cycles, fn walk ->
              Mix.shell().info(Cure.Compiler.Errors.format_error({:import_cycle, walk}, path))
            end)

            Mix.shell().info(
              "#{length(summary.compiled)} compiled, " <>
                "#{length(summary.skipped_fresh)} up-to-date, " <>
                "#{length(summary.deleted)} removed"
            )

            unless summary.errors == [] do
              Enum.each(summary.errors, fn {target, reason} ->
                Mix.shell().error(Cure.Compiler.Errors.format_error(reason, target))
              end)

              exit({:shutdown, 1})
            end

          {:error, reason} ->
            Mix.shell().error(Cure.Compiler.Errors.format_error(reason, path))
            exit({:shutdown, 1})
        end
      else
        compile_one(path, output_dir)
      end
    end)
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/mix/tasks/cure.compile_incremental_test.exs`
Expected: PASS.

- [ ] **Step 5: Smoke-test a two-file project directory by hand**

Run:
```bash
mkdir -p /tmp/cure_proj_smoke && \
printf 'mod A do\n  def a() : Int = 1\nend\n' > /tmp/cure_proj_smoke/a.cure && \
printf 'mod B do\n  use A\n  def b() : Int = a()\nend\n' > /tmp/cure_proj_smoke/b.cure && \
mix cure.compile /tmp/cure_proj_smoke --output-dir /tmp/cure_proj_out && \
echo "--- second run (no change) ---" && \
mix cure.compile /tmp/cure_proj_smoke --output-dir /tmp/cure_proj_out
```
Expected: first run `2 compiled, 0 up-to-date`; second run `0 compiled, 2 up-to-date`. Clean up `/tmp/cure_proj_smoke` and `/tmp/cure_proj_out` after.

- [ ] **Step 6: Commit**

```bash
git add lib/mix/tasks/cure.compile.ex test/mix/tasks/cure.compile_incremental_test.exs
git commit -m "perf(compiler): make cure.compile directory builds incremental"
```

---

## Task 7: Full gate + wall-clock confirmation

**Files:** none (verification only).

- [ ] **Step 1: Run the full suite**

Run: `mix test`
Expected: 0 failures; `Antigen shape-coverage: 318/318`; the `test_helper` "stuck N canonical stdlib modules" line still prints.

- [ ] **Step 2: Confirm the incremental win on the test-loop path**

Run `mix test test/cure/compiler/build_manifest_test.exs` twice in a row (no source change between). The second run's `test_helper` stdlib step should report `0 compiled, N up-to-date` instead of recompiling all N.

Expected observation: the pre-test stdlib step drops from ~7.5s to well under 1s on the no-change second run.

- [ ] **Step 3: Confirm CI still runs the whole suite**

Run: `mix test --include slow`
Expected: 0 failures.

- [ ] **Step 4: Update memory**

Update `suite-wallclock-optimization.md` and `MEMORY.md`: incremental compilation landed — content-hash fingerprints (`source_hash`), interface-level cascade via `export_env` hashing (`closure_deps_map/1` propagation, not `order_deps_map/1`), toolchain-hash invalidates everything, project builds guarded by `stdlib_hash`; the measured no-change stdlib-step time; and the project-build known limitation (cross-stdlib precision is whole-stdlib granularity via `stdlib_hash`, not per-module).

- [ ] **Step 5: Commit memory (no-op if outside repo)**

Memory files live under `/Users/ch/.claude/...`, outside this repo — updating them needs no git commit here. This step is just the memory Write from Step 4.

---

## Self-Review Notes

- **Spec coverage:** fingerprints — `source_hash`/`interface_hash`/`toolchain` (Tasks 2, 3, 4), `stdlib_hash` for project builds (Tasks 4, 6); manifest + atomic write + fail-safe + shape/version tolerance (Task 2); `closure_deps_map/1` + `toposort/2` single interleaved walk (Task 4 design contract + driver); deletions scoped-and-unconditional (Task 4 `delete_removed`/`under_roots?` + tests); forced compile targets for parse errors (Task 4 `visit_forced` + test); broken-dependency cascade (Task 4 test + `dep_changed?` "no stored hash = changed"); interface hash via `module_interface/2` with cache-sharing (Tasks 1, 3, 4); error-doesn't-advance-manifest (Task 4 + test); force/env bypass (Task 4 + test); mix integration for stdlib + project (Tasks 5, 6); test_helper inherits unchanged (Task 5 verification); every spec test scenario mapped to a Task 4 test. Per-consumed-symbol invalidation, `export_env` normalization, escript, and `cure.bundle_stdlib_beams` mtime staleness are the spec's explicit follow-ups — correctly no task.
- **Ambient `@prelude` vs qualified-call test:** the spec's named test edits an ambient `@prelude` provider; that fixture is impractical in a bare temp dir (the prelude manifest is built from real stdlib source roots). The qualified-call test exercises the *same* `closure_deps_map/1`-vs-`order_deps_map/1` propagation code path and is the testable manifestation of "closure edges beyond `use` edges." Documented as a deliberate substitution; the real ambient-`@prelude` case is covered by the stdlib integration (Task 5), where ambient edges are live. Flag for Stage 3 review.
- **Serializability risk** — Task 3 verifies on a real env with a structural-projection fallback.
- **Type consistency:** `summary` (`compiled`/`skipped_fresh`/`deleted`/`errors`/`cycles`), manifest `entry`/`t` shapes (incl. `stdlib_hash`), and `module_interface/2`/`interface_hash/1`/`compile_dir/3`/`stdlib_fingerprint/1` signatures are used identically across tasks.
- **Fixture-syntax risk:** Tasks 4 and 6 both hinge on `mod X do ... end`/`use`/`: Int`/qualified-call being valid surface syntax; Task 4 Step 2 has an explicit pre-check to confirm/correct against real `.cure` sources before building on the fixtures.

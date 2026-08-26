# Deterministic, parallel-safe stdlib in the Cure test suite — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the Cure test suite correct under parallelism and keep it a single suite — eliminate global-BEAM-code-table clobber flakes by sticking the canonical stdlib and namespacing emitter-verifying producer tests.

**Architecture:** Two complementary mechanisms plus carve-outs. (1) At suite startup, load every canonical stdlib beam and mark each module *sticky* (`:code.stick_mod/1`) so nothing can overwrite the canonical surface — this protects the majority of tests, which are pure consumers calling `Cure.Std.X.f`. (2) Thread an optional module-name **prefix** through `Cure.Elab.Emit` so producer tests that deliberately emit their own version of a stdlib module install it under a per-test prefix, never touching the canonical slot. With an empty prefix the emitter output is byte-for-byte identical to today, so production compilation and golden tests are unchanged.

**Tech Stack:** Elixir, ExUnit, Erlang `:code` module (sticky-directory mechanism), Cure compiler (`Cure.Elab.Emit`, `Cure.Stdlib.Preload`).

## Global Constraints

- **TCB-adjacency:** `lib/cure/elab/emit.ex` is TCB-adjacent. The kernel re-checks emitter output, but codegen changes still require the full gate. The authoritative guard that the default emission path is untouched is **Task 8's committed BEAM golden** (it byte-compares compiled output against a pre-change baseline). Task 4's forms-level check is a lighter internal-consistency guard (`module_forms/5` with an empty prefix equals `module_forms/4`), not a pre-change comparison — see Task 4.
- **Empty-prefix byte-identity (invariant):** `module_forms`/`compile_and_load`/`compile_forms` with `prefix: ""` (the default) MUST produce output byte-for-byte identical to before this change. This is what keeps production compilation and the golden gate green.
- **One build at a time:** Never launch concurrent full suites — a past concurrent full-suite run caused a kernel panic. Serialize every `mix test`.
- **Tests are behavioral and immutable:** Each task's red test asserts observable behavior and is not rewritten to match a broken implementation. Fix code, not the test.
- **Git commits carry NO co-author trailer.** Write commits as the user only (repo convention — never co-sign).
- **Stick only `Cure.*` stdlib modules** emitted by `cure.compile_stdlib`. Never stick user/test-emitted modules.
- **Path B baseline stays:** the `module_slice_env` memoization (commit `0c36c631`) is orthogonal and remains; do not touch it.

---

## File Structure

- `test/test_helper.exs` — suite startup. Gains a load-all + `:code.stick_mod` stanza after `cure.compile_stdlib`, with a source-declared-module completeness check (C1).
- `lib/cure/elab/emit.ex` — emitter. Gains `prefix` + `local_owners` threading through `compile_and_load/2`, `compile_forms/4`, `module_forms/5`, and `remote_target/2` (C2). Default empty prefix ⇒ byte-identical.
- `test/cure/elab/emit_prefix_test.exs` — **new** unit test file for the C2 invariants (empty-prefix byte-identity, prefixed isolation, prefixed delegation).
- `test/cure/stdlib/preload_test.exs` — two purge/delete sites gain re-stick in their `after`/cleanup blocks so they leave the canonical resident and sticky (C1).
- `test/cure/stdlib/preload_sticky_test.exs` — **new** unit test proving `load_if_present` tolerates a sticky module (C1 precondition).
- `test/cure/stdlib/set_dependent_run_test.exs` — producer, migrated to prefixed emission (C2).
- `test/cure/stdlib/stdlib_test.exs` — pure consumer, simplified to call the sticky canonical directly (C3).
- `test/cure/stdlib/iter_test.exs` — pure consumer; **no source change**, fixed by C1 alone; flipped to async in C5.
- `test/cure/compiler/actor_quote_golden_test.exs` — golden carve-out; verified unchanged (C4).

## Sequencing (also the falsification plan)

1. **Task 1** — C1 precondition test (preload tolerates sticky).
2. **Task 2** — C1 startup load-all + stick + completeness check. Running the gate here makes the producer worklist appear as deterministic `:sticky_directory` failures, and proves Path B never touched the clobber failures (code-table layer, not elaboration).
3. **Task 3** — C1 re-stick fix for the two `preload_test.exs` purge sites.
4. **Task 4** — C2 emit.ex prefix threading, empty-prefix byte-identity test FIRST (red → green) before any producer migrates.
5. **Task 5** — C2 prefixed-isolation + prefixed-delegation tests.
6. **Task 6** — migrate `set_dependent_run_test.exs` to prefixed emission (C2).
7. **Task 7** — simplify `stdlib_test.exs` to the sticky canonical (C3).
8. **Task 8** — C4 golden carve-out: confirm byte-compare tests still pass un-namespaced.
9. **Task 9** — C5 flip isolated files to async.
10. **Task 10** — determinism gate (two fixed seeds green) + timing.

---

### Task 1: C1 precondition — `load_if_present` tolerates a sticky module

Establishes the safety property C1 depends on: once the canonical stdlib is sticky, re-preload calls (`load_if_present/2`) must no-op, not crash. `load_if_present/2` (`preload.ex:605`) already maps `{:error, _reason}` (including `:sticky_directory`) to `:ok`; this test pins that behavior so a future change to preload cannot silently break sticky. It is a green-on-write guard characterizing existing behavior — there is no honest red for pre-existing correct behavior, so Step 2 verifies it passes and documents *why* it is a guard.

**Files:**
- Test: Create `test/cure/stdlib/preload_sticky_test.exs`

**Interfaces:**
- Consumes: `Cure.Stdlib.Preload.load_if_present/2` is **private**. Do NOT call it directly. Exercise the same code path through the public `Cure.Stdlib.Preload.preload/1`, or, since we specifically need to prove the sticky refusal is tolerated, drive `:code.load_binary` directly and assert it returns `{:error, :sticky_directory}`, then assert a `preload/1` call over a sticky module still returns `:ok`.
- Produces: nothing consumed by later tasks; this is a standalone guard.

- [ ] **Step 1: Write the failing/guard test**

```elixir
defmodule Cure.Stdlib.PreloadStickyTest do
  # async: false — mutates the global code table (loads/sticks a throwaway module).
  use ExUnit.Case, async: false

  alias Cure.Stdlib.Preload

  @throwaway :"Cure.Std.PreloadStickyProbe"

  # A minimal, valid BEAM binary for @throwaway: -module(...). with no exports.
  defp probe_binary do
    forms = [
      {:attribute, 1, :module, @throwaway},
      {:attribute, 1, :export, []}
    ]

    {:ok, ^@throwaway = mod, binary} = :compile.forms(forms, [:return_errors])
    {mod, binary}
  end

  test "a stuck stdlib module refuses load_binary and preload tolerates it" do
    {mod, binary} = probe_binary()

    # Load then stick it, mimicking the C1 startup stanza.
    # NB: `:code.stick_mod/1` returns `true` (not `:ok`) — pattern-match on `true`.
    {:module, ^mod} = :code.load_binary(mod, ~c"nofile", binary)
    true = :code.stick_mod(mod)

    try do
      assert :code.is_sticky(mod)

      # A second load is refused with :sticky_directory (the property Preload must tolerate).
      assert {:error, :sticky_directory} = :code.load_binary(mod, ~c"nofile", binary)

      # A preload pass that would otherwise reload stdlib modules must still return :ok,
      # i.e. it swallows the :sticky_directory refusal rather than raising.
      assert Preload.preload(kind: :none) == :ok
    after
      :code.unstick_mod(mod)
      :code.purge(mod)
      :code.delete(mod)
    end
  end
end
```

- [ ] **Step 2: Run the test**

Run: `mix test test/cure/stdlib/preload_sticky_test.exs`
Expected: PASS. (This is a green-on-write guard: it characterizes the pre-existing tolerance in `load_if_present/2` and the OTP sticky semantics we rely on. If it *fails*, the C1 precondition is false and Task 2 must not proceed — investigate `preload.ex:605` before continuing.)

- [ ] **Step 3: Commit**

```bash
git add test/cure/stdlib/preload_sticky_test.exs
git commit -m "test(stdlib): pin sticky-module tolerance precondition for C1"
```

---

### Task 2: C1 — startup load-all + stick with completeness check (`test/test_helper.exs`)

After `Mix.Task.run("cure.compile_stdlib")`, load every canonical stdlib beam, stick each, and assert completeness against the module names declared in `lib/std/*.cure`. This makes the canonical surface resident and immutable for the whole suite. It also converts every remaining bare-canonical producer into a deterministic `:sticky_directory` failure — that failure list is the migration worklist for Tasks 6–7.

**Files:**
- Modify: `test/test_helper.exs` (insert after line 24, `Mix.Task.run("cure.compile_stdlib")`, before the `:ets.new(:cure_failure_tail, ...)` line)

**Interfaces:**
- Consumes: the beam glob `_build/cure/ebin/Cure.*.beam` (same directory `Cure.Stdlib.Preload` loads from at `preload.ex:592`). Module name = `Path.basename(path, ".beam") |> String.to_atom`.
- Consumes: the module-declaration regex shape from `preload.ex:103`: `~r/^\s*(?:mod|proof|actor|fsm|sup|app)\s+([A-Za-z_][\w\.]*)/m`. Use `Regex.scan/2` (a file may declare more than one module) and map each declared `X` to `:"Cure." <> X`. **Do not** read `Cure.Stdlib.Preload`'s compile-time `@std_module_groups` — it is baked via `@external_resource` and is stale for brand-new source files. Scan freshly at runtime here.
- Produces: a resident, sticky canonical stdlib surface consumed by every later task and by the whole suite.

- [ ] **Step 1: Write the startup stanza**

Insert this block in `test/test_helper.exs` immediately after `Mix.Task.run("cure.compile_stdlib")` (line 24) and before the failure-tail formatter section:

```elixir
# --- C1: load + stick the canonical stdlib -------------------------------------
#
# The BEAM has one global code-table slot per module name. `cure.compile_stdlib`
# has just written the canonical `_build/cure/ebin/Cure.*.beam`. Load every one of
# them and mark it STICKY (`:code.stick_mod/1`): a sticky module refuses
# `:code.load_binary`/`load_file` with `{:error, :sticky_directory}`, so no later
# producer test can overwrite the canonical surface consumers depend on. Any
# producer still emitting a bare canonical name now fails loudly and
# deterministically (a worklist item) instead of silently clobbering.
(fn ->
   ebin = "_build/cure/ebin"

   loaded =
     ebin
     |> Path.join("Cure.*.beam")
     |> Path.wildcard()
     |> Enum.map(fn path ->
       mod = path |> Path.basename(".beam") |> String.to_atom()
       {:module, ^mod} = :code.ensure_loaded(mod)
       # `:code.stick_mod/1` returns `true` (not `:ok`).
       true = :code.stick_mod(mod)
       mod
     end)
     |> MapSet.new()

   if MapSet.size(loaded) == 0 do
     raise """
     test_helper: no canonical stdlib beams found in #{ebin}.
     Expected `mix cure.compile_stdlib` to have written Cure.*.beam there.
     """
   end

   # Completeness: every module DECLARED in lib/std/*.cure must be resident, or a
   # consumer could hit a not-loaded module the sticky set never covered.
   mod_regex = ~r/^\s*(?:mod|proof|actor|fsm|sup|app)\s+([A-Za-z_][\w\.]*)/m

   declared =
     "lib/std/*.cure"
     |> Path.wildcard()
     |> Enum.flat_map(fn path ->
       case File.read(path) do
         {:ok, src} ->
           mod_regex
           |> Regex.scan(src)
           |> Enum.map(fn [_, name] -> String.to_atom("Cure." <> name) end)

         {:error, _} ->
           []
       end
     end)
     |> MapSet.new()

   # Spec C1 requires catching a mismatch in EITHER direction: a declared module
   # not compiled (missing) OR a compiled module not declared (extra) — the latter
   # signals a stale beam or a rename that left an orphan, which would be stuck
   # under a name no source backs.
   missing = MapSet.difference(declared, loaded)
   extra = MapSet.difference(loaded, declared)

   unless MapSet.size(missing) == 0 do
     raise """
     test_helper: these stdlib modules are declared in lib/std/*.cure but were not
     compiled to #{ebin} (so they cannot be made sticky and consumers may flake):
     #{missing |> MapSet.to_list() |> Enum.sort() |> Enum.map_join(", ", &inspect/1)}

     Run `mix cure.compile_stdlib` and check its output for compile errors.
     """
   end

   unless MapSet.size(extra) == 0 do
     raise """
     test_helper: these modules were compiled to #{ebin} but are NOT declared in
     any lib/std/*.cure (a stale beam or an orphaned rename — sticking one would
     freeze a name no current source produces):
     #{extra |> MapSet.to_list() |> Enum.sort() |> Enum.map_join(", ", &inspect/1)}

     Delete the stale beam(s) or run a clean `mix cure.compile_stdlib`.
     """
   end

   # A hard sanity floor in case both scans somehow degrade to empty.
   for sentinel <- [:"Cure.Std.String", :"Cure.Std.Core", :"Cure.Std.List"] do
     unless MapSet.member?(loaded, sentinel) and :code.is_sticky(sentinel) do
       raise "test_helper: sentinel #{inspect(sentinel)} is not loaded+sticky; stdlib compile is incomplete."
     end
   end

   IO.puts("test_helper: stuck #{MapSet.size(loaded)} canonical stdlib modules")
 end).()
```

- [ ] **Step 2: Run the targeted worklist-revealing subset**

Run: `mix test test/cure/stdlib/iter_test.exs test/cure/stdlib/set_dependent_run_test.exs test/cure/stdlib/stdlib_test.exs`
Expected (this is the falsification observation, not a regression):
- `iter_test.exs` (pure consumer) now **passes** — the sticky canonical `Cure.Std.Iter` is resident and correct.
- `set_dependent_run_test.exs` (bare-canonical producer) now **fails deterministically** with `:sticky_directory` (its `{:ok, _} = Emit.compile_and_load(..., module: :"Cure.Std.Set")` cannot load over the sticky slot). This is the intended forcing function; it is resolved in Task 6.
- `stdlib_test.exs` (calls `Cure.Compiler.compile_and_load` under canonical names via `compile_stdlib/1`) now **fails deterministically** with `:sticky_directory`. Resolved in Task 7.

Record which files failed with `:sticky_directory` — that is the migration worklist.

- [ ] **Step 3: Commit**

```bash
git add test/test_helper.exs
git commit -m "test(stdlib): load + stick canonical stdlib at suite startup (C1)"
```

Note: producer tests are expected red between here and Tasks 6–7. This is the sequenced falsification, not a broken build. Do NOT run the full gate until Task 10.

---

### Task 3: C1 — re-stick after the two `preload_test.exs` purge sites

`preload_test.exs` deliberately purges + deletes a canonical module to observe a reload path. **Correcting a common misconception:** `:code.purge`/`:code.delete` do NOT clear the sticky flag — they only *unload* the module. Verified against OTP 29: `is_sticky/1` is `module_loaded(M) andalso ets_lookup({sticky, M})`, so the `{sticky, M}` entry survives purge/delete; `is_sticky` merely reads `false` while the module is unloaded, and any later reload silently restores stickiness.

The real hazard is subtler, and the two sites differ. **Site 1** JIT-compiles `Cure.Std.List` from `priv/std/list.cure` inside its `try` — a genuinely **non-canonical** version. That reload re-marks the module sticky, so a plain `Preload.preload(kind: :all)` afterwards **cannot overwrite it** (`:code.load_binary` returns `{:error, :sticky_directory}`, which `load_if_present` swallows), and the JIT version would stay stuck for the rest of the suite, defeating C1. **Site 2** stages `Cure.Std.Core` from `staged_sample_beam/0`, which normally harvests the CANONICAL beam out of `_build/cure/ebin`, so its reload is already canonical and it is not, by itself, a real hazard — but it is fixed with the same shape for uniformity and to cover the fallback case where the staged beam came from `priv/ebin` and could differ.

Cleanup at both sites therefore **evicts first** (`:code.unstick_mod` + `:code.purge` + `:code.delete`), THEN `Preload.preload(kind: :all)` to reload the CANONICAL bytes from `_build/cure/ebin`, THEN re-sticks, THEN asserts (`is_sticky` + an md5 check that the loaded bytes equal the canonical beam's). Without the `unstick_mod`, `is_sticky` is trivially true (the test's own reload already re-stuck the module), so the eviction is what makes both asserts meaningful. Both sites use `try/after` (not `on_exit`); keep the file `async: false`.

**Files:**
- Modify: `test/cure/stdlib/preload_test.exs` — Site 1 (`compile_missing_from_sources/1` describe, "recovers an unloaded module by compiling it from source", purge at lines 181–182, `after` block ending ~198); Site 2 (`preload/1` describe, "honours :stdlib_beam_dir app-env override", purge at lines 131–132, `after` block lines 140–147).

**Interfaces:**
- Consumes: the C1 startup stanza (Task 2) has already stuck these modules once. This task evicts the test's own reload and restores/confirms the CANONICAL bytes (purge/delete did NOT clear the sticky entry — see description; the eviction is what lets the canonical reload actually replace the test's version at Site 1, and is applied uniformly at Site 2).
- Produces: canonical `Cure.Std.List` (Site 1) and canonical `Cure.Std.Core` (Site 2) left resident **and sticky** after each test.

- [ ] **Step 1: Write the assertions + re-stick — Site 1 ("recovers an unloaded module")**

After the `try`, the module is resident as the JIT-from-source version and (because the try's reload re-marked it) already sticky — so it must be evicted and replaced with the canonical bytes, not merely re-stuck. Change the `after` to evict → reload canonical → re-stick, and add the post-`try` asserts. Concretely, edit the block at lines 185–197:

```elixir
      try do
        assert Preload.compile_missing_from_sources(:collections) == :ok
        assert Code.ensure_loaded?(module)
      after
        Enum.each(hidden_paths, &:code.add_patha/1)

        case previous_beam do
          nil -> Application.delete_env(:cure, :stdlib_beam_dir)
          value -> Application.put_env(:cure, :stdlib_beam_dir, value)
        end

        File.rm_rf!(empty)

        # C1: the try reloaded a JIT-from-source `Cure.Std.List`, which re-marked
        # the module sticky (purge/delete never removed the sticky entry). A plain
        # preload CANNOT overwrite a sticky module, so evict the test's version
        # first, then reload the CANONICAL bytes from `_build/cure/ebin`, then
        # re-stick — leaving the immutable-canonical surface later tests depend on.
        :code.unstick_mod(module)
        :code.purge(module)
        :code.delete(module)
        Cure.Stdlib.Preload.preload(kind: :all)
        :code.stick_mod(module)
      end

      assert :code.is_sticky(module)

      # Discriminating guard for the actual invariant: the CANONICAL bytes are
      # resident, not the stale JIT-from-source version. `is_sticky` alone is
      # trivially true after the try's own reload, so this md5 check is what goes
      # red if the eviction above is dropped. (`module_info(:md5)` is the loaded
      # module's md5; `:beam_lib.md5/1` is the on-disk canonical's — verified equal
      # for a module loaded from its own beam.)
      {:ok, {^module, disk_md5}} = :beam_lib.md5(~c"_build/cure/ebin/Cure.Std.List.beam")
      assert module.module_info(:md5) == disk_md5
```

- [ ] **Step 2: Write the assertions + re-stick — Site 2 ("honours :stdlib_beam_dir app-env override")**

Edit the `after` block at lines 140–147 (inside the `{:ok, module, binary}` branch):

```elixir
          after
            case previous do
              nil -> Application.delete_env(:cure, :stdlib_beam_dir)
              value -> Application.put_env(:cure, :stdlib_beam_dir, value)
            end

            File.rm_rf!(tmp)

            # C1: the try reloaded the STAGED module, which re-marked it sticky
            # (purge/delete never removed the sticky entry, and a sticky module
            # cannot be overwritten by preload). Evict it, reload the CANONICAL
            # bytes from `_build/cure/ebin`, then re-stick.
            :code.unstick_mod(module)
            :code.purge(module)
            :code.delete(module)
            Cure.Stdlib.Preload.preload(kind: :all)
            :code.stick_mod(module)
          end

          assert :code.is_sticky(module)

          # Consistency guard: the loaded bytes equal the canonical beam. Unlike
          # Site 1 this is normally green even without eviction, because the staged
          # beam is harvested from the canonical `_build/cure/ebin` (see Step 3
          # note) — kept for symmetry and to catch the `priv/ebin`-fallback case.
          canonical_beam = String.to_charlist("_build/cure/ebin/#{module}.beam")
          {:ok, {^module, disk_md5}} = :beam_lib.md5(canonical_beam)
          assert module.module_info(:md5) == disk_md5
```

- [ ] **Step 3: Verify the Site-1 guard is honest (red), then green**

First prove the md5 guard discriminates. Site 1 is the reliable red: its `try` reloads a JIT-from-source `Cure.Std.List`, whose bytes differ from the canonical beam. Comment out Site 1's three eviction lines (`:code.unstick_mod`/`:code.purge`/`:code.delete`) and run

Run: `mix test test/cure/stdlib/preload_test.exs`
Expected: **FAIL** on Site 1's `assert module.module_info(:md5) == disk_md5` — without eviction the stale JIT version is still resident (its md5 differs from the canonical beam). This confirms the assertion is not vacuous. (`assert :code.is_sticky` stays green even here, which is exactly why the md5 check is needed.)

> Note on Site 2: `staged_sample_beam/0` harvests `Cure.Std.Core.beam` from `_build/cure/ebin` (the canonical bytes) in the normal suite, so Site 2's reload is already the canonical module and its md5 assert stays green with or without eviction. Site 2's eviction is defensive uniformity (it guarantees canonical even in the fallback case where the staged beam came from `priv/ebin` and could differ); do not expect a Site-2 red.

Then restore the eviction lines and re-run:

Run: `mix test test/cure/stdlib/preload_test.exs`
Expected: PASS. Both sites' `assert :code.is_sticky(module)` and the canonical-md5 asserts are green; the file leaves the canonical modules resident (canonical bytes) and sticky.

- [ ] **Step 4: Commit**

```bash
git add test/cure/stdlib/preload_test.exs
git commit -m "test(stdlib): re-stick canonical modules after preload purge sites (C1)"
```

---

### Task 4: C2 — emit.ex prefix threading + empty-prefix byte-identity (invariant test FIRST)

Thread an optional module-name `prefix` and a `local_owners` set through the emit entry points so a producer's emitted group installs and cross-links under that prefix. With `prefix: ""` (the default) the emitted Erlang forms are byte-for-byte identical to today. **Write the byte-identity test first (red), then implement.**

> **Scope note (do not oversell this test):** post-change, `module_forms/4` delegates to `module_forms/5` with `[]`, so the Step-1 test below (`/4` vs `/5 [prefix: "", local_owners: nil]`) compares two calls that resolve to identical arguments — it is an internal-consistency guard (the empty-prefix branch adds nothing), NOT a comparison against the *pre-change* output. The authoritative pre-change byte-identity guarantee is **Task 8's committed BEAM golden**, which SHA/byte-compares compiled output against a baseline captured before this change. Keep both.

**Files:**
- Test: Create `test/cure/elab/emit_prefix_test.exs`
- Modify: `lib/cure/elab/emit.ex` — `remote_target/2` (line 195), `module_forms/4` (line 127), add `module_forms/5`, `compile_and_load/2` (line 37), `compile_forms/4` (line 83); add three process-dict helper reads.

**Interfaces:**
- Consumes: `Cure.Elab.Name.owner/1`, `Cure.Elab.Name.base/1` (existing, `name.ex:23`/`36`).
- Produces (relied on by Tasks 5–6):
  - `Cure.Elab.Emit.compile_and_load(env, opts)` gains opts `:prefix` (string, default `""`) and `:local_owners` (list of owner strings like `"Std.Map"`, default = owners derived from `:functions`).
  - `Cure.Elab.Emit.module_forms(env, module, names, origins, emit_opts)` — new /5, `emit_opts` a keyword `[prefix: String.t(), local_owners: [String.t()] | nil]`. Existing /3 and /4 preserved, delegating with `prefix: "", local_owners: nil`.
  - Semantics of `remote_target`: for an owner in `local_owners` **and** a non-empty prefix, target `{String.to_atom(prefix <> "Cure." <> owner), base}`; otherwise the bare canonical `{String.to_atom("Cure." <> owner), base}` (identical to today).

- [ ] **Step 1: Write the failing byte-identity + prefix-routing test**

```elixir
defmodule Cure.Elab.EmitPrefixTest do
  # async: false — some cases load modules into the global code table.
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Name, Program, Emit}

  # A small self-contained stdlib module with an intra-group cross-owner call is
  # ideal, but for the byte-identity invariant any real module's forms suffice.
  setup_all do
    src = File.read!("lib/std/set.cure")
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    map_surface = env.defs |> Map.keys() |> Enum.filter(&(Name.owner(&1) == "Std.Map"))

    fns =
      Program.reachable_def_names(
        env,
        [:from_list, :union, :member, :to_list, :add, :new, :size] ++ map_surface
      )

    {:ok, env: env, origins: origins, fns: fns}
  end

  test "empty prefix produces byte-identical forms to the un-prefixed path", ctx do
    %{env: env, origins: origins, fns: fns} = ctx
    set_names = Enum.filter(fns, &(Name.owner(&1) == "Std.Set"))

    baseline = Emit.module_forms(env, :"Cure.Std.Set", set_names, origins)

    prefixed_empty =
      Emit.module_forms(env, :"Cure.Std.Set", set_names, origins, prefix: "", local_owners: nil)

    assert prefixed_empty == baseline
  end

  test "non-empty prefix reroutes intra-group cross-owner calls to the prefixed target", ctx do
    %{env: env, origins: origins, fns: fns} = ctx
    set_names = Enum.filter(fns, &(Name.owner(&1) == "Std.Set"))

    prefixed =
      Emit.module_forms(env, :"T_Probe.Cure.Std.Set", set_names, origins,
        prefix: "T_Probe.",
        local_owners: ["Std.Set", "Std.Map"]
      )

    flat = :erlang.term_to_binary(prefixed)
    # Set delegates to Map; with Map an in-group owner + prefix set, the remote
    # target must be the PREFIXED Map, and the bare canonical must NOT appear.
    assert flat =~ "T_Probe.Cure.Std.Map"
    refute String.contains?(
             flat |> :erlang.binary_to_term() |> inspect(limit: :infinity),
             "{:\"Cure.Std.Map\""
           )
  end
end
```

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/elab/emit_prefix_test.exs`
Expected: FAIL — `Emit.module_forms/5` is undefined (`UndefinedFunctionError`), so both tests error.

- [ ] **Step 3: Implement the threading in `emit.ex`**

3a. Add the /5 head and stash prefix + local_owners alongside origins. Replace `module_forms/4` (lines 126–157) so /4 delegates to /5:

```elixir
  @doc "As `module_forms/3`, with an import-`origins` map (see `compile_forms/4`)."
  @spec module_forms(Env.t(), module(), [atom()], map()) :: [tuple()]
  def module_forms(%Env{} = env, module, names, origins),
    do: module_forms(env, module, names, origins, [])

  @doc """
  As `module_forms/4`, with `emit_opts`:

    * `:prefix` — module-name prefix for the emitted group (default `""`).
    * `:local_owners` — owner strings emitted together in this call, whose
      intra-group calls should target the prefixed module. `nil` (default) means
      "derive from `names`"; only consulted when `:prefix` is non-empty.

  With `prefix: ""` the forms are byte-for-byte identical to `module_forms/4`.
  """
  @spec module_forms(Env.t(), module(), [atom()], map(), keyword()) :: [tuple()]
  def module_forms(%Env{} = env, module, names, origins, emit_opts) do
    prefix = Keyword.get(emit_opts, :prefix, "")

    local_owners =
      case Keyword.get(emit_opts, :local_owners) do
        nil -> names |> Enum.map(&Name.owner/1) |> Enum.reject(&is_nil/1) |> MapSet.new()
        list -> MapSet.new(list)
      end

    Process.put(:cure_emit_origins, origins)
    Process.put(:cure_emit_prefix, prefix)
    Process.put(:cure_emit_local_owners, local_owners)

    aliases =
      Enum.flat_map(names, fn name ->
        key = Env.resolve_key(env, env.defs, name)
        emitted = emit_name_for_key(key)
        [{name, emitted}, {key, emitted}]
      end)

    Process.put(:cure_emit_aliases, Map.new(aliases))

    try do
      fn_forms = Enum.map(names, &function_form(env, &1))
      exports = Enum.map(fn_forms, fn {:function, _l, name, arity, _cls} -> {name, arity} end)

      [
        {:attribute, @line, :module, module},
        {:attribute, @line, :export, exports}
        | no_auto_import_attr(exports) ++ fn_forms
      ]
    after
      Process.delete(:cure_emit_origins)
      Process.delete(:cure_emit_prefix)
      Process.delete(:cure_emit_local_owners)
      Process.delete(:cure_emit_aliases)
    end
  end
```

Add `alias Cure.Elab.Name` if not already aliased at the top of the module (it is referenced fully-qualified today at line 200/201; the new code uses `Name.owner`, so either add the alias or keep it fully qualified — prefer adding `Name` to the existing `alias Cure.Elab.Erase` line: `alias Cure.Elab.{Erase, Name}`).

3b. Add the two process-dict reader helpers next to `emit_origins/0` (line 177):

```elixir
  # The module-name prefix for the group currently being emitted (`""` outside an
  # emit or for the default un-prefixed path).
  defp emit_prefix, do: Process.get(:cure_emit_prefix, "")

  # The owner strings emitted together in this call (empty set outside an emit).
  defp emit_local_owners, do: Process.get(:cure_emit_local_owners, MapSet.new())
```

3c. Rewrite `remote_target/2` (lines 195–209) so an in-group owner under a non-empty prefix routes to the prefixed module; everything else is unchanged:

```elixir
  defp remote_target(name, origins) do
    cond do
      Map.has_key?(emit_aliases(), name) ->
        :local

      (owner = Cure.Elab.Name.owner(name)) != nil ->
        base = String.to_atom(Cure.Elab.Name.base(name))
        prefix = emit_prefix()

        if prefix != "" and MapSet.member?(emit_local_owners(), owner) do
          {String.to_atom(prefix <> "Cure." <> owner), base}
        else
          {String.to_atom("Cure." <> owner), base}
        end

      (mod = Map.get(origins, name)) != nil ->
        {mod, name}

      true ->
        :local
    end
  end
```

3d. Thread the opts through `compile_and_load/2` (lines 37–45):

```elixir
  def compile_and_load(%Env{} = env, opts) do
    module = Keyword.fetch!(opts, :module)
    names = Keyword.fetch!(opts, :functions)
    origins = Keyword.get(opts, :origins, %{})
    emit_opts = Keyword.take(opts, [:prefix, :local_owners])

    with :ok <- reject_holes(env, names) do
      BeamWriter.compile_and_load(module_forms(env, module, names, origins, emit_opts))
    end
  end
```

3e. Thread the opts through `compile_forms/4` (lines 82–104) — add an optional 5th arg with a default so existing /4 callers (the production pipeline) are byte-identical:

```elixir
  @spec compile_forms(Env.t(), module(), [atom()], map()) :: {:ok, [tuple()]} | {:error, term()}
  def compile_forms(%Env{} = env, module, names, origins),
    do: compile_forms(env, module, names, origins, [])

  @spec compile_forms(Env.t(), module(), [atom()], map(), keyword()) ::
          {:ok, [tuple()]} | {:error, term()}
  def compile_forms(%Env{} = env, module, names, origins, emit_opts) do
    with :ok <- reject_holes(env, names) do
      emit_names = Enum.reject(names, &type_level_def?(env, &1))

      try do
        {:ok, module_forms(env, module, emit_names, origins, emit_opts)}
      rescue
        e in ArgumentError -> {:error, {:cannot_emit, Exception.message(e)}}
      end
    end
  end
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/elab/emit_prefix_test.exs`
Expected: PASS — empty-prefix byte-identity holds and the prefixed intra-group target is rerouted.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab/emit.ex test/cure/elab/emit_prefix_test.exs
git commit -m "feat(emit): thread module-name prefix + local_owners through emission (C2)"
```

---

### Task 5: C2 — prefixed-isolation + prefixed-delegation tests

Prove two coexisting prefixed emissions of the same stdlib group are independently callable and do not clobber the canonical, and that a namespaced Set+Map group's delegated call returns correct results (the intra-group remote target really was prefixed and hit the sandbox, not the canonical). These are the behavioral guarantees Task 6's migration relies on.

**Files:**
- Modify: `test/cure/elab/emit_prefix_test.exs` (add two tests)

**Interfaces:**
- Consumes: `Emit.compile_and_load/2` with `:prefix` + `:local_owners` (Task 4).
- Produces: nothing for later tasks; these are behavioral guards.

- [ ] **Step 1: Write the failing tests**

Add to `Cure.Elab.EmitPrefixTest`:

```elixir
  defp emit_group(env, origins, fns, prefix) do
    owners = ["Std.Set", "Std.Map"]

    fns
    |> Enum.group_by(&Name.owner/1)
    |> Enum.each(fn {owner, names} ->
      {:ok, _} =
        Emit.compile_and_load(env,
          module: String.to_atom(prefix <> "Cure." <> owner),
          functions: names,
          origins: origins,
          prefix: prefix,
          local_owners: owners
        )
    end)

    String.to_atom(prefix <> "Cure.Std.Set")
  end

  test "two prefixed emissions coexist and neither clobbers the canonical", ctx do
    %{env: env, origins: origins, fns: fns} = ctx

    a = emit_group(env, origins, fns, "T_A.")
    b = emit_group(env, origins, fns, "T_B.")

    refute a == b
    assert apply(a, :size, [apply(a, :from_list, [[7, 7, 8]])]) == 2
    assert apply(b, :size, [apply(b, :from_list, [[1, 1, 1, 2]])]) == 2

    # Canonical Set is sticky (loaded at suite startup) and still returns its own
    # results — the prefixed emissions never touched its slot.
    assert :code.is_sticky(:"Cure.Std.Set")
    assert apply(:"Cure.Std.Set", :size, [apply(:"Cure.Std.Set", :from_list, [[3, 3, 4, 5]])]) == 3
  end

  test "a prefixed Set+Map group delegates correctly through the prefixed Map", ctx do
    %{env: env, origins: origins, fns: fns} = ctx

    set = emit_group(env, origins, fns, "T_Deleg.")

    # `union`/`intersection` exercise Set's delegated calls into Map. Correct
    # results prove the intra-group remote target resolved to T_Deleg.Cure.Std.Map,
    # not a missing/mismatched module.
    a = apply(set, :from_list, [[1, 2, 3]])
    b = apply(set, :from_list, [[2, 3, 4]])
    assert Enum.sort(apply(set, :to_list, [apply(set, :union, [a, b])])) == [1, 2, 3, 4]
    assert Enum.sort(apply(set, :to_list, [apply(set, :intersection, [a, b])])) == [2, 3]
  end
```

- [ ] **Step 2: Run to verify they pass**

Run: `mix test test/cure/elab/emit_prefix_test.exs`
Expected: PASS — both new tests green (Task 4 already implemented the mechanism; these are its behavioral confirmation). If `union`/`intersection` are not in the reachable set from `setup_all`, add them to the `reachable_def_names` seed list in `setup_all` (they are already emitted by the seed `[:from_list, :union, ...]`).

- [ ] **Step 3: Commit**

```bash
git add test/cure/elab/emit_prefix_test.exs
git commit -m "test(emit): prefixed isolation + delegation guarantees (C2)"
```

---

### Task 6: C2 migrate — `set_dependent_run_test.exs` to prefixed emission

The producer currently emits bare `Cure.Std.Set` / `Cure.Std.Map`, which under C1 fails with `:sticky_directory` (Task 2). Migrate it to emit under a per-test prefix, passing the whole group's owners as `local_owners`, and read the module back under the prefixed name. It no longer touches the canonical slot.

**Files:**
- Modify: `test/cure/stdlib/set_dependent_run_test.exs` (setup_all, lines 31–87)

**Interfaces:**
- Consumes: `Emit.compile_and_load/2` `:prefix` + `:local_owners` (Task 4).
- Produces: `%{m: :"<prefix>Cure.Std.Set"}` for the existing test bodies (they use `apply(m, ...)`, so no test-body change is needed once `m` points at the prefixed module).

- [ ] **Step 1: Rewrite `setup_all` to emit prefixed**

Replace the emission loop (lines 72–86) and add a `prefix_for/1` helper. The two owners are `Std.Set` and `Std.Map`:

```elixir
  # A per-test module-name prefix, sanitized into a valid atom segment.
  defp prefix_for(mod) do
    seg =
      mod
      |> Atom.to_string()
      |> String.replace_prefix("Elixir.", "")
      |> String.replace(".", "_")

    "T_" <> seg <> "."
  end
```

and, in `setup_all`, after computing `fns`:

```elixir
    prefix = prefix_for(__MODULE__)
    owners = fns |> Enum.map(&Name.owner/1) |> Enum.reject(&is_nil/1) |> Enum.uniq()

    # Emit one BEAM module per owning Cure module, under `prefix`. Passing the WHOLE
    # group's `owners` as `local_owners` keeps Set's delegated call to Map pointed at
    # the PREFIXED Map (a genuine cross-module remote call inside the sandbox), never
    # at the sticky canonical. No canonical slot is touched.
    fns
    |> Enum.group_by(&Name.owner/1)
    |> Enum.each(fn {owner, names} ->
      {:ok, _} =
        Emit.compile_and_load(env,
          module: String.to_atom(prefix <> "Cure." <> owner),
          functions: names,
          origins: origins,
          prefix: prefix,
          local_owners: owners
        )
    end)

    {:ok, m: String.to_atom(prefix <> "Cure.Std.Set")}
```

Rewrite the `@moduledoc` to match the new mechanism. The "one BEAM module per owner" and "collides on shared base names" reasoning (lines 15–21) stays accurate — the prefixed group still emits one module per owner. But the paragraph justifying installation "under the shared process-global BEAM name" (lines 23–29) becomes **false**: the migration's whole point is that the group is now installed under a per-test PREFIX and never touches the shared canonical slot, so that safety-by-full-surface rationale no longer applies. Replace that paragraph with the prefixed-isolation rationale (the canonical is sticky/resident from C1; this test's Set+Map are emitted under `prefix <> "Cure.<owner>"` and delegate among themselves via the prefixed remote target, so a consumer's canonical `Cure.Std.Map` is never dropped or clobbered). Keep the `async: false` note.

- [ ] **Step 2: Run the file**

Run: `mix test test/cure/stdlib/set_dependent_run_test.exs`
Expected: PASS — every `apply(m, ...)` test now runs against the prefixed Set, and the canonical slot is untouched (no `:sticky_directory`).

- [ ] **Step 3: Commit**

```bash
git add test/cure/stdlib/set_dependent_run_test.exs
git commit -m "test(stdlib): namespace set_dependent_run producer under per-test prefix (C2)"
```

---

### Task 7: C3 — simplify `stdlib_test.exs` to the sticky canonical

`stdlib_test.exs` compiles each stdlib module itself via `compile_stdlib/1` → `Cure.Compiler.compile_and_load(source, file: path)` (which loads under the canonical name) and purges it on exit. Under C1 that now hits `:sticky_directory`. This test only asserts runtime results the canonical module also produces (it is a pure consumer, not an emitter-output assertion), so drop the self-compilation and call the sticky canonical directly.

**Files:**
- Modify: `test/cure/stdlib/stdlib_test.exs` — remove `compile_stdlib/1` (lines 5–13) and `purge/1` (lines 15–18); update each `setup`/test that used them (Math, Io, Core ×4, List, String, System describe blocks) to reference the canonical module atom.

**Interfaces:**
- Consumes: the sticky canonical modules resident from C1 (`:"Cure.Std.Math"`, `:"Cure.Std.Io"`, `:"Cure.Std.Core"`, `:"Cure.Std.List"`, `:"Cure.Std.String"`, `:"Cure.Std.System"`).
- Produces: nothing for later tasks.

- [ ] **Step 1: Replace the helpers with canonical-name resolution**

Delete `compile_stdlib/1` and `purge/1`. Add a single mapping helper:

```elixir
  # The canonical, sticky stdlib module for a short name (resident from C1).
  defp std(name) do
    module = String.to_atom("Cure.Std." <> Macro.camelize(name))
    {:module, ^module} = :code.ensure_loaded(module)
    module
  end
```

Then in each describe's `setup`, replace:

```elixir
      m = compile_stdlib("math")
      on_exit(fn -> purge(m) end)
```

with:

```elixir
      m = std("math")
```

(and analogously `std("io")`, `std("core")`, `std("list")`, `std("string")`, `std("system")`). Remove every `on_exit(fn -> purge(m) end)` line — nothing is emitted, so nothing needs cleanup. `Macro.camelize("core")` → `"Core"`, `Macro.camelize("system")` → `"System"`; all six short names camelize to the correct owner segment. The test bodies already use `m` via `apply(m, ...)` / `m.fun(...)`, so they need no change.

- [ ] **Step 2: Handle the `run_core_fn` describe (comparison operations)**

The "Std.Core -- comparison operations" describe (line 203) uses `run_core_fn/1` (line 219), which compiles an **ad-hoc snippet** that `use Std.Core` and emits its own non-stdlib module, then `purge(mod)` at line 221. That snippet's module is NOT a canonical stdlib name, so it does **not** hit sticky — but its `use Std.Core` now resolves against the sticky canonical `Cure.Std.Core` (present from C1), which is exactly what previously flaked. Leave `run_core_fn/1` compiling its snippet, but if it references the now-deleted `purge/1`, inline the purge locally:

```elixir
  defp run_core_fn(expr) do
    src = # ... unchanged snippet builder ...
    {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    result = # ... unchanged apply ...
    :code.purge(mod)
    :code.delete(mod)
    result
  end
```

(Only change: replace the `purge(mod)` call with the inlined `:code.purge/:code.delete` since the `purge/1` helper was removed. If `run_core_fn` already inlines these, no change.)

- [ ] **Step 3: Run the file**

Run: `mix test test/cure/stdlib/stdlib_test.exs`
Expected: PASS — all describe blocks resolve against the sticky canonical; no `:sticky_directory`, no `missing_stdlib_module`.

- [ ] **Step 4: Commit**

```bash
git add test/cure/stdlib/stdlib_test.exs
git commit -m "test(stdlib): call sticky canonical stdlib directly, drop self-compile (C3)"
```

---

### Task 8: C4 — golden carve-out verification

Golden tests SHA-256 / byte-compare the compiled BEAM and bake the **canonical** module name into the compared bytes. They MUST stay un-namespaced (empty prefix) and may remain `async: false`. This task is verification-only: confirm they still pass under C1 + C2 (empty prefix ⇒ byte-identical output). No source change expected.

**Files:**
- Verify (no modify expected): `test/cure/compiler/actor_quote_golden_test.exs`.

**Interfaces:**
- Consumes: the empty-prefix byte-identity invariant (Task 4).
- Produces: nothing.

- [ ] **Step 1: Run the golden test**

Run: `mix test test/cure/compiler/actor_quote_golden_test.exs`
Expected: PASS unchanged — it compiles under the canonical name with the default empty prefix, so its bytes match the committed golden. If it fails with `:sticky_directory`, it means the golden test itself loads under a canonical stdlib name; in that case it is a producer, not a pure golden — STOP and report (this would contradict the C4 classification and needs a design note, not a silent workaround).

- [ ] **Step 2: Record the result (no commit if unchanged)**

If the test passes with no source change, note it in the task log; there is nothing to commit. If a change was required, commit with `test(golden): keep actor-quote golden un-namespaced under C1/C2 (C4)`.

---

### Task 9: C5 — reclassify isolated files to async

Files fixed by C1/C2/C3 that have **no other** genuine global-state reason (telemetry handlers, `Application` env mutation, cwd) can flip to `async: true`. Do this only for the files this work isolated; leave genuinely-stateful files serial.

**Files:**
- Modify: `test/cure/stdlib/iter_test.exs` (pure consumer, fixed by C1) → `async: true`.
- Modify: `test/cure/stdlib/stdlib_test.exs` → **stays `async: false`** — the `run_core_fn` describe still compiles+loads+purges an ad-hoc module (global code-table mutation). Do NOT flip it.
- Do NOT flip: `set_dependent_run_test.exs` — it loads prefixed modules into the global code table (still global-state mutation); keep `async: false` (defence-in-depth; its correctness no longer depends on it, but two runs racing to define the same prefixed atom is still global mutation). Note this honestly in the completion report as a "could be async later" item, not done here.
- Do NOT flip: `preload_test.exs`, `preload_sticky_test.exs`, `emit_prefix_test.exs` — all mutate the global code table.

**Interfaces:**
- Consumes: C1 (iter_test now correct without emission).
- Produces: nothing.

- [ ] **Step 1: Flip iter_test to async**

In `test/cure/stdlib/iter_test.exs`, change the `use ExUnit.Case, async: false` line to `use ExUnit.Case, async: true`. (It only calls `Cure.Std.Iter.*` on the sticky canonical — no global mutation.)

- [ ] **Step 2: Run iter_test alone, then alongside a producer to confirm no reintroduced race**

Run: `mix test test/cure/stdlib/iter_test.exs`
Expected: PASS.

Run: `mix test test/cure/stdlib/iter_test.exs test/cure/stdlib/set_dependent_run_test.exs test/cure/stdlib/stdlib_test.exs`
Expected: PASS — iter_test async, the others sync; the sticky canonical keeps iter_test correct regardless of interleaving.

- [ ] **Step 3: Commit**

```bash
git add test/cure/stdlib/iter_test.exs
git commit -m "test(stdlib): iter_test is a pure consumer, run async (C5)"
```

---

### Task 10: Determinism gate + timing

The suite is its own integration test; determinism is the property under test. Run the full suite twice at two fixed seeds — zero failures both times — and record wall-clock. Before this work, a run showed 10 clobber failures; after, both seeds must be green.

**Files:** none (verification only).

- [ ] **Step 1: Full suite, seed 0, timed**

Run (one build at a time — never concurrent):
```bash
/usr/bin/time -p mix test --seed 0 2>&1 | tail -40
```
Expected: `0 failures` (modulo the 1 pre-existing skip). Record wall-clock seconds.

- [ ] **Step 2: Full suite, a second fixed seed, timed**

Run:
```bash
/usr/bin/time -p mix test --seed 4242 2>&1 | tail -40
```
Expected: `0 failures`. Record wall-clock. Two distinct seeds green = determinism demonstrated (order-independence, the clobber's signature).

- [ ] **Step 3: Confirm timing is at or below the Path B baseline**

Expected: wall-clock ≤ the ~6 min Path B baseline, ideally lower now that `iter_test` runs async. If materially slower, investigate before declaring done (sticking is O(#modules) at startup and should be sub-second).

- [ ] **Step 4: Commit any final notes**

If a timing/notes file is produced, commit it; otherwise nothing to commit. The green two-seed runs are the deliverable, recorded in the completion report.

---

## Self-Review

**Spec coverage:**
- C1 (startup load-all + stick, source-declared completeness, sentinel floor, preload-tolerates-sticky precondition, re-stick after purge sites) → Tasks 1, 2, 3. ✓
- C2 (emit prefix + local_owners threading, empty-prefix byte-identity, prefixed isolation, prefixed delegation, producer migration) → Tasks 4, 5, 6. ✓
- C3 (simplify pure consumers) → Task 7. ✓
- C4 (golden carve-out stays un-namespaced) → Task 8. ✓
- C5 (reclassify to async) → Task 9. ✓
- Determinism gate (two seeds) + timing → Task 10. ✓
- Baseline Path B untouched → Global Constraints. ✓

**Placeholder scan:** No TBD/TODO. Every code step shows the actual code. The one "no honest red" case (Task 1) is called out explicitly as a green-on-write guard with a stated failure meaning.

**Type consistency:** `prefix` is a string ending in `.` everywhere (`"T_...."`); `local_owners` is a list of owner strings (`"Std.Map"`) at the API boundary, converted to `MapSet` inside `module_forms/5`. `remote_target/2` reads prefix/local_owners from the process dict (`emit_prefix/0`, `emit_local_owners/0`), matching how `emit_origins/0`/`emit_aliases/0` already work. `module_forms` arities: /3 and /4 preserved, /5 added; `compile_forms` /4 preserved, /5 added; `compile_and_load/2` takes `:prefix`/`:local_owners` in opts. `prefix_for/1` and `std/1` are test-local helpers. Consistent across Tasks 4–7.

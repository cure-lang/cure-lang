defmodule Cure.Stdlib.SetDependentRunTest do
  @moduledoc """
  End-to-end run of the SHIPPING `lib/std/set.cure` through the dependent
  pipeline. `Std.Set` is a `Map(t, Bool)` delegating to `Std.Map`/`Std.List`;
  its `from_list`/`intersection`/`difference` use structural recursion (not a
  `foldl` seeded with a polymorphic `new()`, which leaves the seed's
  metavariables unsolved — see
  `test/cure/elab/fold_accumulator_poly_seed_reach_test.exs`).

  `dependent_elaboration_parity_test.exs` guards that the file *elaborates*;
  `set_dependent_capability_test.exs` guards a self-contained *emit*. This pins
  the actual delegated module's *runtime* behaviour so a regression in the
  cross-module lowering is caught as a wrong answer, not just a type error.

  Emission is ONE BEAM module per Cure owner (`Cure.Std.Set`, `Cure.Std.Map`),
  exactly as the real compiler lowers a multi-module program — Set's delegating
  calls (`new`/`remove`/`size`) reach `Std.Map`'s same-named functions as REMOTE
  calls. Bundling both owners into a single BEAM module is not a real compile
  target and collides on the shared base names (two `new/0`, `remove/2`, …); the
  owner-qualified identities that canonicalization now keeps distinct are what
  make the split faithful.

  This test emits its Set+Map group under a per-test module-name PREFIX
  (`T_<module>.Cure.<owner>`), never touching the shared canonical slots. The
  canonical `Cure.Std.Map`/`Cure.Std.List` are loaded and made *sticky* at suite
  startup (test_helper C1), so a consumer test's canonical `Cure.Std.Map` can
  never be dropped or clobbered by this producer — the historical flake, where a
  tree-shaken partial view overwrote the shared global name. Set's delegated
  calls resolve to the PREFIXED Map (via `remote_target`'s prefix routing, C2), a
  genuine cross-module remote call staying inside this test's sandbox. The
  emitted Map still carries its FULL owner surface (`map_surface` below), so it
  mirrors what the real compiler installs. `async: false` is retained as
  defence-in-depth against two runs racing to define the same prefixed atom, not
  for correctness.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Name, Program, Emit}

  setup_all do
    src = File.read!("lib/std/set.cure")
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    # Seed reachability with the FULL `Std.Map` owner surface, not just Set's
    # delegated subset, so the prefixed `Cure.Std.Map` this test emits mirrors the
    # full module the real compiler installs (the stdlib preload JIT-compiles all
    # of `map.cure`). The real compiler never prunes a dependency owner:
    # `codegen_modules_with_main` emits only the main module and each imported owner
    # is installed at full surface by the preload — so emitting the full owner
    # surface here mirrors the shipping behaviour. Because this now emits under a
    # per-test prefix, it no longer touches the shared canonical slot at all.
    fns =
      Program.reachable_def_names(
        env,
        [
          :from_list,
          :intersection,
          :difference,
          :union,
          :member,
          :to_list,
          :add,
          :remove,
          :new,
          :size
        ]
      )
      |> Enum.filter(&(Name.owner(&1) == "Std.Set"))

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
  end

  # A per-test module-name prefix, sanitized into a valid atom segment.
  defp prefix_for(mod) do
    seg =
      mod
      |> Atom.to_string()
      |> String.replace_prefix("Elixir.", "")
      |> String.replace(".", "_")

    "T_" <> seg <> "."
  end

  test "from_list dedups and size counts distinct elements", %{m: m} do
    assert apply(m, :size, [apply(m, :from_list, [[7, 7, 8]])]) == 2
  end

  test "intersection keeps the shared elements", %{m: m} do
    a = apply(m, :from_list, [[1, 2, 3]])
    b = apply(m, :from_list, [[2, 3, 4]])
    assert Enum.sort(apply(m, :to_list, [apply(m, :intersection, [a, b])])) == [2, 3]
  end

  test "difference keeps only elements not in the second set", %{m: m} do
    a = apply(m, :from_list, [[1, 2, 3]])
    b = apply(m, :from_list, [[2, 3, 4]])
    assert Enum.sort(apply(m, :to_list, [apply(m, :difference, [a, b])])) == [1]
  end

  test "member and remove behave", %{m: m} do
    s = apply(m, :from_list, [[1, 2]])
    assert apply(m, :member, [2, s]) == true
    assert apply(m, :member, [9, s]) == false
    assert apply(m, :member, [2, apply(m, :remove, [2, s])]) == false
  end
end

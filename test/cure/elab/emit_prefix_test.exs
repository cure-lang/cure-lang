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

    fns =
      Program.reachable_def_names(
        env,
        [:from_list, :union, :intersection, :member, :to_list, :add, :new, :size]
      )
      |> Enum.filter(&(Name.owner(&1) == "Std.Set"))

    {:ok, env: env, origins: origins, fns: fns}
  end

  test "empty prefix produces forms identical to the un-prefixed path (α-equivalent)", ctx do
    %{env: env, origins: origins, fns: fns} = ctx
    set_names = Enum.filter(fns, &(Name.owner(&1) == "Std.Set"))

    baseline = Emit.module_forms(env, :"Cure.Std.Set", set_names, origins)

    prefixed_empty =
      Emit.module_forms(env, :"Cure.Std.Set", set_names, origins, prefix: "", local_owners: nil)

    # `module_forms` mints synthetic binder names via `fresh_var/1`, whose global
    # monotonic counter advances every call — so two independent emissions of the
    # same module are α-equivalent but never atom-for-atom equal when a body holds
    # a `case`/`lambda`/`let`. That non-determinism pre-dates this change and is
    # orthogonal to it. Canonicalize the variable names (first-occurrence order,
    # which preserves the binding/use structure) before comparing: what must hold
    # is that the empty-prefix branch reroutes NOTHING — same structure, same
    # remote targets — as the un-prefixed `/4` path.
    assert normalize_vars(prefixed_empty) == normalize_vars(baseline)
  end

  test "non-empty prefix keeps published dependency calls on their canonical target", ctx do
    %{env: env, origins: origins, fns: fns} = ctx
    set_names = Enum.filter(fns, &(Name.owner(&1) == "Std.Set"))

    prefixed =
      Emit.module_forms(env, :"T_Probe.Cure.Std.Set", set_names, origins,
        prefix: "T_Probe.",
        local_owners: ["Std.Set"]
      )

    flat = :erlang.term_to_binary(prefixed)
    # Set delegates to Map; with Map an in-group owner + prefix set, the remote
    # target must be the PREFIXED Map, and the bare canonical must NOT appear.
    refute flat =~ "T_Probe.Cure.Std.Map"

    assert String.contains?(
             flat |> :erlang.binary_to_term() |> inspect(limit: :infinity),
             ~s(:"Cure.Std.Map")
           )
  end

  defp emit_group(env, origins, fns, prefix) do
    owners = ["Std.Set"]

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

  # Canonicalize every `{:var, _, name}` atom in an abstract-forms tree to a
  # first-occurrence-ordered `:_v<n>`, so two α-equivalent emissions compare equal
  # despite `fresh_var/1`'s run-global counter. Structure is walked in a fixed
  # pre-order, so corresponding binders in two structurally-identical trees receive
  # the same canonical index; a genuine structural or remote-target divergence still
  # fails the comparison.
  defp normalize_vars(forms) do
    {normalized, _map} = walk_vars(forms, %{})
    normalized
  end

  defp walk_vars({:var, line, name}, map) do
    case Map.get(map, name) do
      nil ->
        canon = :"_v#{map_size(map)}"
        {{:var, line, canon}, Map.put(map, name, canon)}

      canon ->
        {{:var, line, canon}, map}
    end
  end

  defp walk_vars(tuple, map) when is_tuple(tuple) do
    {list, map} = walk_vars(Tuple.to_list(tuple), map)
    {List.to_tuple(list), map}
  end

  defp walk_vars(list, map) when is_list(list), do: Enum.map_reduce(list, map, &walk_vars/2)

  defp walk_vars(other, map), do: {other, map}
end

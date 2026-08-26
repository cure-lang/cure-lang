defmodule Cure.Stdlib.DynamicRunTest do
  @moduledoc """
  `Std.Dynamic` is a typed stand-in for `Any`: one homogeneous tagged sum
  (`Dynamic`) over the real BEAM value shapes, with a mutually-recursive
  association-list map (`DynamicEntry`) so an arbitrarily-nested document has one
  static type. These tests exercise the module *on its own* — no optics — by
  building `Dynamic` values through its smart constructors and reading them back
  through its total accessors, proving the recursion round-trips end to end.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  setup_all do
    src = File.read!(Path.join(File.cwd!(), "lib/std/dynamic.cure"))
    {:ok, env} = Program.elaborate(src)

    fns =
      Program.reachable_def_names(env, [
        :of_int,
        :of_str,
        :of_list,
        :of_map,
        :entry,
        :tag,
        :entries,
        :entry_key,
        :entry_value
      ])

    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.Test.StdDynamic", functions: fns)
    {:ok, mod: m}
  end

  # Map([ Entry(Str("count"), Int(3)),
  #       Entry(Str("items"), List([Int(1), Int(2)])) ])
  defp sample_doc(m) do
    count = apply(m, :entry, [apply(m, :of_str, [~c"count"]), apply(m, :of_int, [3])])

    items =
      apply(m, :entry, [
        apply(m, :of_str, [~c"items"]),
        apply(m, :of_list, [[apply(m, :of_int, [1]), apply(m, :of_int, [2])]])
      ])

    apply(m, :of_map, [[count, items]])
  end

  test "tag discriminates every constructor shape", %{mod: m} do
    assert apply(m, :tag, [apply(m, :of_int, [7])]) == :int
    assert apply(m, :tag, [apply(m, :of_str, [~c"hi"])]) == :str
    assert apply(m, :tag, [apply(m, :of_list, [[]])]) == :list
    assert apply(m, :tag, [sample_doc(m)]) == :map
  end

  test "a nested document round-trips through the map accessors", %{mod: m} do
    entries = apply(m, :entries, [sample_doc(m)])
    assert length(entries) == 2

    [first, second] = entries

    assert apply(m, :tag, [apply(m, :entry_key, [first])]) == :str
    assert apply(m, :tag, [apply(m, :entry_value, [first])]) == :int

    assert apply(m, :tag, [apply(m, :entry_key, [second])]) == :str
    assert apply(m, :tag, [apply(m, :entry_value, [second])]) == :list
  end

  test "entries on a non-map is empty (total, never crashes)", %{mod: m} do
    assert apply(m, :entries, [apply(m, :of_int, [1])]) == []
  end
end

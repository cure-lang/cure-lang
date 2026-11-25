defmodule Antigen.UniverseFamilyPiecesTest do
  use ExUnit.Case, async: true

  alias Antigen.Challenge
  alias Cure.Core.{Inductive, Serialize, UniverseLevel}

  test "standalone family sort is the first recursive Core piece, not opaque metadata" do
    for sort <- sorts() do
      original = family_challenge(sort)
      assert {scaffold, [{"fam_sort", {:type, ^sort}} | _]} = Challenge.to_pieces(original)
      refute Map.has_key?(scaffold, "fam_level")
      assert scaffold["fam_name"] == "F"
      assert scaffold["fam_param_names"] == ["u"]
      assert [%{"name" => "MkF", "arg_names" => ["x"], "quantities" => ["unrestricted"]}] = scaffold["ctors"]
      assert roundtrip(original) == original
    end
  end

  test "indexed and rewriting family sort pieces use their existing named prefix" do
    for kind <- [:indexed_case, :rewrite_eq], sort <- sorts() do
      family = family_challenge(sort).payload

      payload = %{
        families: [{family.family, family.ctors}],
        def_name: :probe,
        def_type: {:level_type},
        def_body: {:level_value, UniverseLevel.zero()}
      }

      original = Challenge.new(kind: kind, assay: "universes", label: :positive, payload: payload)
      assert {scaffold, [{"fam:0:sort", {:type, ^sort}} | _]} = Challenge.to_pieces(original)
      assert [family_scaffold] = scaffold["families"]
      refute Map.has_key?(family_scaffold, "fam_level")
      assert roundtrip(original) == original
    end
  end

  test "changing only family sort changes serialized term evidence" do
    first = family_challenge({:finite, UniverseLevel.closed(0)})
    second = family_challenge({:finite, UniverseLevel.closed(37)})
    {same_scaffold, first_pieces} = Challenge.to_pieces(first)
    assert {^same_scaffold, second_pieces} = Challenge.to_pieces(second)
    refute encoded(first_pieces) == encoded(second_pieces)

    open = UniverseLevel.atom({:var, 0})
    third = family_challenge({:finite, UniverseLevel.succ(open)})
    assert {_scaffold, [{"fam_sort", term} | _]} = Challenge.to_pieces(third)
    assert Serialize.encode(term) =~ "(atom (var 0) 1)"
  end

  test "bad sort wrappers and duplicate pieces refuse without crashing safe candidate handling" do
    original = family_challenge({:finite, UniverseLevel.closed(0)})
    {scaffold, [{"fam_sort", _} | rest] = pieces} = Challenge.to_pieces(original)

    for bad <- [{:type, 0}, {:level_type}, {:var, 0}, {:type, {:omega, -1}}] do
      assert {:error, %ArgumentError{}} = rebuild_safe(original, scaffold, [{"fam_sort", bad} | rest])
    end

    assert {:error, %ArgumentError{}} = rebuild_safe(original, scaffold, rest)
    assert {:error, %ArgumentError{}} = rebuild_safe(original, scaffold, pieces ++ [hd(pieces)])
    assert {:error, %ArgumentError{}} = rebuild_safe(original, Map.put(scaffold, "fam_level", 0), pieces)
  end

  test "nested family old metadata and malformed sort wrappers never fall back" do
    family = family_challenge({:finite, UniverseLevel.closed(0)}).payload

    original =
      Challenge.new(
        kind: :indexed_case,
        assay: "universes",
        label: :positive,
        payload: %{
          families: [{family.family, family.ctors}],
          def_name: :probe,
          def_type: {:atom_type},
          def_body: {:atom_lit, :ok}
        }
      )

    {scaffold, [{"fam:0:sort", _} | rest]} = Challenge.to_pieces(original)
    assert {:error, %ArgumentError{}} = rebuild_safe(original, scaffold, rest)
    assert {:error, %ArgumentError{}} = rebuild_safe(original, scaffold, [{"fam:0:sort", {:level_type}} | rest])
    [family_scaffold] = scaffold["families"]
    old = put_in(scaffold["families"], [Map.put(family_scaffold, "fam_level", 0)])
    {_scaffold, pieces} = Challenge.to_pieces(original)
    assert {:error, %ArgumentError{}} = rebuild_safe(original, old, pieces)
  end

  test "legacy raw family level records are not current producers" do
    original = family_challenge({:finite, UniverseLevel.closed(0)})
    old_family = original.payload.family |> Map.delete(:sort) |> Map.put(:level, 0)
    old = %{original | payload: %{original.payload | family: old_family}}
    assert_raise ArgumentError, fn -> Challenge.to_pieces(old) end
  end

  defp sorts do
    [
      {:finite, UniverseLevel.closed(37)},
      {:finite, UniverseLevel.succ(UniverseLevel.atom({:var, 0}))},
      {:omega, Integer.pow(10, 100)}
    ]
  end

  defp family_challenge(sort) do
    family = %{name: :F, params: [{:u, {:level_type}}], indices: [], sort: sort}
    ctor = Inductive.ctor(:MkF, [{:x, {:type, {:finite, UniverseLevel.closed(0)}}}], [])
    Challenge.new(kind: :family, assay: "universes", label: :positive, payload: %{family: family, ctors: [ctor]})
  end

  defp roundtrip(original) do
    {scaffold, pieces} = Challenge.to_pieces(original)

    decoded =
      Enum.map(pieces, fn {id, term} ->
        {:ok, term} = Serialize.decode(Serialize.encode(term))
        {id, term}
      end)

    assert {:ok, rebuilt} = rebuild_safe(original, scaffold, decoded)
    rebuilt
  end

  defp rebuild_safe(original, scaffold, pieces),
    do:
      Challenge.safe_from_pieces(
        original.kind,
        original.assay,
        original.label,
        original.seed,
        original.note,
        scaffold,
        pieces
      )

  defp encoded(pieces), do: Enum.map(pieces, fn {id, term} -> {id, Serialize.encode(term)} end)
end

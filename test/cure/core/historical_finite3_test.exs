defmodule Cure.Core.HistoricalFinite3Test do
  use ExUnit.Case, async: true

  alias Cure.Core.{
    Env,
    HistoricalFinite3,
    LevelValue,
    ProofContext,
    ProofRecipe,
    ProofSnapshot,
    ProofSnapshotWire,
    ProofWire,
    Serialize,
    UniverseLevel
  }

  test "new canonical finite0..2 project to the unchanged historical code vectors" do
    for n <- 0..2 do
      current = {:type, {:finite, UniverseLevel.closed(n)}}
      assert {:ok, {:type, ^n}} = HistoricalFinite3.project_finite3(current)
      assert {:ok, {:node, 0, "", ^n, []}} = ProofWire.code(current)

      assert {:ok, %{format: {:cure_historical_finite3, 1}, characters: characters}} =
               ProofWire.encode_finite3(current, [""])

      assert characters == "(;;" <> String.duplicate("1", n) <> ";)"
    end
  end

  test "high, open, limit, old-integer and level nodes refuse in every recursive position" do
    unsupported = [
      {:type, {:finite, UniverseLevel.closed(37)}},
      {:type, {:finite, UniverseLevel.atom({:var, 0})}},
      {:type, {:omega, 0}},
      {:type, 0},
      {:level_type},
      {:level_value, UniverseLevel.zero()}
    ]

    for term <- unsupported do
      for nested <- [
            term,
            {:app, {:var, 0}, term},
            {:pi, :erased, {:atom_type}, term},
            {:data, :ok, [], [term]},
            {:case, {:var, 0}, {:atom_type}, [{:ok, 1, term}]}
          ] do
        assert {:error, _} = HistoricalFinite3.project_finite3(nested)
        assert {:error, _} = ProofWire.code(nested)
      end
    end

    # This is a historical adapter restriction, never a current codec ceiling.
    for term <- Enum.take(unsupported, 3) do
      assert {:ok, ^term} = Serialize.decode(Serialize.encode(term))
    end
  end

  test "private semantic level values are not mistaken for serialized Core levels" do
    for n <- 0..2 do
      assert {:ok, {:sort, ^n}} = ProofContext.value({:vtype, {:finite, LevelValue.closed(n)}}, 0)
      assert {:error, _} = ProofContext.value({:vtype, {:finite, UniverseLevel.closed(n)}}, 0)
      assert {:error, _} = ProofContext.value({:vtype, n}, 0)
    end

    for sort <- [
          {:finite, LevelValue.closed(37)},
          {:finite, %LevelValue{constant: 0, atoms: [{{:vneutral, {:nvar, 0}}, 0}]}},
          {:omega, 0}
        ] do
      assert {:error, _} = ProofContext.value({:vtype, sort}, 1)
    end
  end

  test "nonempty snapshots project family sorts and retain current framed Core" do
    sort = {:finite, UniverseLevel.closed(0)}
    family = %{name: :"Finite3#Empty", params: [], indices: [], sort: sort, ctor_order: []}
    env = %{Env.empty() | families: %{family.name => family}}
    env = env |> Env.with_owner("Finite3") |> Env.add_def(:A, {:type, sort}, {:atom_type})

    assert {:ok, snapshot} = ProofSnapshot.capture(env)
    assert 2 = snapshot["version"]
    assert %{"format" => "cure-historical-finite3", "version" => 1} = snapshot["universe_transport"]
    assert [%{"level" => 0}] = snapshot["families"]
    assert [%{"type" => %{"format" => "cure-core", "version" => 2}}] = snapshot["globals"]
    assert {:ok, generated} = ProofSnapshot.to_agda(env, "Fixtures.Finite3")
    assert generated =~ "(tm-type l0)"
    assert {:ok, _characters} = ProofSnapshotWire.encode(env, ["", "Finite3#Empty", "Finite3#A"])

    for sort <- [{:finite, UniverseLevel.closed(37)}, {:finite, UniverseLevel.atom({:var, 0})}, {:omega, 0}] do
      changed = put_in(env.families[family.name][:sort], sort)
      assert {:error, %{reason: :invalid_universe}} = ProofSnapshot.capture(changed)
    end

    changed = Env.add_def(env, :hidden_level, {:atom_type}, {:lam, :erased, {:atom_type}, {:level_type}})
    assert {:error, %{reason: :unsupported_term}} = ProofSnapshot.capture(changed)
  end

  test "historical recipe sort slots require canonical finite-three projection" do
    assert {:ok, _} =
             ProofRecipe.encode_recipe({:r_cumul, {:finite, UniverseLevel.closed(1)}, :r_leaf}, [
               ""
             ])

    for sort <- [
          0,
          {:omega, 0},
          {:finite, UniverseLevel.closed(37)},
          {:finite, UniverseLevel.atom({:var, 0})}
        ] do
      assert {:error, _} = ProofRecipe.encode_recipe({:r_cumul, sort, :r_leaf}, [""])
    end
  end
end

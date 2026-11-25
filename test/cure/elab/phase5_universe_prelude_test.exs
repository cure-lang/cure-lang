defmodule Cure.Elab.Phase5UniversePreludeTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Sort, UniverseLevel}
  alias Cure.Elab.{Program, ProofDisplay}

  test "proof diagnostics render closed, open and limit universes" do
    assert ProofDisplay.format({:type, Sort.finite_zero()}) == "Type"
    assert ProofDisplay.format({:type, Sort.finite(UniverseLevel.closed(37))}) == "Type37"
    assert ProofDisplay.format({:type, {:omega, 0}}) == "TypeLimit"
    assert ProofDisplay.format({:type, {:omega, 37}}) == "TypeLimit37"
    assert ProofDisplay.format({:level_type}) == "UniverseLevel"

    level = UniverseLevel.atom({:var, 0})
    assert ProofDisplay.format({:type, Sort.finite(level)}, ["l"]) == "Type(l)"
    assert ProofDisplay.format({:level_value, level}, ["l"]) == "l"
  end

  test "prelude closure keeps transitive globals in both universe payload wrappers" do
    for wrap <- [&{:type, Sort.finite(&1)}, &{:level_value, &1}],
        slot <- [:type, :body] do
      hidden = wrap.(UniverseLevel.atom({:global, :"Dependency#level"}))

      defs = %{
        :"Provider#root" => %{type: {:level_type}, body: nil} |> Map.put(slot, hidden),
        :"Dependency#level" => %{type: {:level_type}, body: {:global, :"Dependency#base"}},
        :"Dependency#base" => %{type: {:level_type}, body: {:level_value, UniverseLevel.closed(0)}},
        :"Unrelated#unused" => %{type: {:level_type}, body: nil}
      }

      assert defs |> Program.reachable_global_closure([:"Provider#root"]) |> MapSet.new() ==
               MapSet.new([:"Provider#root", :"Dependency#level", :"Dependency#base"])
    end
  end

  test "prelude closure descends through nested levels and branch bodies" do
    nested =
      {:level_value,
       UniverseLevel.atom(
         {:app, {:global, :"Dependency#outer"},
          {:type, Sort.finite(UniverseLevel.atom({:global, :"Dependency#inner"}))}}
       )}

    defs = %{
      :"Provider#root" => %{
        type: {:level_type},
        body: {:case, {:global, :"Dependency#scrutinee"}, {:level_type}, [{:C, 2, nested}]}
      },
      :"Dependency#outer" => %{type: {:level_type}, body: nil},
      :"Dependency#inner" => %{type: {:level_type}, body: nil},
      :"Dependency#scrutinee" => %{type: {:level_type}, body: nil}
    }

    assert defs |> Program.reachable_global_closure([:"Provider#root"]) |> MapSet.new() ==
             MapSet.new(Map.keys(defs))
  end
end

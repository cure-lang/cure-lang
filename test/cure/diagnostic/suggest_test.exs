defmodule Cure.Diagnostic.SuggestTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Suggest

  test "filters semantic ineligibility before spelling distance" do
    candidates = [
      %{id: :wrong_namespace, name: "pritn", namespace: :type, visibility: :public},
      %{id: :private, name: "print", namespace: :value, visibility: :private},
      %{id: :wrong_arity, name: "print", namespace: :value, arity: 2},
      %{id: :usable, name: "println", namespace: :value, arity: 1, visibility: :public},
      %{id: :qualified, name: "print", namespace: :value, owner: "Std.Io", imported: false}
    ]

    ranked = Suggest.rank(candidates, "pritn", :value, arity: 1)

    assert Enum.map(ranked, & &1.candidate_id) == [:usable, :qualified]
    assert hd(ranked).namespace == :value
    assert hd(ranked).owner == nil
  end

  test "distance is case insensitive and recognizes adjacent transpositions" do
    assert Suggest.distance("Nmae", "Name") == 1
    assert Suggest.distance("Print", "print") == 0
  end

  test "plain candidates remain deterministic and capped" do
    candidates = [:alpha, :alphi, :alpho, :alphe, :completely_unrelated]

    assert Enum.map(Suggest.rank(candidates, "alpah", :value), & &1.name) ==
             ["alpha", "alphe", "alphi"]
  end
end

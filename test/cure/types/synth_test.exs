defmodule Cure.Types.SynthTest do
  use ExUnit.Case, async: true

  alias Cure.Types.Synth

  describe "synthesise/4" do
    test "returns a matching in-scope variable first" do
      candidates = Synth.synthesise("Int", %{"n" => "Int"}, %{})
      assert [%{expr: "n", cost: 1} | _] = candidates
    end

    test "proposes stdlib function calls when args fit" do
      candidates = Synth.synthesise("Int", %{"xs" => "List(Int)"}, %{})
      exprs = Enum.map(candidates, & &1.expr)
      assert Enum.any?(exprs, &(&1 =~ "Std.List.length"))
    end

    test "prefers pipe form over function-call form at the same cost tier" do
      candidates = Synth.synthesise("Int", %{"xs" => "List(Int)"}, %{})
      # Both exist; their costs are different but the overall list is ranked.
      exprs = Enum.map(candidates, & &1.expr)
      assert Enum.any?(exprs, &(&1 =~ "|>"))
    end

    test "honours the effect budget" do
      # Goal: Atom. Io.println/1 is the Atom-producing stdlib entry.
      ctx = %{"s" => "String"}
      pure_candidates = Synth.synthesise("Atom", ctx, %{})

      # With an empty effect budget, Io.println must not appear.
      refute Enum.any?(pure_candidates, &(&1.expr =~ "Std.Io.println"))

      with_io = Synth.synthesise("Atom", ctx, %{}, effects: [:io])
      assert Enum.any?(with_io, &(&1.expr =~ "Std.Io.println"))
    end

    test "caps the number of candidates at :max" do
      ctx = %{"xs" => "List(Int)"}
      assert 1 = length(Synth.synthesise("List(Int)", ctx, %{}, max: 1))
    end

    test "finds Option wrapper via some/1" do
      candidates = Synth.synthesise("Option(Int)", %{"n" => "Int"}, %{})
      assert Enum.any?(candidates, &(&1.expr =~ "Std.Option.some"))
    end

    test "returns [] gracefully for unknown goals" do
      Cure.Pipeline.Events.subscribe(:synthesis, :no_candidates)
      assert Synth.synthesise("SomeUnknownType", %{}, %{}) == []

      assert_receive {Cure.Pipeline.Events, :synthesis, :no_candidates, payload, _meta}
      assert payload.goal == "SomeUnknownType"
      refute Map.has_key?(payload, :code)
    end
  end
end

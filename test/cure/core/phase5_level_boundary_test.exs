defmodule Cure.Core.Phase5LevelBoundaryTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Sort, UniverseLevel, Validator}

  test "default and release boundaries reject integer sorts recursively" do
    legacy = {:type, 0}

    for config <- [Validator.wave0_config(), Validator.release_config()],
        term <- [
          legacy,
          {:pi, :erased, legacy, {:level_type}},
          {:case, {:var, 0}, {:level_type}, [{:C, 2, legacy}]},
          {:future_wrapper, [[legacy]]}
        ] do
      assert {:error, diagnostics} = Validator.validate(term, config)
      assert Enum.any?(diagnostics, &(&1.clause == :level_expr and &1.node == legacy))
    end
  end

  test "canonical finite, open and limit payloads pass the structural boundary" do
    for term <- [
          {:type, Sort.finite_zero()},
          {:type, Sort.finite_closed(37)},
          {:type, Sort.finite(UniverseLevel.atom({:var, 0}))},
          {:type, Sort.omega(37)},
          {:level_value, UniverseLevel.closed(37)}
        ] do
      assert {:ok, []} = Validator.validate(term)
      assert {:ok, []} = Validator.validate(term, Validator.release_config())
    end
  end
end

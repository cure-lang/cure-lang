defmodule Cure.Compiler.MacroUnitsCheckTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, MacroCheck, MacroUnits}
  alias Cure.Diagnostic.Renderer

  test "registers units and elaborates scaled literals" do
    assert {:ok, registry} = MacroUnits.register(%{}, "ms", 1, :duration)
    assert {:ok, registry} = MacroUnits.register(registry, "s", 1_000, :duration)
    assert {:ok, %{scaled: 2_000, unit: %{dimension: :duration}}} = MacroUnits.literal(registry, 2, "s")
    assert {:error, {:unknown_unit, "min"}} = MacroUnits.literal(registry, 1, "min")
  end

  test "malformed registry entries are rejected instead of raising" do
    assert {:error, {:invalid_unit, "ms"}} =
             MacroUnits.literal(%{"ms" => %{scale: :fast, dimension: :duration}}, 1, "ms")
  end

  test "every unit validation branch has stable user-facing output" do
    cases = [
      {fn -> MacroUnits.register(%{"ms" => %{scale: 1, dimension: :duration}}, "ms", 1, :duration) end,
       """
       -- UNIT SUFFIX IS ALREADY DECLARED [E092] --------------------------------------

       The `ms` suffix is registered more than once, so a literal would have two
       possible scales.

       Hint: Keep exactly one declaration for the `ms` suffix
       """},
      {fn -> MacroUnits.register(%{}, "ms", 0, :duration) end,
       """
       -- UNIT DECLARATION IS INVALID [E092] ------------------------------------------

       The `ms` unit needs a text suffix, a positive numeric scale, and an atom naming
       its dimension.

       Hint: Use a positive scale and a stable dimension such as `duration`
       """},
      {fn -> MacroUnits.literal(%{}, 1, "min") end,
       """
       -- UNIT SUFFIX IS UNKNOWN [E092] -----------------------------------------------

       The `min` suffix is used by this literal, but no unit with that suffix is
       registered.

       Hint: Register `min` before using it in a literal
       """},
      {fn -> MacroUnits.literal(%{}, :one, "ms") end,
       """
       -- UNIT LITERAL IS MALFORMED [E092] --------------------------------------------

       A unit literal needs a numeric value and a text suffix, but this one uses value
       `one` and suffix `ms`.

       Hint: Use a number followed by a registered text suffix
       """}
    ]

    Enum.each(cases, fn {run, expected} ->
      assert {:error, reason} = run.()
      {diagnostic, registry} = Errors.to_diagnostic(reason, "units.cure", "")

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_unit_validation
      assert Renderer.plain(diagnostic, registry, width: 80) == String.trim_trailing(expected)

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["relatedInformation"] == []
    end)
  end

  test "property plans are named, typed, and duplicate-free" do
    properties = [%{name: :round_trip, kind: :round_trip, expression: {:call, :round_trip}}]
    assert {:ok, %{kind: :quoted_check_plan, properties: ^properties}} = MacroCheck.plan(:Frame, properties)

    duplicate = properties ++ [%{name: :round_trip, kind: :total, expression: {:call, :total}}]
    assert {:error, :duplicate_check_property} = MacroCheck.plan(:Frame, duplicate)
  end

  test "malformed check plans are rejected instead of raising" do
    assert {:error, {:invalid_check_name, 42}} = MacroCheck.plan(42, [])
    assert {:error, :invalid_check_property} = MacroCheck.plan(:Frame, :not_a_property_list)
  end

  test "every check-plan validation branch has stable user-facing output" do
    valid = %{name: :round_trip, kind: :round_trip, expression: {:call, :round_trip}}

    cases = [
      {fn -> MacroCheck.plan(42, []) end,
       """
       -- CHECK PLAN NAME IS INVALID [E092] -------------------------------------------

       A generated check plan needs an atom or text name, but this plan uses `42`.

       Hint: Use a stable name such as `FrameProperties`
       """},
      {fn -> MacroCheck.plan(:Frame, [%{name: :broken, kind: :mystery}]) end,
       """
       -- CHECK PROPERTY IS MALFORMED [E092] ------------------------------------------

       Every check property needs a name, a supported check kind, and the expression to
       test.

       Hint: Provide `name`, `kind`, and `expression`; use `round_trip`, `total`, `fault_rejection`, `exhaustive`, or `termination`
       """},
      {fn -> MacroCheck.plan(:Frame, [valid, valid]) end,
       """
       -- CHECK PROPERTY NAME IS REPEATED [E092] --------------------------------------

       Two properties in this check plan have the same name, so their generated results
       cannot be distinguished.

       Hint: Give every property in the check plan a unique name
       """}
    ]

    Enum.each(cases, fn {run, expected} ->
      assert {:error, reason} = run.()
      {diagnostic, registry} = Errors.to_diagnostic(reason, "checks.cure", "")

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_check_validation
      assert Renderer.plain(diagnostic, registry, width: 80) == String.trim_trailing(expected)

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["relatedInformation"] == []
    end)
  end
end

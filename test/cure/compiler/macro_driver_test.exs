defmodule Cure.Compiler.MacroDriverTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, MacroDriver}
  alias Cure.Diagnostic.Renderer

  @registers [
    %{name: :status, offset: 0, width: 8, access: :read},
    %{name: :control, offset: 2, width: 16, access: :read_write}
  ]

  test "builds a pure register-map declaration" do
    assert {:ok, driver} = MacroDriver.build(:Sensor, @registers, base: 0x4000)
    registers = @registers
    assert driver.kind == :quoted_driver
    assert driver.base == 0x4000
    assert {:driver_def, [name: :Sensor], ^registers} = hd(driver.declarations)
  end

  test "rejects duplicate and overlapping register ranges" do
    duplicate = [
      %{name: :status, offset: 0, width: 8, access: :read},
      %{name: :status, offset: 2, width: 8, access: :write}
    ]

    assert {:error, :duplicate_driver_register} = MacroDriver.build(:Sensor, duplicate)

    overlap = [%{name: :a, offset: 0, width: 16, access: :read}, %{name: :b, offset: 1, width: 8, access: :read}]
    assert {:error, :overlapping_driver_register} = MacroDriver.build(:Sensor, overlap)

    same_offset = [
      %{name: :a, offset: 0, width: 8, access: :read},
      %{name: :b, offset: 0, width: 8, access: :write}
    ]

    assert {:error, :overlapping_driver_register} = MacroDriver.build(:Sensor, same_offset)
  end

  test "malformed host data is rejected instead of raising" do
    assert {:error, :invalid_driver_register} = MacroDriver.build(:Sensor, [42])
  end

  test "every driver validation branch has stable user-facing output" do
    duplicate = [
      %{name: :x, offset: 0, width: 8, access: :read},
      %{name: :x, offset: 2, width: 8, access: :write}
    ]

    overlap = [
      %{name: :a, offset: 0, width: 8, access: :read},
      %{name: :b, offset: 0, width: 8, access: :write}
    ]

    cases = [
      {fn -> MacroDriver.build(:Sensor, [], base: -1) end,
       """
       -- DRIVER BASE ADDRESS IS INVALID [E092] ---------------------------------------

       A driver base address must be a non-negative integer, but this definition uses
       `-1`.

       Hint: Use the non-negative byte address where this device's register block begins
       """},
      {fn -> MacroDriver.build(:Sensor, [42]) end,
       """
       -- DRIVER REGISTER IS MALFORMED [E092] -----------------------------------------

       Every register needs a name, a non-negative byte offset, an 8-, 16-, or 32-bit
       width, and `read`, `write`, or `read_write` access.

       Hint: Provide `name`, `offset`, `width`, and `access` for every register
       """},
      {fn -> MacroDriver.build(:Sensor, duplicate) end,
       """
       -- DRIVER REGISTER NAME IS REPEATED [E092] -------------------------------------

       Two registers have the same name, so generated accessors would collide.

       Hint: Give every register a unique name
       """},
      {fn -> MacroDriver.build(:Sensor, overlap) end,
       """
       -- DRIVER REGISTER RANGES OVERLAP [E092] ---------------------------------------

       Two registers occupy at least one of the same bytes in the device register map.

       Hint: Choose offsets and widths whose byte ranges do not overlap
       """}
    ]

    Enum.each(cases, fn {run, expected} ->
      assert {:error, reason} = run.()
      {diagnostic, registry} = Errors.to_diagnostic(reason, "driver.cure", "")

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_driver_validation
      assert Renderer.plain(diagnostic, registry, width: 80) == String.trim_trailing(expected)

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["relatedInformation"] == []
    end)
  end
end

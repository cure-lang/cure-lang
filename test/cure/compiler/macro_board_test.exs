defmodule Cure.Compiler.MacroBoardTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, MacroBoard}
  alias Cure.Diagnostic.Renderer

  @definition %{
    chip: :esp32c3,
    pins: {0, 21},
    capabilities: %{8 => [:input, :output], 9 => [:input, :output, :strapping]},
    buses: %{i2c0: %{sda: 8, scl: 9}},
    flash: %{size: 4_000_000, app_offset: 2_400_000, libs_offset: 1_900_000}
  }

  test "builds a board manifest with checked pins, buses, and flash map" do
    assert {:ok, board} = MacroBoard.build(:Esp32c3, @definition)
    assert board.kind == :quoted_board
    assert MapSet.member?(board.pins, 21)
    assert board.buses.i2c0.sda == 8
  end

  test "rejects unknown pins, missing bus capability declarations, and bad flash bounds" do
    assert {:error, {:unknown_board_pin, 22}} =
             MacroBoard.build(:Esp32c3, put_in(@definition.capabilities[22], [:input]))

    bad_bus = put_in(@definition.buses.i2c0.sda, 7)
    assert {:error, {:missing_bus_capability, :i2c0}} = MacroBoard.build(:Esp32c3, bad_bus)

    bad_flash = put_in(@definition.flash.app_offset, 4_000_000)
    assert {:error, :flash_offset_out_of_bounds} = MacroBoard.build(:Esp32c3, bad_flash)
  end

  test "missing and malformed top-level board data returns diagnostics instead of raising" do
    assert {:error, :invalid_board_definition} = MacroBoard.build(:Esp32c3, 42)
    assert {:error, :missing_board_chip} = MacroBoard.build(:Esp32c3, Map.delete(@definition, :chip))
    assert {:error, {:invalid_board_chip, 42}} = MacroBoard.build(:Esp32c3, %{@definition | chip: 42})
  end

  test "every board validation branch has stable user-facing output" do
    definition = @definition

    cases = [
      {fn -> MacroBoard.build(:Board, 42) end,
       """
       -- BOARD DEFINITION IS MALFORMED [E092] ----------------------------------------

       A board definition must be a map containing its chip, pins, capabilities, buses,
       and flash layout.

       Hint: Provide a board definition map with `chip`, `pins`, `capabilities`, `buses`, and `flash`
       """},
      {fn -> MacroBoard.build(42, definition) end,
       """
       -- BOARD NAME IS INVALID [E092] ------------------------------------------------

       A board name must be an atom or string, but this definition uses `42`.

       Hint: Use a stable board name such as `Esp32c3`
       """},
      {fn -> MacroBoard.build(:Board, Map.delete(definition, :chip)) end,
       """
       -- BOARD CHIP IS MISSING [E092] ------------------------------------------------

       The board definition does not identify the chip that owns its pins and
       peripherals.

       Hint: Add a `chip` entry such as `chip: :esp32c3`
       """},
      {fn -> MacroBoard.build(:Board, %{definition | chip: 42}) end,
       """
       -- BOARD CHIP IS INVALID [E092] ------------------------------------------------

       A chip identifier must be an atom or string, but this definition uses `42`.

       Hint: Use a stable chip identifier such as `esp32c3`
       """},
      {fn -> MacroBoard.build(:Board, %{definition | pins: [-1]}) end,
       """
       -- BOARD PIN SET IS INVALID [E092] ---------------------------------------------

       Pins must be a non-negative inclusive range or a list of non-negative pin
       numbers.

       Hint: Use `{first, last}` or a list such as `[0, 1, 2]`
       """},
      {fn -> MacroBoard.build(:Board, %{definition | pins: :all}) end,
       """
       -- BOARD PIN SET IS INVALID [E092] ---------------------------------------------

       Pins must be a non-negative inclusive range or a list of non-negative pin
       numbers.

       Hint: Use `{first, last}` or a list such as `[0, 1, 2]`
       """},
      {fn -> MacroBoard.build(:Board, put_in(definition.capabilities[22], [:input])) end,
       """
       -- CAPABILITY REFERS TO AN UNKNOWN BOARD PIN [E092] ----------------------------

       Pin `22` has capabilities here, but it is not present in the board's pin set.

       Hint: Add pin `22` to `pins`, or remove this capability entry
       """},
      {fn -> MacroBoard.build(:Board, put_in(definition.capabilities[8], [:bogus])) end,
       """
       -- BOARD PIN HAS AN INVALID CAPABILITY [E092] ----------------------------------

       Pin `8` has a capability outside the supported GPIO, analog, strapping, USB, and
       touch set.

       Hint: Use only `input`, `output`, `adc`, `dac`, `strapping`, `usb`, or `touch`
       """},
      {fn -> MacroBoard.build(:Board, %{definition | capabilities: []}) end,
       """
       -- BOARD CAPABILITIES ARE MALFORMED [E092] -------------------------------------

       Board capabilities must be a map from each pin number to a list of supported
       capabilities.

       Hint: Map each pin to its capabilities, for example pin `8` to `input` and `output`
       """},
      {fn -> MacroBoard.build(:Board, %{definition | buses: %{i2c0: 42}}) end,
       """
       -- BOARD BUS WIRING IS INVALID [E092] ------------------------------------------

       The `i2c0` bus needs an atom name and a map from signal names to pin numbers.

       Hint: Map each signal to its pin, for example `sda` to `8` and `scl` to `9`
       """},
      {fn -> MacroBoard.build(:Board, %{definition | buses: %{"i2c0" => %{sda: 8}}}) end,
       """
       -- BOARD BUS WIRING IS INVALID [E092] ------------------------------------------

       The `i2c0` bus needs an atom name and a map from signal names to pin numbers.

       Hint: Map each signal to its pin, for example `sda` to `8` and `scl` to `9`
       """},
      {fn -> MacroBoard.build(:Board, put_in(definition.buses.i2c0.sda, 99)) end,
       """
       -- BOARD BUS USES AN UNKNOWN PIN [E092] ----------------------------------------

       The `i2c0` bus assigns at least one pin that is not present in the board's pin
       set.

       Hint: Assign every `i2c0` signal to a pin declared by `pins`
       """},
      {fn -> MacroBoard.build(:Board, put_in(definition.buses.i2c0.sda, 7)) end,
       """
       -- BOARD BUS PIN HAS NO CAPABILITY DECLARATION [E092] --------------------------

       The `i2c0` bus uses a declared pin whose capabilities are missing, so generated
       peripheral checks cannot validate it.

       Hint: Add each `i2c0` pin to the `capabilities` map
       """},
      {fn -> MacroBoard.build(:Board, %{definition | buses: []}) end,
       """
       -- BOARD BUS TABLE IS MALFORMED [E092] -----------------------------------------

       Board buses must be a map from bus names to signal-to-pin wiring maps.

       Hint: Map each bus name to its signal-to-pin wiring
       """},
      {fn -> MacroBoard.build(:Board, %{definition | flash: %{size: 1}}) end,
       """
       -- BOARD FLASH LAYOUT IS MALFORMED [E092] --------------------------------------

       Flash layout needs a positive total size and non-negative application and
       library offsets.

       Hint: Provide integer `size`, `app_offset`, and `libs_offset` values
       """},
      {fn -> MacroBoard.build(:Board, put_in(definition.flash.app_offset, 4_000_000)) end,
       """
       -- BOARD FLASH OFFSET IS OUTSIDE THE DEVICE [E092] -----------------------------

       The application or library partition starts at or beyond the declared flash
       size.

       Hint: Choose `app_offset` and `libs_offset` values smaller than `size`
       """}
    ]

    Enum.each(cases, fn {run, expected} ->
      assert {:error, reason} = run.()
      {diagnostic, registry} = Errors.to_diagnostic(reason, "board.cure", "")

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_board_validation
      assert Renderer.plain(diagnostic, registry, width: 80) == String.trim_trailing(expected)

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["relatedInformation"] == []
    end)
  end
end

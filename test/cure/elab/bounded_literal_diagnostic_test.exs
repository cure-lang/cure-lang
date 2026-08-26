defmodule Cure.Elab.BoundedLiteralDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "an overflowing bounded literal labels the value and its declared bound" do
    source = "mod Bounds\n  use Std.Bounded\n  fn bad() -> Bounded(3) = 5\nend\n"
    {diagnostic, registry, error} = diagnostic(source, "bounds.cure")

    assert {:bounded_lit_out_of_range, 5, 3} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- 5 IS OUTSIDE `BOUNDED(3)` [E093] -------------------------------- bounds.cure

             `Bounded(3)` contains integer values from `0` through `2`, but this literal is
             `5`.

             at bounds.cure:3:28
             3 |   fn bad() -> Bounded(3) = 5
               |               ----------   ^ this annotation requires `Bounded(3)`; this value does not fit the declared bound

             Hint: Use an integer from 0 through 2
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(2, 27, 28)
    assert [related] = lsp["relatedInformation"]
    assert related["location"]["range"] == range(2, 14, 24)
    assert related["message"] == "this annotation requires `Bounded(3)`"

    assert lsp["data"]["payload"] == %{
             "bound" => 3,
             "kind" => "bounded_lit_out_of_range",
             "maximum" => 2,
             "minimum" => 0,
             "value" => 5
           }

    assert [%{"applicability" => "manual", "edits" => []}] = lsp["data"]["suggestions"]

    fixed = String.replace(source, "= 5", "= 2")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "bounds_fixed.cure")
  end

  test "an empty bounded interval does not claim that any value is legal" do
    source = "mod EmptyBounds\n  use Std.Bounded\n  fn bad() -> Bounded(0) = 0\nend\n"
    {diagnostic, registry, error} = diagnostic(source, "empty_bounds.cure")

    assert {:bounded_lit_out_of_range, 0, 0} = Program.semantic_error(error)

    rendered = Renderer.plain(diagnostic, registry, width: 80)
    assert rendered =~ "in an empty interval because its bound is\n`0`"
    assert rendered =~ "Hint: Use a positive bound before constructing this value"
    refute rendered =~ "through `-1`"

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["data"]["payload"]["maximum"] == nil

    fixed = String.replace(source, "Bounded(0)", "Bounded(1)")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "empty_bounds_fixed.cure")
  end

  defp diagnostic(source, file) do
    assert {:error, error} = Program.elaborate(source, file: file)
    {diagnostic, registry} = Errors.to_diagnostic(error, file, source)
    {diagnostic, registry, error}
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end

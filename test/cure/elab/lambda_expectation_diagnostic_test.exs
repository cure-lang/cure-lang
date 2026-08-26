defmodule Cure.Elab.LambdaExpectationDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a lambda passed to a value parameter labels the complete lambda and first parameter" do
    source =
      "mod M\n  fn consume(value: Bool) -> Bool = value\n  fn bad() -> Bool = consume(fn (x) -> x end)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "lambda_expected.cure")

    assert {:lambda_expected_pi, %{parameter_index: 0}} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- LAMBDA NEEDS A FUNCTION TYPE [E093] -------------------- lambda_expected.cure

             This lambda has parameter 1, but its surrounding context expects `Bool` at that
             point. An untyped lambda parameter can only be checked when the expected type
             provides a corresponding function input.

             at lambda_expected.cure:3:30
             3 |   fn bad() -> Bool = consume(fn (x) -> x end)
               |                              ^^^^^^^^^^^^^^^ this lambda is used where a non-function value is required
               |                                  - this parameter needs a function input type

             Hint: Pass this lambda to a function-valued parameter, or replace it with a `Bool` value
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(2, 29, 44)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(2, 33, 34)
           ]

    assert lsp["data"]["payload"] == %{
             "expected_surface" => "Bool",
             "kind" => "lambda_expected_pi",
             "parameter_index" => 0
           }
  end

  test "a lambda with too many parameters identifies the first unsupported parameter" do
    source =
      "mod M\n  fn consume(f: Int -> Bool) -> Bool = f(1)\n  fn bad() -> Bool = consume(fn (x, y) -> true end)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "lambda_arity.cure")

    assert {:lambda_expected_pi, %{parameter_index: 1, parameter_span: parameter_span}} =
             Program.semantic_error(error)

    assert parameter_span.start_column == 37
    assert diagnostic.title == "Lambda needs a function type"
    assert diagnostic.primary.span.start_column == 30
    assert hd(diagnostic.secondary).span == parameter_span
    assert Renderer.plain(diagnostic, registry, width: 80) =~ "This lambda has parameter 2"
    assert Renderer.lsp(diagnostic, registry)["range"] == range(2, 29, 50)
    refute inspect(diagnostic.payload) =~ "{:data"
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

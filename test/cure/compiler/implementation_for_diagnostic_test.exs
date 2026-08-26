defmodule Cure.Compiler.ImplementationForDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error =
      Enum.find(errors, &match?({:declaration_separator_missing, %{kind: :implementation_for_keyword_missing}}, &1))

    assert {:declaration_separator_missing, details} = error
    {diagnostic, registry} = Errors.to_diagnostic({:parse_error, [error]}, file, source)
    {details, diagnostic, registry}
  end

  test "an omitted `for` in a protocol implementation is inserted before the type" do
    source = "impl Std.Show Int\n  fn show(x: Int) -> String = \"x\"\n"
    {details, diagnostic, registry} = diagnostic(source, "impl_for.cure")

    assert %{
             family: :protocol,
             declaration: "Std.Show",
             repair: :insert,
             expected: :for,
             observed: "Int",
             token_type: :identifier,
             span: %Cure.Diagnostic.Span{},
             opener_span: %Cure.Diagnostic.Span{},
             previous_span: %Cure.Diagnostic.Span{}
           } = details

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- IMPLEMENTATION NEEDS `FOR` [E094] ----------------------------- impl_for.cure

             The implementation of `Std.Show` needs `for` between its interface or protocol
             and the type receiving the implementation.

             A valid continuation here starts with 'for'.

             at impl_for.cure:1:15
             1 | impl Std.Show Int
               | ---- -------- ^^^ this starts the implementation; the implemented interface or protocol ends here; insert `for` before this implementation type

             Hint: Insert `for` before the implementation type
             """)

    assert [%{"edits" => [edit], "applicability" => "machine_applicable"}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"]

    assert edit["newText"] == "for "

    assert edit["range"] == %{
             "start" => %{"line" => 0, "character" => 14},
             "end" => %{"line" => 0, "character" => 14}
           }
  end

  test "a wrong keyword in an interface implementation is replaced with `for`" do
    source = "implementation Eq when Int\n  fn eq(x: Int, y: Int) -> Bool = true\n"
    {details, diagnostic, registry} = diagnostic(source, "implementation_for.cure")

    assert %{
             family: :interface,
             declaration: "Eq",
             repair: :replace,
             expected: :for,
             observed: :when,
             token_type: :keyword,
             span: %Cure.Diagnostic.Span{},
             opener_span: %Cure.Diagnostic.Span{},
             previous_span: %Cure.Diagnostic.Span{}
           } = details

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- IMPLEMENTATION NEEDS `FOR` [E094] ------------------- implementation_for.cure

             The implementation of `Eq` needs `for` between its interface or protocol and the
             type receiving the implementation.

             A valid continuation here starts with 'for'.

             at implementation_for.cure:1:19
             1 | implementation Eq when Int
               | -------------- -- ^^^^ this starts the implementation; the implemented interface or protocol ends here; replace this with `for`

             Hint: Replace this keyword with `for`
             """)

    assert [%{"edits" => [edit], "applicability" => "machine_applicable"}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"]

    assert edit["newText"] == "for"

    assert edit["range"] == %{
             "start" => %{"line" => 0, "character" => 18},
             "end" => %{"line" => 0, "character" => 22}
           }
  end

  test "both implementation grammars use both contextual repair branches" do
    cases = [
      {"impl P when Int\n", :protocol, :replace},
      {"implementation P Int\n", :interface, :insert}
    ]

    for {source, family, repair} <- cases do
      {details, _diagnostic, _registry} = diagnostic(source, "matrix.cure")
      assert details.family == family
      assert details.repair == repair
    end
  end
end

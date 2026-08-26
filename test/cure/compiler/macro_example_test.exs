# test/cure/compiler/macro_example_test.exs
defmodule Cure.Compiler.MacroExampleTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp syntax_rule({:macro_def, _, rules}), do: Enum.find(rules, &(&1[:kind] == :syntax))
  defp syntax_rule({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &syntax_rule/1)
  defp syntax_rule(_), do: nil

  test "an example expands sub-block attaches to its syntax rule" do
    node =
      parse!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(500)\n"
      )

    rule = syntax_rule(node)
    assert [ex] = rule.examples
    # use_site captured as raw tokens: every 500
    assert Enum.map(ex.use_site, & &1.value) == ["every", 500]
    # expected expansion captured as AST
    assert {:expansion, {:function_call, _, _}} = ex.expected
  end

  test "a type-only example pin (`expands : Type`) is captured as {:type, _}" do
    node =
      parse!("macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands : Int\n")

    rule = syntax_rule(node)
    assert [%{expected: {:type, _}}] = rule.examples
  end

  test "a syntax rule with no example has an empty examples list (non-breaking)" do
    node = parse!("macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n")
    assert syntax_rule(node).examples == []
  end

  test "an invalid nested example line reports the owning syntax rule and exact source" do
    source = "macro Now\n  syntax now becomes 1\n    oops\n"

    {:ok, tokens} = Lexer.tokenize(source, file: "example.cure", emit_events: false)
    assert {:error, [error]} = Parser.parse(tokens, emit_events: false)

    assert {:macro_nested_syntax,
            %{
              kind: :macro_example_entry_invalid,
              expected: :example,
              observed: "oops",
              token_type: :identifier,
              span: %Cure.Diagnostic.Span{} = span,
              opener_span: %Cure.Diagnostic.Span{},
              previous_span: %Cure.Diagnostic.Span{},
              line: 3,
              column: 5
            }} = error

    assert span.start_column == 5
    assert span.end_column == 9

    {diagnostic, registry} = Errors.to_diagnostic({:parse_error, [error]}, "example.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO EXAMPLE ENTRY IS INVALID [E094] -------------------------- example.cure

             'oops' cannot start a pinned macro example. Each line in this nested block must
             use `example use_site expands expected`.

             A valid continuation here starts with 'example'.

             at example.cure:3:5
             2 |   syntax now becomes 1
               |   ------ this syntax rule owns the example block
             3 |     oops
               |     ^^^^ start this line with `example`

             Hint: Write `example use_site expands expected` on this line
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 2, "character" => 4},
             "end" => %{"line" => 2, "character" => 8}
           }
  end

  alias Cure.Compiler.MacroValidate

  defp macro_def!(src) do
    node = parse!(src)

    find = fn find, n ->
      case n do
        {:macro_def, _, _} = m -> m
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end

    find.(find, node)
  end

  test "a syntax rule with no example is rule_unpinned" do
    md = macro_def!("macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n")
    assert {:error, {:rule_unpinned, ["every"]}} = MacroValidate.check_rules_pinned(md)

    rendered = Errors.format_error({:rule_unpinned, ["every"]}, "m.cure")
    assert rendered =~ "every"
    assert rendered =~ "example"
    refute rendered =~ ":rule_unpinned"
  end

  test "a syntax rule WITH an example checks clean" do
    md =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(500)\n"
      )

    assert :ok = MacroValidate.check_rules_pinned(md)
  end

  test "only unpinned syntax rules are reported (mixed macro)" do
    md =
      macro_def!("macro M\n  syntax a becomes X\n    example a expands X\n  syntax b becomes Y\n")

    assert {:error, {:rule_unpinned, ["b"]}} = MacroValidate.check_rules_pinned(md)
  end

  test "the program validation path labels every unpinned authored rule" do
    source =
      "macro M\n  syntax a becomes X\n  syntax b becomes Y\n  explain\n    keyword \"a\" => \"a\"\n    keyword \"b\" => \"b\"\n"

    {:ok, tokens} = Lexer.tokenize(source, file: "unpinned.cure", emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)

    assert {:error, {:source_context, {:rule_unpinned, ["a", "b"]}, context} = reason} =
             MacroValidate.check_program(ast, Cure.Core.Env.empty())

    assert %{span: %Cure.Diagnostic.Span{}, rule_spans: [%Cure.Diagnostic.Span{}, %Cure.Diagnostic.Span{}]} =
             context

    {diagnostic, registry} = Errors.to_diagnostic(reason, "unpinned.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO RULE NEEDS A WORKED EXAMPLE [E092] ---------------------- unpinned.cure

             These macro rules have no worked example: a, b.

             at unpinned.cure:2:3
             2 |   syntax a becomes X
               |   ^^^^^^^^^^^^^^^^^^ add a worked example beneath this rule
             3 |   syntax b becomes Y
               |   ------------------ this rule also needs a worked example

             Hint: Add `example use_site expands expected` beneath each listed rule
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 1, "character" => 2},
             "end" => %{"line" => 1, "character" => 20}
           }

    assert length(lsp["relatedInformation"]) == 1
  end

  test "an unpinned computed rule is also rule_unpinned" do
    md = macro_def!("macro Mk\n  syntax mk computed by build_it\n")
    assert {:error, {:rule_unpinned, ["mk"]}} = MacroValidate.check_rules_pinned(md)
  end
end

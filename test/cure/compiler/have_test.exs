defmodule Cure.Compiler.HaveTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Formatter, Lexer, MacroSyntax, Parser, Printer}
  alias Cure.MetaAST.Metadata
  alias Cure.MetaAST.{Metadata, SourceInfo}

  defp parse!(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: "have.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "have.cure", emit_events: false)
    ast
  end

  test "have is contextual and remains an ordinary identifier" do
    assert {:ok, [token | _]} = Lexer.tokenize("have", emit_events: false)
    assert token.type == :identifier
    assert :have in Lexer.contextual_keywords()

    assert {:function_def, meta, [{:variable, _, "have"}]} =
             parse!("fn keep(have: Int) -> Int = have\n")

    assert [{:param, _, "have"}] = meta[:params]
  end

  test "inferred and annotated have facts use the existing assignment shape" do
    {:function_def, _, [{:block, _, [inferred, annotated, {:variable, _, "second"}]}]} =
      parse!("fn f() -> Int =\n  have first = 1\n  have second: Int = first\n  second\n")

    assert {:assignment, inferred_meta, [{:variable, _, "first"}, {:literal, _, 1}]} = inferred
    assert inferred_meta[:let] and inferred_meta[:have]
    refute Keyword.has_key?(inferred_meta, :type_annotation)

    assert {:assignment, annotated_meta, [{:variable, _, "second"}, {:variable, _, "first"}]} = annotated
    assert annotated_meta[:let] and annotated_meta[:have]
    assert {:variable, _, "Int"} = annotated_meta[:type_annotation]

    assert %SourceInfo{name: name, annotation: annotation, body: body, whole: whole} =
             Metadata.source_info(annotated_meta)

    assert name && annotation && body && whole
  end

  test "malformed local facts are rejected by the binding grammar" do
    for source <- [
          "fn f() -> Int =\n  have fact: = 1\n  1\n",
          "fn f() -> Int =\n  have fact Int = 1\n  1\n"
        ] do
      assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      assert {:error, errors} = Parser.parse(tokens, emit_events: false)
      assert errors != []
    end
  end

  test "nested facts shadow normally and canonical printing round-trips" do
    source = "fn f() -> Int =\n  have fact = 1\n  have fact: Int = 2\n  fact\n"
    ast = parse!(source)
    printed = Printer.quoted_to_string(ast)

    assert printed =~ "have fact = 1"
    assert printed =~ "have fact: Int = 2"
    assert Printer.quoted_to_string(parse!(printed)) == printed
  end

  test "formatter preserves canonical have and is idempotent" do
    source = "fn f() -> Int =\n  have fact: Int = 1\n  fact\n"
    assert {:ok, once} = Formatter.format(source)
    assert once =~ "have fact: Int = 1"
    assert {:ok, ^once} = Formatter.format(once)
  end

  test "the have marker survives syntax reflection" do
    {:function_def, _, [{:block, _, [assignment, _]}]} =
      parse!("fn f() -> Int =\n  have fact = 1\n  fact\n")

    {:assignment, meta, _} =
      assignment |> MacroSyntax.to_syntax() |> MacroSyntax.from_syntax()

    assert meta[:let] and meta[:have]
  end

  test "macro expansion preserves have and hygienically freshens its binder" do
    ast =
      parse!(
        "mod M\n  macro Fact\n    syntax fact becomes have evidence = 1 in evidence\n  fn f(evidence: Int) -> Int = fact\n"
      )
      |> Metadata.strip_diagnostics()

    {:container, _, children} = ast

    function =
      Enum.find(children, fn
        {:function_def, meta, _} -> to_string(meta[:name]) == "f"
        _ -> false
      end)

    {:function_def, _, [{:block, _, [{:assignment, meta, [{:variable, _, binder}, _]}, {:variable, _, use}]}]} =
      function

    assert meta[:have]
    assert binder == use
    refute binder == "evidence"
  end
end

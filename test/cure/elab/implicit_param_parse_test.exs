defmodule Cure.Elab.ImplicitParamParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    ast
  end

  test "parses brace-implicit parameters alongside explicit ones" do
    src = "fn compose({as}, {d1}, l: SF(as, d1)) -> SF(as, d1) = l\n"
    assert {:function_def, meta, _body} = parse(src)

    assert [{:param, m1, "as"}, {:param, m2, "d1"}, {:param, m3, "l"}] =
             Keyword.get(meta, :params)

    assert Keyword.get(m1, :implicit) == true
    assert Keyword.get(m2, :implicit) == true
    assert Keyword.get(m3, :implicit) != true
    assert {:function_call, meta, _} = Keyword.get(m3, :type)
    assert Keyword.get(meta, :name) == "SF"
  end

  test "parses an implicit parameter with an explicit type annotation" do
    src = "fn f({as: SVDesc}, x: SF(as)) -> SF(as) = x\n"
    assert {:function_def, meta, _body} = parse(src)
    assert [{:param, m1, "as"}, {:param, _m2, "x"}] = Keyword.get(meta, :params)
    assert Keyword.get(m1, :implicit) == true
    assert {:variable, _, "SVDesc"} = Keyword.get(m1, :type)
  end
end

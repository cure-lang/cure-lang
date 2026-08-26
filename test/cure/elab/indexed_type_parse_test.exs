defmodule Cure.Elab.IndexedTypeParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.MetaAST.Metadata

  defp parse(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Metadata.strip_diagnostics(ast)
  end

  test "parses an indexed type declaration with constructor signatures" do
    src = """
    type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
      prim : SF(as, bs, Causal)
      seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, and(d1, d2))
    """

    assert {:indexed_type, meta, ctors} = parse(src)
    assert Keyword.get(meta, :name) == "SF"
    # SF is parameter-free: all three appear in the `indices` clause.
    assert Keyword.get(meta, :params) == []
    assert length(Keyword.get(meta, :indices)) == 3
    assert [{:gadt_ctor, m1, t1}, {:gadt_ctor, m2, t2}] = ctors
    assert Keyword.get(m1, :name) == "prim"
    assert Keyword.get(m2, :name) == "seq"

    # prim: a single-element chain; the SF head is preserved (not mangled).
    assert [{:arrow_chain, _chain_meta, [{:function_call, [name: "SF"], _}]}] = t1

    # seq: two domains + a result, every SF application head intact, and the
    # computed result index `and(d1, d2)` preserved as a nested application.
    assert [{:arrow_chain, _chain_meta, [dom1, dom2, result]}] = t2
    assert {:function_call, [name: "SF"], _} = dom1
    assert {:function_call, [name: "SF"], _} = dom2
    assert {:function_call, [name: "SF"], [_, _, {:function_call, [name: "and"], [_, _]}]} = result
  end
end

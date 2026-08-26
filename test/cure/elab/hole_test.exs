defmodule Cure.Elab.HoleTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.Env
  alias Cure.Elab.Declarations

  @base """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  fn andd(x: Dec, y: Dec) -> Dec = x
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  """

  defp elaborate_all(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)

    items =
      case ast do
        {:block, _, xs} -> xs
        x -> [x]
      end

    Enum.reduce_while(items, {:ok, Env.empty()}, fn decl, {:ok, env} ->
      case Declarations.elaborate(decl, env) do
        {:ok, env2} -> {:cont, {:ok, env2}}
        err -> {:halt, err}
      end
    end)
  end

  defp unwrap_lams({:lam, _g, _dom, body}), do: unwrap_lams(body)
  defp unwrap_lams(term), do: term

  test "the lexer/parser turn ?body into a hole node" do
    {:ok, toks} = Lexer.tokenize("fn f() -> Int = ?body\n", emit_events: false)
    {:ok, {:function_def, _meta, [hole]}} = Parser.parse(toks, emit_events: false)
    assert {:hole, meta, []} = hole
    assert Keyword.get(meta, :name) == "body"
  end

  test "sketch typechecks with a hole and records it in the body" do
    src =
      @base <>
        "fn sketch({as: SVDesc}, {bs: SVDesc}, {cs: SVDesc}, {d1: Dec}, {d2: Dec}, l: SF(as, bs, d1), r: SF(bs, cs, d2)) -> SF(as, cs, andd(d1, d2)) = ?body\n"

    assert {:ok, env} = elaborate_all(src)
    assert %{name: :sketch, body: body} = Env.get_def(env, :sketch)
    # The hole survives to the Core body (so codegen can refuse to emit it),
    # carrying a unique id derived from its `?body` name (first-class holes).
    assert {:hole, id} = unwrap_lams(body)
    assert String.contains?(id, "body")
  end
end

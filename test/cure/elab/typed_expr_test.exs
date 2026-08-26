defmodule Cure.Elab.TypedExprTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.{Context, Env, Eval}
  alias Cure.Elab.{Declarations, Elaborator}

  @src """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  fn andd(x: Dec, y: Dec) -> Dec = x
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  """

  defp build_env do
    {:ok, toks} = Lexer.tokenize(@src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)

    items =
      case ast do
        {:block, _, xs} -> xs
        x -> [x]
      end

    Enum.reduce(items, Env.empty(), fn decl, e ->
      {:ok, e2} = Declarations.elaborate(decl, e)
      e2
    end)
  end

  defp sf(a, b, d),
    do: Eval.eval({:data, :SF, [], [{:ctor, a, []}, {:ctor, b, []}, {:ctor, d, []}]}, [])

  test "elaborates a bare variable to its de Bruijn index and context type" do
    env = build_env()
    ctx = Context.empty(env) |> Context.extend(sf(:SVNil, :SVNil, :Causal))

    assert {:ok, {:var, 0}, {:vdata, :SF, _}} =
             Elaborator.elaborate_expr_typed({:variable, [], "x"}, ["x"], ctx, env)
  end

  test "elaborates seq(l, r) in a typing context, inferring erased indices" do
    env = build_env()

    ctx =
      Context.empty(env)
      |> Context.extend(sf(:SVNil, :SVNil, :Causal))
      |> Context.extend(sf(:SVNil, :SVNil, :Causal))

    names = ["r", "l"]

    expr =
      {:function_call, [name: "seq"], [{:variable, [], "l"}, {:variable, [], "r"}]}

    assert {:ok, {:ctor, :seq, args}, {:vdata, :SF, [_, _, _]}} =
             Elaborator.elaborate_expr_typed(expr, names, ctx, env)

    assert length(args) == 7

    assert Enum.take(args, 5) == [
             {:ctor, :SVNil, []},
             {:ctor, :SVNil, []},
             {:ctor, :Causal, []},
             {:ctor, :SVNil, []},
             {:ctor, :Causal, []}
           ]

    assert Enum.drop(args, 5) == [{:var, 1}, {:var, 0}]
  end
end

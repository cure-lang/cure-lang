defmodule Cure.Elab.IndexedDeclarationsTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.Declarations

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

  @src """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  fn andd(x: Dec, y: Dec) -> Dec = x
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  """

  test "elaborates the SF GADT to a kernel-accepted indexed family" do
    assert {:ok, env} = elaborate_all(@src)
    assert Inductive.family?(env, :SF)
    assert length(Inductive.index_telescope(env, :SF)) == 3
    assert Inductive.ctor_family(env, :seq) == :SF
    assert Inductive.ctor_family(env, :prim) == :SF
  end

  test "seq infers 5 implicit index vars + 2 explicit args, with computed result index" do
    {:ok, env} = elaborate_all(@src)
    assert length(Inductive.arg_telescope(env, :seq)) == 7

    assert [_as, _cs, and_index] = Inductive.ctor_result_indices(env, :seq)
    assert {:app, {:app, {:global, :andd}, {:var, _}}, {:var, _}} = and_index
  end

  test "prim has only the two implicit index vars and a Causal result index" do
    {:ok, env} = elaborate_all(@src)
    assert length(Inductive.arg_telescope(env, :prim)) == 2
    assert [_as, _bs, {:ctor, :Causal, []}] = Inductive.ctor_result_indices(env, :prim)
  end
end

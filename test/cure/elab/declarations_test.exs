defmodule Cure.Elab.DeclarationsTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.Declarations

  defp decls(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)

    case ast do
      {:block, _, items} -> items
      single -> [single]
    end
  end

  defp elaborate_all(src) do
    Enum.reduce_while(decls(src), {:ok, Env.empty()}, fn decl, {:ok, env} ->
      case Declarations.elaborate(decl, env) do
        {:ok, env2} -> {:cont, {:ok, env2}}
        err -> {:halt, err}
      end
    end)
  end

  test "elaborates a nullary ADT to a Core family at level 0" do
    assert {:ok, env} = elaborate_all("type Dec = Dcoupled | Causal\n")
    assert Inductive.family?(env, :Dec)
    assert Inductive.get_family(env, :Dec).level == 0
    assert Inductive.ctor_family(env, :Causal) == :Dec
    assert Inductive.ctor_family(env, :Dcoupled) == :Dec
  end

  test "a constructor field of type Type forces the family to level 1" do
    assert {:ok, env} = elaborate_all("type Sig = C(Type) | E(Type)\n")
    assert Inductive.get_family(env, :Sig).level == 1
  end

  test "elaborates a recursive ADT (SVDesc) and accepts it (strictly positive)" do
    src = "type Sig = C(Type) | E(Type)\ntype SVDesc = SVNil | SVCons(Sig, SVDesc)\n"
    assert {:ok, env} = elaborate_all(src)
    assert Inductive.family?(env, :SVDesc)
    assert length(Inductive.arg_telescope(env, :SVCons)) == 2
  end
end

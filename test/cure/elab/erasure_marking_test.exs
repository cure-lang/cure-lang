defmodule Cure.Elab.ErasureMarkingTest do
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

  test "GADT implicit index args are erased (0), explicit args present (ω)" do
    {:ok, env} = elaborate_all(@src)

    assert Inductive.ctor_quantities(env, :seq) ==
             [:erased, :erased, :erased, :erased, :erased, :unrestricted, :unrestricted]

    assert Inductive.ctor_quantities(env, :prim) == [:erased, :erased]
  end

  test "plain ADT constructor fields are all runtime-relevant (present)" do
    {:ok, env} = elaborate_all(@src)
    assert Inductive.ctor_quantities(env, :SVCons) == [:unrestricted, :unrestricted]
    assert Inductive.ctor_quantities(env, :SVNil) == []
  end

  test "the count of erased args equals the inferred implicit-index arity" do
    {:ok, env} = elaborate_all(@src)
    erased = env |> Inductive.ctor_quantities(:seq) |> Enum.count(&(&1 == :erased))
    present = env |> Inductive.ctor_quantities(:seq) |> Enum.count(&(&1 == :unrestricted))
    assert erased == 5
    assert present == 2
  end

  test "named GADT fields preserve explicit source grades" do
    src = """
    type Tag = Only
    type Witness indices (x: Tag)
      WitnessOnly : Witness(Only())
    type Box indices (x: Tag)
      Boxed : (@erased proof : Witness(x)) -> (value: Tag) -> Box(x)
    fn consume(@erased proof : Witness(Only()), value: Tag) -> Tag = value
    fn run() -> Tag = consume(WitnessOnly(), Only())
    """

    {:ok, env} = elaborate_all(src)
    assert Inductive.ctor_quantities(env, :Boxed) == [:erased, :erased, :unrestricted]
    assert Env.get_def(env, :consume).plicities == [:explicit, :explicit]
  end
end

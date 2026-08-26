defmodule Cure.Elab.CtorAppTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.Env
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

  # Type as a (closed) Core term, as the caller passes it.
  defp sf_term(a, b, d) do
    {:data, :SF, [], [{:ctor, a, []}, {:ctor, b, []}, {:ctor, d, []}]}
  end

  test "seq(l, r) infers the five erased index arguments from l and r's types" do
    env = build_env()
    lspec = {{:global, :l}, sf_term(:SVNil, :SVNil, :Causal)}
    rspec = {{:global, :r}, sf_term(:SVNil, :SVNil, :Causal)}

    assert {:ok, {:ctor, :seq, args}, result_type} =
             Elaborator.elaborate_ctor_app(env, :seq, [lspec, rspec])

    assert length(args) == 7

    assert Enum.take(args, 5) ==
             [
               {:ctor, :SVNil, []},
               {:ctor, :SVNil, []},
               {:ctor, :Causal, []},
               {:ctor, :SVNil, []},
               {:ctor, :Causal, []}
             ]

    assert Enum.drop(args, 5) == [{:global, :l}, {:global, :r}]
    assert {:vdata, :SF, [_as, _cs, _and]} = result_type
  end

  test "rejects seq(l, r) when the middle indices disagree (bs ≠ bs')" do
    env = build_env()
    # l : SF(SVNil, SVNil, Causal); r : SF(SVCons(..), SVNil, Causal)
    # l's bs (SVNil) must equal r's first index (SVCons ..) — it does not.
    r_bs =
      {:data, :SF, [],
       [
         {:ctor, :SVCons, [{:ctor, :CSig, []}, {:ctor, :SVNil, []}]},
         {:ctor, :SVNil, []},
         {:ctor, :Causal, []}
       ]}

    lspec = {{:global, :l}, sf_term(:SVNil, :SVNil, :Causal)}
    rspec = {{:global, :r}, r_bs}

    assert {:error, _} = Elaborator.elaborate_ctor_app(env, :seq, [lspec, rspec])
  end

  test "prim() with no explicit args leaves both erased indices unsolved" do
    env = build_env()
    # prim has only erased args and no present args to infer from → unsolved metas
    assert {:error, {:unsolved_metavariables, :prim}} =
             Elaborator.elaborate_ctor_app(env, :prim, [])
  end
end

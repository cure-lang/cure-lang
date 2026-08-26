defmodule Cure.Elab.ComposeTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.Env
  alias Cure.Elab.Declarations

  @src """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  fn andd(x: Dec, y: Dec) -> Dec = x
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  fn compose({as: SVDesc}, {bs: SVDesc}, {cs: SVDesc}, {d1: Dec}, {d2: Dec}, l: SF(as, bs, d1), r: SF(bs, cs, d2)) -> SF(as, cs, andd(d1, d2)) = seq(l, r)
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

  test "compose = seq(l, r) elaborates and kernel-checks from source" do
    assert {:ok, env} = elaborate_all(@src)
    assert %{name: :compose, type: type, body: body} = Env.get_def(env, :compose)

    # A 7-argument λ (5 erased indices + l + r) whose body is the seq application.
    assert {:ctor, :seq, args} = unwrap_lams(body)
    assert length(args) == 7

    # Its declared type is a 7-binder Π ending in the SF family.
    assert {:pi, _g, _, _} = type
  end

  test "rejects compose when the declared return index contradicts and's result" do
    # Declare the return decoupledness as Dcoupled while seq computes andd(d1,d2);
    # with d1=d2 free these are not definitionally equal ⇒ conversion error.
    bad =
      String.replace(
        @src,
        "-> SF(as, cs, andd(d1, d2)) = seq(l, r)",
        "-> SF(as, cs, Dcoupled) = seq(l, r)"
      )

    assert {:error, _} = elaborate_all(bad)
  end
end

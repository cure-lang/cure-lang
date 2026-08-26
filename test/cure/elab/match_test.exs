defmodule Cure.Elab.MatchTest do
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
  fn tag({as: SVDesc}, {bs: SVDesc}, {d: Dec}, s: SF(as, bs, d)) -> Dec = match s
    prim() -> Causal
    seq(l, r) -> Dcoupled
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

  test "tag pattern-matches on SF and kernel-checks (coverage + branch arities)" do
    assert {:ok, env} = elaborate_all(@src)
    assert %{name: :tag, body: body} = Env.get_def(env, :tag)

    assert {:case, _scrut, _motive, branches} = unwrap_lams(body)
    # branch arity is the FULL ctor telescope (erased indices + present args):
    # prim ⇒ 2 (as, bs); seq ⇒ 7 (as,bs,cs,d1,d2,l,r)
    assert branches |> Enum.map(fn {c, ar, _} -> {c, ar} end) |> Enum.sort() ==
             [{:prim, 2}, {:seq, 7}]
  end

  test "rejects a non-exhaustive match (missing the seq case)" do
    bad = String.replace(@src, "  seq(l, r) -> Dcoupled\n", "")
    assert {:error, _} = elaborate_all(bad)
  end

  test "validates typed payload annotations against the constructor field type" do
    src = """
    mod M
      type Message = Ping(Int)
      fn read(message: Message) -> Int = match message
        Ping(value: Bool) -> 0
    """

    assert {:error, {:source_context, {:typed_pattern_type_mismatch, _}, _}} = Cure.Elab.Program.elaborate(src)
  end
end

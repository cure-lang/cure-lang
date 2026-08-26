defmodule Cure.Elab.SigmaSurfaceTest do
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

  # The dependent-pair surface now lowers onto the builtin inductive Sigma, so the
  # base env must carry the seeded `:Sigma` family + `mk_pair` ctor AND the
  # `sigma_first`/`sigma_second` projection globals that `.1`/`.2` lower to. An
  # empty-module `Program.elaborate` gives exactly that (auto-seed + auto-prelude
  # of Std.Sigma), replacing the former raw `Env.empty()` start.
  defp base_env do
    {:ok, env} = Cure.Elab.Program.elaborate("mod SigmaSurfaceBase\n")
    env
  end

  defp elaborate_all(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)

    items =
      case ast do
        {:block, _, xs} -> xs
        x -> [x]
      end

    Enum.reduce_while(items, {:ok, base_env()}, fn decl, {:ok, env} ->
      case Declarations.elaborate(decl, env) do
        {:ok, env2} -> {:cont, {:ok, env2}}
        err -> {:halt, err}
      end
    end)
  end

  # Does `term` mention a node headed by `tag` anywhere?
  defp mentions?(term, tag) when is_tuple(term),
    do: elem(term, 0) == tag or term |> Tuple.to_list() |> Enum.any?(&mentions?(&1, tag))

  defp mentions?(list, tag) when is_list(list), do: Enum.any?(list, &mentions?(&1, tag))
  defp mentions?(_other, _tag), do: false

  defp unwrap_lams({:lam, _g, _dom, body}), do: unwrap_lams(body)
  defp unwrap_lams(term), do: term

  test "forget_dec packages the decoupledness index into a Sigma pair" do
    src =
      @base <>
        "fn forget_dec({as: SVDesc}, {bs: SVDesc}, d: Dec, sf: SF(as, bs, d)) -> Sigma(x: Dec, SF(as, bs, x)) = %[d, sf]\n"

    assert {:ok, env} = elaborate_all(src)
    assert %{name: _, type: type, body: body} = Env.get_def(env, :forget_dec)
    # Core shape flipped (D2): the pair is the builtin Sigma ctor, not `{:pair,…}`.
    assert {:ctor, :"Std.Sigma#mk_pair", [_d, _sf]} = unwrap_lams(body)
    refute mentions?(body, :pair)
    # Declared type ends in a dependent Σ.
    assert {:pi, _g, _, _} = type
  end

  test "recover projects the second component at the projected index type" do
    src =
      @base <>
        "fn recover({as: SVDesc}, {bs: SVDesc}, p: Sigma(x: Dec, SF(as, bs, x))) -> SF(as, bs, p.1) = p.2\n"

    assert {:ok, env} = elaborate_all(src)
    assert %{name: _, body: body} = Env.get_def(env, :recover)
    # Core shape flipped (D2): `.2` lowers to the `sigma_second` projection global,
    # not the primitive `{:snd,…}` node.
    refute mentions?(body, :snd)
    refute mentions?(body, :fst)
    assert mentions?(unwrap_lams(body), :global)
  end

  test "rejects a pair whose second component's type mismatches B[a/x]" do
    # Claim the pair packs Dcoupled, but sf : SF(as,bs,d) with d free ≠ Dcoupled.
    src =
      @base <>
        "fn bad({as: SVDesc}, {bs: SVDesc}, {d: Dec}, sf: SF(as, bs, d)) -> Sigma(x: Dec, SF(as, bs, x)) = %[Dcoupled, sf]\n"

    assert {:error, _} = elaborate_all(src)
  end
end

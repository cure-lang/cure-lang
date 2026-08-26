defmodule Cure.Elab.SigmaInductiveTest do
  @moduledoc """
  D2 T2/T3 red-green driver: every surface `%[..]` / `Sigma(..)` / `.1` / `.2`
  lowers onto the builtin inductive Sigma (`{:ctor, :mk_pair, _}` /
  `{:data, :Sigma, _, _}` / projection-global spines), with NO primitive
  `{:pair}`/`{:sigma}`/`{:fst}`/`{:snd}` Core node produced, and the runtime BEAM
  representation (bare 2-tuple) unchanged.
  """
  use ExUnit.Case, async: false
  alias Cure.Core.Env

  @base """
  mod SigmaInductiveProbe
    type Dec = Dcoupled | Causal
    type Sig = CSig | ESig
    type SVDesc = SVNil | SVCons(Sig, SVDesc)
    fn andd(x: Dec, y: Dec) -> Dec = x
    type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
      prim : SF(as, bs, Causal)
      seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  """

  # Recursive "does this Core term mention a node with this head tag anywhere?"
  defp mentions?(term, tag) when is_tuple(term) do
    elem(term, 0) == tag or term |> Tuple.to_list() |> Enum.any?(&mentions?(&1, tag))
  end

  defp mentions?(list, tag) when is_list(list), do: Enum.any?(list, &mentions?(&1, tag))
  defp mentions?(_other, _tag), do: false

  # Does `term` contain a `{:data, fam, _, _}` node anywhere?
  defp has_data?({:data, fam, _, _}, fam), do: true

  defp has_data?(term, fam) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.any?(&has_data?(&1, fam))

  defp has_data?(list, fam) when is_list(list), do: Enum.any?(list, &has_data?(&1, fam))
  defp has_data?(_other, _fam), do: false

  defp unwrap_lams({:lam, _g, _dom, body}), do: unwrap_lams(body)
  defp unwrap_lams(term), do: term

  defp elaborate(src) do
    {:ok, env} = Cure.Elab.Program.elaborate(src)
    env
  end

  test "dependent-pair construction %[..] lowers to {:ctor, :mk_pair} / {:data, :Sigma}" do
    src =
      @base <>
        "  fn forget_dec({as: SVDesc}, {bs: SVDesc}, d: Dec, sf: SF(as, bs, d)) -> Sigma(x: Dec, SF(as, bs, x)) = %[d, sf]\nend\n"

    env = elaborate(src)
    assert %{type: type, body: body} = Env.get_def(env, :forget_dec)

    body_core = unwrap_lams(body)
    assert {:ctor, :"Std.Sigma#mk_pair", [_, _]} = body_core
    refute mentions?(body, :pair)

    # Declared type's Π codomain is the inductive Sigma, not the primitive node.
    assert has_data?(type, :"Std.Sigma#Sigma")
    refute mentions?(type, :sigma)
  end

  test ".1/.2 on a Sigma-typed parameter produce no primitive {:fst}/{:snd}" do
    src =
      @base <>
        "  fn snd_of(p: Sigma(x: Dec, Dec)) -> Dec = p.2\n" <>
        "  fn fst_of(p: Sigma(x: Dec, Dec)) -> Dec = p.1\nend\n"

    env = elaborate(src)
    assert %{body: snd_body} = Env.get_def(env, :snd_of)
    assert %{body: fst_body} = Env.get_def(env, :fst_of)

    refute mentions?(snd_body, :snd)
    refute mentions?(snd_body, :fst)
    refute mentions?(fst_body, :snd)
    refute mentions?(fst_body, :fst)
  end

  test "type-position projection SF(as, bs, p.1) produces no primitive {:snd}/{:fst}" do
    src =
      @base <>
        "  fn recover({as: SVDesc}, {bs: SVDesc}, p: Sigma(x: Dec, SF(as, bs, x))) -> SF(as, bs, p.1) = p.2\nend\n"

    env = elaborate(src)
    assert %{type: type, body: body} = Env.get_def(env, :recover)

    refute mentions?(type, :snd)
    refute mentions?(type, :fst)
    refute mentions?(body, :snd)
    refute mentions?(body, :fst)
  end

  # Runtime/ABI check: %[..] compiles to a bare BEAM 2-tuple and .2 extracts the
  # second element — captured from today's primitive path (identical to the
  # immutable dependent_surface_codegen ABI gate). RED under T2 alone (the generic
  # tagged-ctor path emits {:mk_pair, A, B}); GREEN after the T3 emit hook restores
  # the bare 2-tuple. Tagged :t3 so it is excluded from T2's scoped run and never
  # committed red.
  @tag :t3
  test "%[..] is a bare 2-tuple and .2 extracts element 2 (ABI preserved)" do
    src = """
    mod SigmaAbiProbe
      type Dec = Dcoupled | Causal
      fn pack(d: Dec) -> Sigma(x: Dec, Dec) = %[d, d]
      fn recover(p: Sigma(x: Dec, Dec)) -> Dec = p.2
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :pack, [:Causal]) == {:Causal, :Causal}
    assert apply(mod, :recover, [{:Dcoupled, :Causal}]) == :Causal
  end
end

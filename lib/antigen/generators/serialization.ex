defmodule Antigen.Generators.Serialization do
  @moduledoc """
  Parametric generator for the `serialize/roundtrip` metamorphic vertical
  (`Antigen.Assays.Serialization`): closed Core terms spanning every serialisable
  shape, over which `decode(encode(t)) == t` must hold (serialisation is lossless).

  This is the lever for `Cure.Core.Serialize`'s DECODE path — `tokenize` / `parse`
  / `parse_list` / `take_atom` / `build` / `build_node` / `build_branches` /
  `build_all` — which the coverage campaign never exercises otherwise: `mix antigen
  cover` runs the live explorer, which BANKS (encode) but never REPLAYS (decode).
  The roundtrip assay decodes every generated term in-process, so both directions
  run live.

  Terms are drawn to bounded depth over all `Cure.Core.Term.term?`-valid
  constructors (so the runner's well-formedness gate keeps them), with names/ops
  from a fixed allowlisted pool for `:safe` corpus replay.
  """
  alias Antigen.{Gen, Challenge}

  @data_names [:Nat, :Vec, :Bd]
  @ctor_names [:Z, :S, :vnil]
  @globals [:plus, :dbl]
  @op_globals [:int_add, :int_mul, :int_lt]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(term(3), fn t ->
      Gen.return(
        Challenge.new(
          kind: :serialize,
          assay: "serialize/roundtrip",
          label: :lossless,
          payload: %{term: t},
          note: "serialization roundtrip (decode ∘ encode = id)"
        )
      )
    end)
  end

  defp term(0), do: leaf()

  defp term(depth) do
    d = depth - 1

    Gen.frequency([
      {4, leaf()},
      {1, binary(:pi, d)},
      {1, binary(:lam, d)},
      {1, binary(:app, d)},
      # (:refl/:eq/:rewrite retired with the primitive identity forms, Phase C;
      # :sigma/:pair/:fst/:snd retired with the primitive Sigma, D2 —
      # the inductive spellings ride the :data/:ctor/:case arms below.)
      {1, data_term(d)},
      {1, ctor_term(d)},
      {1, prim_term(d)},
      {1, case_term(d)}
    ])
  end

  defp leaf do
    Gen.one_of([
      Gen.bind(Gen.int(0, 1), fn n -> Gen.return({:type, n}) end),
      Gen.bind(Gen.int(0, 4), fn k -> Gen.return({:var, k}) end),
      Gen.return({:int_type}),
      Gen.return({:float_type}),
      Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:int_lit, n}) end),
      Gen.bind(Gen.int(0, 9), fn n -> Gen.return({:nat_lit, n}) end),
      Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:float_lit, n / 2}) end),
      Gen.bind(Gen.member_of(@globals), fn g -> Gen.return({:global, g}) end)
    ])
  end

  # `:pi`/`:lam` are BINDERS and carry a QTT grade; `:app` does not. The tuple is
  # assembled from a tag, so no textual migration can see it.
  defp binary(tag, d) when tag in [:pi, :lam] do
    Gen.bind(term(d), fn a ->
      Gen.bind(term(d), fn b -> Gen.return({tag, Cure.Core.Grade.unrestricted(), a, b}) end)
    end)
  end

  defp binary(tag, d),
    do: Gen.bind(term(d), fn a -> Gen.bind(term(d), fn b -> Gen.return({tag, a, b}) end) end)

  defp data_term(d) do
    Gen.bind(Gen.member_of(@data_names), fn n ->
      Gen.bind(term_list(d), fn ps ->
        Gen.bind(term_list(d), fn is -> Gen.return({:data, n, ps, is}) end)
      end)
    end)
  end

  defp ctor_term(d) do
    Gen.bind(Gen.member_of(@ctor_names), fn n ->
      Gen.bind(term_list(d), fn args -> Gen.return({:ctor, n, args}) end)
    end)
  end

  # Builtin-op global spines (K2: the {:prim} grammar rows re-spell as
  # 2-arg application spines headed by a registered op global).
  defp prim_term(d) do
    Gen.bind(Gen.member_of(@op_globals), fn g ->
      Gen.bind(term(d), fn a ->
        Gen.bind(term(d), fn b -> Gen.return({:app, {:app, {:global, g}, a}, b}) end)
      end)
    end)
  end

  defp case_term(d) do
    Gen.bind(term(d), fn scrut ->
      Gen.bind(term(d), fn motive ->
        Gen.bind(branches(d), fn brs -> Gen.return({:case, scrut, motive, brs}) end)
      end)
    end)
  end

  defp branches(d) do
    Gen.frequency([
      {1, Gen.return([])},
      {2, Gen.bind(branch(d), fn b -> Gen.return([b]) end)},
      {1, Gen.bind(branch(d), fn a -> Gen.bind(branch(d), fn b -> Gen.return([a, b]) end) end)}
    ])
  end

  defp branch(d) do
    Gen.bind(Gen.member_of(@ctor_names), fn c ->
      Gen.bind(Gen.int(0, 2), fn arity ->
        Gen.bind(term(d), fn body -> Gen.return({c, arity, body}) end)
      end)
    end)
  end

  # 0-2 element term lists (params / indices / args)
  defp term_list(d) do
    Gen.frequency([
      {2, Gen.return([])},
      {2, Gen.bind(term(d), fn a -> Gen.return([a]) end)},
      {1, Gen.bind(term(d), fn a -> Gen.bind(term(d), fn b -> Gen.return([a, b]) end) end)}
    ])
  end
end

defmodule Antigen.Generators.ConversionTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Conversion, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel}

  defp sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "conv_reject: every carrier at a range of depths infer-REJECTS, with kernel-free witness" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    depths =
      for c <- sample(Conversion.conv_reject(), 300) do
        p = c.payload
        assert %Antigen.Challenge{kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed} = c
        f = p.fault
        assert f.carrier in Conversion.carriers()
        assert f.witness == :conv and f.reduction == :required
        # kernel-free non-convertibility witness
        assert f.actual_index == f.expected_index + 1
        assert f.depth == f.expected_index
        # the discriminating index position is a plus REDEX, not a numeral (conversion-at-depth)
        assert redex?(f.carrier, p.term)
        # construction guarantee (+ totality)
        assert {:error, _} = Kernel.infer(ctx, p.term)
        f.depth
      end

    # depth reached; d=0 exercised
    assert Enum.member?(depths, 0) and Enum.max(depths) >= 4
    assert length(Enum.uniq(depths)) >= 3
  end

  test "conv_accept: every carrier at a range of depths is ACCEPTED by all term/* assays" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    assays = ["term/infer_check", "term/subject_reduction", "term/normalization"]

    depths =
      for assay <- assays, c <- sample(Conversion.conv_accept(assay), 60) do
        assert %Antigen.Challenge{kind: :typed_term, label: :well_typed} = c
        assert {:ok, _} = Kernel.infer(ctx, c.payload.term)
        # reduces to accept
        assert Antigen.Assays.Term.run(c) == :ok
        # accept term also carries a plus redex at its index (reduction-required)
        assert redex?(detect(c.payload.term), c.payload.term)
        idx_depth(c.payload.term)
      end

    assert Enum.max(depths) >= 4
  end

  test "control: an accept shape with the REJECT filler is infer-rejected (accept is not vacuous)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    # conv_index at d=2: matched filler accepts, one-deeper filler rejects
    ok = Conversion.carrier_term(:conv_index, 1, 1, 2)
    bad = Conversion.carrier_term(:conv_index, 1, 1, 3)
    assert {:ok, _} = Kernel.infer(ctx, ok)
    assert {:error, _} = Kernel.infer(ctx, bad)
  end

  defp detect({:ctor, :vcons, _}), do: :conv_index
  defp detect({:case, _, _, _}), do: :conv_motive
  defp idx_depth({:ctor, :vcons, [{:app, {:app, {:global, :plus}, a}, b}, _, _]}), do: nat(a) + nat(b)

  defp idx_depth({:case, _, {:lam, _g, _, {:data, :Vec, _, [{:app, {:app, {:global, :plus}, a}, b}]}}, _}),
    do: nat(a) + nat(b)

  defp nat({:ctor, :Z, []}), do: 0
  defp nat({:ctor, :S, [n]}), do: 1 + nat(n)

  test "default_gen produces both conversion polarities" do
    cs = sample(Mix.Tasks.Antigen.default_gen(), 800)
    rej = Enum.filter(cs, fn c -> c.kind == :mutant_term and Map.get(c.payload.fault, :witness) == :conv end)

    acc =
      Enum.filter(cs, fn c ->
        c.kind == :typed_term and
          match?({:ctor, :vcons, [{:app, {:app, {:global, :plus}, _}, _}, _, _]}, c.payload.term)
      end)

    assert rej != [] and acc != []
  end

  test "conversion_metrics: ≥2 carriers, both polarities present" do
    cs = sample(Mix.Tasks.Antigen.default_gen(), 800)
    m = Antigen.Runner.conversion_metrics(cs)
    assert m.conv_carrier_diversity >= 2
    assert m.conv_both_polarities == true
    assert m.conv_reject_count > 0 and m.conv_accept_count > 0
  end

  test "conversion_metrics does NOT misclassify ordinary typed-terms (no plus) as accept carriers" do
    ordinary = sample(Antigen.Generators.Term.typed_term("term/infer_check"), 200)
    m = Antigen.Runner.conversion_metrics(ordinary)
    assert m.conv_accept_count == 0
  end

  defp redex?(:conv_index, {:ctor, :vcons, [n, _, _]}), do: is_plus(n)
  defp redex?(:conv_motive, {:case, _, {:lam, _g, _, {:data, :Vec, _, [idx]}}, _}), do: is_plus(idx)
  defp is_plus({:app, {:app, {:global, :plus}, _}, _}), do: true
  defp is_plus(_), do: false
end

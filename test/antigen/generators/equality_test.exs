defmodule Antigen.Generators.EqualityTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Equality, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.Challenge
  alias Cure.Core.{Context, Kernel, Normalise}

  @sample 400

  test "every sampled equality challenge is a well-typed :typed_term over v1" do
    for %Challenge{} = c <- B.interp(Equality.gen()) |> Enum.take(@sample) do
      assert c.kind == :typed_term
      assert c.assay in Antigen.Generators.Term.assay_ids()
      assert c.payload.sig == :v1

      cx = SigMenu.rebuild_context(SigMenu.env_of(:v1), c.payload.ctx)

      case Kernel.infer(cx, c.payload.term) do
        {:ok, inferred} ->
          assert Normalise.quote(inferred, Context.length(cx), Context.signature(cx)) == c.payload.type
          assert Normalise.nf(cx, c.payload.term, fuel: 500_000) != :fuel_exhausted

        other ->
          flunk("equality term failed to infer: #{inspect(c.payload.term)} -> #{inspect(other)}")
      end
    end
  end

  test "the sample exercises Equivalent-type, transport, and checked-reflexive shapes" do
    sample = B.interp(Equality.gen()) |> Enum.take(@sample)
    heads = sample |> Enum.map(fn c -> elem(c.payload.term, 0) end) |> MapSet.new()

    # inductive Equivalent propositions + J/subst :case transports (an :app of a
    # :case) replaced the retired {:refl}/{:eq}/{:rewrite} shapes.
    for h <- [:data, :app], do: assert(h in heads, "shape #{h} never generated")

    # an Equivalent-type challenge is a Type-0 proposition (family formation)
    assert Enum.any?(sample, fn c ->
             match?({:data, :Equivalent, _, _}, c.payload.term) and c.payload.type == {:type, 0}
           end)

    # a transport challenge is an :app whose head is a :case over a reflexive
    # branch (the J/subst eliminator)
    assert Enum.any?(sample, fn c ->
             match?({:app, {:case, _, _, [{:reflexive, 1, _}]}, _}, c.payload.term)
           end)

    # a checked-reflexive transport claims an Equivalent type (fields-only
    # reflexive in the checked body slot)
    assert Enum.any?(sample, fn c ->
             match?({:app, _, {:ctor, :reflexive, [_]}}, c.payload.term) and
               match?({:data, :Equivalent, _, _}, c.payload.type)
           end)
  end

  test "neutral Equivalent propositions carry a non-empty context and a neutral subject" do
    sample = B.interp(Equality.gen()) |> Enum.take(@sample)

    neutral_props =
      Enum.filter(sample, fn c ->
        match?(
          {:data, :Equivalent, _, [subj, _]} when elem(subj, 0) in [:app, :case],
          c.payload.term
        ) and c.payload.ctx != []
      end)

    assert neutral_props != [],
           "no neutral Equivalent propositions generated (needed for Conv neutral paths)"

    subjects =
      neutral_props
      |> Enum.map(fn c ->
        {:data, :Equivalent, _, [subj, _]} = c.payload.term
        elem(subj, 0)
      end)
      |> MapSet.new()

    # Σ projections are now single-branch ι-on-`:case` over mk_pair (D2), so the
    # former `:fst`/`:snd` neutral subjects are `:case`-headed; the former :prim
    # subjects are builtin-op global spines, i.e. `:app`-headed (K2).
    for s <- [:app, :case], do: assert(s in subjects, "neutral subject #{s} never generated")
  end
end

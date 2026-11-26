defmodule Antigen.Phase5DepMatchTypedMotiveTest do
  use ExUnit.Case, async: true

  alias Antigen.{Challenge, Corpus}
  alias Antigen.Backend.StreamData, as: Backend
  alias Antigen.Generators.{DepMatch, SigMenu}
  alias Cure.Core.{Context, Eval, Inductive, Kernel, Normalise, Serialize, Sort}
  alias Cure.Core.Term, as: CoreTerm

  test "the v1 signature independently checks all family and constructor declarations" do
    env = SigMenu.env_of(:v1)

    for {name, family} <- env.families do
      assert :ok = Kernel.check_family(env, family), inspect(name)

      for ctor <- Inductive.ctors_of(env, name) do
        assert :ok = Kernel.check_ctor(env, family, ctor), inspect({name, ctor.name})
      end
    end

    assert %{result_indices: [{:data, :Int, [], []}]} = Inductive.get_ctor(env, :tint)
    assert %{result_indices: [{:data, :Vec, [], [_]}]} = Inductive.get_ctor(env, :tvec)
  end

  test "every retained variant has a typed telescope, raw motive, canonical claim and subject reduction" do
    env = SigMenu.env_of(:v1)
    variants = DepMatch.case_variants()
    assert length(variants) == 36

    for {{weight, generator}, index} <- Enum.with_index(variants),
        sample <- Backend.sample_seeded(generator, 3, 20_261_123 + index) do
      assert {types, {:case, _, motive, _} = term, type} = sample
      assert weight > 0
      ctx = checked_context(env, types)
      assert {:ok, _} = Kernel.infer(ctx, motive)
      assert {:ok, {:vtype, _}} = Kernel.infer(ctx, type)
      assert {:ok, inferred} = Kernel.infer(ctx, term)
      assert Normalise.quote(inferred, Context.length(ctx), env) == type
      assert :ok = Kernel.check(ctx, term, Eval.eval(type, Context.env(ctx)))
      nf = Normalise.nf(ctx, term, fuel: 500_000)
      refute nf == :fuel_exhausted
      assert :ok = Kernel.check(ctx, nf, inferred)

      for assay <- ["term/infer_check", "term/subject_reduction", "term/normalization"] do
        challenge =
          Challenge.new(
            kind: :typed_term,
            assay: assay,
            label: :well_typed,
            payload: %{sig: :v1, ctx: types, term: term, type: type}
          )

        assert :ok = Antigen.Assays.Term.run(challenge), inspect({index, assay})
        assert {:ok, replayed} = challenge |> Corpus.encode_record() |> Corpus.decode_record()
        assert :ok = Antigen.Assays.Term.run(replayed), inspect({index, assay, :replayed})
      end
    end
  end

  test "the original off-by-one Sq major annotation remains independently rejected" do
    env = SigMenu.env_of(:v1)

    {types, {:case, scrutinee, motive, branches}, _} =
      variant_samples()
      |> Enum.find(fn {types, _, _} -> match?([{:data, :Sq, _, _}, _, _], types) end)

    ctx = checked_context(env, types)
    assert {:lam, g1, first, {:lam, g2, second, {:lam, g3, _, result}}} = motive
    wrong_domain = {:data, :Sq, [], [{:var, 2}, {:var, 1}]}
    wrong = {:lam, g1, first, {:lam, g2, second, {:lam, g3, wrong_domain, result}}}
    assert {:error, _} = Kernel.infer(ctx, wrong)
    assert {:error, :bad_motive} = Kernel.infer(ctx, {:case, scrutinee, wrong, branches})
  end

  test "a dependent result cannot be retargeted to an unrelated well-typed vector goal" do
    env = SigMenu.env_of(:v1)

    {types, term, type} =
      variant_samples()
      |> Enum.find(fn {_, _, type} -> match?({:data, :Vec, [], [{:var, _}]}, type) end)

    ctx = checked_context(env, types)
    assert :ok = Kernel.check(ctx, term, Eval.eval(type, Context.env(ctx)))
    other = Context.extend(ctx, Eval.eval(SigMenu.nat(), Context.env(ctx)))
    wrong = SigMenu.vec({:var, 0})
    assert {:ok, {:vtype, _}} = Kernel.infer(other, wrong)
    assert {:error, _} = Kernel.check(other, CoreTerm.shift(term, 1, 0), Eval.eval(wrong, Context.env(other)))
  end

  test "universe application rejection is predicative, not an obsolete finite ceiling" do
    ctx = Context.empty(SigMenu.env_of(:v1))

    for level <- [0, 37, 10 ** 40] do
      term = Antigen.Generators.Malformed.universe_application(level)
      assert {:app, identity, universe} = term
      assert {:ok, _} = Kernel.infer(ctx, universe)
      assert {:ok, _} = Kernel.infer(ctx, identity)
      assert {:error, {:conversion_failure, _, _}} = Kernel.infer(ctx, term)
      accepted = if level == 0, do: SigMenu.nat(), else: {:type, Sort.finite_closed(level - 1)}
      assert {:ok, _} = Kernel.infer(ctx, {:app, identity, accepted})

      challenge =
        Challenge.new(
          kind: :malformed,
          assay: "term/rejection",
          label: :ill_typed,
          payload: %{sig: :v1, ctx: [], term: term}
        )

      assert :ok = Antigen.Assays.Malformed.run(challenge)
      assert {:ok, replayed} = challenge |> Corpus.encode_record() |> Corpus.decode_record()
      assert :ok = Antigen.Assays.Malformed.run(replayed)
    end
  end

  test "the separately archived bare-Type2 claim is valid and its replacement really rejects" do
    inventory = File.read!("test/antigen/fixtures/phase5_malformed_universe_claim.json") |> :json.decode()
    assert {:ok, original} = Serialize.decode(inventory["original_term"])
    ctx = Context.empty(SigMenu.env_of(:v1))
    assert {:ok, inferred} = Kernel.infer(ctx, original)
    assert Serialize.encode(Normalise.quote(inferred, 0, Context.signature(ctx))) == inventory["current_inferred_type"]
    assert {:ok, replacement} = Serialize.decode(inventory["replacement_term"])
    assert {:error, {:conversion_failure, _, _}} = Kernel.infer(ctx, replacement)
  end

  test "the non-data case cell reaches that guard rather than a malformed motive" do
    ctx = Context.empty(SigMenu.env_of(:v1))

    cases =
      Antigen.Generators.Malformed.gen()
      |> Backend.sample_seeded(500, 20_261_124)
      |> Enum.filter(&(&1.cover_tag == :case_scrutinee_not_data))

    assert [_ | _] = cases

    for challenge <- cases do
      assert {:error, :case_scrutinee_not_data} = Kernel.infer(ctx, challenge.payload.term)
    end
  end

  defp variant_samples do
    for {{_, generator}, index} <- Enum.with_index(DepMatch.case_variants()),
        sample <- Backend.sample_seeded(generator, 1, 20_261_123 + index),
        do: sample
  end

  defp checked_context(env, types) do
    Enum.reduce(Enum.reverse(types), Context.empty(env), fn type, ctx ->
      assert {:ok, {:vtype, _}} = Kernel.infer(ctx, type), inspect(type)
      Context.extend(ctx, Eval.eval(type, Context.env(ctx)))
    end)
  end
end

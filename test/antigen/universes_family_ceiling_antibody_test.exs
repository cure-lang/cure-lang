defmodule Antigen.UniversesFamilyFormationAntibodyTest do
  @moduledoc """
  The historical ceiling antibody is replaced by genuine family formation.
  A scoped dependent index must name a type, not a value; arbitrary finite
  result sorts remain accepted. Constructor predicativity is checked separately.
  """
  use ExUnit.Case, async: true

  alias Antigen.{Corpus, Challenge}
  alias Antigen.Assays.Universes, as: Assay
  alias Antigen.Generators.Universes, as: Gen
  alias Cure.Core.{Env, Inductive, Kernel, Sort}

  @levels [0, 37, 10 ** 40]

  defmodule ObservedAssay do
    def run(challenge) do
      send(self(), {:formation_assay_called, challenge.label})
      Antigen.Assays.Universes.run(challenge)
    end
  end

  test "dependent family formation discriminates a type from its inhabitant at any finite level" do
    for level <- @levels do
      good = Gen.family_formation(:well_typed, level)
      bad = Gen.family_formation(:ill_typed, level)
      assert [] = good.payload.ctors
      assert [] = bad.payload.ctors
      assert Sort.finite_closed(level) == good.payload.family.sort
      assert :ok = Kernel.check_family(Env.empty(), good.payload.family)
      assert {:error, :not_a_type} = Kernel.check_family(Env.empty(), bad.payload.family)

      for challenge <- [good, bad] do
        assert :ok = Assay.run(challenge)
        assert {:ok, replayed} = challenge |> Corpus.encode_record() |> Corpus.decode_record()
        assert replayed.payload == challenge.payload
        assert :ok = Assay.run(replayed)
      end
    end
  end

  test "omitting check_family is detected without a constructor recheck masking it" do
    operations = %{
      check_family: fn _, _ -> :ok end,
      check_ctor: fn _, _, _ -> flunk("the formation probe must have no constructors") end
    }

    for level <- @levels do
      assert :ok = Assay.run(Gen.family_formation(:well_typed, level), operations)

      assert {:violation, {:wrongly_accepted, :Over}} =
               Assay.run(Gen.family_formation(:ill_typed, level), operations)
    end
  end

  @tag :tmp_dir
  test "both formation labels reach the live runner assay without structural discards", %{tmp_dir: root} do
    result =
      Antigen.Runner.explore(
        challenges: [Gen.family_formation(:well_typed), Gen.family_formation(:ill_typed)],
        count: 2,
        assay: ObservedAssay,
        corpus_path: Path.join(root, "corpus.sexp"),
        seeds_path: Path.join(root, "seeds.sexp"),
        report_dir: Path.join(root, "reports")
      )

    assert result.infections == 0
    assert result.health.discard_rate == 0.0
    assert_received {:formation_assay_called, :well_typed}
    assert_received {:formation_assay_called, :ill_typed}
  end

  test "canonical families above the historical ceiling are accepted independently" do
    for level <- @levels do
      family = Inductive.family(:Over, [], [], Sort.finite_closed(level))
      assert :ok = Kernel.check_family(Env.empty(), family)
    end
  end

  test "the live kernel probe advertises and replays the replacement formation judgment" do
    assert {"kernel/probe", :family_formation} in Antigen.Generators.KernelProbe.cover_cells()
    refute {"kernel/probe", :family_ceiling} in Antigen.Generators.KernelProbe.cover_cells()

    challenge =
      Challenge.new(
        kind: :kernel_probe,
        assay: "kernel/probe",
        label: :probe,
        payload: %{probe: :family_formation},
        cover_tag: :family_formation
      )

    assert :ok = Antigen.Assays.KernelProbe.run(challenge)
    assert {:ok, ^challenge} = challenge |> Corpus.encode_record() |> Corpus.decode_record()
    assert :ok = Antigen.Assays.KernelProbe.run(challenge)
  end
end

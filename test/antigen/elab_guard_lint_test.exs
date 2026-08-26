defmodule Antigen.ElabGuardLintTest do
  @moduledoc """
  Spec 2026-07-08-guard-coverage-lint §6: the lint-soundness vertical. The
  catalog pins hand-verified exhaustive/non-exhaustive labels two-sided; the
  metamorphic layer pins that dropping a guard from a proven-exhaustive set
  flips the verdict (the lint is load-bearing and never over-proves).
  """
  use ExUnit.Case, async: false

  alias Antigen.Challenge
  alias Antigen.Assays.Elab, as: Assay
  alias Antigen.Generators.ElabGuardLint, as: Gen

  describe "assay discrimination" do
    test "a correct catalog cell passes" do
      [c | _] = Gen.guard_lint_challenges()
      assert Assay.run(c) == :ok
    end

    test "a wrong expected verdict is a violation" do
      [c | _] = Gen.guard_lint_challenges()
      flipped = %{c | payload: %{c.payload | expect: :reject}}
      assert {:violation, {:guard_lint_verdict_wrong, _, _}} = Assay.run(flipped)
    end

    test "a wrong reject-reason head is a violation" do
      c = Enum.find(Gen.guard_lint_challenges(), &(&1.payload.expect == :reject))
      wrong = %{c | payload: Map.put(c.payload, :expect_error, :not_the_real_head)}
      assert {:violation, {:guard_lint_wrong_reject_reason, _, _}} = Assay.run(wrong)
    end

    test "a broken :flip (identical base and variant) is a violation" do
      src = Gen.source("exhaustive/trichotomy")

      c =
        Challenge.new(
          kind: :elab_program,
          assay: "elab/guard_lint",
          label: :none,
          payload: %{id: "x", transform: "t", relation: :flip, base_src: src, variant_src: src},
          note: "discrimination"
        )

      assert {:violation, {:guard_lint_relation_wrong, _, _, _}} = Assay.run(c)
    end
  end

  describe "two-sided catalog gate" do
    test "every cell's verdict and reject-head match the elaborator" do
      for c <- Gen.guard_lint_challenges() do
        assert Assay.run(c) == :ok, "catalog cell #{c.payload.id} disagrees with the elaborator"
      end
    end

    test "the catalog is two-sided and six cells" do
      expects = Gen.catalog() |> Enum.map(&elem(&1, 1))
      assert length(expects) == 6
      assert :accept in expects and :reject in expects
    end
  end

  describe "metamorphic gate" do
    test "every relation holds (drop_guard flips, alpha_rename holds)" do
      for c <- Gen.metamorphic_challenges() do
        assert Assay.run(c) == :ok,
               "metamorphic #{c.payload.id}/#{c.payload.transform} (#{c.payload.relation}) violated"
      end
    end

    test "drop_guard produces flips for exactly the two proven-exhaustive cells" do
      flips =
        Gen.metamorphic_challenges()
        |> Enum.filter(&(&1.payload.transform == "drop_guard"))
        |> Enum.map(& &1.payload.id)
        |> Enum.sort()

      assert flips == ["exhaustive/complement", "exhaustive/trichotomy"]
    end
  end

  describe "corpus round-trip" do
    test "an accept cell survives to_pieces/from_pieces" do
      c = Enum.find(Gen.guard_lint_challenges(), &(&1.payload.expect == :accept))
      {scaffold, pieces} = Challenge.to_pieces(c)
      c2 = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
      assert Assay.run(c2) == :ok
    end

    test "a reject cell (expect_error-carrying) survives to_pieces/from_pieces" do
      c = Enum.find(Gen.guard_lint_challenges(), &(&1.payload.expect == :reject))
      {scaffold, pieces} = Challenge.to_pieces(c)
      c2 = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
      assert c2.payload.expect_error == c.payload.expect_error
      assert Assay.run(c2) == :ok
    end
  end

  test "runner registry resolves the assay" do
    assert Antigen.Runner.assay_module_for("elab/guard_lint") == Antigen.Assays.Elab
  end
end

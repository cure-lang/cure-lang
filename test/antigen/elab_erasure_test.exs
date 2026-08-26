defmodule Antigen.ElabErasureTest do
  @moduledoc """
  Tests for the two-sided elaborator ERASURE vertical (a generative pin on the
  `{0,ω}` relevance check, `Cure.Elab.Relevance`). These test the VERTICAL — that
  the assay discriminates correctly in both directions and that the catalog's
  expected verdicts hold — and, because the check is now live, the catalog gate
  and metamorphic gates double as regression gates on the check itself.
  """
  use ExUnit.Case, async: true

  alias Antigen.Assays.Elab
  alias Antigen.Challenge
  alias Antigen.Generators.ElabErasure

  describe "assay discrimination (red-green of the vertical itself)" do
    test "erasure assay is :ok when the actual verdict matches the expected one" do
      accept =
        Challenge.new(
          kind: :elab_program,
          assay: "elab/erasure",
          label: :accept,
          payload: %{id: "acc", src: ElabErasure.source("type_position"), expect: :accept}
        )

      reject =
        Challenge.new(
          kind: :elab_program,
          assay: "elab/erasure",
          label: :reject,
          payload: %{id: "rej", src: ElabErasure.source("returned"), expect: :reject}
        )

      assert :ok = Elab.run(accept)
      assert :ok = Elab.run(reject)
    end

    test "erasure assay fires when the actual verdict contradicts the expected one" do
      # An accepting program mislabelled :reject must infect (proves the assay is
      # not vacuously :ok), and vice versa.
      mislabelled_accept =
        Challenge.new(
          kind: :elab_program,
          assay: "elab/erasure",
          label: :reject,
          payload: %{id: "wrong", src: ElabErasure.source("type_position"), expect: :reject}
        )

      mislabelled_reject =
        Challenge.new(
          kind: :elab_program,
          assay: "elab/erasure",
          label: :accept,
          payload: %{id: "wrong", src: ElabErasure.source("returned"), expect: :accept}
        )

      assert {:violation, {:erasure_verdict_wrong, "wrong", %{expected: :reject, actual: :accept}}} =
               Elab.run(mislabelled_accept)

      assert {:violation, {:erasure_verdict_wrong, "wrong", %{expected: :accept, actual: :reject}}} =
               Elab.run(mislabelled_reject)
    end
  end

  describe "two-sided catalog gate (the check holds today, both directions)" do
    test "every catalog entry elaborates to its expected verdict" do
      violations =
        ElabErasure.erasure_challenges()
        |> Enum.map(fn c -> {c.payload.id, Elab.run(c)} end)
        |> Enum.reject(fn {_id, v} -> v == :ok end)

      assert violations == [],
             "erasure catalog verdict wrong (check under/over-strict):\n" <>
               Enum.map_join(violations, "\n", &inspect/1)
    end

    test "the catalog is genuinely two-sided (has both accept and reject cases)" do
      verdicts = ElabErasure.catalog() |> Enum.map(&elem(&1, 1)) |> Enum.uniq() |> Enum.sort()
      assert verdicts == [:accept, :reject]
    end
  end

  describe "metamorphic gates" do
    test "relevance_injection flips an accepting base to reject; perturbations do not" do
      violations =
        ElabErasure.metamorphic_challenges()
        |> Enum.map(fn c -> {c.payload.id, c.payload.transform, c.payload.relation, Elab.run(c)} end)
        |> Enum.reject(fn {_id, _t, _r, v} -> v == :ok end)

      assert violations == [],
             "erasure metamorphic relation broken:\n" <>
               Enum.map_join(violations, "\n", &inspect/1)
    end

    test "at least one relevance_injection (flip) challenge exists — the check is load-bearing" do
      flips =
        ElabErasure.metamorphic_challenges()
        |> Enum.filter(fn c -> c.payload.relation == :flip end)

      assert flips != []
      # And each flip genuinely flips: base accepts, variant rejects.
      Enum.each(flips, fn c -> assert :ok = Elab.run(c) end)
    end
  end

  describe "corpus round-trip (serialization parity)" do
    test "an erasure :elab_program challenge survives to_pieces/from_pieces" do
      [c | _] = ElabErasure.erasure_challenges()
      {scaffold, pieces} = Challenge.to_pieces(c)
      back = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
      assert back.payload == c.payload
      assert back.assay == c.assay
    end
  end

  describe "registry wiring" do
    test "the runner maps elab/erasure to the Elab assay module" do
      assert Antigen.Runner.assay_module_for("elab/erasure") == Antigen.Assays.Elab
    end
  end
end

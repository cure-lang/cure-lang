defmodule Antigen.ElabNatRepTest do
  @moduledoc """
  Spec 2026-07-08-nat-int-erasure §3: representation agreement. The kernel's
  certified-δ normalisation of `main` (inductive semantics, decoded S-spine →
  integer) must equal BEAM execution of the emitted module (Int rep). Kernel is
  the oracle; emit is the system under test.
  """
  use ExUnit.Case, async: false

  alias Antigen.Challenge
  alias Antigen.Assays.Elab, as: Assay
  alias Antigen.Generators.ElabNatRep, as: Gen

  test "assay discrimination: an unelaborable program is a violation" do
    c =
      Challenge.new(
        kind: :elab_program,
        assay: "elab/nat_rep",
        label: :none,
        payload: %{id: "broken", src: "mod P\n  fn\nend\n", functions: [:main]},
        note: "discrimination"
      )

    assert {:violation, {:nat_rep_program_rejected, "broken", _}} = Assay.run(c)
  end

  test "catalog gate: every cell agrees (kernel int == BEAM int)" do
    challenges = Gen.nat_rep_challenges()
    assert length(challenges) >= 8

    for c <- challenges do
      assert Assay.run(c) == :ok, "nat_rep cell #{c.payload.id} disagreed"
    end
  end

  test "corpus round-trip survives to_pieces/from_pieces" do
    [c | _] = Gen.nat_rep_challenges()
    {scaffold, pieces} = Challenge.to_pieces(c)
    c2 = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
    assert Assay.run(c2) == :ok
  end

  test "runner registry resolves the assay" do
    assert Antigen.Runner.assay_module_for("elab/nat_rep") == Antigen.Assays.Elab
  end
end

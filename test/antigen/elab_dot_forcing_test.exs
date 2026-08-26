defmodule Antigen.ElabDotForcingTest do
  @moduledoc """
  Tests for the source-level dot-forcing vertical (spec
  2026-07-08-antigen-elab-dot-forcing-design): challenges entering at
  Program.elaborate/1 so the named-implicit check's CALL-SITE WIRING (the C-a
  defect class) is covered — the value-level forcing/dot oracle is structurally
  blind to a caller that skips the check. These test the VERTICAL (assay
  discrimination, catalog verdicts, metamorphic relations); the catalog gate
  doubles as a regression gate on #12's C-a/C-c fixes.
  """
  use ExUnit.Case, async: true

  alias Antigen.Assays.Elab
  alias Antigen.Challenge
  alias Antigen.Generators.ElabErasure

  # Grammar-stage typo: lexes fine, fails in the PARSER, whose error payload is
  # a LIST (parser.ex `{:error, Enum.reverse(errors)}`) — the §2.3 non-tuple
  # guard's target shape.
  @grammar_broken "mod P\n  fn\nend\n"

  defp catalog_challenge(id, src, expect, extra \\ %{}) do
    Challenge.new(
      kind: :elab_program,
      assay: "elab/dot_forcing",
      label: expect,
      payload: Map.merge(%{id: id, src: src, expect: expect}, extra)
    )
  end

  describe "assay discrimination (red-green of the vertical itself)" do
    test "catalog clause is :ok when the actual verdict matches the expected one" do
      assert :ok = Elab.run(catalog_challenge("acc", ElabErasure.source("type_position"), :accept))
      assert :ok = Elab.run(catalog_challenge("rej", ElabErasure.source("returned"), :reject))
    end

    test "catalog clause fires on a verdict contradiction, both directions" do
      assert {:violation, {:dot_forcing_verdict_wrong, "w1", %{expected: :reject, actual: :accept}}} =
               Elab.run(catalog_challenge("w1", ElabErasure.source("type_position"), :reject))

      assert {:violation, {:dot_forcing_verdict_wrong, "w2", %{expected: :accept, actual: :reject}}} =
               Elab.run(catalog_challenge("w2", ElabErasure.source("returned"), :accept))
    end

    test "expect_error head match passes; a mismatched head is wrong_reject_reason" do
      # source("returned") rejects with head :erased_used_relevantly.
      assert :ok =
               Elab.run(
                 catalog_challenge("h1", ElabErasure.source("returned"), :reject, %{
                   expect_error: :erased_used_relevantly
                 })
               )

      assert {:violation, {:dot_forcing_wrong_reject_reason, "h2", :erased_used_relevantly}} =
               Elab.run(
                 catalog_challenge("h2", ElabErasure.source("returned"), :reject, %{
                   expect_error: :forced_pattern_mismatch
                 })
               )
    end

    test "non-tuple (parser-list) reject never matches a head and never crashes" do
      assert {:violation, {:dot_forcing_wrong_reject_reason, "h3", :non_tuple_error}} =
               Elab.run(
                 catalog_challenge("h3", @grammar_broken, :reject, %{
                   expect_error: :forced_pattern_mismatch
                 })
               )
    end

    test "relation clause: :flip with an identical variant fires" do
      src = ElabErasure.source("type_position")

      c =
        Challenge.new(
          kind: :elab_program,
          assay: "elab/dot_forcing",
          label: :none,
          payload: %{id: "f1", transform: "identity", relation: :flip, base_src: src, variant_src: src}
        )

      assert {:violation,
              {:dot_forcing_relation_wrong, "f1", "identity", %{relation: :flip, base: :accept, variant: :accept}}} =
               Elab.run(c)
    end

    test "relation clause: :same with agreeing sources is :ok" do
      src = ElabErasure.source("type_position")

      c =
        Challenge.new(
          kind: :elab_program,
          assay: "elab/dot_forcing",
          label: :none,
          payload: %{id: "s1", transform: "identity", relation: :same, base_src: src, variant_src: src}
        )

      assert :ok = Elab.run(c)
    end
  end

  describe "registry wiring" do
    test "the runner maps elab/dot_forcing to the Elab assay module" do
      assert Antigen.Runner.assay_module_for("elab/dot_forcing") == Antigen.Assays.Elab
    end
  end

  describe "catalog gate (all six cells hold on today's post-#12 elaborator)" do
    alias Antigen.Generators.ElabDotForcing

    test "the catalog has exactly the six specced cells" do
      assert ElabDotForcing.catalog() |> Enum.map(&elem(&1, 0)) |> Enum.sort() == [
               "forced/carried/right",
               "forced/carried/wrong",
               "forced/plain/right",
               "forced/plain/wrong",
               "unforced/bind_erased",
               "unforced/bind_relevant"
             ]
    end

    test "the catalog is genuinely two-sided" do
      verdicts = ElabDotForcing.catalog() |> Enum.map(&elem(&1, 1)) |> Enum.uniq() |> Enum.sort()
      assert verdicts == [:accept, :reject]
    end

    test "every catalog entry elaborates to its expected verdict (and error head)" do
      violations =
        ElabDotForcing.dot_forcing_challenges()
        |> Enum.map(fn c -> {c.payload.id, Elab.run(c)} end)
        |> Enum.reject(fn {_id, v} -> v == :ok end)

      assert violations == [],
             "dot-forcing catalog verdict wrong (call-site wiring or check regressed):\n" <>
               Enum.map_join(violations, "\n", &inspect/1)
    end

    test "reject cells carry their expected error heads" do
      by_id = Map.new(ElabDotForcing.dot_forcing_challenges(), &{&1.payload.id, &1.payload})
      assert by_id["forced/carried/wrong"].expect_error == :forced_pattern_mismatch
      assert by_id["forced/plain/wrong"].expect_error == :forced_pattern_mismatch
      assert by_id["unforced/bind_relevant"].expect_error == :erased_used_relevantly
      refute Map.has_key?(by_id["forced/carried/right"], :expect_error)
    end
  end

  describe "metamorphic gates" do
    alias Antigen.Generators.ElabDotForcing

    test "every metamorphic relation holds (flips flip, sames stay)" do
      violations =
        ElabDotForcing.metamorphic_challenges()
        |> Enum.map(fn c -> {c.payload.id, c.payload.transform, c.payload.relation, Elab.run(c)} end)
        |> Enum.reject(fn {_id, _t, _r, v} -> v == :ok end)

      assert violations == [],
             "dot-forcing metamorphic relation broken:\n" <>
               Enum.map_join(violations, "\n", &inspect/1)
    end

    test "the C-a causal pin exists: corrupt_dot flips BOTH dispatch paths" do
      flips =
        ElabDotForcing.metamorphic_challenges()
        |> Enum.filter(fn c -> c.payload.transform == "corrupt_dot" end)
        |> Enum.map(fn c -> c.payload.id end)
        |> Enum.sort()

      assert flips == ["forced/carried/right", "forced/plain/right"]
    end

    test "the C-c load-bearing pin exists: promote_use flips bind_erased" do
      assert [%{payload: %{id: "unforced/bind_erased", relation: :flip}}] =
               ElabDotForcing.metamorphic_challenges()
               |> Enum.filter(fn c -> c.payload.transform == "promote_use" end)
    end
  end

  describe "corpus round-trip (serialization parity)" do
    test "an accept catalog challenge (no expect_error key) survives to_pieces/from_pieces" do
      c =
        Antigen.Generators.ElabDotForcing.dot_forcing_challenges()
        |> Enum.find(&(&1.payload.id == "forced/carried/right"))

      {scaffold, pieces} = Challenge.to_pieces(c)
      back = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
      assert back.payload == c.payload
      assert back.assay == c.assay
    end

    test "a reject catalog challenge carrying expect_error survives to_pieces/from_pieces" do
      c =
        Antigen.Generators.ElabDotForcing.dot_forcing_challenges()
        |> Enum.find(&(&1.payload.id == "forced/carried/wrong"))

      {scaffold, pieces} = Challenge.to_pieces(c)
      back = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
      assert back.payload == c.payload
      assert back.assay == c.assay
    end
  end
end

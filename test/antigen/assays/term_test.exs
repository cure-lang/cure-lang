defmodule Antigen.Assays.TermTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Term, as: A
  alias Antigen.Challenge
  alias Antigen.Generators.{Term, SigMenu}
  alias Antigen.Backend.StreamData, as: B

  defp samples(id, n), do: B.interp(Term.typed_term(id)) |> Enum.take(n)

  test "infer_check assay is green on generated well-typed terms" do
    for c <- samples("term/infer_check", 60), do: assert(A.run(c) == :ok)
  end

  test "subject_reduction assay is green on generated well-typed terms" do
    for c <- samples("term/subject_reduction", 60), do: assert(A.run(c) == :ok)
  end

  test "normalization assay is green on generated well-typed terms" do
    for c <- samples("term/normalization", 60), do: assert(A.run(c) == :ok)
  end

  test "erasure_preservation assay is green on generated well-typed terms" do
    for c <- samples("term/erasure_preservation", 60), do: assert(A.run(c) == :ok)
  end

  # -- BANKED FINDING: Normalise non-idempotence on context-closing lambdas ----
  #
  # A frozen Pi-goal challenge (captured from the generator, ctx depth 4) on which
  # the trusted `Cure.Core.Normalise` is NON-IDEMPOTENT: nf(nf t) ≠ nf(t), the
  # normal form oscillating with period 2 (two context de Bruijn indices are
  # transposed on each renormalization). The `term/normalization` assay correctly
  # flags it. This is a REAL kernel (TCB) finding — the reach-expansion's Pi goals
  # surfaced it. Pi menu seeds are withheld (see SigMenu.goal_types/0) until it is
  # fixed; when the normalizer is corrected, THIS ASSERTION FLIPS to `:ok` — the
  # red-green target for the fix (same banking pattern as the erase/parse_model
  # findings). Report: docs/superpowers/reports/2026-07-04-antigen-nf-nonidempotence-finding.md
  # Regression guard for the Normalise index-reflection fix. This frozen Pi
  # challenge (ctx depth 4) once made `nf` oscillate with period 2 (nf(nf t) ≠
  # nf(t), transposing two context de Bruijn indices) because nf_struct stored a
  # reified binder body under an empty closure env. After the fix (identity env),
  # nf is idempotent and the assay is green. See
  # docs/superpowers/reports/2026-07-04-antigen-nf-nonidempotence-finding.md.
  test "regression: the once-oscillating Pi challenge now normalizes idempotently" do
    {payload, _} = Code.eval_file("test/antigen/fixtures/nf_oscillation_pi.exs")
    c = Challenge.new(kind: :typed_term, assay: "term/normalization", label: :well_typed, payload: payload)
    assert A.run(c) == :ok
    env = SigMenu.env_of(:v1)
    ctx = SigMenu.rebuild_context(env, payload.ctx)
    assert {:ok, _} = Cure.Core.Kernel.infer(ctx, payload.term)
    nf1 = Cure.Core.Normalise.nf(ctx, payload.term, fuel: 500_000)
    assert Cure.Core.Normalise.nf(ctx, nf1, fuel: 500_000) == nf1, "nf must be a fixpoint now"
  end

  test "a deliberately ill-typed :typed_term is caught (mechanism check)" do
    # hand-break the claim: term {:var,0} but empty context → infer fails
    bad =
      Challenge.new(
        kind: :typed_term,
        assay: "term/infer_check",
        label: :well_typed,
        payload: %{sig: :v1, ctx: [], type: SigMenu.nat(), term: {:var, 0}}
      )

    assert {:violation, {:infer_failed, _}} = A.run(bad)
  end
end

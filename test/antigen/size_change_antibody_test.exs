defmodule Antigen.SizeChangeAntibodyTest do
  @moduledoc """
  Size-change termination antibody (#14). Guards the size-change certification
  added to trusted direct-call extraction and the proof-carrying closure path on both
  sides of the LJB principle, using the totality assay (oracle = known label):

    * REACH (must-eventually-accept): single-function, multi-argument lexicographic
      recursion — Ackermann — where NO single fixed argument position decreases at
      every self-call. Rejected by the old fixed-position guard; certified now via
      the change-matrix closure + reconstruct-equal (the inner call's first arg
      `S m'` is a rebuilt constructor that reconstructs the matched pattern, so it
      is size-`:equal` to the parameter). If reconstruct-equal regressed, Ackermann
      would fail to certify and this antibody goes red.

    * CONTROL (must-reject): single-function, multi-argument non-total recursion —
      `loop a b = loop (S a) (S b)` — whose parameters are UNMATCHED, so no
      reconstruction exists to fire on. Every arc is `:unknown`, the sole idempotent
      loop lacks a `:smaller` diagonal, and the def is soundly rejected. If
      reconstruct-equal ever fired on an unmatched param (a soundness infection),
      this loop would be wrongly certified and this antibody goes red.

  Direct-assertion antibody (cf. `certify_hardening_antibody_test.exs`): the assay
  IS the oracle check — `:ok` iff the certifier's verdict matches the by-construction
  label.
  """
  use ExUnit.Case, async: true

  alias Antigen.Assays.Totality, as: Assay
  alias Antigen.Generators.Totality

  test "REACH: Ackermann (lexicographic, single-function) now certifies total" do
    challenge = Totality.wellfounded_ackermann()
    assert challenge.label == :terminating
    # :ok ⇒ the certifier certifies every focus def, i.e. the reach flipped.
    assert :ok == Assay.run(challenge),
           "Ackermann must certify total under size-change + reconstruct-equal"
  end

  test "CONTROL: loop a b = loop (S a) (S b) is rejected (non-total multi-arg)" do
    challenge = Totality.diverging_size_change_control()
    assert challenge.label == :diverging
    # :ok ⇒ the certifier certifies NONE of the focus defs, i.e. loop stays rejected.
    assert :ok == Assay.run(challenge),
           "the non-total multi-arg control must NOT be certified"
  end

  test "CONTROL is rejected precisely because reconstruct-equal does not fire on unmatched params" do
    # The parameters a, b are never matched, so `S a` / `S b` reconstruct no
    # tracked pattern form — every change-matrix arc is :unknown, giving an
    # all-unknown idempotent loop with no :smaller diagonal.
    env = Totality.env_of(Totality.diverging_size_change_control())
    refute Cure.Elab.TotalityClosure.provably_total?(env, :loop)
  end

  # -- Cross-function / mutual size-change (#13) ------------------------------
  #
  # Generalises the LJB principle from self-calls to intra-SCC calls. Same two
  # sides of the criterion, now across the call boundary.

  test "MUTUAL REACH: well-founded even/odd pair now certifies total (#13)" do
    challenge = Totality.wellfounded_even_odd()
    assert challenge.label == :terminating
    # :ok ⇒ the certifier certifies every focus def — the cross-function reach flipped.
    assert :ok == Assay.run(challenge),
           "even/odd must certify total under cross-function size-change"
  end

  test "MUTUAL REACH: permuted pair (descent only across the swap) now certifies total (#13)" do
    challenge = Totality.wellfounded_permuted_pair()
    assert challenge.label == :terminating

    assert :ok == Assay.run(challenge),
           "the permuted well-founded pair must certify total under cross-function size-change"
  end

  test "MUTUAL CONTROL (d13d718 antibody): diverging f→g→f pair stays rejected (#13)" do
    # The permanent regression guard for the once-live mutual-recursion hole. It
    # is now rejected by the size-change criterion ITSELF, not a blanket
    # short-circuit: the composed f→g→f change matrix is the all-`:equal`
    # identity — an idempotent endo-edge with no `:smaller` diagonal.
    challenge = Totality.diverging_mutual_pair()
    assert challenge.label == :diverging
    # :ok ⇒ the certifier certifies NONE of the focus defs (soundness preserved).
    assert :ok == Assay.run(challenge),
           "the diverging mutual pair must NOT be certified (d13d718 must stay green)"
  end

  test "MUTUAL CONTROL: one-leg pair stays rejected — composition, not per-call, decides (#13)" do
    # f decreases (f→g on the S-predecessor), g regrows (g→f on `S n`); the
    # COMPOSED f→g→f cycle is non-decreasing (`:unknown` diagonal). LJB's
    # motivating case: certification must consider cycle composition.
    challenge = Totality.diverging_one_leg_pair()
    assert challenge.label == :diverging

    assert :ok == Assay.run(challenge),
           "the one-leg mutual pair must NOT be certified (composed cycle non-decreasing)"
  end
end

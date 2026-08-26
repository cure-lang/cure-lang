defmodule Antigen.TotalityPendingSiblingAntibodyTest do
  @moduledoc """
  Antigen antibody for the premature totality-certification finding: an earlier
  member of a mutual cycle must NOT be certified while a sibling's body is still an
  elaborator `{:hole, "__pending__"}` placeholder. `Certificate.mutual_group`
  reconstructs the SCC from sibling bodies read out of the env; a pending sibling
  has no visible callees, so the SCC of the earlier member collapses to a singleton
  and the size-change check certifies it as non-recursive — a false certificate,
  which is δ-transparent.

  Antigen's totality vertical missed this because its `env_of` always rebuilt a
  COMPLETE env (every def's real body present), the one state in which the SCC is
  fully visible and the divergent pair is correctly rejected. The pending-sibling
  env state — the mid-body_pass reality — was never constructed. `pending: [:g]`
  in the payload (honoured by `env_of`) closes that gap.

  Obligations:
    * DISCRIMINATION — with `g` pending, component certification leaves `f`
      `false` (deferred); the pre-fix certifier returned `true` here (guarded by
      `mutual_cycle_pending_cert_test`). With BOTH bodies present the same pair is
      also rejected (the mutual check), so the antibody isolates the pending state.
    * ASSAY — the totality `:diverging` assay replays the probe to `:ok` (`f` is not
      wrongly certified).
  """
  use ExUnit.Case, async: true
  alias Antigen.Assays.Totality, as: Assay
  alias Antigen.Generators.Totality, as: Gen
  alias Cure.Core.Env

  test "env_of registers the pending sibling as a hole and keeps the focus body real" do
    c = Gen.diverging_pending_sibling()
    env = Gen.env_of(c)

    assert %{body: {:hole, "__pending__"}} = Env.get_def(env, :g)
    assert %{body: {:lam, _g, _, _}} = Env.get_def(env, :f)
  end

  test "the certifier DEFERS f while g is pending (does not certify)" do
    c = Gen.diverging_pending_sibling()
    env = Gen.env_of(c)

    refute Cure.Elab.TotalityClosure.provably_total?(env, :f),
           "f must not be certified while sibling g is a pending placeholder"
  end

  test "the pending-sibling antibody replays :ok through the totality assay" do
    c = Gen.diverging_pending_sibling()
    assert c.label == :diverging
    assert c.payload.pending == [:g]
    assert :ok == Assay.run(c)
  end
end

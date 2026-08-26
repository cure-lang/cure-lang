defmodule Antigen.Assays.InductiveEnvTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.InductiveEnv, as: A
  alias Antigen.Challenge
  alias Cure.Core.Inductive

  defp canonical_ctor(result_indices) do
    Inductive.ctor(
      :antigenA,
      [{:x, {:var, 0}}, {:y, {:var, 1}}],
      result_indices,
      [:erased, :unrestricted],
      [{:var, 2}]
    )
  end

  defp canonical_family, do: Inductive.family(:AntigenEnv, [{:a, {:type, 0}}], [{:n, {:data, :Int, [], []}}], 0)

  defp canonical_challenge(result_indices \\ [{:int_lit, 3}]) do
    Challenge.new(
      kind: :family,
      assay: "inductive/env_roundtrip",
      label: :well_typed,
      payload: %{family: canonical_family(), ctors: [canonical_ctor(result_indices)]}
    )
  end

  test "the canonical well-typed shape passes every property (kernel soundness, roundtrip, " <>
         "negative space, legacy back-compat, register_builtin invariant)" do
    assert A.run(canonical_challenge()) == :ok
  end

  test "a genuinely ill-typed declaration mislabeled :well_typed is caught by the kernel-" <>
         "soundness check (not silently accepted by the accessor layer)" do
    # 2 result indices against a 1-index family telescope — real arity mismatch, not
    # a constructed accessor bug — Kernel.check_ctor must reject it.
    bad = canonical_challenge([{:int_lit, 1}, {:int_lit, 2}])
    assert {:violation, {:wrongly_rejected, :AntigenEnv, _reason}} = A.run(bad)
  end
end

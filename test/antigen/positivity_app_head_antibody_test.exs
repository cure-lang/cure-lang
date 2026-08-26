defmodule Antigen.PositivityAppHeadAntibodyTest do
  @moduledoc """
  Antigen antibody for finding S8: the strict-positivity checker's catch-all
  (`strictly_positive?/4` last clause) must reject an occurrence of the subject in
  a ctor field type whose HEAD is neither `pi` nor `data` — i.e. an application
  (`Fp Pgen`) or a lambda (`λ_. Pgen`). The pre-S8 catch-all returned `true`
  unconditionally (fail-open), admitting such a family unsoundly.

  Antigen missed S8 because the positivity generator only ever built field types
  headed by `pi`/`data`/`Sigma` — never an `:app`/`:lam` head — so the catch-all
  was never exercised with the subject present. These constructors close that gap.

  Two obligations:
    * ORACLE: the real `Inductive.positive?` rejects the app/lam-headed negatives
      and accepts the subject-free app-headed positive.
    * DISCRIMINATION: run the negatives through the positivity assay against a
      FAIL-OPEN kernel op (`positive?: fn _,_ -> :ok end`, exactly the pre-S8
      catch-all) via the assay's sensitivity seam — the assay must raise
      `{:wrongly_accepted, …}`. This is the violation Antigen would have reported.
  """
  use ExUnit.Case, async: true
  alias Antigen.Assays.Positivity, as: Assay
  alias Antigen.Generators.Positivity, as: Gen
  alias Cure.Core.Inductive

  # The pre-S8 catch-all: accept every family regardless of occurrence.
  defp fail_open, do: %{positive?: fn _env, _fam -> :ok end}

  defp oracle(c) do
    env = Gen.env_of(c)
    Inductive.positive?(env, Inductive.get_family(env, c.payload.family.name))
  end

  test "the real oracle rejects the app/lam-headed negatives" do
    for c <- [Gen.app_head_negative(), Gen.lam_head_negative()] do
      assert c.label == :negative
      assert {:error, {:non_strictly_positive, _}} = oracle(c), "oracle should reject #{c.note}"
    end
  end

  test "the real oracle admits the subject-free app-headed positive (no over-correction)" do
    c = Gen.app_head_positive()
    assert c.label == :positive
    assert :ok == oracle(c)
  end

  test "a fail-open catch-all (the pre-S8 kernel) is caught as :wrongly_accepted" do
    for c <- [Gen.app_head_negative(), Gen.lam_head_negative()] do
      assert {:violation, {:wrongly_accepted, :Pgen}} = Assay.run(c, fail_open()),
             "assay must flag a fail-open kernel on #{c.note}"
    end
  end

  test "against the real (fixed) kernel these negatives replay :ok" do
    for c <- [Gen.app_head_negative(), Gen.lam_head_negative(), Gen.app_head_positive()] do
      assert :ok == Assay.run(c), "fixed kernel should agree with the label for #{c.note}"
    end
  end
end

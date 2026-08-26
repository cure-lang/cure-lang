defmodule Antigen.Generators.InductiveEnvTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.InductiveEnv
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Challenge, Assays}

  @sample 100

  test "every sampled challenge is a :family env-roundtrip probe the assay accepts" do
    for %Challenge{} = c <- B.interp(InductiveEnv.gen()) |> Enum.take(@sample) do
      assert c.kind == :family
      assert c.assay == "inductive/env_roundtrip"
      assert c.label == :well_typed

      assert Assays.InductiveEnv.run(c) == :ok,
             "assay rejected #{inspect(c.payload)}"
    end
  end

  test "the shape is a parameterized, Int-indexed family with a two-field mixed-quantity ctor" do
    for %Challenge{payload: %{family: fam, ctors: [ctor]}} <-
          B.interp(InductiveEnv.gen()) |> Enum.take(20) do
      assert fam.name == :AntigenEnv
      assert fam.params == [{:a, {:type, 0}}]
      assert fam.indices == [{:n, {:data, :Int, [], []}}]
      assert fam.level == 0

      assert ctor.name == :antigenA
      assert ctor.args == [{:x, {:var, 0}}, {:y, {:var, 1}}]
      assert ctor.quantities == [:erased, :unrestricted]
      assert ctor.result_params == [{:var, 2}]
      assert match?([{:int_lit, _}], ctor.result_indices)
    end
  end

  test "the result-index literal varies across draws (not a constant shape)" do
    values =
      B.interp(InductiveEnv.gen())
      |> Enum.take(50)
      |> Enum.map(fn %Challenge{payload: %{ctors: [%{result_indices: [{:int_lit, n}]}]}} -> n end)
      |> Enum.uniq()

    assert length(values) > 1
  end
end

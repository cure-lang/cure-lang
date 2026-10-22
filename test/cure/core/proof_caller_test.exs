defmodule Cure.Core.ProofCallerTest do
  @moduledoc """
  Caller data production, not semantic Context extraction or admission.
  Agda checks the generated caller against the literal source/certificate.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.ProofRecipe
  alias Cure.Test.{ProofBundleFixture, ProofCallerFixture}

  @artifact Path.expand("../../..", __DIR__) <> "/proof/Fixtures/ExecutableCaller.agda"

  test "the literal dependent caller artifact is reproducible" do
    assert {:ok, generated} = ProofCallerFixture.to_agda()
    assert generated == File.read!(@artifact)

    assert {:ok, characters} = ProofRecipe.encode_caller(ProofCallerFixture.request(), ProofBundleFixture.table())
    assert String.starts_with?(characters, "(" <> String.duplicate("1", 19) <> ";")
  end

  test "exact caller tuple and binder shapes are required" do
    for caller <- [
          {:caller},
          {:caller, [], [], [], [], {:var, 0}, {:var, 1}, :r_leaf},
          {:caller, [{"A", {:type, 0}, :extra}], [], [], [], {:var, 0}, {:var, 1}, :r_leaf, :r_leaf},
          {:caller, [fn -> {"A", {:type, 0}} end], [], [], [], {:var, 0}, {:var, 1}, :r_leaf, :r_leaf},
          %{}
        ] do
      assert {:error, {:malformed_recipe, _kind, _value}} =
               ProofRecipe.encode_caller(caller, ProofBundleFixture.table())
    end
  end

  test "improper caller vectors and invalid binder identities return errors" do
    for caller <- [
          {:caller, [{"A", {:type, 0}} | :improper], [], [], [], {:var, 0}, {:var, 1}, :r_leaf, :r_leaf},
          {:caller, [], [:r_leaf | :improper], [], [], {:var, 0}, {:var, 1}, :r_leaf, :r_leaf},
          {:caller, [], [], [{:atom_type} | :improper], [], {:var, 0}, {:var, 1}, :r_leaf, :r_leaf},
          {:caller, [{42, {:type, 0}}], [], [], [], {:var, 0}, {:var, 1}, :r_leaf, :r_leaf}
        ] do
      assert {:error, {:malformed_recipe, _kind, _value}} =
               ProofRecipe.encode_caller(caller, ProofBundleFixture.table())
    end
  end

  test "caller table, term payload and unknown-name errors propagate" do
    assert {:error, {:malformed_table, _table}} =
             ProofRecipe.encode_caller(ProofCallerFixture.request(), ["" | :improper])

    assert {:error, {:unknown_name, "A"}} = ProofRecipe.encode_caller(ProofCallerFixture.request(), [""])

    assert {:error, {:unsupported_term, {:float_lit, 0.5}}} =
             ProofRecipe.encode_caller(
               {:caller, [], [], [{:float_lit, 0.5}], [], {:atom_type}, {:type, 0}, :r_leaf, :r_leaf},
               ProofBundleFixture.table()
             )
  end

  test "production does not assert caller typing or exact vector alignment" do
    # A structurally valid but ill-typed/escaped request is still DATA.
    # Independent caller replay, not this encoder, rejects it.
    assert {:ok, _characters} =
             ProofRecipe.encode_caller(
               {:caller, [], [], [], [], {:var, 0}, {:type, 2}, :r_leaf, :r_leaf},
               ProofBundleFixture.table()
             )
  end
end

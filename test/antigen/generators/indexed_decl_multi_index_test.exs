defmodule Antigen.Generators.IndexedDeclMultiIndexTest do
  @moduledoc """
  Regression for the constructor-declaration de Bruijn seeding bug: a Type-
  parametrized family whose constructor's generalized field is repeated across
  ≥2 index positions (each index type referencing the parameter) was wrongly
  rejected by `check_result_indices` — `do_spine` seeded an empty evaluation
  environment, so the second index's parameter reference `{:var, 1}` mis-levelled
  to a bogus neutral (`{:conversion_failure, {:var, 1}, {:var, 0}}`). The three
  variants below pin the trigger to the (Type param ∧ var repeated across ≥2
  indices) conjunction.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}

  defp check_ctor_decl(fam, ctor) do
    env = Inductive.declare(Env.empty(), fam, [ctor])
    with :ok <- Kernel.check_family(env, fam), do: Kernel.check_ctor(env, fam, ctor)
  end

  test "V1: Type param, generalized var used in ONE index → accepted" do
    fam = Inductive.family(:MyEq2, [{:a, {:type, 0}}], [{:x, {:var, 0}}], 0)
    ctor = Inductive.ctor(:mrefl2, [{:w, {:var, 0}}], [{:var, 0}], [:many], [{:var, 1}])
    assert check_ctor_decl(fam, ctor) == :ok
  end

  test "V2: NO Type param, generalized var repeated across TWO indices → accepted" do
    fam = Inductive.family(:Pair2, [], [{:x, {:int_type}}, {:y, {:int_type}}], 0)
    ctor = Inductive.ctor(:same2, [{:w, {:int_type}}], [{:var, 0}, {:var, 0}], [:many], [])
    assert check_ctor_decl(fam, ctor) == :ok
  end

  test "V3: Type param AND var repeated across TWO indices → accepted (the bug)" do
    # index telescope types both reference the param `a`: x:a = {:var,0}, y:a =
    # {:var,1} (a shifted past x). The ctor's single field w:a is written into
    # both result-index positions.
    fam = Inductive.family(:MyEq3, [{:a, {:type, 0}}], [{:x, {:var, 0}}, {:y, {:var, 1}}], 0)
    ctor = Inductive.ctor(:mrefl3, [{:w, {:var, 0}}], [{:var, 0}, {:var, 0}], [:many], [{:var, 1}])
    assert check_ctor_decl(fam, ctor) == :ok
  end

  test "V4: Type param, var repeated across THREE indices → accepted" do
    fam =
      Inductive.family(:MyEq4, [{:a, {:type, 0}}], [{:x, {:var, 0}}, {:y, {:var, 1}}, {:z, {:var, 2}}], 0)

    ctor =
      Inductive.ctor(:mrefl4, [{:w, {:var, 0}}], [{:var, 0}, {:var, 0}, {:var, 0}], [:many], [{:var, 1}])

    assert check_ctor_decl(fam, ctor) == :ok
  end
end

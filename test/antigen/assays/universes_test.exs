defmodule Antigen.Assays.UniversesTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Universes, as: A
  alias Antigen.Generators.Universes, as: G

  test "Type 0 : Type 0 is rejected (no Type-in-Type)" do
    assert :ok == A.run(G.type_in_type(:ill_typed))
  end

  test "a def cannot be annotated AT the ceiling (Type 2 has no sort)" do
    assert :ok == A.run(G.ceiling(:ill_typed))
  end

  test "cumulativity: Nat : Type 0 is accepted at Type 1" do
    assert :ok == A.run(G.cumulativity(:well_typed))
  end

  test "stratification: Type 0 : Type 1 is accepted" do
    assert :ok == A.run(G.stratification(:well_typed))
  end

  test "two-universe ctor-field rule: a Type-0 field does not fit a level-0 family" do
    assert :ok == A.run(G.ctor_field(:ill_typed))
  end

  test "two-universe ctor-field rule: a Type-0 field fits a level-1 family" do
    assert :ok == A.run(G.ctor_field(:well_typed))
  end
end

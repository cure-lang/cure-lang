defmodule Antigen.Assays.UniversesTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Universes, as: A
  alias Antigen.Generators.Universes, as: G
  alias Antigen.Corpus
  alias Cure.Core.Kernel

  @levels [0, 37, 10 ** 40]

  test "Type 0 : Type 0 is rejected (no Type-in-Type)" do
    assert :ok == A.run(G.type_in_type(:ill_typed))
  end

  test "finite universes have successors but never inhabit themselves" do
    for level <- @levels, label <- [:well_typed, :ill_typed] do
      challenge = G.finite_successor(label, level)
      assert :ok = A.run(challenge)
      assert {:ok, replayed} = challenge |> Corpus.encode_record() |> Corpus.decode_record()
      assert :ok = A.run(replayed)
    end
  end

  test "the finite self-inhabitation antibody detects omitted definition checking" do
    for level <- @levels do
      assert {:violation, {:wrongly_accepted, :u}} =
               A.run(G.finite_successor(:ill_typed, level), %{check_def: fn _, _ -> :ok end})
    end
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

  test "constructor fields retain predicativity at arbitrary finite levels" do
    for level <- @levels, label <- [:well_typed, :ill_typed] do
      challenge = G.ctor_field(label, level)
      assert :ok = A.run(challenge)
      assert {:ok, replayed} = challenge |> Corpus.encode_record() |> Corpus.decode_record()
      assert :ok = A.run(replayed)
    end
  end

  test "omitting constructor checking cannot pass the field predicativity antibody" do
    operations = %{check_family: &Kernel.check_family/2, check_ctor: fn _, _, _ -> :ok end}

    for level <- @levels do
      assert :ok = A.run(G.ctor_field(:well_typed, level), operations)
      assert {:violation, {:wrongly_accepted, :Foo}} = A.run(G.ctor_field(:ill_typed, level), operations)
    end
  end
end

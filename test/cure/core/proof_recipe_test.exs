defmodule Cure.Core.ProofRecipeTest do
  @moduledoc """
  Data-production regressions, not kernel-acceptance or extraction theorems.
  Agda separately checks the generated complete certificate's literal bytes.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.ProofRecipe
  alias Cure.Test.ProofRecipeFixture

  @table ["", "a"]
  @leaf [0]
  @term [18, 0, 0]
  @artifact Path.expand("../../..", __DIR__) <> "/proof/Fixtures/ExecutableCertificate.agda"

  test "all conversion constructors use their own exact tags and argument groups" do
    vectors = [
      {:c_refl, [0]},
      {{:c_sym, :c_refl}, [1, @leaf]},
      {{:c_trans, {:atom_type}, :c_refl, :c_beta}, [2, @term, @leaf, [10]]},
      {{:c_pi, :c_refl, :c_refl}, [3, @leaf, @leaf]},
      {{:c_app, :c_refl, :c_refl}, [4, @leaf, @leaf]},
      {{:c_data, [:c_refl], [:c_beta]}, [5, [@leaf], [[10]]]},
      {{:c_ctor, [:c_refl]}, [6, [@leaf]]},
      {{:c_effect_type, :c_refl}, [7, @leaf]},
      {{:c_effect_pure, :c_refl}, [8, @leaf]},
      {{:c_effect_bind, :c_refl, :c_refl}, [9, @leaf, @leaf]},
      {:c_beta, [10]},
      {:c_zeta, [11]},
      {{:c_delta, :a}, [12, 1]},
      {:c_nat_zero, [13]},
      {:c_bounded_zero, [14]},
      {:c_nat_suc, [15]},
      {:c_bounded_suc, [16]}
    ]

    for {recipe, node} <- vectors do
      assert {:ok, characters} = ProofRecipe.encode_conversion(recipe, @table)
      assert characters == wire(node)
    end
  end

  test "all ordinary constructors preserve nested vectors, term witnesses and branch pairs" do
    vectors = [
      {:r_leaf, [0]},
      {{:r_pi, :r_leaf, :r_leaf}, [1, @leaf, @leaf]},
      {{:r_lam, :r_leaf, :r_leaf}, [2, @leaf, @leaf]},
      {{:r_app, :r_leaf, :r_leaf}, [3, @leaf, @leaf]},
      {{:r_let, :r_leaf, :r_leaf, :r_leaf}, [4, @leaf, @leaf, @leaf]},
      {{:r_data, [:r_leaf], []}, [5, [@leaf], []]},
      {{:r_ctor, [{:atom_type}], [:r_leaf], [:r_leaf]}, [6, [@term], [@leaf], [@leaf]]},
      {{:r_claim, {:atom_type}, :r_leaf}, [7, @term, @leaf]},
      {{:r_cumul, 2, :r_leaf}, [8, 2, @leaf]},
      {{:r_convert, {:atom_type}, :c_refl, :r_leaf}, [9, @term, @leaf, @leaf]},
      {{:r_case, :r_leaf, [], [:r_leaf], 0, :r_leaf, :r_leaf, [{[:r_leaf], :r_leaf}]},
       [10, @leaf, [], [@leaf], 0, @leaf, @leaf, [[[@leaf], @leaf]]]}
    ]

    for {recipe, node} <- vectors do
      assert {:ok, characters} = ProofRecipe.encode_recipe(recipe, @table)
      assert characters == wire(node)
    end

    assert {:ok, "(;)"} = ProofRecipe.encode_recipe(:r_leaf, [])
    assert {:ok, "(" <> _rest} = ProofRecipe.encode_conversion(:c_beta, [])
  end

  test "container vectors retain order and absent bodies differ from present bodies" do
    constructor = {:constructor_recipe, [:r_leaf], [], [], [:r_leaf]}
    family = {:family_recipe, [], [:r_leaf], [constructor]}
    packet = {:packet, :r_leaf, :r_leaf}

    assert {:ok, absent} = ProofRecipe.encode_packet({:packet, :r_leaf, nil}, [])
    assert absent == wire([11, @leaf, []])
    assert {:ok, present} = ProofRecipe.encode_packet(packet, [])
    assert present == wire([11, @leaf, [@leaf]])
    refute absent == present
    assert {:ok, ctor} = ProofRecipe.encode_constructor(constructor, [])
    assert ctor == wire([12, [@leaf], [], [], [@leaf]])
    assert {:ok, fam} = ProofRecipe.encode_family(family, [])
    assert fam == wire([13, [], [@leaf], [[12, [@leaf], [], [], [@leaf]]]])
    assert {:ok, complete} = ProofRecipe.encode_certificate({:certificate, [family], [packet]}, [])
    assert complete == wire([14, [[13, [], [@leaf], [[12, [@leaf], [], [], [@leaf]]]]], [[11, @leaf, [@leaf]]]])
  end

  test "all entry points validate the whole table before producing data" do
    for {encoder, value} <- [
          {&ProofRecipe.encode_conversion/2, :c_refl},
          {&ProofRecipe.encode_recipe/2, :r_leaf},
          {&ProofRecipe.encode_packet/2, {:packet, :r_leaf, nil}},
          {&ProofRecipe.encode_constructor/2, {:constructor_recipe, [], [], [], []}},
          {&ProofRecipe.encode_family/2, {:family_recipe, [], [], []}},
          {&ProofRecipe.encode_certificate/2, {:certificate, [], []}}
        ],
        table <- [42, ["a", 42], ["a", <<255>>], ["a" | :improper]] do
      assert {:error, {:malformed_table, ^table}} = encoder.(value, table)
    end
  end

  test "malformed tuples and cross-namespace recipes fail rather than defaulting" do
    for recipe <- [
          :unknown,
          :c_beta,
          {:r_leaf},
          {:r_pi, :r_leaf},
          {:r_lam, :r_leaf, :r_leaf, :surplus},
          {:r_claim, {:atom_type}},
          {:r_convert, {:atom_type}, :r_leaf, :r_leaf},
          {:r_case, :r_leaf, [], [], 0, :r_leaf, :r_leaf},
          {:node, 0, 0, 0, []},
          fn -> :r_leaf end
        ] do
      assert {:error, {:malformed_recipe, _kind, _value}} = ProofRecipe.encode_recipe(recipe, @table)
    end

    assert {:error, {:malformed_recipe, :conversion, :r_leaf}} =
             ProofRecipe.encode_conversion(:r_leaf, @table)
  end

  test "invalid levels and improper nested vectors return structured errors" do
    for level <- [-1, 3, 1.0, :l0] do
      assert {:error, {:malformed_recipe, :level, ^level}} =
               ProofRecipe.encode_recipe({:r_cumul, level, :r_leaf}, @table)

      assert {:error, {:malformed_recipe, :level, ^level}} =
               ProofRecipe.encode_recipe({:r_case, :r_leaf, [], [], level, :r_leaf, :r_leaf, []}, @table)
    end

    for recipe <- [
          {:r_data, [:r_leaf | :improper], []},
          {:r_ctor, [{:atom_type} | :improper], [], []},
          {:r_case, :r_leaf, [], [], 0, :r_leaf, :r_leaf, [{[], :r_leaf} | :improper]},
          {:r_case, :r_leaf, [], [], 0, :r_leaf, :r_leaf, [{[:r_leaf | :improper], :r_leaf}]},
          {:r_case, :r_leaf, [], [], 0, :r_leaf, :r_leaf, [{[], :r_leaf, :surplus}]}
        ] do
      assert {:error, {:malformed_recipe, _kind, _value}} = ProofRecipe.encode_recipe(recipe, @table)
    end
  end

  test "container arity and body errors cannot be silently omitted" do
    for {encoder, value} <- [
          {&ProofRecipe.encode_packet/2, {:packet, :r_leaf, []}},
          {&ProofRecipe.encode_packet/2, {:packet, :r_leaf}},
          {&ProofRecipe.encode_constructor/2, {:constructor_recipe, [], [], []}},
          {&ProofRecipe.encode_family/2, {:family_recipe, [], [], [:r_leaf]}},
          {&ProofRecipe.encode_certificate/2, {:certificate, [], [{:packet, :r_leaf, nil} | :improper]}}
        ] do
      assert {:error, {:malformed_recipe, _kind, _value}} = encoder.(value, @table)
    end
  end

  test "term payload exclusions and missing names propagate through recipes" do
    assert {:error, {:unsupported_term, {:float_lit, 0.5}}} =
             ProofRecipe.encode_recipe({:r_claim, {:float_lit, 0.5}, :r_leaf}, @table)

    assert {:error, {:malformed_term, {:type, 3}}} =
             ProofRecipe.encode_conversion({:c_trans, {:type, 3}, :c_refl, :c_refl}, @table)

    assert {:error, {:unknown_name, "missing"}} =
             ProofRecipe.encode_recipe({:r_claim, {:global, :missing}, :r_leaf}, @table)

    assert {:error, {:unknown_name, :missing}} = ProofRecipe.encode_conversion({:c_delta, :missing}, @table)

    assert {:error, {:malformed_recipe, :conversion, _value}} =
             ProofRecipe.encode_conversion({:c_delta, <<255>>}, @table)

    assert ProofRecipe.encode_conversion({:c_delta, :a}, @table) ==
             ProofRecipe.encode_conversion({:c_delta, "a"}, @table)
  end

  test "the complete literal Agda artifact is byte-for-byte reproducible" do
    assert {:ok, generated} = ProofRecipeFixture.to_agda()
    assert generated == File.read!(@artifact)
    assert {:certificate, [_family], [_answer, _held, _packed, _unpack]} = ProofRecipeFixture.certificate()
  end

  defp wire(number) when is_integer(number), do: String.duplicate("1", number) <> ";"
  defp wire(children) when is_list(children), do: "(" <> Enum.map_join(children, &wire/1) <> ")"
end

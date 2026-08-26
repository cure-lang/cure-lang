defmodule Antigen.Generators.IndexedDeclTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.IndexedDecl
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Challenge, Assays}

  @sample 500

  test "every sampled challenge is a :family universes probe the assay judges :ok" do
    for %Challenge{} = c <- B.interp(IndexedDecl.gen()) |> Enum.take(@sample) do
      assert c.kind == :family
      assert c.assay == "universes"
      assert c.label in [:well_typed, :ill_typed]
      # the known-label oracle must agree with the kernel (well_typed accepted,
      # ill_typed rejected) — a self-consistency guard on the generator.
      assert Assays.Universes.run(c) == :ok,
             "oracle disagreed on #{inspect(c.payload.ctors)} (#{c.label})"
    end
  end

  test "the sample covers the success path and both ill-typed rejection paths" do
    sample = B.interp(IndexedDecl.gen()) |> Enum.take(@sample)
    ctor_index = fn c -> hd(c.payload.ctors).result_indices end

    # well-typed: a single matching-type literal result index → check_result_indices success
    assert Enum.any?(sample, fn c ->
             c.label == :well_typed and match?([{lit, _}] when lit in [:int_lit, :float_lit], ctor_index.(c))
           end)

    # ill-typed by wrong result-index arity (0 or 2 indices vs the 1-index telescope)
    assert Enum.any?(sample, fn c -> c.label == :ill_typed and length(ctor_index.(c)) != 1 end)

    # ill-typed by wrong literal TYPE (single index, but mismatched against the telescope)
    assert Enum.any?(sample, fn c -> c.label == :ill_typed and length(ctor_index.(c)) == 1 end)

    # both index-type families appear
    assert Enum.any?(sample, fn c -> hd(c.payload.family.indices) == {:n, {:data, :Int, [], []}} end)
    assert Enum.any?(sample, fn c -> hd(c.payload.family.indices) == {:n, {:float_type}} end)

    # an arg-bearing ctor (non-empty field telescope) → check_ctor_args
    assert Enum.any?(sample, fn c -> hd(c.payload.ctors).args != [] end)

    # a parameterized family (non-empty param telescope) → check_uniform_params,
    # including a non-uniform (ill_typed) instance
    assert Enum.any?(sample, fn c -> c.payload.family.params != [] end)
    assert Enum.any?(sample, fn c -> c.payload.family.params != [] and c.label == :ill_typed end)

    # the dependent-index family: a Type param AND ≥2 index positions whose types
    # reference that param → check_result_indices' parameter-seeding path (the
    # dp01/dp02 datatype shape). Every such challenge is :well_typed (the self-
    # consistency test above already asserts the kernel accepts it).
    assert Enum.any?(sample, fn c ->
             c.payload.family.name == :MyEqK and
               length(c.payload.family.indices) >= 2 and
               Enum.all?(c.payload.family.indices, fn {_n, t} -> match?({:var, _}, t) end) and
               c.label == :well_typed
           end)
  end
end

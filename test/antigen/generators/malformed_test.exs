defmodule Antigen.Generators.MalformedTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Malformed
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Challenge, Assays}

  @sample 500

  test "every sampled malformed term is rejected by the kernel (assay :ok)" do
    for %Challenge{} = c <- B.interp(Malformed.gen()) |> Enum.take(@sample) do
      assert c.kind == :malformed
      assert c.assay == "term/rejection"
      assert c.label == :ill_typed

      assert Assays.Malformed.run(c) == :ok,
             "kernel accepted a malformed term: #{inspect(c.payload.term)}"
    end
  end

  test "the sample covers every malformation family" do
    sample = B.interp(Malformed.gen()) |> Enum.take(@sample)
    heads = MapSet.new(sample, fn c -> elem(c.payload.term, 0) end)

    # :rewrite retired (Phase C): the ill-typed transport shapes now carry an
    # :app head (J/subst case-transport applications).
    for h <- [:absurd, :global, :data, :ctor, :case, :app] do
      assert h in heads, "missing malformation family: #{h}"
    end

    # A canonical bare finite universe is valid, not a rejection family. Its
    # obsolete ceiling cell is replaced by a predicative application failure.
    # Require every named semantic cell, a stronger check than head tags alone.
    cells = MapSet.new(sample, & &1.cover_tag)

    for {"term/rejection", cell} <- Malformed.cover_cells() do
      assert MapSet.member?(cells, cell), "missing malformation cell: #{cell}"
    end
  end
end

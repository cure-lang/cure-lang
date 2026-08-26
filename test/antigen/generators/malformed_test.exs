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
    for h <- [:absurd, :global, :data, :ctor, :case, :app, :type] do
      assert h in heads, "missing malformation family: #{h}"
    end
  end
end

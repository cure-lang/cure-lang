defmodule Antigen.Generators.SerializationTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Serialization
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Challenge, Assays}
  alias Cure.Core.Term

  @sample 1000

  test "every generated term is well-formed and roundtrips losslessly" do
    for %Challenge{} = c <- B.interp(Serialization.gen()) |> Enum.take(@sample) do
      assert c.kind == :serialize
      assert Term.term?(c.payload.term), "not a valid term: #{inspect(c.payload.term)}"
      assert Assays.Serialization.run(c) == :ok, "roundtrip failed: #{inspect(c.payload.term)}"
    end
  end

  test "the sample spans the full range of serialisable shapes" do
    heads =
      B.interp(Serialization.gen())
      |> Enum.take(@sample)
      |> MapSet.new(fn c -> elem(c.payload.term, 0) end)

    # (:eq/:refl/:rewrite retired with the primitive identity forms, Phase C;
    # :sigma/:pair/:fst/:snd retired with the primitive Sigma, D2; :prim retired
    # with the builtin-op globals, K2 — those spellings serialize through the
    # :data/:ctor/:case/:app shapes.)
    for h <- [:pi, :lam, :app, :data, :ctor, :case, :type, :var, :int_lit, :float_lit, :global] do
      assert h in heads, "missing serialisable shape: #{h}"
    end
  end
end

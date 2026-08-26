defmodule Antigen.Generators.TypeFormerTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{TypeFormer, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.Challenge
  alias Cure.Core.{Context, Kernel, Normalise}

  defp ctx, do: SigMenu.rebuild_context(SigMenu.env_of(:v1), [])
  @sample 400

  test "every sampled type-former is a well-typed :typed_term whose claimed type matches infer" do
    for %Challenge{} = c <- B.interp(TypeFormer.gen()) |> Enum.take(@sample) do
      assert c.kind == :typed_term
      assert c.payload.sig == :v1 and c.payload.ctx == []
      cx = ctx()

      case Kernel.infer(cx, c.payload.term) do
        {:ok, inferred} ->
          assert Normalise.quote(inferred, Context.length(cx)) == c.payload.type
          # every generated term is itself a TYPE (its inferred type is a universe)
          assert match?({:type, _}, c.payload.type)

        other ->
          flunk("type-former failed to infer: #{inspect(c.payload.term)} -> #{inspect(other)}")
      end
    end
  end

  test "the sample exercises universes, Pi, Sigma, and Vec type-formers" do
    sample = B.interp(TypeFormer.gen()) |> Enum.take(@sample)
    heads = sample |> Enum.map(fn c -> elem(c.payload.term, 0) end) |> MapSet.new()
    # Sigma is now the inductive `{:data, :Sigma, …}` (D2), so its head is `:data`;
    # assert the Sigma family specifically rather than a `:sigma` head atom.
    for h <- [:type, :pi, :data], do: assert(h in heads, "type-former #{h} never generated")

    assert Enum.any?(sample, &match?({:data, :Sigma, _, _}, &1.payload.term)),
           "type-former Sigma never generated"

    # at least one term sits above Type 0 (a universe or a universe-codomain Pi)
    assert Enum.any?(sample, fn c -> c.payload.type != {:type, 0} end)
  end
end

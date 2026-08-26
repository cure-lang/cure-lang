defmodule Antigen.Generators.TotalityTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Totality
  alias Antigen.Corpus
  alias Cure.Core.Env

  test "emits the confirmed diverging mutual cycle f→g→f as a labeled challenge" do
    c = Totality.diverging_mutual_pair()
    assert c.label == :diverging and c.kind == :def_group
    env = Totality.env_of(c)
    assert %{body: bf} = Env.get_def(env, :f)
    assert %{body: bg} = Env.get_def(env, :g)
    assert calls_global?(bf, :g)
    assert calls_global?(bg, :f)
  end

  test "emits a terminating structural def labeled :terminating" do
    c = Totality.structural_terminating()
    assert c.label == :terminating
  end

  test "every live certifier-driver's known label agrees with the real certifier" do
    drivers = [
      Totality.enriched_terminating(),
      Totality.nonvar_scrutinee_terminating(),
      Totality.reconstruct_equal_diverging(),
      Totality.unknown_arg_diverging(),
      Totality.two_arg_terminating(),
      Totality.terminating_mutual_pair(),
      Totality.swap_terminating(),
      Totality.nullary_self_loop(),
      Totality.nullary_mutual_loop()
    ]

    for c <- drivers do
      assert Antigen.Assays.Totality.run(c) == :ok,
             "certifier disagreed with the #{c.label} label on: #{c.note}"
    end
  end

  test "a :def_group challenge's focus list survives a corpus encode/decode round trip" do
    c = Totality.diverging_mutual_pair()
    line = Corpus.encode_record(c)
    assert {:ok, c2} = Corpus.decode_record(line)
    assert Enum.sort(c2.payload.focus) == Enum.sort(c.payload.focus)

    assert Map.keys(Totality.env_of(c2).defs) |> Enum.sort() ==
             Map.keys(Totality.env_of(c).defs) |> Enum.sort()
  end

  defp calls_global?({:global, n}, n), do: true
  defp calls_global?(t, n) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&calls_global?(&1, n))
  defp calls_global?(l, n) when is_list(l), do: Enum.any?(l, &calls_global?(&1, n))
  defp calls_global?(_, _), do: false
end

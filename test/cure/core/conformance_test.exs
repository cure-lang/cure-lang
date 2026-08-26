defmodule Cure.Core.ConformanceTest do
  @moduledoc """
  Commitment C3 (design spec §9): a corpus of positive/negative Core terms every
  kernel implementation must agree on. Terms are stored in the portable C2
  S-expression format, decoded with `Cure.Core.Serialize`, and judged by
  `Cure.Core.Kernel` — exactly the artifacts an independent kernel would re-check.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Kernel, Quote, Serialize}

  @corpus Path.join([__DIR__, "..", "..", "fixtures", "core_conformance.txt"])

  defp entries do
    @corpus
    |> File.read!()
    |> String.split("\n", trim: true)
    |> Enum.reject(&(String.starts_with?(&1, "#") or &1 == ""))
    |> Enum.map(fn line ->
      case String.split(line, " | ") do
        [verdict, term] -> {verdict, term, nil}
        [verdict, term, type] -> {verdict, term, type}
      end
    end)
  end

  test "the kernel agrees with every verdict in the conformance corpus" do
    ctx = Context.empty(Builtins.seed(Env.empty()))

    for {verdict, term_sexp, type_sexp} <- entries() do
      {:ok, term} = Serialize.decode(term_sexp)
      result = Kernel.infer(ctx, term)

      case verdict do
        "accept" ->
          assert {:ok, type_value} = result, "expected #{term_sexp} to typecheck"

          if type_sexp do
            got = type_value |> Quote.reify(0) |> Serialize.encode()
            assert got == type_sexp, "#{term_sexp}: inferred #{got}, corpus says #{type_sexp}"
          end

        "reject" ->
          assert {:error, _} = result, "expected #{term_sexp} to be rejected"
      end
    end
  end
end

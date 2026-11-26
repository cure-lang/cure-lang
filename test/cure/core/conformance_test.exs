defmodule Cure.Core.ConformanceTest do
  @moduledoc """
  Commitment C3 (design spec §9): a corpus of positive/negative Core terms every
  kernel implementation must agree on. Terms are stored in the portable C2
  S-expression format, decoded with `Cure.Core.Serialize`, and judged by
  `Cure.Core.Kernel` — exactly the artifacts an independent kernel would re-check.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Eval, Kernel, Quote, Serialize}

  @corpus Path.join([__DIR__, "..", "..", "fixtures", "core_conformance.txt"])

  defp entries do
    contents = File.read!(@corpus)
    assert String.starts_with?(contents, "# cure-core-conformance 2\n")

    contents
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

    for {operation, term_sexp, type_sexp} <- entries() do
      {:ok, term} = Serialize.decode(term_sexp)

      case operation do
        "infer_accept" ->
          assert {:ok, type_value} = Kernel.infer(ctx, term), "expected #{term_sexp} to typecheck"

          if type_sexp do
            got = type_value |> Quote.reify(0, Context.signature(ctx)) |> Serialize.encode()
            assert got == type_sexp, "#{term_sexp}: inferred #{got}, corpus says #{type_sexp}"
          end

        "infer_reject" ->
          assert {:error, _} = Kernel.infer(ctx, term), "expected #{term_sexp} to be rejected"

        check when check in ["check_accept", "check_reject"] ->
          assert is_binary(type_sexp), "checking entries require an explicit expected type"
          assert {:ok, expected} = Serialize.decode(type_sexp)
          result = Kernel.check(ctx, term, Eval.eval(expected, Context.env(ctx)))

          if check == "check_accept",
            do: assert(:ok == result, "expected #{term_sexp} to check at #{type_sexp}"),
            else: assert(match?({:error, _}, result), "expected #{term_sexp} to fail at #{type_sexp}")
      end
    end
  end
end

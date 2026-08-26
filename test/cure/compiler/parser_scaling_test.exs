defmodule Cure.Compiler.ParserScalingTest do
  # Not async: this test measures wall-clock scaling, so it must not compete
  # with other CPU-bound suites for schedulers.
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}

  # Token lookup must be O(1). When it is not (e.g. `length/1` per peek plus
  # `Enum.at/2` into a list), parsing is O(n^2) and per-token cost grows with
  # file size — which is what this test pins down.
  #
  # Ratios for a 4x larger input: linear ~4x, quadratic ~16x. The 8x bound sits
  # between the two so the test separates the algorithms rather than the machine.
  @growth_factor 4
  @max_ratio 8

  defp source(fn_count) do
    body =
      for i <- 1..fn_count do
        "  fn f#{i}(a: Int, b: Int) -> Int = a + b * #{i}"
      end
      |> Enum.join("\n")

    "mod ScalingProbe\n" <> body <> "\n"
  end

  defp parse_us(fn_count) do
    {:ok, toks} = Lexer.tokenize(source(fn_count))
    # Warm up so the first-call cost is not attributed to the measured run.
    {:ok, _} = Parser.parse(toks, emit_events: false)
    {us, {:ok, _ast}} = :timer.tc(fn -> Parser.parse(toks, emit_events: false) end)
    {us, length(toks)}
  end

  test "parse time grows about linearly with token count" do
    small = 150
    large = small * @growth_factor

    {small_us, small_tokens} = parse_us(small)
    {large_us, large_tokens} = parse_us(large)

    # Guard the premise: the big input really is ~@growth_factor bigger.
    token_ratio = large_tokens / small_tokens
    assert_in_delta token_ratio, @growth_factor, 0.5

    time_ratio = large_us / max(small_us, 1)

    assert time_ratio < @max_ratio, """
    Parse time scales super-linearly with input size.

      #{small_tokens} tokens: #{Float.round(small_us / 1000, 2)} ms \
    (#{Float.round(small_us / small_tokens, 2)} us/token)
      #{large_tokens} tokens: #{Float.round(large_us / 1000, 2)} ms \
    (#{Float.round(large_us / large_tokens, 2)} us/token)

    time ratio #{Float.round(time_ratio, 1)}x for a #{Float.round(token_ratio, 1)}x \
    bigger input (linear ~#{@growth_factor}x, quadratic ~#{@growth_factor * @growth_factor}x).
    """
  end
end

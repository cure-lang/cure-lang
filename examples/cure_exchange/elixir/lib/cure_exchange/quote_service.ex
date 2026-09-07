defmodule CureExchange.QuoteService do
  @moduledoc """
  Generates rate-lock quotes.

  A quote is a `quote_id`, a spot `rate`, and how long the lock is good for
  (`ttl_ms`) before `TradeWorker` reacts to its expiry by sending
  `:QuoteExpired` to the escrow FSM. This is a plain module rather than a
  process: nothing here needs mutable state beyond a monotonically
  increasing id, which `:erlang.unique_integer/1` already gives us.
  """

  @type t :: %{quote_id: String.t(), rate: float(), ttl_ms: non_neg_integer()}

  @default_ttl_ms 5_000

  @doc """
  A new quote for converting from `from_currency` to `to_currency`, valid
  for `ttl_ms` (default #{@default_ttl_ms}ms).
  """
  @spec new_quote(atom(), atom(), non_neg_integer()) :: t()
  def new_quote(from_currency, to_currency, ttl_ms \\ @default_ttl_ms) do
    %{
      quote_id: "Q-#{:erlang.unique_integer([:positive, :monotonic])}",
      rate: spot_rate(from_currency, to_currency),
      ttl_ms: ttl_ms
    }
  end

  # A tiny static rate table -- enough to make `convert/3` calls in the demo
  # produce a different number than the source amount, not a real feed.
  @rates %{
    {:usd, :eur} => 0.92,
    {:eur, :usd} => 1.09,
    {:usd, :gbp} => 0.79,
    {:gbp, :usd} => 1.27,
    {:eur, :gbp} => 0.86,
    {:gbp, :eur} => 1.16
  }

  defp spot_rate(currency, currency), do: 1.0
  defp spot_rate(from, to), do: Map.fetch!(@rates, {from, to})
end

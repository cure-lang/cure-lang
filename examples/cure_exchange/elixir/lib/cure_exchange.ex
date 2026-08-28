defmodule CureExchange do
  @moduledoc """
  Ergonomic Elixir API over a multi-currency exchange and escrow engine
  whose state graph is implemented in Cure (`cure_src/escrow_fsm.cure`,
  compiled to `:"Cure.Main.EscrowFsm"`).

  ## Example

      CureExchange.open_account(1, "Alice", 1_000_000, :usd)

      {:ok, pid, quote_id} = CureExchange.open_trade(1, :usd, 10_000)
      CureExchange.match_counterparty(pid, :"T-1")
      # ... some time later, once the simulated bank webhook or a timeout fires ...
      CureExchange.status(pid)
      # => %{state: :Completed, data: %{amount: 10_000, ...}}
  """

  alias CureExchange.{Ledger, Money, QuoteService, TradeSupervisor, TradeWorker}

  @default_quote_ttl_ms 5_000
  @default_settle_ttl_ms 5_000
  @default_bank_delay_ms 200

  # -- Accounts ---------------------------------------------------------------

  @doc "Open an account with an initial balance in `currency` (minor units)."
  @spec open_account(integer(), String.t(), integer(), atom()) :: :ok
  def open_account(id, owner, amount_minor, currency) do
    Ledger.open_account(id, owner, Money.new(amount_minor, currency))
  end

  @doc "The available balance of account `id`."
  @spec balance(integer()) :: {:ok, Money.t()} | {:error, String.t()}
  def balance(id), do: Ledger.balance(id)

  @doc "The amount currently held in escrow for account `id`."
  @spec held(integer()) :: {:ok, Money.t()} | {:error, String.t()}
  def held(id), do: Ledger.held(id)

  # -- Trades -------------------------------------------------------------

  @doc """
  Open a new escrow trade: lock `amount_minor` of `currency` from
  `account_id` behind a fresh quote, and start a `TradeWorker` to run it.

  Options:

    * `:quote_ttl_ms`   -- how long the rate lock is good for (default #{@default_quote_ttl_ms})
    * `:settle_ttl_ms`  -- the settlement safety-net timeout (default #{@default_settle_ttl_ms})
    * `:bank_delay_ms`  -- how long the simulated bank webhook takes (default #{@default_bank_delay_ms})
    * `:bank_outcome`   -- what the webhook will report, `:confirmed` or `:failed` (default `:confirmed`)

  Returns `{:ok, pid, quote_id}`.
  """
  @spec open_trade(integer(), atom(), integer(), keyword()) ::
          {:ok, pid(), atom()} | {:error, term()}
  def open_trade(account_id, currency, amount_minor, opts \\ []) do
    quote_info = QuoteService.new_quote(currency, currency, Keyword.get(opts, :quote_ttl_ms, @default_quote_ttl_ms))
    quote_id = String.to_atom(quote_info.quote_id)

    worker_opts = [
      account_id: account_id,
      currency: currency,
      amount: amount_minor,
      quote_id: quote_id,
      quote_ttl_ms: quote_info.ttl_ms,
      settle_ttl_ms: Keyword.get(opts, :settle_ttl_ms, @default_settle_ttl_ms),
      bank_delay_ms: Keyword.get(opts, :bank_delay_ms, @default_bank_delay_ms),
      bank_outcome: Keyword.get(opts, :bank_outcome, :confirmed)
    ]

    case TradeSupervisor.start_trade(worker_opts) do
      {:ok, pid} -> {:ok, pid, quote_id}
      other -> other
    end
  end

  @doc "A counterparty was found for the trade at `pid`; starts the swap."
  @spec match_counterparty(pid(), atom()) :: :ok
  def match_counterparty(pid, trade_id), do: TradeWorker.match_counterparty(pid, trade_id)

  @doc "The escrow's current FSM state and data."
  @spec status(pid()) :: %{state: atom(), data: map()}
  def status(pid), do: TradeWorker.status(pid)
end

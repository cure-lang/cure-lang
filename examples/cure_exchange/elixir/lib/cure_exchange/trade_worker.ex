defmodule CureExchange.TradeWorker do
  @moduledoc """
  Owns one escrow trade end to end: starts the compiled Cure FSM
  (`:"Cure.Main.EscrowFsm"`), drives it with `:gen_statem.cast/2`, and
  provides everything the FSM itself deliberately does not know about --
  the rate-lock timer, the simulated bank webhook, a settlement safety-net
  timer, and the multi-step refund rollback against `CureExchange.Ledger`.

  ## Wire format

  The compiled FSM's states are plain atoms (`:Created`, `:FundsReserved`,
  ...); its data is a positional record tuple `{:EscrowData, amount,
  quote_id, trade_id, attempts}`; its events are `:EventName` for
  payload-less events and `{:EventName, ...fields}` for the two
  payload-bearing ones (`LockFunds`, `CounterpartyMatched`). This was
  confirmed by starting the compiled module directly and inspecting
  `:sys.get_state/1` after each cast -- see `README.md`.

  ## Timers as events

  A rate-lock expiry and a bank webhook are both, from the FSM's point of
  view, just an event that arrives some time after `LockFunds`. This worker
  models both as literally that: `Process.send_after/3` messages that get
  turned into `:gen_statem.cast/2` calls in `handle_info/2`. Before applying
  either one's *side effect* (releasing or capturing the ledger hold), it
  re-reads the FSM's actual current state with `:sys.get_state/1` -- a timer
  that fires after the state has already moved on (the counterparty was
  matched right before `:quote_expired` arrived, say) is confirmed to be a
  no-op before any money moves, matching the FSM's own safe fallback for an
  event with no matching row.
  """

  use GenServer
  require Logger

  alias CureExchange.{Ledger, Money}

  @escrow_fsm :"Cure.Main.EscrowFsm"
  @compile {:no_warn_undefined, @escrow_fsm}

  defstruct [
    :fsm,
    :account_id,
    :hold,
    :quote_id,
    :trade_id,
    :quote_timer,
    :settle_timer,
    :bank_timer,
    :bank_outcome,
    :settle_ttl_ms,
    :bank_delay_ms
  ]

  # -- Public API -----------------------------------------------------------

  @doc """
  Child spec for `CureExchange.TradeSupervisor`. Required opts:
  `:account_id`, `:currency`, `:amount`, `:quote_id`, `:quote_ttl_ms`,
  `:settle_ttl_ms`, `:bank_delay_ms`, `:bank_outcome` (`:confirmed` or
  `:failed` -- what the simulated webhook will eventually report).
  """
  @spec child_spec(keyword()) :: Supervisor.child_spec()
  def child_spec(opts) do
    %{
      id: {__MODULE__, Keyword.fetch!(opts, :quote_id)},
      start: {__MODULE__, :start_link, [opts]},
      restart: :transient
    }
  end

  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts), do: GenServer.start_link(__MODULE__, opts)

  @doc "A counterparty was found for this trade; starts the swap."
  @spec match_counterparty(pid(), atom()) :: :ok
  def match_counterparty(pid, trade_id) when is_atom(trade_id) do
    GenServer.cast(pid, {:match_counterparty, trade_id})
  end

  @doc "The escrow's current FSM state and data."
  @spec status(pid()) :: %{state: atom(), data: map()}
  def status(pid), do: GenServer.call(pid, :status)

  # -- GenServer callbacks ----------------------------------------------------

  @impl true
  def init(opts) do
    account_id = Keyword.fetch!(opts, :account_id)
    hold = Money.new(Keyword.fetch!(opts, :amount), Keyword.fetch!(opts, :currency))
    quote_id = Keyword.fetch!(opts, :quote_id)

    with :ok <- Ledger.reserve(account_id, hold),
         {:ok, fsm} <- apply(@escrow_fsm, :start_link, [{:EscrowData, 0, :none, :none, 0}]) do
      :gen_statem.cast(fsm, {:LockFunds, hold.amount, quote_id})
      quote_timer = Process.send_after(self(), :quote_expired, Keyword.fetch!(opts, :quote_ttl_ms))

      {:ok,
       %__MODULE__{
         fsm: fsm,
         account_id: account_id,
         hold: hold,
         quote_id: quote_id,
         quote_timer: quote_timer,
         bank_outcome: Keyword.fetch!(opts, :bank_outcome),
         settle_ttl_ms: Keyword.fetch!(opts, :settle_ttl_ms),
         bank_delay_ms: Keyword.fetch!(opts, :bank_delay_ms)
       }}
    else
      {:error, reason} -> {:stop, {:reserve_failed, reason}}
    end
  end

  @impl true
  def handle_cast({:match_counterparty, trade_id}, state) do
    cancel_timer(state.quote_timer)
    :gen_statem.cast(state.fsm, {:CounterpartyMatched, trade_id})

    bank_timer = Process.send_after(self(), :bank_webhook, state.bank_delay_ms)
    settle_timer = Process.send_after(self(), :settle_timeout, state.settle_ttl_ms)

    {:noreply, %{state | trade_id: trade_id, bank_timer: bank_timer, settle_timer: settle_timer}}
  end

  @impl true
  def handle_call(:status, _from, state) do
    {fsm_state, data} = :sys.get_state(state.fsm)
    {:reply, %{state: fsm_state, data: decode_data(data)}, state}
  end

  @impl true
  def handle_info(:quote_expired, state) do
    if fsm_state(state) == :FundsReserved do
      :gen_statem.cast(state.fsm, :QuoteExpired)
      Ledger.release(state.account_id, state.hold)
      Logger.info("trade #{state.quote_id}: quote expired, released #{Money.show(state.hold)}")
    end

    {:noreply, %{state | quote_timer: nil}}
  end

  def handle_info(:bank_webhook, state) do
    cancel_timer(state.settle_timer)

    if fsm_state(state) == :ExecutingSwap do
      case state.bank_outcome do
        :confirmed ->
          :gen_statem.cast(state.fsm, :BankConfirmed)
          Ledger.capture(state.account_id, state.hold)
          Logger.info("trade #{state.quote_id}: bank confirmed, captured #{Money.show(state.hold)}")

        :failed ->
          :gen_statem.cast(state.fsm, :BankFailed)
          refund(state)
      end
    end

    {:noreply, %{state | bank_timer: nil, settle_timer: nil}}
  end

  def handle_info(:settle_timeout, state) do
    cancel_timer(state.bank_timer)

    if fsm_state(state) == :ExecutingSwap do
      :gen_statem.cast(state.fsm, :SettleTimeout)
      refund(state)
    end

    {:noreply, %{state | bank_timer: nil, settle_timer: nil}}
  end

  # -- The multi-step refund rollback -----------------------------------------
  #
  # 1. release the hold back to the account's available balance,
  # 2. record that the refund happened (here, a log line; a real system
  #    might also credit the counterparty's own leg or emit a ledger entry),
  # 3. only once the money has actually moved does the FSM hear about it.
  defp refund(state) do
    :ok = Ledger.release(state.account_id, state.hold)
    Logger.info("trade #{state.quote_id}: refunding, released #{Money.show(state.hold)} back to account #{state.account_id}")
    :gen_statem.cast(state.fsm, :RefundCompleted)
  end

  defp fsm_state(state) do
    {name, _data} = :sys.get_state(state.fsm)
    name
  end

  defp cancel_timer(nil), do: :ok
  defp cancel_timer(ref), do: Process.cancel_timer(ref)

  defp decode_data({:EscrowData, amount, quote_id, trade_id, attempts}) do
    %{amount: amount, quote_id: quote_id, trade_id: trade_id, attempts: attempts}
  end
end

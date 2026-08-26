defmodule CureMoneta do
  @moduledoc """
  Ergonomic Elixir API over a money and ledger library implemented in Cure.

  The heavy lifting lives in `cure_src/moneta.cure`, which compiles to the
  BEAM module `:"Cure.Moneta"`, and in `cure_src/transaction.cure`, which
  compiles to `:"Cure.Main.Transaction"` (a gen_statem in callback mode).

  This module:

    * constructs plain Elixir values and converts them at the Cure boundary,
    * delegates arithmetic and ledger operations to the Cure module,
    * unwraps `Result` tuples (`{:ok, v}` / `{:error, reason}`),
    * exposes `begin_transaction/0` to spawn a supervised transaction FSM.

  ## Currencies

  Amounts are always in *minor units* (smallest denomination):
  EUR/USD/GBP/CHF use cents (100 per unit), JPY uses whole yen (1 per unit),
  OMR uses baisa (1000 per unit).

  ## Example

      eur100 = CureMoneta.money(:eur, 10_000)   # EUR 100.00
      jpy500 = CureMoneta.money(:jpy, 500)       # JPY 500
      omr1   = CureMoneta.money(:omr, 1_000)     # OMR 1.000

      :ok = CureMoneta.open_account(1, "Alice", :eur, 10_000)
      :ok = CureMoneta.deposit(1, :eur, 500)
      {:ok, bal} = CureMoneta.balance(1)
      CureMoneta.show(bal)
      # => "EUR 105.00"

      usd = CureMoneta.convert(eur100, :usd, 1.08)
      CureMoneta.show(usd)
      # => "USD 108.00"
  """

  @moneta :"Cure.Moneta"
  @tx_fsm :"Cure.Main.Transaction"

  @compile {:no_warn_undefined, @moneta}
  @compile {:no_warn_undefined, @tx_fsm}

  # Default fractional units per currency (minor units per major unit).
  @frac_for %{eur: 100, usd: 100, gbp: 100, jpy: 1, chf: 100, omr: 1000}

  # -- Money construction -----------------------------------------------------

  @doc """
  Construct a Cure Money map using the default fractional units for `currency`.

      CureMoneta.money(:eur, 1050)   # EUR 10.50
      CureMoneta.money(:jpy, 750)    # JPY 750
      CureMoneta.money(:omr, 1500)   # OMR 1.500
  """
  @spec money(atom(), integer()) :: map()
  def money(currency, amount_minor) when is_atom(currency) do
    frac = Map.fetch!(@frac_for, currency)
    %{__struct__: :money, amount: amount_minor, currency: {currency}, fractional_units: frac}
  end

  @doc "Construct a Cure Money map with an explicit `fractional_units` value."
  @spec money(atom(), integer(), pos_integer()) :: map()
  def money(currency, amount_minor, fractional_units) when is_atom(currency) do
    %{
      __struct__: :money,
      amount: amount_minor,
      currency: {currency},
      fractional_units: fractional_units
    }
  end

  # -- Show and Eq ------------------------------------------------------------

  @doc "Render a Currency or Money value to a string (delegates to the Cure Show protocol)."
  @spec show(map() | tuple()) :: String.t()
  def show(value), do: @moneta.show(to_cure_money(value)) |> List.to_string()

  @doc "Test equality of two Money or Currency values (delegates to the Cure Eq protocol)."
  @spec eq(map() | tuple(), map() | tuple()) :: boolean()
  def eq(a, b), do: @moneta.eq(to_cure_money(a), to_cure_money(b))

  # -- Arithmetic -------------------------------------------------------------

  @doc "Add two Money values of the same currency."
  @spec add(map(), map()) :: {:ok, map()} | {:error, String.t()}
  def add(a, b), do: @moneta.add(to_cure_money(a), to_cure_money(b)) |> map_money_result()

  @doc "Subtract `b` from `a`. Returns an error for currency mismatch or insufficient funds."
  @spec subtract(map(), map()) :: {:ok, map()} | {:error, String.t()}
  def subtract(a, b),
    do: @moneta.subtract(to_cure_money(a), to_cure_money(b)) |> map_money_result()

  @doc "Scale Money by a positive integer factor."
  @spec scale(map(), pos_integer()) :: map()
  def scale(m, factor), do: @moneta.scale(to_cure_money(m), factor) |> from_cure_money()

  @doc """
  Convert Money to `target_currency` at the given spot `rate`.

  `rate` is target minor units per source minor unit. Uses the default
  `fractional_units` for the target currency.
  """
  @spec convert(map(), atom(), float()) :: map()
  def convert(m, target_currency, rate) when is_atom(target_currency) do
    frac = Map.fetch!(@frac_for, target_currency)

    @moneta.convert(to_cure_money(m), currency_atom(target_currency), rate, frac)
    |> from_cure_money()
  end

  @doc "Convert Money with an explicit target `fractional_units`."
  @spec convert(map(), atom(), float(), pos_integer()) :: map()
  def convert(m, target_currency, rate, fractional_units) when is_atom(target_currency) do
    @moneta.convert(to_cure_money(m), currency_atom(target_currency), rate, fractional_units)
    |> from_cure_money()
  end

  # -- Ledger operations (via LedgerServer) -----------------------------------

  @doc "Open an account on the shared ledger with an initial balance in `currency`."
  @spec open_account(integer(), String.t(), atom(), integer()) :: :ok
  def open_account(id, owner, currency, amount_minor) do
    balance = money(currency, amount_minor)
    CureMoneta.LedgerServer.open_account(id, owner, balance)
  end

  @doc "Deposit `amount_minor` units of `currency` into account `id`."
  @spec deposit(integer(), atom(), integer()) :: :ok | {:error, String.t()}
  def deposit(id, currency, amount_minor) do
    CureMoneta.LedgerServer.deposit(id, money(currency, amount_minor))
  end

  @doc "Withdraw `amount_minor` units of `currency` from account `id`."
  @spec withdraw(integer(), atom(), integer()) :: :ok | {:error, String.t()}
  def withdraw(id, currency, amount_minor) do
    CureMoneta.LedgerServer.withdraw(id, money(currency, amount_minor))
  end

  @doc "Transfer `amount_minor` units of `currency` from account `from_id` to `to_id`."
  @spec transfer(integer(), integer(), atom(), integer()) :: :ok | {:error, String.t()}
  def transfer(from_id, to_id, currency, amount_minor) do
    CureMoneta.LedgerServer.transfer(from_id, to_id, money(currency, amount_minor))
  end

  @doc "Return the current balance of account `id`."
  @spec balance(integer()) :: {:ok, map()} | {:error, String.t()}
  def balance(id), do: CureMoneta.LedgerServer.balance(id)

  # -- Transaction FSM --------------------------------------------------------

  @doc """
  Spawn a new transaction FSM under `CureMoneta.TxSupervisor`.

  Returns `{:ok, pid}`. The FSM starts in the `:Idle` state. Drive it with
  `tx_event/2` and inspect it with `tx_state/1`.

  Typical lifecycle:

      {:ok, pid} = CureMoneta.begin_transaction()
      CureMoneta.tx_event(pid, :create)
      CureMoneta.tx_event(pid, :submit)
      # :dispatch fires automatically (hard event)
      CureMoneta.tx_event(pid, :confirm)
      {:Settled, _} = CureMoneta.tx_state(pid)
  """
  @spec begin_transaction() :: {:ok, pid()} | {:error, term()}
  def begin_transaction do
    spec = %{
      id: make_ref(),
      start: {@tx_fsm, :start_link, [0]},
      restart: :transient
    }

    DynamicSupervisor.start_child(CureMoneta.TxSupervisor, spec)
  end

  @doc "Send `event` to the transaction FSM at `pid` (async cast)."
  @spec tx_event(pid(), atom()) :: :ok
  def tx_event(pid, event) do
    :gen_statem.cast(pid, event)
    :ok
  end

  @doc "Return `{state_atom, payload}` for the transaction FSM at `pid` (synchronous)."
  @spec tx_state(pid()) :: {atom(), term()}
  def tx_state(pid), do: :sys.get_state(pid)

  defp currency_atom(currency) when is_atom(currency) do
    currency |> Atom.to_string() |> String.upcase() |> String.to_atom()
  end

  defp to_cure_money({:Money, _amount, _currency, _fractional_units} = money), do: money

  defp to_cure_money(%{
         __struct__: :money,
         amount: amount,
         currency: {currency},
         fractional_units: fractional_units
       }) do
    {:Money, amount, currency_atom(currency), fractional_units}
  end

  defp from_cure_money({:Money, amount, currency, fractional_units}) do
    %{
      __struct__: :money,
      amount: amount,
      currency:
        currency |> Atom.to_string() |> String.downcase() |> String.to_atom() |> then(&{&1}),
      fractional_units: fractional_units
    }
  end

  defp map_money_result({:ok, money}), do: {:ok, from_cure_money(money)}
  defp map_money_result({:error, reason}), do: {:error, List.to_string(reason)}
end

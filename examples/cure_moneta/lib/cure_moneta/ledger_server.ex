defmodule CureMoneta.LedgerServer do
  @moduledoc """
  GenServer that holds a `Cure.Moneta` ledger as its state.

  All computation is delegated to the compiled Cure module; this process
  is purely a state container and OTP lifecycle manager. It starts with an
  empty ledger (no accounts).

  ## Example

      CureMoneta.LedgerServer.open_account(1, "Alice", eur_balance)
      CureMoneta.LedgerServer.deposit(1, eur_100)
      {:ok, balance} = CureMoneta.LedgerServer.balance(1)

  The `CureMoneta` module wraps these calls with friendlier argument types.
  """

  use GenServer

  @moneta :"Cure.Moneta"

  # Silence "module not yet available" warnings: the Cure-compiled module is
  # loaded from `_build/cure/ebin/` at runtime, after Elixir compilation.
  @compile {:no_warn_undefined, @moneta}

  # -- Public API -------------------------------------------------------------

  @doc "Start the server under a supervisor (default name: `CureMoneta.LedgerServer`)."
  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, :ok, Keyword.put_new(opts, :name, __MODULE__))
  end

  @doc """
  Open a new account on the ledger.

  `balance` must be a Cure `Money` map (`%{__struct__: :money, ...}`).
  """
  @spec open_account(integer(), String.t(), map()) :: :ok
  def open_account(id, owner, balance) do
    GenServer.call(__MODULE__, {:open_account, id, owner, balance})
  end

  @doc "Deposit `amount` (a Cure Money map) into account `id`."
  @spec deposit(integer(), map()) :: :ok | {:error, String.t()}
  def deposit(id, amount) do
    GenServer.call(__MODULE__, {:deposit, id, amount})
  end

  @doc "Withdraw `amount` (a Cure Money map) from account `id`."
  @spec withdraw(integer(), map()) :: :ok | {:error, String.t()}
  def withdraw(id, amount) do
    GenServer.call(__MODULE__, {:withdraw, id, amount})
  end

  @doc "Transfer `amount` from account `from_id` to account `to_id`."
  @spec transfer(integer(), integer(), map()) :: :ok | {:error, String.t()}
  def transfer(from_id, to_id, amount) do
    GenServer.call(__MODULE__, {:transfer, from_id, to_id, amount})
  end

  @doc "Return the balance of account `id` as a Cure Money map, or an error."
  @spec balance(integer()) :: {:ok, map()} | {:error, String.t()}
  def balance(id) do
    GenServer.call(__MODULE__, {:balance, id})
  end

  # -- GenServer callbacks ----------------------------------------------------

  @impl true
  def init(:ok) do
    {:ok, @moneta.new_ledger([])}
  end

  @impl true
  def handle_call({:open_account, id, owner, balance}, _from, ledger) do
    new_ledger = @moneta.open_account(ledger, id, owner, to_cure_money(balance))
    {:reply, :ok, new_ledger}
  end

  def handle_call({:deposit, id, amount}, _from, ledger) do
    case @moneta.deposit(ledger, id, to_cure_money(amount)) do
      {:ok, new_ledger} -> {:reply, :ok, new_ledger}
      {:error, reason} -> {:reply, {:error, List.to_string(reason)}, ledger}
    end
  end

  def handle_call({:withdraw, id, amount}, _from, ledger) do
    case @moneta.withdraw(ledger, id, to_cure_money(amount)) do
      {:ok, new_ledger} -> {:reply, :ok, new_ledger}
      {:error, reason} -> {:reply, {:error, List.to_string(reason)}, ledger}
    end
  end

  def handle_call({:transfer, from_id, to_id, amount}, _from, ledger) do
    case @moneta.transfer(ledger, from_id, to_id, to_cure_money(amount)) do
      {:ok, new_ledger} -> {:reply, :ok, new_ledger}
      {:error, reason} -> {:reply, {:error, List.to_string(reason)}, ledger}
    end
  end

  def handle_call({:balance, id}, _from, ledger) do
    {:reply, map_money_result(@moneta.balance(ledger, id)), ledger}
  end

  defp to_cure_money({:Money, _amount, _currency, _fractional_units} = money), do: money

  defp to_cure_money(%{
         __struct__: :money,
         amount: amount,
         currency: {currency},
         fractional_units: fractional_units
       }) do
    {:Money, amount, currency |> Atom.to_string() |> String.upcase() |> String.to_atom(),
     fractional_units}
  end

  defp map_money_result({:ok, {:Money, amount, currency, fractional_units}}) do
    {:ok,
     %{
       __struct__: :money,
       amount: amount,
       currency: {currency |> Atom.to_string() |> String.downcase() |> String.to_atom()},
       fractional_units: fractional_units
     }}
  end

  defp map_money_result({:error, reason}), do: {:error, List.to_string(reason)}
  defp map_money_result(other), do: other
end

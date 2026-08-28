defmodule CureExchange.Ledger do
  @moduledoc """
  A `GenServer` holding accounts, each with an available `:balance` and an
  escrow `:held` amount.

  Mirrors `examples/cure_exchange/cure`'s `Exchange.Ledger`, but in Elixir:
  `reserve/2` moves funds from `balance` to `held` (`LockFunds`), `capture/2`
  removes a hold entirely (`BankConfirmed` / `Completed`), and `release/2`
  moves a hold back to `balance` (a refund, after `Refunding`).
  """

  use GenServer

  alias CureExchange.Money

  @type account :: %{owner: String.t(), balance: Money.t(), held: Money.t()}

  # -- Public API ---------------------------------------------------------

  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, :ok, Keyword.put_new(opts, :name, __MODULE__))
  end

  @doc "Open a new account with an initial available `balance`."
  @spec open_account(integer(), String.t(), Money.t()) :: :ok
  def open_account(id, owner, %Money{} = balance) do
    GenServer.call(__MODULE__, {:open_account, id, owner, balance})
  end

  @doc "Move `amount` from account `id`'s balance into its hold (`LockFunds`)."
  @spec reserve(integer(), Money.t()) :: :ok | {:error, String.t()}
  def reserve(id, %Money{} = amount), do: GenServer.call(__MODULE__, {:reserve, id, amount})

  @doc "Remove `amount` from account `id`'s hold entirely (paid out)."
  @spec capture(integer(), Money.t()) :: :ok | {:error, String.t()}
  def capture(id, %Money{} = amount), do: GenServer.call(__MODULE__, {:capture, id, amount})

  @doc "Move `amount` from account `id`'s hold back to its balance (a refund)."
  @spec release(integer(), Money.t()) :: :ok | {:error, String.t()}
  def release(id, %Money{} = amount), do: GenServer.call(__MODULE__, {:release, id, amount})

  @doc "The available balance of account `id`."
  @spec balance(integer()) :: {:ok, Money.t()} | {:error, String.t()}
  def balance(id), do: GenServer.call(__MODULE__, {:balance, id})

  @doc "The amount currently held in escrow for account `id`."
  @spec held(integer()) :: {:ok, Money.t()} | {:error, String.t()}
  def held(id), do: GenServer.call(__MODULE__, {:held, id})

  # -- GenServer callbacks --------------------------------------------------

  @impl true
  def init(:ok), do: {:ok, %{}}

  @impl true
  def handle_call({:open_account, id, owner, balance}, _from, accounts) do
    account = %{owner: owner, balance: balance, held: Money.zero(balance.currency)}
    {:reply, :ok, Map.put(accounts, id, account)}
  end

  def handle_call({:reserve, id, amount}, _from, accounts) do
    with_account(accounts, id, fn account ->
      with {:ok, new_balance} <- Money.subtract(account.balance, amount),
           {:ok, new_held} <- Money.add(account.held, amount) do
        {:ok, %{account | balance: new_balance, held: new_held}}
      end
    end)
  end

  def handle_call({:capture, id, amount}, _from, accounts) do
    with_account(accounts, id, fn account ->
      with {:ok, new_held} <- Money.subtract(account.held, amount) do
        {:ok, %{account | held: new_held}}
      end
    end)
  end

  def handle_call({:release, id, amount}, _from, accounts) do
    with_account(accounts, id, fn account ->
      with {:ok, new_held} <- Money.subtract(account.held, amount),
           {:ok, new_balance} <- Money.add(account.balance, amount) do
        {:ok, %{account | held: new_held, balance: new_balance}}
      end
    end)
  end

  def handle_call({:balance, id}, _from, accounts) do
    {:reply, fetch_field(accounts, id, :balance), accounts}
  end

  def handle_call({:held, id}, _from, accounts) do
    {:reply, fetch_field(accounts, id, :held), accounts}
  end

  # -- Helpers --------------------------------------------------------------

  defp with_account(accounts, id, effect) do
    case Map.fetch(accounts, id) do
      :error ->
        {:reply, {:error, "account not found: #{id}"}, accounts}

      {:ok, account} ->
        case effect.(account) do
          {:ok, updated} -> {:reply, :ok, Map.put(accounts, id, updated)}
          {:error, reason} -> {:reply, {:error, reason}, accounts}
        end
    end
  end

  defp fetch_field(accounts, id, field) do
    case Map.fetch(accounts, id) do
      :error -> {:error, "account not found: #{id}"}
      {:ok, account} -> {:ok, Map.fetch!(account, field)}
    end
  end
end

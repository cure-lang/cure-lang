defmodule CureExchange.Money do
  @moduledoc """
  Money values in minor units (cents), plain Elixir.

  This is deliberately ordinary Elixir, not Cure: per this project's split,
  only the escrow state graph (`cure_src/escrow_fsm.cure`) is written in
  Cure. Everything that touches money lives here instead.

  ## Example

      iex> a = CureExchange.Money.new(10_000, :usd)
      iex> CureExchange.Money.show(a)
      "USD 100.00"
  """

  @enforce_keys [:amount, :currency]
  defstruct [:amount, :currency]

  @type t :: %__MODULE__{amount: integer(), currency: atom()}

  @doc "Construct a Money value from a minor-unit amount and a currency atom."
  @spec new(integer(), atom()) :: t()
  def new(amount, currency) when is_integer(amount) and is_atom(currency) do
    %__MODULE__{amount: amount, currency: currency}
  end

  @doc "A zero balance in `currency`."
  @spec zero(atom()) :: t()
  def zero(currency), do: new(0, currency)

  @doc "Add two Money values of the same currency."
  @spec add(t(), t()) :: {:ok, t()} | {:error, String.t()}
  def add(%__MODULE__{currency: c} = a, %__MODULE__{currency: c} = b) do
    {:ok, new(a.amount + b.amount, c)}
  end

  def add(%__MODULE__{} = a, %__MODULE__{} = b) do
    {:error, "currency mismatch: cannot add #{a.currency} and #{b.currency}"}
  end

  @doc "Subtract `b` from `a`. Fails on currency mismatch or a negative result."
  @spec subtract(t(), t()) :: {:ok, t()} | {:error, String.t()}
  def subtract(%__MODULE__{currency: c} = a, %__MODULE__{currency: c} = b) do
    if a.amount >= b.amount do
      {:ok, new(a.amount - b.amount, c)}
    else
      {:error, "insufficient funds: balance #{show(a)} < #{show(b)}"}
    end
  end

  def subtract(%__MODULE__{} = a, %__MODULE__{} = b) do
    {:error, "currency mismatch: cannot subtract #{b.currency} from #{a.currency}"}
  end

  @doc """
  Convert Money to `target_currency` at spot `rate` (target minor units per
  source minor unit).
  """
  @spec convert(t(), atom(), float()) :: t()
  def convert(%__MODULE__{} = m, target_currency, rate) when is_float(rate) do
    new(round(m.amount * rate), target_currency)
  end

  @doc ~S(Renders as `"USD 100.50"`, with a leading `-` for negative amounts.)
  @spec show(t()) :: String.t()
  def show(%__MODULE__{amount: amount, currency: currency}) do
    sign = if amount < 0, do: "-", else: ""
    abs_amount = abs(amount)
    major = div(abs_amount, 100)
    minor = rem(abs_amount, 100)

    "#{sign}#{currency |> Atom.to_string() |> String.upcase()} #{major}.#{pad2(minor)}"
  end

  defp pad2(n) when n < 10, do: "0#{n}"
  defp pad2(n), do: "#{n}"
end

defmodule CureExample do
  @moduledoc """
  Demonstrates calling Cure-compiled BEAM modules from Elixir.

  Cure compiles `.cure` source files into Elixir-style BEAM modules with
  a `Cure.` prefix (e.g., `mod Calculator` becomes `Cure.Calculator`).
  These modules are callable from Elixir like any other module.
  """

  @doc """
  Greets a person using the Cure `Greeter` module.

      iex> CureExample.greet("World")
      "Hello, World!"
  """
  def greet(name),
    do: call(:"Cure.Greeter", :hello, [to_cure_string(name)]) |> from_cure_string()

  @doc """
  Says farewell using the Cure `Greeter` module.

      iex> CureExample.farewell("World")
      "Goodbye, World. See you soon!"
  """
  def farewell(name),
    do: call(:"Cure.Greeter", :farewell, [to_cure_string(name)]) |> from_cure_string()

  @doc """
  Computes n! using the Cure `Calculator` module.

      iex> CureExample.factorial(10)
      3628800
  """
  def factorial(n), do: call(:"Cure.Calculator", :factorial, [n])

  @doc """
  Computes the n-th Fibonacci number using the Cure `Calculator` module.

      iex> CureExample.fibonacci(10)
      55
  """
  def fibonacci(n), do: call(:"Cure.Calculator", :fibonacci, [n])

  @doc """
  Classifies an integer as "positive", "negative", or "zero".

      iex> CureExample.classify(42)
      "positive"
      iex> CureExample.classify(-1)
      "negative"
      iex> CureExample.classify(0)
      "zero"
  """
  def classify(n), do: call(:"Cure.Calculator", :classify, [n]) |> from_cure_string()

  @doc """
  Safe division that returns `{:ok, result}` or `{:error, reason}`.

      iex> CureExample.safe_divide(10, 2)
      {:ok, 5}
      iex> CureExample.safe_divide(10, 0)
      {:error, "division by zero"}
  """
  def safe_divide(a, b) do
    case call(:"Cure.Calculator", :safe_divide, [a, b]) do
      {:ok, value} -> {:ok, value}
      {:error, reason} -> {:error, from_cure_string(reason)}
      {:Ok, value} -> {:ok, value}
      {:Error, reason} -> {:error, from_cure_string(reason)}
    end
  end

  @doc """
  Runs a demo showing all the Cure modules in action.
  """
  def demo do
    IO.puts("--- Cure Example: Greeter ---")
    IO.puts(greet("Elixir"))
    IO.puts(farewell("Elixir"))

    IO.puts("\n--- Cure Example: Calculator ---")
    IO.puts("5 + 3 = #{call(:"Cure.Calculator", :add, [5, 3])}")
    IO.puts("10 - 4 = #{call(:"Cure.Calculator", :sub, [10, 4])}")
    IO.puts("6 * 7 = #{call(:"Cure.Calculator", :mul, [6, 7])}")
    IO.puts("10! = #{factorial(10)}")
    IO.puts("fib(10) = #{fibonacci(10)}")

    IO.puts("\n--- Cure Example: Pattern Guards ---")
    IO.puts("classify(42) = #{classify(42)}")
    IO.puts("classify(-1) = #{classify(-1)}")
    IO.puts("classify(0)  = #{classify(0)}")

    IO.puts("\n--- Cure Example: Result Types ---")
    IO.puts("safe_divide(10, 2) = #{inspect(safe_divide(10, 2))}")
    IO.puts("safe_divide(10, 0) = #{inspect(safe_divide(10, 0))}")
  end

  defp call(module, function, arguments), do: apply(module, function, arguments)

  # `String` is a nominal Cure type (`rec String { characters: List(Char) }`),
  # not a bare charlist -- it erases to the tagged pair `{String,
  # code_points}`. A `.cure` function that takes or returns `String` expects
  # exactly that shape at the Elixir boundary, not a raw charlist or binary.
  defp to_cure_string(s) when is_binary(s), do: {:String, String.to_charlist(s)}
  defp from_cure_string({:String, chars}), do: List.to_string(chars)
end

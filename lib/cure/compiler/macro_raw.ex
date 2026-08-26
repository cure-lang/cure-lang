defmodule Cure.Compiler.MacroRaw do
  @moduledoc "Pure delimiter-bounded token capture for Tier-5 raw macro holes."

  alias Cure.Compiler.Token

  @spec capture([Token.t()], String.t()) ::
          {:ok, [Token.t()], [Token.t()]}
          | {:error, {:missing_raw_delimiter, String.t()} | {:invalid_raw_delimiter, term()} | :invalid_raw_tokens}
  def capture(tokens, delimiter) when is_list(tokens) and is_binary(delimiter) do
    if Enum.all?(tokens, &match?(%Token{}, &1)) do
      case Enum.split_while(tokens, &(not delimiter?(&1, delimiter))) do
        {prefix, [_delimiter | rest]} -> {:ok, prefix, rest}
        {_prefix, []} -> {:error, {:missing_raw_delimiter, delimiter}}
      end
    else
      {:error, :invalid_raw_tokens}
    end
  end

  def capture(_tokens, delimiter) when not is_binary(delimiter),
    do: {:error, {:invalid_raw_delimiter, delimiter}}

  def capture(_tokens, _delimiter), do: {:error, :invalid_raw_tokens}

  defp delimiter?(%Token{type: type, value: value}, delimiter) do
    to_string(type) == delimiter or (is_binary(value) and value == delimiter)
  end
end

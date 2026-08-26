defmodule Antigen.CoverFixture do
  @moduledoc false
  def classify(n) when is_integer(n) do
    cond do
      n < 0 -> :neg
      n == 0 -> :zero
      true -> :pos
    end
  end
end

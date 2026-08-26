defmodule Cure.Compiler.MacroParse do
  @moduledoc "Pure parser-grammar validation for the concrete parse macro library."

  @spec build(String.t() | atom(), [map()]) :: {:ok, map()} | {:error, term()}
  def build(name, productions) when (is_atom(name) or is_binary(name)) and is_list(productions) do
    cond do
      Enum.any?(productions, fn production -> not valid_production?(production) end) ->
        {:error, :invalid_parse_production}

      duplicate_names?(productions) ->
        {:error, :duplicate_parse_production}

      left_recursive?(productions) ->
        {:error, {:left_recursive_parse_production, left_recursive_names(productions)}}

      true ->
        {:ok,
         %{
           kind: :quoted_parse_grammar,
           name: name,
           productions: productions,
           declarations: [{:parse_def, [name: name], productions}]
         }}
    end
  end

  def build(name, _productions) when not is_atom(name) and not is_binary(name),
    do: {:error, {:invalid_parse_name, name}}

  def build(_name, _productions), do: {:error, :invalid_parse_productions}

  defp valid_production?(%{name: name, body: body})
       when (is_atom(name) or is_binary(name)) and is_list(body) and body != [],
       do: Enum.all?(body, &(is_binary(&1) or is_atom(&1)))

  defp valid_production?(_), do: false

  defp duplicate_names?(productions) do
    names = Enum.map(productions, & &1.name)
    length(names) != MapSet.size(MapSet.new(names))
  end

  defp left_recursive?(productions), do: left_recursive_names(productions) != []

  defp left_recursive_names(productions) do
    production_names = MapSet.new(Enum.map(productions, & &1.name))

    productions
    |> Enum.filter(fn %{name: name, body: [first | _]} -> first == name and MapSet.member?(production_names, first) end)
    |> Enum.map(& &1.name)
  end
end

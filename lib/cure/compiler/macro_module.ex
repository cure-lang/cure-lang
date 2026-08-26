defmodule Cure.Compiler.MacroModule do
  @moduledoc """
  Pure execution and composition helpers for Tier-5 macro rules.

  Module expansion returns ordinary parser AST. It does not register, compile,
  or load a module; callers still send the result through normal elaboration.
  """

  alias Cure.Compiler.{MacroFuzz, Parser}

  @spec execute_module_rule(map(), [map()], map()) :: {:ok, term()} | {:error, term()}
  def execute_module_rule(%{kind: :syntax, module_rule: true} = rule, rules, bindings)
      when is_list(rules) and is_map(bindings) do
    if Enum.all?(rules, &is_map/1) do
      with {:ok, tokens} <- MacroFuzz.assemble_use_site(rule, bindings),
           expansion = Parser.expand_example(rules, tokens),
           false <- match?({:example_use_site_not_fully_consumed, _, _}, expansion) do
        {:ok, expansion}
      else
        true -> {:error, :module_rule_not_fully_consumed}
        {:error, _} = error -> error
      end
    else
      {:error, :invalid_module_rule_set}
    end
  end

  def execute_module_rule(%{kind: :syntax, module_rule: true}, rules, _bindings) when not is_list(rules),
    do: {:error, :invalid_module_rule_set}

  def execute_module_rule(%{kind: :syntax, module_rule: true}, _rules, bindings) when not is_map(bindings),
    do: {:error, :invalid_module_rule_bindings}

  def execute_module_rule(_rule, _rules, _bindings), do: {:error, :not_a_module_rule}

  @spec compose_open_categories([map()], [map()]) :: {:ok, [map()]} | {:error, term()}
  def compose_open_categories(base_rules, extension_rules)
      when is_list(base_rules) and is_list(extension_rules) do
    if Enum.all?(base_rules ++ extension_rules, &is_map/1) do
      compose_valid_categories(base_rules, extension_rules)
    else
      {:error, :invalid_macro_extension_rule}
    end
  end

  def compose_open_categories(_base_rules, _extension_rules),
    do: {:error, :invalid_macro_extension_rules}

  defp compose_valid_categories(base_rules, extension_rules) do
    open_categories =
      base_rules
      |> Enum.filter(&(&1[:kind] == :open_category))
      |> Enum.map(& &1.name)
      |> MapSet.new()

    extensions = Enum.filter(extension_rules, &(&1[:category] in open_categories))
    closed = Enum.filter(extension_rules, &(&1[:kind] in [:syntax, :computed] and &1[:category]))

    duplicate_keywords =
      (Enum.map(base_rules, & &1[:keyword]) ++ Enum.map(extensions, & &1[:keyword]))
      |> Enum.reject(&is_nil/1)
      |> Enum.frequencies()
      |> Enum.filter(fn {_keyword, count} -> count > 1 end)
      |> Enum.map(&elem(&1, 0))

    invalid_closed = closed |> Enum.reject(&(&1 in extensions)) |> Enum.uniq()

    cond do
      invalid_closed != [] ->
        {:error, {:closed_category_extension, Enum.map(invalid_closed, & &1.category) |> Enum.uniq()}}

      duplicate_keywords != [] ->
        {:error, {:ambiguous_macro_extension, duplicate_keywords}}

      true ->
        {:ok, base_rules ++ extensions}
    end
  end
end

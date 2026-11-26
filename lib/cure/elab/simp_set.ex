defmodule Cure.Elab.SimpSet do
  @moduledoc """
  Admission policy for ambient simplification lemmas.

  `@simp` and `@lemma(:simp)` opt into declaration-time validation. Legacy
  `@lemma` rules remain available only when they satisfy the same safe ordering.
  Entries live in the existing lemma registry, including across module imports.
  """

  alias Cure.Core.{Env, Inductive}

  def explicit?(meta) do
    case Keyword.get(meta, :decorator) do
      {:decorator, decorator_meta, args} when is_list(decorator_meta) ->
        Keyword.get(decorator_meta, :name) == :simp or
          (Keyword.get(decorator_meta, :name) == :lemma and match?([{:literal, _, :simp}], args))

      _ ->
        false
    end
  end

  defp declaration_error(meta, cause) do
    reason = {:invalid_simp_lemma, Keyword.get(meta, :name), cause}

    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{} = info ->
        {:error,
         {:source_context, reason,
          %{
            span: info.name || info.whole,
            declaration_span: info.whole,
            expectation_origin: :simp_declaration
          }}}

      _ ->
        {:error, reason}
    end
  end

  def lemma?(meta) do
    case Keyword.get(meta, :decorator) do
      {:decorator, decorator_meta, _args} when is_list(decorator_meta) ->
        Keyword.get(decorator_meta, :name) in [:lemma, :simp]

      _ ->
        false
    end
  end

  def validate(meta, type, env) do
    if explicit?(meta) do
      case orientation(type, env) do
        :ok -> validate_arguments(meta)
        {:error, cause} -> declaration_error(meta, cause)
      end
    else
      :ok
    end
  end

  defp validate_arguments(meta) do
    case Keyword.get(meta, :decorator) do
      {:decorator, decorator_meta, args} when is_list(decorator_meta) ->
        case {Keyword.get(decorator_meta, :name), args} do
          {:simp, []} -> :ok
          {:lemma, [{:literal, _, :simp}]} -> :ok
          _ -> declaration_error(meta, :unexpected_arguments)
        end

      _ ->
        declaration_error(meta, :unexpected_arguments)
    end
  end

  def orientation({:pi, _, _, body}, env), do: orientation(body, env)

  def orientation({:data, equality, [_level, _carrier], [left, right]}, env),
    do: orientation_eq(equality, left, right, env)

  def orientation({:data, equality, [_carrier], [left, right]}, env),
    do: orientation_eq(equality, left, right, env)

  def orientation(_type, _env), do: {:error, :not_equality}

  defp orientation_eq(equality, left, right, env) do
    cond do
      equality != Inductive.builtin(env, :eq) -> {:error, :not_equality}
      not first_order?(left) or not first_order?(right) -> {:error, :unsupported_binder}
      size(left) <= size(right) -> {:error, :non_decreasing_orientation}
      not variables_decrease?(left, right) -> {:error, :variable_duplication}
      true -> :ok
    end
  end

  def entries(env, head) do
    env
    |> Env.lemmas(head)
    |> Enum.filter(&(orientation(&1.type, env) == :ok))
    |> Enum.uniq_by(& &1.name)
  end

  # A common strict size ordering rules out cycles even between imported sets.
  # Variable multiplicities must not grow: small schematic RHSs can otherwise
  # become larger than their LHSs after substituting a large argument.
  defp variables_decrease?(left, right) do
    available = variables(left, %{})
    Enum.all?(variables(right, %{}), fn {index, count} -> count <= Map.get(available, index, 0) end)
  end

  defp variables({tag, _} = term, counts) when tag in [:type, :level_value],
    do: Enum.reduce(Cure.Core.Term.level_atoms(term), counts, &variables/2)

  defp variables({:var, index}, counts), do: Map.update(counts, index, 1, &(&1 + 1))
  defp variables(term, counts) when is_tuple(term), do: variables(Tuple.to_list(term), counts)
  defp variables(term, counts) when is_list(term), do: Enum.reduce(term, counts, &variables/2)
  defp variables(_leaf, counts), do: counts

  defp first_order?({tag, _} = term) when tag in [:type, :level_value],
    do: Enum.all?(Cure.Core.Term.level_atoms(term), &first_order?/1)

  defp first_order?(term) when is_tuple(term) do
    elem(term, 0) not in [:pi, :lam, :let, :case, :hole] and
      Enum.all?(Tuple.to_list(term), &first_order?/1)
  end

  defp first_order?(term) when is_list(term), do: Enum.all?(term, &first_order?/1)
  defp first_order?(_leaf), do: true

  def size({tag, _} = term) when tag in [:type, :level_value],
    do: 1 + Enum.sum(Enum.map(Cure.Core.Term.level_atoms(term), &size/1))

  def size(term) when is_tuple(term), do: 1 + size(Tuple.to_list(term))
  def size(term) when is_list(term), do: term |> Enum.map(&size/1) |> Enum.sum()
  def size(_leaf), do: 0
end

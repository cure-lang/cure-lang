defmodule Cure.Core.HistoricalFinite3 do
  @moduledoc """
  Explicit representation projection for the historical finite-0..2 Agda model.

  This adapter does not extend that model or prove current universe semantics.
  It accepts only new canonical finite closed sorts in the historical range.
  Open/high/limit sorts and all level terms are refused recursively. Current
  source, interfaces, serialization and runtime compilation never call this
  adapter as an admission restriction.
  """

  alias Cure.Core.{Grade, LevelValue, UniverseLevel}

  @identity {:cure_historical_finite3, 1}
  def transport_identity, do: @identity

  @doc "Project canonical current Core syntax to historical proof syntax explicitly."
  def project_finite3({:type, sort} = term) do
    case project_sort_finite3(sort) do
      {:ok, level} -> {:ok, {:type, level}}
      {:error, _} -> unsupported(term)
    end
  end

  def project_finite3({tag, grade, domain, body} = term) when tag in [:pi, :lam] do
    with true <- Grade.grade?(grade),
         {:ok, domain} <- project_finite3(domain),
         {:ok, body} <- project_finite3(body) do
      {:ok, {tag, grade, domain, body}}
    else
      false -> malformed(term)
      error -> error
    end
  end

  def project_finite3({:let, grade, type, value, body} = term) do
    with true <- Grade.grade?(grade),
         {:ok, type} <- project_finite3(type),
         {:ok, value} <- project_finite3(value),
         {:ok, body} <- project_finite3(body) do
      {:ok, {:let, grade, type, value, body}}
    else
      false -> malformed(term)
      error -> error
    end
  end

  def project_finite3({tag, left, right}) when tag in [:app, :effect_bind] do
    with {:ok, left} <- project_finite3(left),
         {:ok, right} <- project_finite3(right),
         do: {:ok, {tag, left, right}}
  end

  def project_finite3({tag, inner}) when tag in [:effect_type, :effect_pure] do
    with {:ok, inner} <- project_finite3(inner), do: {:ok, {tag, inner}}
  end

  def project_finite3({:data, name, params, indices} = term) do
    with true <- valid_name?(name),
         {:ok, params} <- terms(params),
         {:ok, indices} <- terms(indices) do
      {:ok, {:data, name, params, indices}}
    else
      false -> malformed(term)
      error -> error
    end
  end

  def project_finite3({:ctor, name, args} = term) do
    with true <- valid_name?(name),
         {:ok, args} <- terms(args) do
      {:ok, {:ctor, name, args}}
    else
      false -> malformed(term)
      error -> error
    end
  end

  def project_finite3({:case, scrutinee, motive, branches}) do
    with {:ok, scrutinee} <- project_finite3(scrutinee),
         {:ok, motive} <- project_finite3(motive),
         {:ok, branches} <- branches(branches) do
      {:ok, {:case, scrutinee, motive, branches}}
    end
  end

  def project_finite3({tag} = term)
      when tag in [:int_type, :float_type, :binary_type, :atom_type, :absurd],
      do: {:ok, term}

  def project_finite3({tag, n} = term)
      when tag in [:var, :nat_lit, :bounded_lit] and is_integer(n) and n >= 0,
      do: {:ok, term}

  def project_finite3({:int_lit, n} = term) when is_integer(n), do: {:ok, term}
  def project_finite3({:float_lit, n} = term) when is_float(n), do: unsupported(term)
  def project_finite3({:hole, name} = term) when is_binary(name), do: {:ok, term}

  def project_finite3({tag, name} = term) when tag in [:global, :atom_lit] do
    if valid_name?(name), do: {:ok, term}, else: malformed(term)
  end

  def project_finite3({:level_type} = term), do: unsupported(term)
  def project_finite3({:level_value, _} = term), do: unsupported(term)
  def project_finite3(term), do: malformed(term)

  @doc "Project only a new canonical closed finite sort, never an old integer."
  def project_sort_finite3({:finite, %UniverseLevel{constant: n, atoms: []} = level})
      when is_integer(n) and n in 0..2 do
    if UniverseLevel.validate(level, nil) == :ok, do: {:ok, n}, else: unsupported(level)
  end

  def project_sort_finite3(sort), do: unsupported(sort)

  @doc "Project a private semantic sort only after checking its exact representation."
  def project_value_sort_finite3({:finite, %LevelValue{constant: n, atoms: []} = level})
      when is_integer(n) and n in 0..2 do
    if LevelValue.valid?(level), do: {:ok, n}, else: unsupported(level)
  end

  def project_value_sort_finite3(sort), do: unsupported(sort)

  defp terms([]), do: {:ok, []}

  defp terms([term | rest]) do
    with {:ok, term} <- project_finite3(term),
         {:ok, rest} <- terms(rest),
         do: {:ok, [term | rest]}
  end

  defp terms(other), do: malformed(other)

  defp branches([]), do: {:ok, []}

  defp branches([{name, arity, body} | rest]) when is_integer(arity) and arity >= 0 do
    with true <- valid_name?(name),
         {:ok, body} <- project_finite3(body),
         {:ok, rest} <- branches(rest) do
      {:ok, [{name, arity, body} | rest]}
    else
      false -> malformed({name, arity, body})
      error -> error
    end
  end

  defp branches(other), do: malformed(other)
  defp unsupported(term), do: {:error, {:unsupported_term, term}}
  defp malformed(term), do: {:error, {:malformed_term, term}}
  defp valid_name?(name) when is_atom(name), do: true
  defp valid_name?(name) when is_binary(name), do: String.valid?(name)
  defp valid_name?(_), do: false
end

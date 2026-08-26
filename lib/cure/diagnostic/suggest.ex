defmodule Cure.Diagnostic.Suggest do
  @moduledoc """
  Deterministic name-candidate ranking for compiler diagnostics.

  Eligibility is decided before spelling distance: namespace, visibility,
  arity, and import/qualification usability always outrank a closer typo.
  """

  @type candidate :: %{
          required(:name) => String.t(),
          optional(:namespace) => atom() | String.t() | nil,
          optional(:visibility) => atom() | String.t() | nil,
          optional(:arity) => non_neg_integer() | nil,
          optional(:owner) => term(),
          optional(:imported) => boolean(),
          optional(:qualification) => term(),
          optional(:requires_import) => boolean(),
          optional(:origin) => term(),
          optional(:candidate_id) => term()
        }

  @doc "Return at most three semantically usable candidates in stable order."
  @spec rank([term()], String.t(), atom(), keyword()) :: [candidate()]
  def rank(candidates, spelling, namespace, opts \\ []) when is_list(candidates) do
    strict? = Enum.any?(candidates, &candidate_with_identity?/1)
    opts = Keyword.put(opts, :strict_candidate_filter, strict?)

    candidates
    |> Enum.map(&detail/1)
    |> Enum.filter(&allowed?(&1, namespace, opts))
    |> Enum.sort_by(fn candidate ->
      {
        unusable?(candidate),
        candidate.namespace not in [nil, namespace],
        arity_mismatch?(candidate.arity, Keyword.get(opts, :arity)),
        candidate.visibility not in [nil, :public],
        qualification_cost(candidate),
        distance(spelling, candidate.name),
        candidate.name
      }
    end)
    |> Enum.filter(&matches_spelling?(&1, spelling, strict?))
    |> Enum.uniq_by(&{&1.name, &1.owner, &1.candidate_id})
    |> Enum.take(3)
  end

  @doc "Compute case-insensitive restricted Damerau-Levenshtein distance."
  @spec distance(String.t(), String.t()) :: non_neg_integer()
  def distance(left, right) do
    left = String.downcase(left) |> String.graphemes()
    right = String.downcase(right) |> String.graphemes()
    left_size = length(left)
    right_size = length(right)

    cond do
      left_size == 0 ->
        right_size

      right_size == 0 ->
        left_size

      true ->
        matrix =
          Enum.reduce(0..left_size, %{}, &Map.put(&2, {&1, 0}, &1))
          |> then(fn matrix -> Enum.reduce(0..right_size, matrix, &Map.put(&2, {0, &1}, &1)) end)

        matrix =
          Enum.reduce(1..left_size, matrix, fn row, matrix ->
            Enum.reduce(1..right_size, matrix, fn column, matrix ->
              substitution =
                Map.fetch!(matrix, {row - 1, column - 1}) +
                  if(Enum.at(left, row - 1) == Enum.at(right, column - 1), do: 0, else: 1)

              transposition =
                if row > 1 and column > 1 and Enum.at(left, row - 1) == Enum.at(right, column - 2) and
                     Enum.at(left, row - 2) == Enum.at(right, column - 1) do
                  Map.fetch!(matrix, {row - 2, column - 2}) + 1
                else
                  substitution + 1
                end

              value =
                min(
                  Map.fetch!(matrix, {row - 1, column}) + 1,
                  min(Map.fetch!(matrix, {row, column - 1}) + 1, min(substitution, transposition))
                )

              Map.put(matrix, {row, column}, value)
            end)
          end)

        Map.fetch!(matrix, {left_size, right_size})
    end
  end

  defp allowed?(candidate, namespace, opts) do
    strict? = Keyword.get(opts, :strict_candidate_filter, false)

    (not strict? or not candidate.rich? or candidate.namespace in [nil, namespace]) and
      candidate.visibility not in [:private, "private"] and
      (not strict? or not arity_mismatch?(candidate.arity, Keyword.get(opts, :arity)))
  end

  defp matches_spelling?(%{rich?: false}, _spelling, _strict?), do: true
  defp matches_spelling?(_candidate, _spelling, false), do: true
  defp matches_spelling?(candidate, spelling, true), do: distance(spelling, candidate.name) <= 2

  defp candidate_with_identity?(candidate) when is_map(candidate),
    do: Map.has_key?(candidate, :id) or Map.has_key?(candidate, "id")

  defp candidate_with_identity?(_candidate), do: false

  defp detail(candidate) when is_map(candidate) do
    %{
      name: name(Map.get(candidate, :name, Map.get(candidate, "name", "<unknown>"))),
      namespace: Map.get(candidate, :namespace, Map.get(candidate, "namespace")),
      visibility: Map.get(candidate, :visibility, Map.get(candidate, "visibility")),
      arity: Map.get(candidate, :arity, Map.get(candidate, "arity")),
      owner: Map.get(candidate, :owner, Map.get(candidate, "owner")),
      imported: Map.get(candidate, :imported, Map.get(candidate, "imported", true)),
      qualification: Map.get(candidate, :qualification, Map.get(candidate, "qualification")),
      requires_import: Map.get(candidate, :requires_import, Map.get(candidate, "requires_import")),
      origin: Map.get(candidate, :origin, Map.get(candidate, "origin")),
      candidate_id: Map.get(candidate, :id, Map.get(candidate, "id", Map.get(candidate, :name))),
      rich?: true
    }
  end

  defp detail(candidate) do
    %{
      name: name(candidate),
      namespace: nil,
      visibility: nil,
      arity: nil,
      owner: nil,
      imported: true,
      qualification: nil,
      requires_import: false,
      origin: nil,
      candidate_id: candidate,
      rich?: false
    }
  end

  defp name(value) when is_binary(value), do: value
  defp name(value) when is_atom(value), do: Atom.to_string(value)
  defp name(value), do: to_string(value)

  defp unusable?(%{visibility: visibility, imported: imported}),
    do: visibility == :private or imported == false

  defp arity_mismatch?(_candidate, nil), do: false
  defp arity_mismatch?(nil, _expected), do: false
  defp arity_mismatch?(candidate, expected), do: candidate != expected

  defp qualification_cost(%{owner: nil}), do: 0
  defp qualification_cost(%{imported: true}), do: 0
  defp qualification_cost(_candidate), do: 1
end

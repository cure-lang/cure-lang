defmodule Cure.Core.SizeChange do
  @moduledoc """
  Trusted size-change matrix primitives.

  Graph search belongs to the elaborator, as in Agda's `CallGraph`; this module
  contains only the small algebra the kernel needs to replay a submitted
  derivation and check the Lee-Jones-Ben-Amram condition. Matrices follow Agda's
  `SparseMatrix` representation: dimensions are explicit and absent entries are
  `:unknown`. Composition visits only pairs of present arcs.
  """

  defmodule Matrix do
    @moduledoc "A sparse size-change matrix; absent coordinates mean `:unknown`."
    @enforce_keys [:rows, :columns, :entries]
    defstruct [:rows, :columns, :entries]

    @type t :: %__MODULE__{
            rows: non_neg_integer(),
            columns: non_neg_integer(),
            entries: %{{non_neg_integer(), non_neg_integer()} => Cure.Core.SizeChange.relation()}
          }
  end

  @type relation :: :smaller | :equal | :unknown
  @type matrix :: Matrix.t()
  @type legacy_matrix :: [[relation()]]
  @type edge :: %{source: atom(), target: atom(), matrix: matrix() | legacy_matrix()}

  @doc "Convert the former dense representation to canonical sparse storage."
  @spec from_dense(legacy_matrix()) :: matrix()
  def from_dense(rows) when is_list(rows) do
    row_count = length(rows)

    column_count =
      case rows do
        [] -> 0
        [row | _] -> length(row)
      end

    entries =
      rows
      |> Enum.with_index()
      |> Enum.reduce(%{}, fn {row, i}, acc ->
        if length(row) != column_count do
          raise ArgumentError, "ragged size-change matrix"
        end

        row
        |> Enum.with_index()
        |> Enum.reduce(acc, fn
          {:unknown, _j}, inner -> inner
          {relation, j}, inner when relation in [:smaller, :equal] -> Map.put(inner, {i, j}, relation)
          {relation, _j}, _inner -> raise ArgumentError, "invalid size-change relation: #{inspect(relation)}"
        end)
      end)

    %Matrix{rows: row_count, columns: column_count, entries: entries}
  end

  @doc "Materialize a sparse matrix for diagnostics and compatibility tests."
  @spec to_dense(matrix() | legacy_matrix()) :: legacy_matrix()
  def to_dense(%Matrix{} = matrix) do
    rows(matrix.rows, fn i ->
      rows(matrix.columns, fn j -> Map.get(matrix.entries, {i, j}, :unknown) end)
    end)
  end

  def to_dense(rows) when is_list(rows), do: rows

  @doc "Return canonical sparse storage for either supported input representation."
  @spec sparse(matrix() | legacy_matrix()) :: matrix()
  def sparse(%Matrix{} = matrix), do: matrix
  def sparse(rows) when is_list(rows), do: from_dense(rows)

  @spec compose_edges(edge(), edge()) :: {:ok, edge()} | :incompatible
  def compose_edges(%{target: middle} = left, %{source: middle} = right) do
    left_matrix = sparse(left.matrix)
    right_matrix = sparse(right.matrix)

    if right_matrix.columns == left_matrix.rows do
      {:ok,
       %{
         source: left.source,
         target: right.target,
         matrix: compose_matrices(right_matrix, left_matrix)
       }}
    else
      :incompatible
    end
  end

  def compose_edges(_left, _right), do: :incompatible

  @spec compose_matrices(matrix() | legacy_matrix(), matrix() | legacy_matrix()) :: matrix()
  def compose_matrices(a, b) do
    a = sparse(a)
    b = sparse(b)

    if a.columns != b.rows do
      raise ArgumentError,
            "incompatible size-change dimensions #{a.rows}×#{a.columns} and #{b.rows}×#{b.columns}"
    end

    # Agda's sparse multiplication indexes the right operand at the shared
    # coordinate. Unknown arcs are absent, so no dense i×j×k scan is needed.
    right_by_row =
      Enum.reduce(b.entries, %{}, fn {{k, j}, relation}, acc ->
        Map.update(acc, k, [{j, relation}], &[{j, relation} | &1])
      end)

    entries =
      Enum.reduce(a.entries, %{}, fn {{i, k}, left_relation}, acc ->
        Enum.reduce(Map.get(right_by_row, k, []), acc, fn {j, right_relation}, inner ->
          relation = path_multiply(left_relation, right_relation)
          Map.update(inner, {i, j}, relation, &add_relation(&1, relation))
        end)
      end)

    %Matrix{rows: a.rows, columns: b.columns, entries: entries}
  end

  @spec idempotent?(matrix() | legacy_matrix()) :: boolean()
  def idempotent?(matrix) do
    matrix = sparse(matrix)
    matrix.rows == matrix.columns and compose_matrices(matrix, matrix) == matrix
  end

  @spec smaller_diagonal?(matrix() | legacy_matrix()) :: boolean()
  def smaller_diagonal?(matrix) do
    matrix = sparse(matrix)

    matrix.rows > 0 and matrix.rows == matrix.columns and
      Enum.any?(0..(matrix.rows - 1)//1, &(Map.get(matrix.entries, {&1, &1}) == :smaller))
  end

  @doc "Return the complete diagonal, including implicit `:unknown` entries."
  @spec diagonal(matrix() | legacy_matrix()) :: [relation()]
  def diagonal(matrix) do
    matrix = sparse(matrix)
    size = min(matrix.rows, matrix.columns)
    rows(size, &Map.get(matrix.entries, {&1, &1}, :unknown))
  end

  defp path_multiply(:smaller, _), do: :smaller
  defp path_multiply(_, :smaller), do: :smaller
  defp path_multiply(:equal, :equal), do: :equal

  defp add_relation(:smaller, _), do: :smaller
  defp add_relation(_, :smaller), do: :smaller
  defp add_relation(:equal, :equal), do: :equal

  defp rows(n, _fun) when n <= 0, do: []
  defp rows(n, fun), do: Enum.map(0..(n - 1)//1, fun)
end

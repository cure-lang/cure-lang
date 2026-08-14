defmodule Cure.Core.SizeChange do
  @moduledoc """
  Trusted size-change matrix primitives.

  Graph search belongs to the elaborator, as in Agda's `CallGraph`; this module
  contains only the small algebra the kernel needs to replay a submitted
  derivation and check the Lee-Jones-Ben-Amram condition.
  """

  @type relation :: :smaller | :equal | :unknown
  @type matrix :: [[relation()]]
  @type edge :: %{source: atom(), target: atom(), matrix: matrix()}

  @spec compose_edges(edge(), edge()) :: {:ok, edge()} | :incompatible
  def compose_edges(%{target: middle} = left, %{source: middle} = right) do
    if row_length(right.matrix) == length(left.matrix) do
      {:ok,
       %{
         source: left.source,
         target: right.target,
         matrix: compose_matrices(right.matrix, left.matrix)
       }}
    else
      :incompatible
    end
  end

  def compose_edges(_left, _right), do: :incompatible

  @spec compose_matrices(matrix(), matrix()) :: matrix()
  def compose_matrices(a, b) do
    inner = length(b)
    columns = row_length(b)
    a = Enum.map(a, &List.to_tuple/1) |> List.to_tuple()
    b = Enum.map(b, &List.to_tuple/1) |> List.to_tuple()

    rows(tuple_size(a), fn i ->
      rows(columns, fn j ->
        reduce_inner(inner, fn k, acc ->
          add_relation(acc, path_multiply(elem(elem(a, i), k), elem(elem(b, k), j)))
        end)
      end)
    end)
  end

  @spec idempotent?(matrix()) :: boolean()
  def idempotent?(matrix), do: compose_matrices(matrix, matrix) == matrix

  @spec smaller_diagonal?(matrix()) :: boolean()
  def smaller_diagonal?(matrix) do
    size = length(matrix)
    tuples = Enum.map(matrix, &List.to_tuple/1) |> List.to_tuple()
    size > 0 and Enum.any?(0..(size - 1)//1, &(elem(elem(tuples, &1), &1) == :smaller))
  end

  defp path_multiply(:unknown, _), do: :unknown
  defp path_multiply(_, :unknown), do: :unknown
  defp path_multiply(:smaller, _), do: :smaller
  defp path_multiply(_, :smaller), do: :smaller
  defp path_multiply(:equal, :equal), do: :equal

  defp add_relation(:smaller, _), do: :smaller
  defp add_relation(_, :smaller), do: :smaller
  defp add_relation(:equal, _), do: :equal
  defp add_relation(_, :equal), do: :equal
  defp add_relation(:unknown, :unknown), do: :unknown

  defp rows(n, _fun) when n <= 0, do: []
  defp rows(n, fun), do: Enum.map(0..(n - 1)//1, fun)

  defp reduce_inner(n, _fun) when n <= 0, do: :unknown
  defp reduce_inner(n, fun), do: Enum.reduce(0..(n - 1)//1, :unknown, fun)

  defp row_length([]), do: 0
  defp row_length([row | _]), do: length(row)
end

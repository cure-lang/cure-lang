defmodule Antigen.Gen do
  @moduledoc "Reified, inspectable generator AST (spec §6). Data only; interpreted by a Backend."
  @type t ::
          {:return, term()}
          | {:member_of, [term()]}
          | {:integer, integer(), integer()}
          | {:one_of, [t()]}
          | {:frequency, [{pos_integer(), t()}]}
          | {:bind, t(), (term() -> t())}
          | {:sized, (non_neg_integer() -> t())}
          | {:resize, non_neg_integer(), t()}
          | {:tagged, :unsized | :size_monotonic, t()}
          | {:lazy, (-> t())}

  def return(x), do: {:return, x}
  def member_of(list) when is_list(list), do: {:member_of, list}
  def one_of(gens) when is_list(gens), do: {:one_of, gens}
  def frequency(weighted) when is_list(weighted), do: {:frequency, weighted}
  def bind(g, f) when is_function(f, 1), do: {:bind, g, f}
  def sized(f) when is_function(f, 1), do: {:sized, f}
  def resize(n, g) when is_integer(n) and n >= 0, do: {:resize, n, g}
  def tag(g, t) when t in [:unsized, :size_monotonic], do: {:tagged, t, g}
  def int(lo, hi) when lo <= hi, do: member_of(Enum.to_list(lo..hi))

  def integer(lo, hi) when is_integer(lo) and is_integer(hi) and lo <= hi,
    do: {:integer, lo, hi}

  @doc """
  Defer construction of a sub-generator until it is actually sampled. The backend
  interprets this without forcing `fun` until generation descends into it, so a
  recursively-built generator (e.g. `Generators.Term.gen/3`) materializes only
  along the sampled path — O(depth), not the O(branching^depth) that eager
  construction of the reified AST would cost. Like `bind`/`sized`, the thunk is
  opaque to `support/1` (it reports `:over_approx`).
  """
  def lazy(fun) when is_function(fun, 0), do: {:lazy, fun}

  @doc "Structural support over-approximation (spec §6). `bind`'s continuation is opaque."
  @spec support(t()) :: {:finite, MapSet.t()} | :over_approx
  def support({:return, x}), do: {:finite, MapSet.new([x])}
  def support({:member_of, xs}), do: {:finite, MapSet.new(xs)}
  def support({:integer, _lo, _hi}), do: :over_approx
  def support({:one_of, gs}), do: union_support(gs)
  def support({:frequency, ws}), do: union_support(Enum.map(ws, fn {_w, g} -> g end))
  def support({:resize, _n, g}), do: support(g)
  def support({:tagged, _t, g}), do: support(g)
  def support({:sized, _f}), do: :over_approx
  def support({:bind, _g, _f}), do: :over_approx
  def support({:lazy, _f}), do: :over_approx

  defp union_support(gs) do
    Enum.reduce_while(gs, {:finite, MapSet.new()}, fn g, {:finite, acc} ->
      case support(g) do
        {:finite, s} -> {:cont, {:finite, MapSet.union(acc, s)}}
        :over_approx -> {:halt, :over_approx}
      end
    end)
  end
end

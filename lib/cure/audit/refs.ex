defmodule Cure.Audit.Refs do
  @moduledoc """
  A **fail-closed** walk over `Cure.Core.Term`.

  `Cure.Elab.Program.global_refs/1` ends in a catch-all `_leaf -> []`. That is
  benign for codegen and fatal for an audit: when the Core grammar grows a
  former, reachability silently under-reports and the ledger quietly stops
  finding axioms. (It has already happened — `global_refs/1` has no `:let`
  clause.)

  Every clause of `Cure.Core.Term.term?/1` is enumerated here explicitly, and
  anything else raises. The two exceptions are non-`Core.Term` sentinels that
  occupy a def's `body` slot: `{:extern, mfa}` and `nil` (every `builtin_op`).

  Untrusted; outside the TCB.
  """

  @type scan :: %{
          globals: [atom()],
          families: [atom()],
          holes: [String.t()],
          absurd: non_neg_integer()
        }

  @empty %{globals: [], families: [], holes: [], absurd: 0}

  @spec globals(term()) :: [atom()]
  def globals(t), do: scan(t).globals

  @doc """
  The inductive families a term mentions, by canonical family key.

  Constructors are deliberately not counted: a ctor key (`Std.List#Cons`) does
  not name its family (`Std.List#List`), and the one consumer — the trust
  ledger's opaque-type surface — is asking about types that appear in a
  signature, which is always a `:data` occurrence.
  """
  @spec families(term()) :: [atom()]
  def families(t), do: scan(t).families

  @spec scan(term()) :: scan()
  def scan(t) do
    acc = walk(t, @empty)

    %{
      acc
      | globals: acc.globals |> Enum.uniq() |> Enum.sort(),
        families: acc.families |> Enum.uniq() |> Enum.sort(),
        holes: Enum.sort(acc.holes)
    }
  end

  # -- non-Core sentinels occupying a def's `body` slot -----------------------

  defp walk({:extern, {m, f, a}}, acc) when is_atom(m) and is_atom(f) and is_integer(a), do: acc
  defp walk(nil, acc), do: acc

  # -- Core.Term, one clause per term?/1 clause -------------------------------

  defp walk({:global, name}, acc), do: %{acc | globals: [name | acc.globals]}
  defp walk({:hole, name}, acc), do: %{acc | holes: [name | acc.holes]}
  defp walk({:absurd}, acc), do: %{acc | absurd: acc.absurd + 1}

  defp walk({:type, _}, acc), do: acc
  defp walk({:var, _}, acc), do: acc
  defp walk({:int_type}, acc), do: acc
  defp walk({:int_lit, _}, acc), do: acc
  defp walk({:nat_lit, _}, acc), do: acc
  defp walk({:bounded_lit, _}, acc), do: acc
  defp walk({:float_type}, acc), do: acc
  defp walk({:float_lit, _}, acc), do: acc
  defp walk({:binary_type}, acc), do: acc
  defp walk({:atom_type}, acc), do: acc
  defp walk({:atom_lit, _}, acc), do: acc
  defp walk({:effect_type, payload}, acc), do: walk(payload, acc)
  defp walk({:effect_pure, value}, acc), do: walk(value, acc)

  defp walk({:effect_bind, effect, continuation}, acc),
    do: acc |> then(&walk(effect, &1)) |> then(&walk(continuation, &1))

  # `:pi`/`:lam`/`:let` carry a QTT grade (`:erased`/`:linear`/`:affine`/
  # `:unrestricted`) — an atom with no globals, so it is ignored.
  defp walk({:pi, _g, dom, cod}, acc), do: acc |> then(&walk(dom, &1)) |> then(&walk(cod, &1))
  defp walk({:lam, _g, dom, body}, acc), do: acc |> then(&walk(dom, &1)) |> then(&walk(body, &1))

  defp walk({:let, _g, ty, val, body}, acc),
    do: acc |> then(&walk(ty, &1)) |> then(&walk(val, &1)) |> then(&walk(body, &1))

  defp walk({:app, f, a}, acc), do: acc |> then(&walk(f, &1)) |> then(&walk(a, &1))

  defp walk({:data, name, params, indices}, acc),
    do: Enum.reduce(params ++ indices, %{acc | families: [name | acc.families]}, &walk/2)

  defp walk({:ctor, _name, args}, acc), do: Enum.reduce(args, acc, &walk/2)

  defp walk({:case, scrut, motive, branches}, acc) do
    acc
    |> then(&walk(scrut, &1))
    |> then(&walk(motive, &1))
    |> then(fn a -> Enum.reduce(branches, a, fn {_c, _arity, body}, a2 -> walk(body, a2) end) end)
  end

  defp walk(other, _acc) do
    raise ArgumentError, "unknown Core term in Audit.Refs: #{inspect(other)}"
  end
end

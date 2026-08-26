defmodule Antigen.Generators.Context do
  @moduledoc """
  Generates Γ as a genuinely dependent telescope (spec §5.1): a size-bounded
  number of entries, each entry's TYPE generated in the context of the entries
  outer to it, so an inner entry may depend on an outer one (e.g. `Vec(n)` after
  `n : Nat`). Deliberately repeats type shapes at nearby positions so de Bruijn
  arithmetic is exercised. Returns a kernel-order list (index 0 = innermost).
  """
  alias Antigen.Gen
  alias Antigen.Generators.SigMenu

  @spec gen(Cure.Core.Env.t()) :: Gen.t()
  def gen(env) do
    Gen.sized(fn size ->
      count = min(size, 4)
      build(env, [], count)
    end)
  end

  # Accumulate entries innermost-LAST; we prepend each new inner entry so the
  # returned list is kernel-order (index 0 innermost). `acc` is the telescope
  # built so far in kernel order.
  defp build(_env, acc, 0), do: Gen.return(acc)

  defp build(env, acc, n) do
    Gen.bind(entry_type(env, acc), fn ty ->
      build(env, [ty | acc], n - 1)
    end)
  end

  # A type valid in the current prefix (= the acc telescope). Depends on what is
  # already in scope: `Vec(n)` is only offered when some `n : Nat` variable
  # exists in acc. `Nat`/`Bd` are always available (and repeated to force
  # shadowing / nearby de Bruijn reuse).
  defp entry_type(_env, acc) do
    nat_vars = nat_var_indices(acc)

    vec_choices =
      for k <- nat_vars, do: {2, Gen.return(SigMenu.vec({:var, k}))}

    Gen.frequency([
      {3, Gen.return(SigMenu.nat())},
      {2, Gen.return(SigMenu.bd())},
      {1, Gen.return(SigMenu.vec({:ctor, :Z, []}))}
      | vec_choices
    ])
  end

  # Indices (into the FUTURE context, i.e. counting from the body that will sit
  # under the whole telescope) of acc entries whose type is exactly Nat. `acc` is
  # kernel-order with the innermost bound entry at the head; an entry at position
  # `i` in `acc` (0 = head/innermost-so-far) sits at de Bruijn index `i` relative
  # to a new entry prepended in front of it.
  defp nat_var_indices(acc) do
    acc
    |> Enum.with_index()
    |> Enum.filter(fn {ty, _i} -> match?({:data, :Nat, [], []}, ty) end)
    |> Enum.map(fn {_ty, i} -> i end)
  end
end

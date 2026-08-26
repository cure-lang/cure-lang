defmodule Cure.Core.Quote do
  @moduledoc """
  Read-back (quote): convert a `Cure.Core.Value` into a **β-normal**
  `Cure.Core.Term` (design spec §4.5; mirrors Idris `Core/Normalise/Quote.idr`).

  `depth` is the number of binders entered so far. A neutral variable carries a
  de Bruijn *level*; read-back converts it to an index via `depth - level - 1`.
  Going under a binder, we apply the closure to a fresh neutral at the current
  level and reify the result at `depth + 1`, exactly as Idris's `quoteGenNF`
  does for `NBind` (and `quoteBinder` reifies the binder's domain type).

  η is **not** performed here — read-back stays untyped and β-normal. η-equality
  is decided in `Cure.Core.Conv` (it needs the neutral's type, which a `Value`
  does not carry).

  ## Signature-aware read-back (`sig`)

  A data VALUE `{:vdata, name, args}` flattens a family's parameters and indices
  into one arg list (M3.4). Without the family signature the split is not
  recoverable, so read-back defaults (`sig = nil`) to putting them all in the
  `params` slot with empty `indices` — the flat form that conversion compares
  (conversion never asks for the split, so this stays consistent). When a caller
  that DOES need the split passes the signature (`Env.t()`), the `{:vdata}`
  read-back recovers `{:data, name, params, indices}` from the family's parameter
  telescope length — Agda `getNumberOfParameters` / Lean `inductive_val.get_nparams`
  prior art. This is required by the kernel's motive-well-formedness check, which
  reifies indexed-family Eq endpoints and re-`check`s them against their type (a
  collapsed split otherwise fails with an arity error and false-rejects the motive).
  """

  alias Cure.Core.Eval

  @doc """
  Read a value back into a β-normal term. `depth` = binders entered so far.
  `sig` (optional) is the inductive signature used to recover the param/index
  split of data values; `nil` (default) keeps the flat read-back.
  """
  @spec reify(Cure.Core.Value.t(), non_neg_integer(), Cure.Core.Env.t() | nil) ::
          Cure.Core.Term.t()
  def reify(value, depth \\ 0, sig \\ nil)

  def reify({:vtype, level}, _depth, _sig), do: {:type, level}

  def reify({:vpi, g, dom, {:closure, env, cod}}, depth, sig) do
    body = Eval.eval(cod, [{:vneutral, {:nvar, depth}} | env])
    {:pi, g, reify(dom, depth, sig), reify(body, depth + 1, sig)}
  end

  def reify({:vlam, g, dom, {:closure, env, b}}, depth, sig) do
    body = Eval.eval(b, [{:vneutral, {:nvar, depth}} | env])
    {:lam, g, reify(dom, depth, sig), reify(body, depth + 1, sig)}
  end

  # Data value read-back. With a signature the param/index split is recovered from
  # the family's parameter telescope length; without one, all args stay in `params`
  # (the flat form conversion compares). See the moduledoc.
  def reify({:vdata, name, vs}, depth, sig) do
    {params, indices} = split_data_args(name, vs, sig)
    {:data, name, Enum.map(params, &reify(&1, depth, sig)), Enum.map(indices, &reify(&1, depth, sig))}
  end

  def reify({:vctor, name, vs}, depth, sig), do: {:ctor, name, Enum.map(vs, &reify(&1, depth, sig))}

  # NOTE(int-facade): kept so read-back stays total on a legacy/deserialized
  # `{:vint_type}` value, even though fresh elaboration never produces one
  # (spec 2026-07-18 §3a).
  def reify({:vint_type}, _depth, _sig), do: {:int_type}
  def reify({:vint, n}, _depth, _sig), do: {:int_lit, n}
  # Read a compact Nat back to a compact literal term — NOT an `S`-tower (which
  # would reintroduce the blow-up at read-back time).
  def reify({:vnat, n}, _depth, _sig), do: {:nat_lit, n}
  def reify({:vbounded, n}, _depth, _sig), do: {:bounded_lit, n}
  def reify({:vfloat_type}, _depth, _sig), do: {:float_type}
  def reify({:vbinary_type}, _depth, _sig), do: {:binary_type}
  def reify({:vfloat, f}, _depth, _sig), do: {:float_lit, f}
  def reify({:vatom_type}, _depth, _sig), do: {:atom_type}
  def reify({:vatom, a}, _depth, _sig), do: {:atom_lit, a}

  # Inert effect values read back structurally into their term nodes — shape
  # preserved exactly, subterms reified at the same depth (nothing binds here).
  def reify({:veffect_type, v}, depth, sig), do: {:effect_type, reify(v, depth, sig)}
  def reify({:veffect_pure, v}, depth, sig), do: {:effect_pure, reify(v, depth, sig)}

  def reify({:veffect_bind, ve, vk}, depth, sig),
    do: {:effect_bind, reify(ve, depth, sig), reify(vk, depth, sig)}

  def reify({:vneutral, n}, depth, sig), do: reify_neutral(n, depth, sig)

  # -- data param/index split -------------------------------------------------

  # Recover a data value's (params, indices) split. `nil` signature → cannot split,
  # so all args are params (flat read-back). With a signature, the first
  # `length(family.params)` args are parameters and the rest are indices (Agda
  # `getNumberOfParameters` / Lean `get_nparams`). An unknown family also stays flat
  # — never unsound, at worst the pre-existing collapse.
  defp split_data_args(_name, vs, nil), do: {vs, []}

  defp split_data_args(name, vs, sig) do
    case Cure.Core.Inductive.get_family(sig, name) do
      %{params: ptele} -> Enum.split(vs, length(ptele))
      _ -> {vs, []}
    end
  end

  # -- neutrals ---------------------------------------------------------------

  defp reify_neutral({:nvar, level}, depth, _sig), do: {:var, depth - level - 1}
  defp reify_neutral({:nglobal, name}, _depth, _sig), do: {:global, name}
  # A hole neutral reads back to its `{:hole, id}` term; a spined hole reads back
  # via the `{:napp, …}` arm below, reconstructing the original application
  # (first-class holes).
  defp reify_neutral({:nhole, id}, _depth, _sig), do: {:hole, id}

  defp reify_neutral({:napp, n, v}, depth, sig),
    do: {:app, reify_neutral(n, depth, sig), reify(v, depth, sig)}

  defp reify_neutral({:ncase, neutral, motive_cl, branch_cls}, depth, sig) do
    scrut = reify_neutral(neutral, depth, sig)
    motive = reify(instantiate(motive_cl), depth, sig)
    branches = Enum.map(branch_cls, fn {c, ar, cl} -> {c, ar, reify_branch(cl, ar, depth, sig)} end)
    {:case, scrut, motive, branches}
  end

  # Evaluate a closure body in its captured environment (no extra binder).
  defp instantiate({:closure, env, term}), do: Eval.eval(term, env)

  # Read a branch-body closure back under the constructor's `arity` binders.
  defp reify_branch({:closure, env, body}, arity, depth, sig),
    do: reify(Eval.open_branch(env, body, arity, depth), depth + arity, sig)
end

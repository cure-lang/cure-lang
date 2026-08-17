defmodule Cure.Elab.Subst.Prefix do
  @moduledoc false

  alias Cure.Elab.CallAttemptProfile

  @chunk_size 32
  defstruct size: 0, chunks: %{}

  @type t :: %__MODULE__{size: non_neg_integer(), chunks: %{non_neg_integer() => tuple()}}

  @spec new([term()]) :: t()
  def new(values) when is_list(values) do
    chunks =
      values
      |> Enum.with_index()
      |> Enum.group_by(fn {_value, index} -> div(index, @chunk_size) end, fn {value, _index} -> value end)
      |> Map.new(fn {chunk, entries} -> {chunk, List.to_tuple(entries)} end)

    %__MODULE__{size: length(values), chunks: chunks}
  end

  @spec get(t(), non_neg_integer()) :: term()
  def get(%__MODULE__{size: size} = prefix, index) when index >= 0 and index < size do
    CallAttemptProfile.increment(:constructor_prefix_cells_read)

    prefix.chunks
    |> Map.fetch!(div(index, @chunk_size))
    |> elem(rem(index, @chunk_size))
  end

  @spec put(t(), non_neg_integer(), term()) :: t()
  def put(%__MODULE__{} = prefix, index, value) when index >= 0 and index < prefix.size do
    CallAttemptProfile.increment(:constructor_prefix_cells_reused)

    chunk_index = div(index, @chunk_size)
    chunk = Map.fetch!(prefix.chunks, chunk_index)
    updated = put_elem(chunk, rem(index, @chunk_size), value)
    %{prefix | chunks: Map.put(prefix.chunks, chunk_index, updated)}
  end

  @spec materialize(t(), non_neg_integer()) :: [term()]
  def materialize(_prefix, 0), do: []

  def materialize(%__MODULE__{} = prefix, count) when count >= 0 and count <= prefix.size do
    CallAttemptProfile.increment(:constructor_prefix_cells_materialized, count)

    for index <- 0..(count - 1)//1, do: get(prefix, index)
  end
end

defmodule Cure.Elab.Subst.Frame do
  @moduledoc false

  alias Cure.Elab.Subst.Prefix
  alias Cure.Elab.CallAttemptProfile

  defstruct params: {}, prefix: nil, prefix_size: 0, zonker: nil

  @type t :: %__MODULE__{
          params: tuple(),
          prefix: Prefix.t(),
          prefix_size: non_neg_integer(),
          zonker: (term() -> term()) | nil
        }

  @spec new([term()], Prefix.t(), non_neg_integer()) :: t()
  @spec new([term()], Prefix.t(), non_neg_integer(), (term() -> term()) | nil) :: t()
  def new(params, %Prefix{} = prefix, prefix_size, zonker \\ nil) when prefix_size >= 0 do
    CallAttemptProfile.increment(:constructor_prefix_frames)

    %__MODULE__{params: List.to_tuple(params), prefix: prefix, prefix_size: prefix_size, zonker: zonker}
  end

  @spec size(t()) :: non_neg_integer()
  def size(%__MODULE__{params: params, prefix_size: prefix_size}),
    do: tuple_size(params) + prefix_size

  @spec get(t(), non_neg_integer()) :: term()
  def get(%__MODULE__{} = frame, index) when is_integer(index) do
    telescope_index = size(frame) - 1 - index
    params_size = tuple_size(frame.params)

    if telescope_index < params_size do
      elem(frame.params, telescope_index)
    else
      value = Prefix.get(frame.prefix, telescope_index - params_size)
      if is_function(frame.zonker, 1), do: frame.zonker.(value), else: value
    end
  end
end

defmodule Cure.Elab.Subst do
  @moduledoc """
  De Bruijn shifting and telescope instantiation for *elaborator* terms — Core
  terms that may still carry unsolved metavariables `{:meta, id}` (design spec
  §5.3).

  The trusted kernel's `Core.Term.shift`/`subst` cannot be reused here: they do
  not know about `{:meta, …}` (metavariables never reach the kernel), and the
  kernel instantiates telescopes by evaluating in a value environment — a path
  that would drag metavariables into the trusted evaluator. So the untrusted
  elaborator carries its own meta-aware substitution.

  `instantiate/2` replaces a term's leading de Bruijn binders with a list of
  closed values in telescope order (`values[0]` is the outermost binder), and
  strengthens any variable that referred past the telescope. This is the operation
  constructor-application inference uses to specialise each argument's expected
  type given the arguments chosen so far.

  ## Both walkers are TOTAL over `Core.Term.t()`, and FAIL CLOSED

  This module is a *renumberer*: its whole contract is that every `{:var, i}` in
  the term comes out correctly renumbered, and every other field comes out
  untouched. A missed compound former violates the first half silently (the
  variables inside it are returned unrenumbered, pointing at the wrong binder),
  and a rebuilt-but-altered field violates the second half silently. Both have
  happened here, and neither was caught by anything downstream:

    * `{:effect_pure, _}` and `{:effect_bind, _, _}` had no clause and fell to an
      identity catch-all, so variables inside an effect payload were never
      renumbered at all. Via `wrap_join` that rejected well-typed effectful
      programs; via `Erase`'s collapsible-case optimisation — which runs AFTER the
      kernel, with nothing to re-verify it — it silently resolved a variable to
      the wrong binder and emitted wrong code.

    * Every binder clause rebuilt its node with `Grade.unrestricted()` hardcoded,
      discarding the incoming grade. On `:pi`/`:lam` that is invisible, because
      `Kernel.infer` re-derives those grades from the registered declaration. On
      `:let` there is nothing to re-derive from — `Relevance` is the only reader of
      a let's grade in the entire codebase — so this silently erased the binder's
      usage obligation, and an `:erased` proof could be used at runtime.

  So: **every leaf is enumerated explicitly, every compound former is enumerated
  explicitly, and anything else raises.** A term is not permitted to pass through
  here unrecognised. The next former added to `Core.Term` breaks this module
  loudly, at the exact two functions that must be taught about it, instead of
  being silently treated as a leaf. This is the same doctrine `Unify.escapes?`
  already states for itself; `Subst` predates it.
  """

  alias Cure.Core.Term
  alias Cure.Elab.Subst.Frame

  @type uterm :: Term.t() | {:meta, non_neg_integer()}

  # Leaves: no subterms, so nothing to renumber. `{:meta, _}` is elaborator-only.
  # Enumerated by tag/arity rather than caught by a wildcard — see the moduledoc.
  defguardp is_leaf(t)
            when is_tuple(t) and
                   elem(t, 0) in [
                     :var,
                     :meta,
                     :type,
                     :global,
                     :int_type,
                     :int_lit,
                     :nat_lit,
                     :bounded_lit,
                     :float_type,
                     :float_lit,
                     :binary_type,
                     :atom_type,
                     :atom_lit,
                     :hole,
                     :absurd
                   ]

  @doc """
  Instantiate the outermost `length(values)` binders of `term` with `values`
  (telescope order: `values[0]` replaces the outermost binder). Variables beyond
  the telescope are strengthened by `length(values)`.
  """
  @spec instantiate(uterm(), [uterm()]) :: uterm()
  def instantiate(term, values) when is_list(values) do
    env = Enum.reverse(values)
    replace(term, env, length(env), 0)
  end

  @spec instantiate(uterm(), Frame.t()) :: uterm()
  def instantiate(term, %Frame{} = frame), do: replace(term, frame, Frame.size(frame), 0)

  # `env` maps de Bruijn index j (0-based, innermost telescope binder first) to
  # its replacement; `k` = telescope size; `depth` = binders crossed so far.
  defp replace({:var, i}, env, k, depth) do
    cond do
      i < depth -> {:var, i}
      i - depth < k -> shift(env_get(env, i - depth), depth, 0)
      true -> {:var, i - k}
    end
  end

  # Binders. The grade is THREADED, never rebuilt: this walker renumbers variables
  # and must not have an opinion about anything else.
  defp replace({:pi, g, d, c}, env, k, depth),
    do: {:pi, g, replace(d, env, k, depth), replace(c, env, k, depth + 1)}

  defp replace({:lam, g, d, b}, env, k, depth),
    do: {:lam, g, replace(d, env, k, depth), replace(b, env, k, depth + 1)}

  defp replace({:let, g, t, v, b}, env, k, depth),
    do: {:let, g, replace(t, env, k, depth), replace(v, env, k, depth), replace(b, env, k, depth + 1)}

  defp replace({:app, f, x}, env, k, depth),
    do: {:app, replace(f, env, k, depth), replace(x, env, k, depth)}

  defp replace({:data, n, ps, is}, env, k, depth),
    do: {:data, n, Enum.map(ps, &replace(&1, env, k, depth)), Enum.map(is, &replace(&1, env, k, depth))}

  defp replace({:ctor, n, args}, env, k, depth),
    do: {:ctor, n, Enum.map(args, &replace(&1, env, k, depth))}

  defp replace({:case, s, m, brs}, env, k, depth) do
    {:case, replace(s, env, k, depth), replace(m, env, k, depth),
     Enum.map(brs, fn {cn, ar, b} -> {cn, ar, replace(b, env, k, depth + ar)} end)}
  end

  # Effect formers bind nothing themselves — the continuation's binder lives in the
  # `:lam` that `effect_bind` carries — so every subterm is walked at the SAME depth,
  # exactly like `:app`. Mirrors the trusted `Core.Term.subst`.
  defp replace({:effect_type, inner}, env, k, depth),
    do: {:effect_type, replace(inner, env, k, depth)}

  defp replace({:effect_pure, a}, env, k, depth),
    do: {:effect_pure, replace(a, env, k, depth)}

  defp replace({:effect_bind, e, kont}, env, k, depth),
    do: {:effect_bind, replace(e, env, k, depth), replace(kont, env, k, depth)}

  defp replace(leaf, _env, _k, _depth) when is_leaf(leaf), do: leaf
  defp replace(other, _env, _k, _depth), do: unrecognised!(other, "replace/4")

  defp env_get(%Frame{} = frame, index), do: Frame.get(frame, index)
  defp env_get(env, index), do: Enum.at(env, index)

  @doc "Shift free de Bruijn variables of a (meta-bearing) term above `cutoff` by `amount`."
  @spec shift(uterm(), integer(), non_neg_integer()) :: uterm()
  def shift(term, 0, _cutoff), do: term

  def shift({:var, i}, amount, cutoff) when i >= cutoff, do: {:var, i + amount}
  def shift({:var, _} = v, _amount, _cutoff), do: v

  def shift({:pi, g, d, c}, amount, cutoff),
    do: {:pi, g, shift(d, amount, cutoff), shift(c, amount, cutoff + 1)}

  def shift({:lam, g, d, b}, amount, cutoff),
    do: {:lam, g, shift(d, amount, cutoff), shift(b, amount, cutoff + 1)}

  def shift({:let, g, t, v, b}, amount, cutoff),
    do: {:let, g, shift(t, amount, cutoff), shift(v, amount, cutoff), shift(b, amount, cutoff + 1)}

  def shift({:app, f, x}, amount, cutoff),
    do: {:app, shift(f, amount, cutoff), shift(x, amount, cutoff)}

  def shift({:data, n, ps, is}, amount, cutoff),
    do: {:data, n, Enum.map(ps, &shift(&1, amount, cutoff)), Enum.map(is, &shift(&1, amount, cutoff))}

  def shift({:ctor, n, args}, amount, cutoff),
    do: {:ctor, n, Enum.map(args, &shift(&1, amount, cutoff))}

  def shift({:case, s, m, brs}, amount, cutoff) do
    {:case, shift(s, amount, cutoff), shift(m, amount, cutoff),
     Enum.map(brs, fn {cn, ar, b} -> {cn, ar, shift(b, amount, cutoff + ar)} end)}
  end

  def shift({:effect_type, inner}, amount, cutoff),
    do: {:effect_type, shift(inner, amount, cutoff)}

  def shift({:effect_pure, a}, amount, cutoff),
    do: {:effect_pure, shift(a, amount, cutoff)}

  def shift({:effect_bind, e, kont}, amount, cutoff),
    do: {:effect_bind, shift(e, amount, cutoff), shift(kont, amount, cutoff)}

  def shift(leaf, _amount, _cutoff) when is_leaf(leaf), do: leaf
  def shift(other, _amount, _cutoff), do: unrecognised!(other, "shift/3")

  # FAIL CLOSED. A former this module has never been taught about cannot be assumed
  # to be a leaf: if it carries subterms, treating it as one returns its variables
  # unrenumbered and the caller cannot tell the difference. Raise instead.
  @spec unrecognised!(term(), String.t()) :: no_return()
  defp unrecognised!(other, fun) do
    raise ArgumentError,
          "Cure.Elab.Subst.#{fun}: unrecognised Core former #{inspect(other, limit: 3)}. " <>
            "Every former in Core.Term.t() must be enumerated here — a compound former " <>
            "silently treated as a leaf returns its subterms' de Bruijn indices unrenumbered."
  end
end

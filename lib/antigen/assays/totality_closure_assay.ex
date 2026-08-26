defmodule Antigen.Assays.TotalityClosureAssay do
  @moduledoc """
  Property tests for the untrusted totality-closure driver
  `Cure.Elab.TotalityClosure` (spec: antigen-totality-closure).

    * totality_closure/soundness    — a diverging function reachable from a type
      position must be REJECTED by `certify_type_level` (V5a). An all-total env
      must certify (`:accept` control).
    * totality_closure/completeness — `type_level_fns(env)` is a superset of an
      independent type-position reachability walk (V5b).

  The driver ops go through an injectable @real map (run/2); negative controls
  weaken them without touching `Cure.Elab`/`Cure.Core` or using :meck.
  """
  alias Antigen.Challenge
  alias Cure.Elab.TotalityClosure
  alias Cure.Core.Env

  @real %{
    certify: &TotalityClosure.certify_type_level/1,
    type_level_fns: &TotalityClosure.type_level_fns/1
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :closure_env} = c), do: run(c, @real)

  def run(%Challenge{kind: :closure_env, assay: "totality_closure/soundness", payload: %{env: env, expect: :reject}}, k) do
    case k.certify.(env) do
      {:error, {:totality_required, _}} -> :ok
      {:ok, _} -> {:violation, {:diverging_certified, env}}
      other -> {:violation, {:unexpected_certify_result, other}}
    end
  end

  def run(%Challenge{kind: :closure_env, assay: "totality_closure/soundness", payload: %{env: env, expect: :accept}}, k) do
    case k.certify.(env) do
      {:ok, _} -> :ok
      other -> {:violation, {:total_env_not_certified, other}}
    end
  end

  def run(%Challenge{kind: :closure_env, assay: "totality_closure/completeness", payload: %{env: env}}, k) do
    independent = __reachable__(env)
    closure = k.type_level_fns.(env)
    missing = MapSet.difference(independent, closure)

    if MapSet.size(missing) == 0 do
      :ok
    else
      {:violation, {:closure_missed, MapSet.to_list(missing)}}
    end
  end

  @doc false
  # Independent re-derivation of type-position reachability (spec §3 V5b), over
  # the FULL Cure.Core.Term taxonomy. ({:prim} retired, K2: builtin-op spines
  # are ordinary :app chains, and their op names — int_add, int_eq, … — appear
  # in call graphs as terminal nodes with no body to close over.) Returns a
  # MapSet of global names.
  def __reachable__(%Env{} = env) do
    seeds = reach_seeds(env)
    reach_close(env, MapSet.to_list(seeds), seeds)
  end

  defp reach_seeds(%Env{families: fams, ctors: cts}) do
    from_fams = fams |> Map.values() |> Enum.flat_map(fn f -> tele(f.params) ++ tele(f.indices) end)

    from_cts =
      cts |> Map.values() |> Enum.flat_map(fn c -> tele(c.args) ++ Enum.flat_map(c.result_indices, &globals/1) end)

    MapSet.new(from_fams ++ from_cts)
  end

  defp tele(t), do: Enum.flat_map(t, fn {_n, ty} -> globals(ty) end)

  defp reach_close(_env, [], acc), do: acc

  defp reach_close(env, [n | rest], acc) do
    case Env.get_def(env, n) do
      nil ->
        reach_close(env, rest, acc)

      %{body: b} ->
        fresh = b |> globals() |> Enum.reject(&MapSet.member?(acc, &1))
        reach_close(env, rest ++ fresh, Enum.reduce(fresh, acc, &MapSet.put(&2, &1)))
    end
  end

  defp globals({:global, n}), do: [n]
  defp globals({:pi, _g, d, c}), do: globals(d) ++ globals(c)
  defp globals({:lam, _g, d, b}), do: globals(d) ++ globals(b)
  defp globals({:app, f, a}), do: globals(f) ++ globals(a)
  defp globals({:data, _n, ps, is}), do: Enum.flat_map(ps, &globals/1) ++ Enum.flat_map(is, &globals/1)
  defp globals({:ctor, _n, args}), do: Enum.flat_map(args, &globals/1)

  defp globals({:case, s, m, brs}),
    do: globals(s) ++ globals(m) ++ Enum.flat_map(brs, fn {_c, _ar, b} -> globals(b) end)

  # Fail closed on an unrecognized node, exactly as `TotalityClosure.collect/1` does. This
  # walker is the INDEPENDENT oracle for that one, and a catch-all `[]` here reproduced the
  # subject's blind spot verbatim: both sides missed a global reachable only through a node
  # neither list names, so the completeness property could never fail. An oracle that shares
  # its subject's bug tests nothing.
  defp globals(term) when is_tuple(term) do
    term
    |> Tuple.to_list()
    |> Enum.flat_map(fn
      child when is_tuple(child) -> globals(child)
      children when is_list(children) -> Enum.flat_map(children, &globals_child/1)
      _leaf -> []
    end)
  end

  defp globals(_), do: []

  defp globals_child(child) when is_tuple(child), do: globals(child)
  defp globals_child(_other), do: []
end

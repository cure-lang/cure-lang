defmodule Cure.Elab.DirectCallProvenance do
  @moduledoc """
  Correlates expanded surface call sites with final trusted Core call ordinals.

  Core deliberately carries no source locations. After a body has elaborated
  successfully, its trusted direct-call summary supplies stable Core ordinals
  while the expanded MetaAST still supplies authored spans and macro expansion
  frames. This module joins those diagnostic projections by canonical callee
  and occurrence order. Elaborator-inserted calls simply have no matching
  surface site and retain semantic Core-only provenance.

  Attached fields are excluded from direct-summary and module-interface
  semantic hashes. They can improve a rejection but never affect acceptance.
  """

  alias Cure.Core.{Certificate, Env}
  alias Cure.Elab.Resolution
  alias Cure.MetaAST.Metadata

  @spec attach(Env.t(), atom(), term()) :: Env.t()
  def attach(%Env{} = env, name, expanded_body) do
    key = Env.resolve_key(env, env.defs, name)

    case Env.direct_call_summary(env, key) do
      nil ->
        env

      summary ->
        sites = expanded_body |> collect_sites(env, []) |> Enum.reverse()
        queues = Enum.group_by(sites, & &1.callee)

        {provenance_by_path, _queues} =
          summary.calls
          |> Enum.sort_by(& &1.provenance.core_path)
          |> Enum.reduce({%{}, queues}, fn call, {provenance, remaining} ->
            case Map.get(remaining, call.callee, []) do
              [site | rest] ->
                {Map.put(provenance, call.provenance.core_path, Map.delete(site, :callee)),
                 Map.put(remaining, call.callee, rest)}

              [] ->
                {provenance, remaining}
            end
          end)

        Env.put_direct_call_summary(env, key, Certificate.attach_provenance(summary, provenance_by_path))
    end
  end

  defp collect_sites({:function_call, meta, children}, env, acc) when is_list(meta) and is_list(children) do
    acc =
      with name when is_binary(name) <- Keyword.get(meta, :name),
           {:ok, callee} <- resolve_name(env, name),
           site when not is_nil(site) <- source_site(meta) do
        [Map.put(site, :callee, callee) | acc]
      else
        _ -> acc
      end

    Enum.reduce(children, acc, &collect_sites(&1, env, &2))
  end

  defp collect_sites({_tag, _meta, children}, env, acc) when is_list(children),
    do: Enum.reduce(children, acc, &collect_sites(&1, env, &2))

  defp collect_sites(tuple, env, acc) when is_tuple(tuple) do
    tuple
    |> Tuple.to_list()
    |> Enum.reduce(acc, &collect_sites(&1, env, &2))
  end

  defp collect_sites(list, env, acc) when is_list(list),
    do: Enum.reduce(list, acc, &collect_sites(&1, env, &2))

  defp collect_sites(_other, _env, acc), do: acc

  defp resolve_name(env, name) do
    if String.contains?(name, ".") do
      Resolution.resolve_qualified(env, name, :value)
    else
      atom = String.to_atom(name)

      case Resolution.resolve_bare(env, atom) do
        {:ok, key} ->
          {:ok, key}

        _ ->
          key = Env.resolve_key(env, env.defs, atom)
          if Env.get_def(env, key), do: {:ok, key}, else: :error
      end
    end
  end

  defp source_site(meta) do
    case Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{} = info ->
        if is_nil(info.whole) and info.provenance == [],
          do: nil,
          else: %{source_span: info.whole, macro_expansion: info.provenance}

      _ ->
        nil
    end
  end
end

defmodule Cure.Test.TotalityCertificateHelper do
  @moduledoc false

  alias Cure.Core.{Certificate, Env, TotalityCertificate}
  alias Cure.Elab.TotalityGraph

  # Matrix and fail-closed walker unit tests intentionally use small synthetic
  # Core fragments that are not complete kernel programs. Build the same trusted
  # local summaries and externally proposed Agda-style certificates as production,
  # but do not re-run Core typing: typing is outside those tests' stated property.
  def provably_total?(%Env{} = env, name) do
    names =
      env.defs
      |> Enum.flat_map(fn
        {key, %{body: body}} when is_tuple(body) and elem(body, 0) not in [:extern, :hole] -> [key]
        _ -> []
      end)
      |> Enum.sort()

    env =
      Enum.reduce(names, env, fn key, acc ->
        %{body: body} = Env.get_def(acc, key)
        Env.put_direct_call_summary(acc, key, Certificate.direct_summary(key, body, acc))
      end)

    canonical = Env.resolve_key(env, env.defs, name)

    if canonical in names do
      partition = TotalityGraph.propose_partition(env, names)
      component_id = Map.fetch!(partition.component_of, canonical)
      %{members: members} = Map.fetch!(partition.components, component_id)
      candidate = Cure.Elab.TotalityCertificate.propose(env, members)
      match?({:ok, :total}, TotalityCertificate.verify(env, members, candidate))
    else
      false
    end
  end
end

defmodule Cure.Diagnostic.InternalContext do
  @moduledoc false

  @fields [
    :declaration,
    :span,
    :core_term,
    :core_trace,
    :expected_type,
    :inferred_type,
    :unresolved_global,
    :closure_path,
    :provenance
  ]

  @spec normalize(map() | keyword()) :: map()
  def normalize(context) when is_list(context), do: context |> Map.new() |> normalize()

  def normalize(context) when is_map(context) do
    context = Map.take(context, @fields)

    %{
      declaration: Map.get(context, :declaration),
      span: Map.get(context, :span),
      core_term: bounded_term(Map.get(context, :core_term)),
      core_trace: Map.get(context, :core_trace, []),
      expected_type: bounded_term(Map.get(context, :expected_type)),
      inferred_type: bounded_term(Map.get(context, :inferred_type)),
      unresolved_global: Map.get(context, :unresolved_global),
      closure_path: Map.get(context, :closure_path, []),
      provenance: Map.get(context, :provenance, [])
    }
  end

  @spec bounded_term(term()) :: String.t() | nil
  def bounded_term(nil), do: nil
  def bounded_term(term), do: inspect(term, limit: 24, printable_limit: 480, width: 80)
end

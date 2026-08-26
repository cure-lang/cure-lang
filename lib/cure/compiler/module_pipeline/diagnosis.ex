defmodule Cure.Compiler.ModulePipeline.Diagnosis do
  @moduledoc """
  Causal shaping of pipeline failures.

  The elaborator reports what it could not do at the point it could not do it.
  This module answers the question a user actually asks — *which* declaration
  reached for *which* missing key, and by what path — using the manifest and the
  module skeletons rather than a second scan of the source.
  """

  alias Cure.Compiler.ModuleSkeleton
  alias Cure.Diagnostic.Span
  alias Cure.Elab.Name

  @doc """
  Reshape a module body-check failure into a typed pipeline error.

  An unresolved global is reported as `:unresolved_global` with the key, the
  origin span, and the closure path that reached it. Anything else is passed
  through unchanged rather than guessed at.
  """
  @spec body_failure({String.t(), String.t()}, ModuleSkeleton.t() | nil, term()) :: term()
  def body_failure(identity, skeleton, reason) do
    case unknown_global(reason) do
      {:ok, name, span, context} -> unresolved_global(identity, skeleton, name, span, context)
      :error -> {:module_body_check_failed, identity, reason}
    end
  end

  defp unresolved_global({package, module_name} = identity, skeleton, name, span, context) do
    key = global_key(package, module_name, name)

    {:unresolved_global,
     %{
       key: key,
       origin: origin(span),
       closure_path: closure_path(identity, skeleton, span, key),
       source_context: context,
       provenance: provenance(context)
     }}
  end

  # A bare global is owned by the module that failed to resolve it; a qualified
  # one already names its owner and keeps it.
  defp global_key(package, module_name, name) do
    case Name.split(name) do
      {nil, base} -> {package, module_name, :value, base}
      {owner, base} -> {package, owner, :value, base}
    end
  end

  defp origin(%Span{} = span), do: span
  defp origin(_span), do: nil

  defp provenance(context) when is_map(context) do
    Map.get(context, :expansion_provenance, Map.get(context, :provenance, []))
  end

  defp provenance(_context), do: []

  # The predecessor is the declaration whose source range encloses the failure:
  # that is the definition whose emission closure would have demanded the key.
  defp closure_path(_identity, nil, _span, key), do: [key]

  defp closure_path(_identity, skeleton, %Span{} = span, key) do
    case enclosing_declaration(skeleton, span) do
      nil -> [key]
      declaration -> [declaration.key, key]
    end
  end

  defp closure_path(_identity, _skeleton, _span, key), do: [key]

  defp enclosing_declaration(skeleton, span) do
    skeleton.declarations
    |> Map.values()
    |> Enum.filter(&encloses?(&1.extent, span))
    |> Enum.min_by(&width(&1.extent), fn -> nil end)
  end

  defp encloses?(%Span{} = extent, %Span{} = span),
    do: extent.start_byte <= span.start_byte and extent.end_byte >= span.end_byte

  defp encloses?(_extent, _span), do: false

  defp width(%Span{} = span), do: span.end_byte - span.start_byte

  @doc """
  Whether a failure is a module's own fault or the downstream shadow of a
  provider that already failed.

  Only the first is worth reporting: a consumer of a module that did not check
  has nothing useful to say about it.
  """
  @spec provider_failure?(term()) :: boolean()
  def provider_failure?({:interface_dependency_unavailable, _identity, _dependency}), do: true
  def provider_failure?({:module_interface_registration_failed, _identity, reason}), do: provider_failure?(reason)
  def provider_failure?({:module_type_skeleton_failed, _identity, reason}), do: provider_failure?(reason)
  def provider_failure?(_reason), do: false

  @doc """
  A component failure as a reportable diagnostic, or `nil` when it is only the
  shadow of a provider that already failed.

  Suppression is the whole point: a run where one module does not check must
  report that module once, not once per module that names it.
  """
  @spec diagnostic(term(), {String.t(), String.t()}, Path.t()) :: map() | nil
  def diagnostic(reason, fallback_identity, source_path) do
    if provider_failure?(reason) do
      nil
    else
      identity = failing_identity(reason, fallback_identity)

      %{
        code: :provider_check_failed,
        severity: :error,
        module: elem(identity, 1),
        primary: %{span: failure_span(reason, source_path), message: message(reason)},
        reason: reason
      }
    end
  end

  defp failing_identity({:unresolved_global, %{key: {package, module_name, _namespace, _name}}}, _fallback),
    do: {package, module_name}

  defp failing_identity(reason, fallback) when is_tuple(reason) and tuple_size(reason) >= 2 do
    case elem(reason, 1) do
      {package, module_name} when is_binary(package) and is_binary(module_name) -> {package, module_name}
      _ -> fallback
    end
  end

  defp failing_identity(_reason, fallback), do: fallback

  defp failure_span({:unresolved_global, %{origin: %{} = origin}}, _source_path), do: origin
  defp failure_span(_reason, source_path), do: %{path: source_path, line: 1, column: 1}

  defp message({:unresolved_global, %{key: {_package, _module, _namespace, name}}}),
    do: "`#{name}` does not resolve to any declaration in scope"

  defp message(_reason), do: "this module did not check"

  defp unknown_global({:source_context, inner, context}) do
    case unknown_global(inner) do
      {:ok, name, nil, inner_context} -> {:ok, name, context_span(context), Map.merge(inner_context, context)}
      {:ok, name, span, inner_context} -> {:ok, name, span, Map.merge(inner_context, context)}
      other -> other
    end
  end

  defp unknown_global({:unknown_global, name, details}) when is_map(details),
    do: {:ok, to_string(name), Map.get(details, :span), details}

  defp unknown_global({:unknown_global, name, _details}), do: {:ok, to_string(name), nil, %{}}
  defp unknown_global({:unknown_global, name}), do: {:ok, to_string(name), nil, %{}}

  defp unknown_global(reason) when is_tuple(reason) do
    reason |> Tuple.to_list() |> unknown_global()
  end

  defp unknown_global(reasons) when is_list(reasons), do: Enum.find_value(reasons, :error, &find_unknown/1)
  defp unknown_global(_reason), do: :error

  defp find_unknown(candidate) do
    case unknown_global(candidate) do
      {:ok, _name, _span, _context} = found -> found
      :error -> nil
    end
  end

  defp context_span(%{span: %Span{} = span}), do: span
  defp context_span(_context), do: nil
end

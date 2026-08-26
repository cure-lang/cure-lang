defmodule Cure.Elab.SourceMetadata do
  @moduledoc """
  Ephemeral authored-source metadata for the active elaboration process.

  These ranges support related diagnostic labels but deliberately never enter
  `Cure.Core.Env`, Core terms, caches, hashes, or serialized artifacts.
  """

  @parameter_key {__MODULE__, :parameter_spans}
  @parameter_site_key {__MODULE__, :parameter_sites}
  @record_field_key {__MODULE__, :record_field_sites}
  @declaration_key {__MODULE__, :declaration_spans}
  @equation_key {__MODULE__, :equations}
  @interface_method_key {__MODULE__, :interface_method_spans}
  @instance_origin_key {__MODULE__, :instance_origins}

  def reset do
    Enum.each(
      [
        @parameter_key,
        @parameter_site_key,
        @record_field_key,
        @declaration_key,
        @equation_key,
        @interface_method_key,
        @instance_origin_key
      ],
      &Process.delete/1
    )

    :ok
  end

  def put_parameter_spans(name, spans) when is_atom(name) and is_list(spans) do
    Process.put(@parameter_key, Map.put(Process.get(@parameter_key, %{}), name, spans))
    :ok
  end

  def parameter_spans(name) when is_atom(name), do: Process.get(@parameter_key, %{}) |> Map.get(name, [])

  def put_parameter_sites(name, sites) when is_atom(name) and is_list(sites) do
    Process.put(@parameter_site_key, Map.put(Process.get(@parameter_site_key, %{}), name, sites))
    :ok
  end

  def parameter_sites(name) when is_atom(name),
    do: Process.get(@parameter_site_key, %{}) |> Map.get(name, [])

  def put_record_field_sites(name, sites) when is_atom(name) and is_map(sites) do
    Process.put(@record_field_key, Map.put(Process.get(@record_field_key, %{}), name, sites))
    :ok
  end

  def record_field_sites(name) when is_atom(name),
    do: Process.get(@record_field_key, %{}) |> Map.get(name, %{})

  def put_declaration_span(name, span) when is_atom(name) do
    Process.put(@declaration_key, Map.put(Process.get(@declaration_key, %{}), name, span))
    :ok
  end

  def declaration_span(name) when is_atom(name),
    do: Process.get(@declaration_key, %{}) |> Map.get(name)

  def put_equation(theorem, metadata) when is_atom(theorem) and is_map(metadata) do
    Process.put(@equation_key, Map.put(Process.get(@equation_key, %{}), theorem, metadata))
    :ok
  end

  def equation(theorem) when is_atom(theorem), do: Process.get(@equation_key, %{}) |> Map.get(theorem, %{})

  def put_interface_method_span(interface, method, span) when is_atom(interface) and is_atom(method) do
    key = {interface, method}
    Process.put(@interface_method_key, Map.put(Process.get(@interface_method_key, %{}), key, span))
    :ok
  end

  def interface_method_span(interface, method) when is_atom(interface) and is_atom(method),
    do: Process.get(@interface_method_key, %{}) |> Map.get({interface, method})

  def put_instance_origin(kind, key, origin) when kind in [:anonymous, :named] and is_map(origin) do
    origins = Process.get(@instance_origin_key, %{})
    Process.put(@instance_origin_key, Map.update(origins, {kind, key}, [origin], &(&1 ++ [origin])))
    :ok
  end

  def instance_origins(kind, key) when kind in [:anonymous, :named],
    do: Process.get(@instance_origin_key, %{}) |> Map.get({kind, key}, [])
end

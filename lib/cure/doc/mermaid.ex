defmodule Cure.Doc.Mermaid do
  @moduledoc """
  Mermaid diagram emission for lifted Cure modules.

  The renderer consumes only the generic lifted-module metadata contract. A
  module's behavior is displayed as a label; no behavior-specific compiler or
  documentation registry is required.
  """

  alias Cure.Pipeline.Events

  @doc "Render a single lifted module node as a Mermaid class diagram."
  @spec render(tuple(), keyword()) :: String.t() | nil
  def render(ast, opts \\ [])

  def render({:lift_module, meta, _body}, opts) when is_list(meta) do
    name = Keyword.get(meta, :module, "Unknown") |> to_string()
    behaviour = Keyword.get(meta, :behaviour, :unknown)
    callbacks = Keyword.get(meta, :callbacks, [])
    declarations = Keyword.get(meta, :declarations, [])
    file = Keyword.get(opts, :file, "nofile")
    line = Keyword.get(meta, :line, 1)

    Events.emit(
      :doc_mermaid,
      :emitted,
      %{kind: :lift_module, name: name},
      Events.meta(file, line)
    )

    render_module(name, behaviour, callbacks, declarations)
  end

  def render(_other, _opts), do: nil

  defp render_module(name, behaviour, callbacks, declarations) do
    id = state_id(name)
    callback_lines = Enum.map(callbacks, &callback_line/1)

    [
      "classDiagram",
      "  class #{id} {",
      "    behaviour #{behaviour}",
      "    callbacks #{length(callbacks)}",
      "    declarations #{length(declarations)}",
      callback_lines,
      "  }"
    ]
    |> List.flatten()
    |> Enum.reject(&(&1 == "    "))
    |> Enum.join("\n")
  end

  defp callback_line(callback) when is_map(callback) do
    name = Map.get(callback, :name, "unknown")
    arity = Map.get(callback, :arity, length(Map.get(callback, :params, [])))
    "    #{name}/#{arity} callback"
  end

  defp callback_line(callback) when is_list(callback) do
    name = Keyword.get(callback, :name, "unknown")
    arity = Keyword.get(callback, :arity, length(Keyword.get(callback, :params, [])))
    "    #{name}/#{arity} callback"
  end

  defp callback_line(_callback), do: "    unknown/0 callback"

  defp state_id(name), do: String.replace(to_string(name), ~r/[^A-Za-z0-9_]/, "_")
end

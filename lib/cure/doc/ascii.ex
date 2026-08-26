defmodule Cure.Doc.Ascii do
  @moduledoc """
  ASCII / Unicode box-drawing diagrams for lifted Cure modules.

  The renderer consumes the generic `{:lift_module, meta, body}` contract. It
  deliberately does not interpret any behavior vocabulary: macro-defined
  behavior metadata remains data, while callbacks and declarations are shown
  using the same shape for every lifted module.
  """

  alias Cure.Pipeline.Events

  @doc "Render a single lifted module AST node as ASCII."
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
      :doc_ascii,
      %{kind: :lift_module, name: name},
      Events.meta(file, line)
    )

    render_module(name, behaviour, callbacks, declarations)
  end

  def render(_other, _opts), do: nil

  @doc "Render every lifted module in a Cure source file in source order."
  @spec render_file(Path.t(), keyword()) :: {:ok, String.t()} | {:error, term()}
  def render_file(path, opts \\ []) do
    filter = Keyword.get(opts, :filter, :all)

    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, file: path, emit_events: false) do
      diagrams =
        ast
        |> collect_lifted_modules()
        |> Enum.filter(&filter_kind?(&1, filter))
        |> Enum.map(&render(&1, file: path))
        |> Enum.reject(&is_nil/1)

      {:ok, Enum.join(diagrams, "\n\n")}
    end
  end

  defp collect_lifted_modules({:lift_module, meta, _body} = module) when is_list(meta), do: [module]

  defp collect_lifted_modules({:block, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &collect_lifted_modules/1)

  defp collect_lifted_modules(_), do: []

  defp filter_kind?(_node, kind) when kind in [:all, :lifted], do: true
  defp filter_kind?(_node, _kind), do: false

  defp render_module(name, behaviour, callbacks, declarations) do
    header = "module #{name}"
    underline = String.duplicate("=", String.length(header))

    callback_lines =
      callbacks
      |> Enum.map(fn callback ->
        callback_name = callback_value(callback, :name, "unknown")
        arity = callback_value(callback, :arity, length(callback_value(callback, :params, [])))
        "  #{callback_name}/#{arity}"
      end)

    declaration_count = length(declarations)

    [
      [header, underline, "behaviour: #{behaviour}"],
      ["", "callbacks:" | callback_lines],
      ["", "declarations: #{declaration_count}"]
    ]
    |> Enum.map(&Enum.join(&1, "\n"))
    |> Enum.join("\n")
  end

  defp callback_value(callback, key, default) when is_map(callback), do: Map.get(callback, key, default)
  defp callback_value(callback, key, default) when is_list(callback), do: Keyword.get(callback, key, default)
  defp callback_value(_callback, _key, default), do: default
end

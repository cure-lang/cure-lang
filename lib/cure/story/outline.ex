defmodule Cure.Story.Outline do
  @moduledoc """
  Top-down structural outline builder for `cure story` (v0.32.0).

  Walks all `.cure` source files in a project, parses them, and
  classifies AST container nodes into a hierarchical outline:

      apps -> supervisors -> actors -> fsms -> types

  The outline is a simple nested map structure consumed by
  `Cure.Story.Narrator` to generate narrative prose.
  """

  @type outline :: %{
          apps: [app_node()],
          supervisors: [sup_node()],
          actors: [actor_node()],
          fsms: [fsm_node()],
          types: [type_node()]
        }

  @type app_node :: %{name: String.t(), file: String.t(), supervisors: [String.t()], actors: [String.t()]}
  @type sup_node :: %{name: String.t(), file: String.t(), strategy: atom(), children: [String.t()]}
  @type actor_node :: %{name: String.t(), file: String.t(), effects: [String.t()], messages: [String.t()]}
  @type fsm_node :: %{name: String.t(), file: String.t(), states: [String.t()], transitions: [transition()]}
  @type type_node :: %{name: String.t(), file: String.t(), kind: :enum | :record | :alias, doc: String.t() | nil}
  @type transition :: %{from: String.t(), event: String.t(), to: String.t()}

  @doc """
  Build a structural outline from all `.cure` sources under `root`.

  Reads and parses each file silently; parse errors are skipped without
  raising.
  """
  @spec build(String.t()) :: outline()
  def build(root \\ ".") when is_binary(root) do
    files =
      root
      |> Path.join("lib/**/*.cure")
      |> Path.wildcard()
      |> Enum.sort()

    Enum.reduce(files, empty_outline(), fn file, outline ->
      case parse_file(file) do
        {:ok, ast} -> merge_outline(outline, walk(ast, file))
        {:error, _} -> outline
      end
    end)
  end

  # -- Outline accumulation -----------------------------------------------------

  defp empty_outline do
    %{apps: [], supervisors: [], actors: [], fsms: [], types: []}
  end

  defp merge_outline(acc, additions) do
    %{
      apps: acc.apps ++ additions.apps,
      supervisors: acc.supervisors ++ additions.supervisors,
      actors: acc.actors ++ additions.actors,
      fsms: acc.fsms ++ additions.fsms,
      types: acc.types ++ additions.types
    }
  end

  # -- AST walking --------------------------------------------------------------

  defp walk(ast, file) do
    walk_node(ast, file, empty_outline())
  end

  defp walk_node({:block, _, children}, file, acc) when is_list(children) do
    Enum.reduce(children, acc, fn child, a -> walk_node(child, file, a) end)
  end

  defp walk_node({:container, meta, body}, file, acc) when is_list(meta) do
    acc =
      case Keyword.get(meta, :container_type) do
        :module ->
          Enum.reduce(body, acc, fn child, a -> walk_node(child, file, a) end)

        :enum ->
          node = %{
            name: Keyword.get(meta, :name, "Unknown"),
            file: file,
            kind: :enum,
            doc: Keyword.get(meta, :doc)
          }

          %{acc | types: [node | acc.types]}

        :struct ->
          node = %{
            name: Keyword.get(meta, :name, "Unknown"),
            file: file,
            kind: :record,
            doc: Keyword.get(meta, :doc)
          }

          %{acc | types: [node | acc.types]}

        _ ->
          acc
      end

    acc
  end

  defp walk_node({:lift_module, meta, _body}, file, acc) when is_list(meta) do
    name = Keyword.get(meta, :module, "Unknown") |> to_string()

    case Keyword.get(meta, :behaviour) do
      :application ->
        %{acc | apps: [%{name: name, file: file, supervisors: [], actors: []} | acc.apps]}

      :supervisor ->
        node = %{name: name, file: file, strategy: :one_for_one, children: []}
        %{acc | supervisors: [node | acc.supervisors]}

      :gen_server ->
        node = %{name: name, file: file, effects: [], messages: []}
        %{acc | actors: [node | acc.actors]}

      :gen_statem ->
        node = %{name: name, file: file, states: [], transitions: []}
        %{acc | fsms: [node | acc.fsms]}

      _ ->
        acc
    end
  end

  defp walk_node({:type_annotation, meta, _}, file, acc) when is_list(meta) do
    node = %{
      name: Keyword.get(meta, :name, "Unknown"),
      file: file,
      kind: :alias,
      doc: Keyword.get(meta, :doc)
    }

    %{acc | types: [node | acc.types]}
  end

  defp walk_node(_, _file, acc), do: acc

  # -- File parsing -------------------------------------------------------------

  defp parse_file(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <-
           Cure.Compiler.Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <-
           Cure.Compiler.Parser.parse(tokens, file: path, emit_events: false) do
      {:ok, ast}
    else
      {:error, reason} -> {:error, reason}
    end
  end
end

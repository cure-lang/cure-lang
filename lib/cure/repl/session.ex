defmodule Cure.REPL.Session do
  @moduledoc """
  Accumulator for top-level declarations (`fn`, `type`, `rec`, `interface`,
  `implementation`, `proof`) submitted interactively to the REPL.

  ## Why this exists

  The raw evaluator in `Cure.REPL` wraps every submission as the body
  of an implicit `fn main() -> Any = <src>`. That is the right shape
  for expressions but the wrong shape for declarations -- a top-level
  `fn add(...) -> Int = ...` parses as a named-function AST in
  expression position and lowers to the `:undefined` atom at codegen
  time. This module gives the REPL a place to stash declarations in
  between submissions and recompiles them into a synthetic
  `Repl.Session` module that subsequent expression submissions can
  `use` unqualified.

  ## State shape

  A session is a plain list of entries, in insertion order, with
  last-writer-wins semantics on `:key`:

      %{
        key:    {:fn, "add", 2, :public},
        kind:   :fn,
        label:  "add/2",
        source: "fn add(a: Int, b: Int) -> Int = a + b"
      }

  Keys are chosen so that redefining the same declaration replaces the
  earlier entry but overloading (by arity, or by protocol + for-type)
  keeps the earlier entry alive:

  * `:fn`    -> `{:fn, name, arity, visibility}`
  * `:type`  -> `{:type, name}`
  * `:rec`   -> `{:rec, name}`
  * `:interface`      -> `{:interface, name}`
  * `:implementation` -> `{:implementation, interface, for_name}`
  * `:proof` -> `{:proof, name}`

  ## Synthesised module

  The emitted source is always wrapped as `mod Repl.Session` with the
  raw declaration sources indented two spaces. The BEAM atom for the
  module is `:"Cure.Repl.Session"`; `Cure.REPL` adds `Repl.Session` to
  the `use`-list of every expression module it compiles while any
  entries are present, so unqualified calls like `add(2, 3)` resolve
  through the same canonical module interface as ordinary source imports.
  """

  alias Cure.Compiler

  @module_name "Repl.Session"
  @module_atom :"Cure.Repl.Session"

  @type visibility :: :public | :private

  @type key ::
          {:fn, String.t(), non_neg_integer(), visibility()}
          | {:type, String.t()}
          | {:rec, String.t()}
          | {:interface, String.t()}
          | {:implementation, String.t(), String.t()}
          | {:proof, String.t()}

  @type entry :: %{
          key: key(),
          kind: :fn | :type | :rec | :interface | :implementation | :proof,
          label: String.t(),
          source: String.t()
        }

  @type classification ::
          {:definitions, [entry()]}
          | :expression

  @doc "Cure-level module name used in the synthesised `mod ...` header."
  @spec module_name() :: String.t()
  def module_name, do: @module_name

  @doc "BEAM atom the synthesised module is compiled to."
  @spec module_atom() :: atom()
  def module_atom, do: @module_atom

  # ---------------------------------------------------------------------------
  # Classification
  # ---------------------------------------------------------------------------

  @doc """
  Inspect a raw REPL submission and decide whether it contains only
  top-level declarations that the session should absorb, or an
  expression that should continue to flow through the legacy
  `Cure.REPL.evaluate/2` path.

  Returns `{:definitions, [entry, ...]}` when every top-level AST node
  is a recognised declaration, `:expression` otherwise. Parse failures
  are also funnelled into `:expression` so the compiler's diagnostics
  surface through the existing wrapping path instead of being
  suppressed here.
  """
  @spec classify(String.t()) :: classification()
  def classify(src) when is_binary(src) do
    trimmed = String.trim(src)

    if trimmed == "" do
      :expression
    else
      case Cure.quote(trimmed, file: "repl") do
        {:ok, ast} -> classify_ast(ast, trimmed)
        {:error, _} -> :expression
      end
    end
  end

  # Single top-level node
  defp classify_ast({:block, _meta, nodes}, src) when is_list(nodes) do
    classify_nodes(nodes, src)
  end

  defp classify_ast(node, src), do: classify_nodes([node], src)

  defp classify_nodes([], _src), do: :expression

  defp classify_nodes(nodes, src) do
    entries =
      Enum.reduce_while(nodes, [], fn node, acc ->
        case entry_from_node(node, node_source(node, src)) do
          {:ok, entry} -> {:cont, [entry | acc]}
          :skip -> {:cont, acc}
          :expression -> {:halt, :expression}
        end
      end)

    case entries do
      :expression -> :expression
      [] -> :expression
      list -> {:definitions, Enum.reverse(list)}
    end
  end

  # A submission may contain several declarations. Each session entry must own
  # only its declaration; storing the entire submission on every entry duplicates
  # siblings when `build_source/1` reassembles the module and breaks generated
  # equation ownership. Parser spans are byte offsets into this exact trimmed
  # submission, so slicing is lossless (fall back for synthetic/spanless nodes).
  defp node_source({_tag, meta, _children}, src) when is_list(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{start_byte: first, end_byte: last}}
      when first >= 0 and last >= first and last <= byte_size(src) ->
        binary_part(src, first, last - first)

      _ ->
        src
    end
  end

  defp node_source(_node, src), do: src

  # `line_comment` / `comment` nodes can appear at the top level. They
  # should not flip the whole submission into expression territory
  # (users routinely prefix defs with `# ...`) but they do not carry
  # independent source that must be re-emitted either -- the comment
  # text is already part of the saved `:source` snippet of the next
  # real entry if it lives on the same visual line. We therefore skip
  # them for classification purposes.
  defp entry_from_node({:line_comment, _meta, _text}, _src), do: :skip
  defp entry_from_node({:comment, _meta, _text}, _src), do: :skip
  defp entry_from_node({:doc_comment, _meta, _text}, _src), do: :skip

  defp entry_from_node({:function_def, meta, _body}, src) when is_list(meta) do
    # Skip ADT variants that happen to reuse the `function_def` tag
    # (`type Foo = Bar(Int)` parses variants as `{:function_def, ...,
    # variant: true}`). A bare `variant: true` node at the top level
    # is almost certainly a user error; route it to the expression
    # path so the compiler can complain meaningfully.
    if Keyword.get(meta, :variant, false) do
      :expression
    else
      name = Keyword.get(meta, :name, "unknown")
      arity = Keyword.get(meta, :arity, length(Keyword.get(meta, :params, [])))
      visibility = Keyword.get(meta, :visibility, :public)
      key = {:fn, name, arity, visibility}

      {:ok,
       %{
         key: key,
         kind: :fn,
         label: "#{name}/#{arity}",
         source: String.trim(src)
       }}
    end
  end

  defp entry_from_node({:container, meta, _body}, src) when is_list(meta) do
    case Keyword.get(meta, :container_type) do
      :struct -> container_entry(:rec, meta, src)
      :enum -> container_entry(:type, meta, src)
      :protocol -> container_entry(:proto, meta, src)
      :trait -> impl_entry(meta, src)
      :proof -> container_entry(:proof, meta, src)
      _ -> :expression
    end
  end

  defp entry_from_node({:interface, meta, _body}, src) when is_list(meta),
    do: container_entry(:interface, meta, src)

  defp entry_from_node({:implementation, meta, _body}, src) when is_list(meta),
    do: implementation_entry(meta, src)

  # `type Foo = Existing` elaborates to a `:type_annotation` node, not
  # a container. Treat it as a `type` entry.
  defp entry_from_node({:type_annotation, meta, _body}, src) when is_list(meta) do
    name = Keyword.get(meta, :name)

    if is_binary(name) do
      {:ok,
       %{
         key: {:type, name},
         kind: :type,
         label: "type #{name}",
         source: String.trim(src)
       }}
    else
      :expression
    end
  end

  defp entry_from_node(_other, _src), do: :expression

  defp container_entry(kind, meta, src) do
    name = Keyword.get(meta, :name, "Unnamed")
    label = label_for(kind, name)

    {:ok,
     %{
       key: {kind, name},
       kind: kind,
       label: label,
       source: String.trim(src)
     }}
  end

  defp impl_entry(meta, src) do
    proto = Keyword.get(meta, :protocol, "Unknown")
    for_name = Keyword.get(meta, :for, "Unknown")
    full = Keyword.get(meta, :name, "#{proto}.#{for_name}")

    {:ok,
     %{
       key: {:impl, proto, for_name},
       kind: :impl,
       label: "impl #{full}",
       source: String.trim(src)
     }}
  end

  defp implementation_entry(meta, src) do
    interface = Keyword.get(meta, :interface, "Unknown")
    for_name = Keyword.get(meta, :for, "Unknown")
    as_name = Keyword.get(meta, :as)

    label =
      "implementation #{interface} for #{for_name}" <>
        if(is_binary(as_name), do: " as #{as_name}", else: "")

    {:ok,
     %{
       key: {:implementation, interface, as_name || for_name},
       kind: :implementation,
       label: label,
       source: String.trim(src)
     }}
  end

  defp label_for(:rec, name), do: "rec #{name}"
  defp label_for(:type, name), do: "type #{name}"
  defp label_for(:proto, name), do: "proto #{name}"
  defp label_for(:interface, name), do: "interface #{name}"
  defp label_for(:proof, name), do: "proof #{name}"

  # ---------------------------------------------------------------------------
  # State helpers
  # ---------------------------------------------------------------------------

  @doc """
  Merge a list of freshly-parsed entries into an existing ordered list
  of session entries. New entries replace earlier entries with the
  same `:key` in-place (preserving position) so users can iterate on
  a definition without watching it drift to the bottom of `:defs`.

  Returns `{new_defs, annotated}` where `annotated` has each incoming
  entry tagged as `{:new | :redefined, entry}` for the REPL's status
  line.
  """
  @spec merge([entry()], [entry()]) :: {[entry()], [{:new | :redefined, entry()}]}
  def merge(existing, incoming) do
    {defs, annotated} =
      Enum.reduce(incoming, {existing, []}, fn entry, {acc, events} ->
        case replace_by_key(acc, entry) do
          {:replaced, new_acc} -> {new_acc, [{:redefined, entry} | events]}
          :not_found -> {acc ++ [entry], [{:new, entry} | events]}
        end
      end)

    {defs, Enum.reverse(annotated)}
  end

  defp replace_by_key(list, %{key: key} = entry) do
    case Enum.find_index(list, fn %{key: k} -> k == key end) do
      nil -> :not_found
      idx -> {:replaced, List.replace_at(list, idx, entry)}
    end
  end

  # ---------------------------------------------------------------------------
  # Source synthesis
  # ---------------------------------------------------------------------------

  @doc """
  Render an ordered list of entries as a compileable `mod Repl.Session`
  source string. Returns `\"\"` for an empty list; callers should skip
  compilation entirely in that case.
  """
  @spec build_source([entry()]) :: String.t()
  def build_source([]), do: ""

  def build_source(defs) when is_list(defs) do
    body =
      defs
      |> Enum.map_join("\n\n", fn %{source: src} -> indent(src, "  ") end)

    "mod " <> @module_name <> "\n" <> body <> "\n"
  end

  defp indent(src, prefix) do
    src
    |> String.split("\n")
    |> Enum.map_join("\n", fn
      "" -> ""
      line -> prefix <> line
    end)
  end

  # ---------------------------------------------------------------------------
  # Compilation
  # ---------------------------------------------------------------------------

  @doc """
  Compile and load the synthetic session module from `defs`. On an
  empty list the previously loaded module (if any) is purged and the
  call returns `:empty`.
  """
  @spec compile([entry()]) :: {:ok, module()} | {:error, term()} | :empty
  def compile([]) do
    clear()
    :empty
  end

  def compile(defs) when is_list(defs) do
    source = build_source(defs)
    Compiler.compile_and_load(source, file: "repl/session", emit_events: false)
  end

  @doc "Elaborate the synthetic session and return typed hole goals without emitting it."
  @spec hole_goals([entry()]) :: {:ok, [map()]} | {:error, term()}
  def hole_goals([]), do: {:ok, []}

  def hole_goals(defs) when is_list(defs) do
    defs
    |> build_source()
    |> Cure.Elab.Program.elaborate()
    |> case do
      {:ok, env} -> {:ok, Cure.Elab.Program.hole_goals(env)}
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Best-effort unload of the session module. Safe to call when nothing
  has been compiled yet.
  """
  @spec clear() :: :ok
  def clear do
    _ = :code.purge(@module_atom)
    _ = :code.delete(@module_atom)
    _ = :code.purge(@module_atom)
    :ok
  end

  # ---------------------------------------------------------------------------
  # Signatures (for the type checker)
  # ---------------------------------------------------------------------------
end

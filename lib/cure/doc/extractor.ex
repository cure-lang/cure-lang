defmodule Cure.Doc.Extractor do
  @moduledoc """
  Extracts structured documentation from a module AST.

  Takes a parsed MetaAST node (with doc comments attached by the parser)
  and produces a structured map containing module name, module doc,
  function signatures with docs, protocol definitions, and type definitions.
  """

  alias Cure.Compiler.Printer

  @doc """
  Extract documentation from a module AST.

  Returns a map with:
  - `:module` -- module name
  - `:module_doc` -- module-level documentation
  - `:functions` -- list of function doc maps
  - `:protocols` -- list of protocol doc maps
  - `:types` -- list of type doc maps
  """
  @spec extract(tuple()) :: map()
  def extract({:container, meta, body}) do
    case Keyword.get(meta, :container_type) do
      :module ->
        %{
          module: Keyword.get(meta, :name, "Unknown"),
          module_doc: Keyword.get(meta, :doc, nil),
          functions: extract_functions(body),
          protocols: extract_protocols(body),
          types: extract_types(body)
        }

      _ ->
        %{module: "Unknown", module_doc: nil, functions: [], protocols: [], types: []}
    end
  end

  def extract({:block, _, children}) do
    case Enum.find(children, fn
           {:container, m, _} when is_list(m) ->
             Keyword.get(m, :container_type) == :module

           _ ->
             false
         end) do
      {:container, _, _} = mod -> extract(mod)
      nil -> %{module: "Unknown", module_doc: nil, functions: [], protocols: [], types: []}
    end
  end

  def extract(_), do: %{module: "Unknown", module_doc: nil, functions: [], protocols: [], types: []}

  # -- Function Extraction -----------------------------------------------------

  defp extract_functions(stmts) do
    Enum.flat_map(stmts, fn
      {:function_def, meta, _body} ->
        [extract_function(meta)]

      {:container, meta, body} when is_list(meta) ->
        case Keyword.get(meta, :container_type) do
          :trait ->
            Enum.flat_map(body, fn
              {:function_def, m, _} -> [extract_function(m)]
              _ -> []
            end)

          _ ->
            []
        end

      _ ->
        []
    end)
  end

  defp extract_function(meta) do
    name = Keyword.get(meta, :name, "unknown")
    params = Keyword.get(meta, :params, [])
    return_type_ast = Keyword.get(meta, :return_type)
    effects = Keyword.get(meta, :effects)
    visibility = Keyword.get(meta, :visibility, :public)
    doc = Keyword.get(meta, :doc)
    clauses = Keyword.get(meta, :clauses)
    extern = Keyword.get(meta, :extern)
    guards = Keyword.get(meta, :guards)

    param_list =
      Enum.map(params, fn {:param, pmeta, pname} ->
        type_ast = Keyword.get(pmeta, :type)
        type_str = if type_ast, do: render_type(type_ast), else: "Any"
        {pname, type_str}
      end)

    ret_str =
      if return_type_ast do
        render_type(return_type_ast)
      else
        nil
      end

    effect_list =
      if effects do
        Enum.map(effects, &render_effect/1)
      else
        []
      end

    clause_count =
      cond do
        clauses != nil -> length(clauses)
        true -> 1
      end

    %{
      name: name,
      params: param_list,
      return_type: ret_str,
      effects: effect_list,
      visibility: visibility,
      doc: doc,
      clauses: clause_count,
      extern: extern != nil,
      guards: guards != nil
    }
  end

  # -- Protocol Extraction -----------------------------------------------------

  defp extract_protocols(stmts) do
    Enum.flat_map(stmts, fn
      {:container, meta, body} when is_list(meta) ->
        case Keyword.get(meta, :container_type) do
          :protocol ->
            [
              %{
                name: Keyword.get(meta, :name, "Unknown"),
                type_params: Keyword.get(meta, :type_params, []),
                doc: Keyword.get(meta, :doc),
                methods:
                  Enum.flat_map(body, fn
                    {:function_def, m, _} -> [extract_function(m)]
                    _ -> []
                  end)
              }
            ]

          _ ->
            []
        end

      _ ->
        []
    end)
  end

  # -- Type Extraction ---------------------------------------------------------

  defp extract_types(stmts) do
    Enum.flat_map(stmts, fn
      {:type_annotation, meta, _children} ->
        [
          %{
            name: Keyword.get(meta, :name, "Unknown"),
            doc: Keyword.get(meta, :doc)
          }
        ]

      {:container, meta, variants} when is_list(meta) ->
        case Keyword.get(meta, :container_type) do
          :enum ->
            variant_names =
              Enum.map(variants, fn
                {:function_def, m, _} -> Keyword.get(m, :name, "?")
                {:variable, _, n} -> n
                _ -> "?"
              end)

            [
              %{
                name: Keyword.get(meta, :name, "Unknown"),
                doc: Keyword.get(meta, :doc),
                variants: variant_names
              }
            ]

          _ ->
            []
        end

      _ ->
        []
    end)
  end

  # Render a parser type-annotation AST to its surface string. The classic
  # `Cure.Types.Type.display/1` was removed with the classic pathway (#18); the
  # shared frontend printer renders the same type nodes (`{:variable, _, "Int"}`,
  # `{:function_call, [name: "List"], [...]}`) verbatim.
  defp render_type(type_ast), do: Printer.quoted_to_string(type_ast)

  # Effects are bare atoms on the `:effects` meta key (e.g. `:io`). Present them
  # in the capitalised surface spelling used in `! Io` signatures.
  defp render_effect(effect) when is_atom(effect),
    do: effect |> Atom.to_string() |> Macro.camelize()

  defp render_effect(effect), do: Printer.quoted_to_string(effect)
end

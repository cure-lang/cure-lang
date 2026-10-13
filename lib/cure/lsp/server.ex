defmodule Cure.LSP.Server do
  @moduledoc """
  Language Server Protocol implementation for Cure.

  Implements the LSP over stdio, providing:
  - Real-time diagnostics (compile errors) on document changes
  - Hover information (function signatures, types)
  - Document synchronization (full sync mode)

  ## Usage

  Start from the command line:

      mix cure.lsp

  Or programmatically:

      {:ok, pid} = Cure.LSP.Server.start_link()
  """

  use GenServer

  alias Cure.LSP.Transport
  alias Cure.LSP.Positions
  alias Cure.Compiler.{Formatter, Lexer, Parser, Printer}
  alias Cure.MetaAST.Metadata

  defstruct [
    :reader_pid,
    initialized: false,
    position_encoding: :utf16,
    documents: %{},
    ast_cache: %{},
    buffer: ""
  ]

  # -- Public API --------------------------------------------------------------

  @doc "Start the LSP server."
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, name: __MODULE__)
  end

  @doc """
  Process a raw incoming message (used by the stdin reader or tests).
  """
  def handle_raw_message(message) when is_map(message) do
    GenServer.cast(__MODULE__, {:message, message})
  end

  @doc """
  Process a raw message directly, returning the server's response action.

  Used for testing without the GenServer.
  """
  @spec process_message(map(), map()) :: {map(), [map()]}
  def process_message(message, state) do
    method = Map.get(message, "method")
    id = Map.get(message, "id")
    params = Map.get(message, "params", %{})

    do_handle(method, id, params, state)
  end

  # -- GenServer Callbacks -----------------------------------------------------

  @impl true
  def init(_opts) do
    # Start the stdin reader process that reads LSP frames and sends messages
    server = self()

    reader =
      spawn_link(fn ->
        lsp_reader_loop(server)
      end)

    {:ok, %__MODULE__{reader_pid: reader}}
  end

  @impl true
  def handle_cast({:message, message}, state) do
    {new_state, _responses} = process_message(message, state)
    {:noreply, struct(__MODULE__, new_state)}
  end

  @impl true
  def handle_info({:lsp_message, message}, state) do
    {new_state, _} = process_message(message, Map.from_struct(state))
    {:noreply, struct(__MODULE__, new_state)}
  end

  def handle_info(_msg, state), do: {:noreply, state}

  # -- Message Dispatch --------------------------------------------------------

  defp do_handle("initialize", id, params, state) do
    position_encoding = negotiate_position_encoding(params)

    result = %{
      "capabilities" => %{
        "positionEncoding" => position_encoding_name(position_encoding),
        "textDocumentSync" => %{
          "openClose" => true,
          "change" => 1,
          "save" => %{"includeText" => true}
        },
        "hoverProvider" => true,
        "definitionProvider" => true,
        "referencesProvider" => true,
        "documentHighlightProvider" => true,
        "foldingRangeProvider" => true,
        "callHierarchyProvider" => true,
        "documentSymbolProvider" => true,
        "workspaceSymbolProvider" => true,
        # Formatting is handled by `Cure.Compiler.Formatter`, a
        # source-preserving formatter that round-trip-validates its
        # output against the original AST before returning edits.
        # The destructive AST pretty printer is still available via
        # `cure fmt --aggressive` for users who want canonicalisation.
        "documentFormattingProvider" => true,
        "documentRangeFormattingProvider" => true,
        "documentOnTypeFormattingProvider" => %{
          "firstTriggerCharacter" => "\n",
          "moreTriggerCharacter" => ["|", "="]
        },
        "renameProvider" => %{"prepareProvider" => true},
        "signatureHelpProvider" => %{
          "triggerCharacters" => ["(", ","]
        },
        "inlayHintProvider" => %{"resolveProvider" => false},
        "semanticTokensProvider" => %{
          "legend" => %{
            "tokenTypes" => [
              "keyword",
              "function",
              "variable",
              "type",
              "string",
              "number",
              "comment",
              "operator"
            ],
            "tokenModifiers" => []
          },
          "full" => true,
          "range" => false
        },
        "codeLensProvider" => %{"resolveProvider" => false},
        "codeActionProvider" => %{
          "codeActionKinds" => ["quickfix"]
        },
        "completionProvider" => %{
          "triggerCharacters" => [".", ":", "?"]
        }
      },
      "serverInfo" => %{
        "name" => "cure-lsp",
        "version" => Cure.version()
      }
    }

    Transport.send_response(id, result)
    {state |> Map.put(:initialized, true) |> Map.put(:position_encoding, position_encoding), []}
  end

  defp do_handle("initialized", _id, _params, state) do
    {state, []}
  end

  defp do_handle("shutdown", id, _params, state) do
    Transport.send_response(id, nil)
    {state, []}
  end

  defp do_handle("exit", _id, _params, state) do
    System.halt(0)
    {state, []}
  end

  defp do_handle("textDocument/didOpen", _id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    text = Map.get(td, "text", "")

    docs = Map.get(state, :documents, %{})
    state = Map.put(state, :documents, Map.put(docs, uri, text))

    diagnostics = compute_diagnostics(uri, text, Map.get(state, :position_encoding, :utf16))
    publish_diagnostics(uri, diagnostics)

    {state, diagnostics}
  end

  defp do_handle("textDocument/didChange", _id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    version = Map.get(td, "version")
    changes = Map.get(params, "contentChanges", [])

    text =
      case changes do
        [%{"text" => full_text} | _] -> full_text
        _ -> Map.get(Map.get(state, :documents, %{}), uri, "")
      end

    docs = Map.get(state, :documents, %{})
    state = Map.put(state, :documents, Map.put(docs, uri, text))

    # Check AST cache -- skip reparse if version unchanged
    cache = Map.get(state, :ast_cache, %{})
    cached_version = get_in(cache, [uri, :version])

    if cached_version == version and version != nil do
      # Same version, skip diagnostics
      {state, []}
    else
      diagnostics = compute_diagnostics(uri, text, Map.get(state, :position_encoding, :utf16))
      publish_diagnostics(uri, diagnostics)

      # Update cache
      cache = Map.put(cache, uri, %{version: version, diagnostics: diagnostics})
      state = Map.put(state, :ast_cache, cache)

      {state, diagnostics}
    end
  end

  defp do_handle("textDocument/didClose", _id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    state = Map.put(state, :documents, Map.delete(docs, uri))

    # Clear diagnostics
    publish_diagnostics(uri, [])
    {state, []}
  end

  defp do_handle("textDocument/didSave", _id, _params, state) do
    {state, []}
  end

  defp do_handle("textDocument/hover", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)

    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")
    result = compute_hover(text, line, char)

    Transport.send_response(id, result)
    {state, []}
  end

  defp do_handle("textDocument/completion", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    position = Map.get(params, "position", %{})
    prefix = document_prefix(text, Map.get(position, "line", 0), Map.get(position, "character", 0))
    items = keyword_completions() ++ context_completions(text, prefix)
    Transport.send_response(id, items)
    {state, []}
  end

  defp do_handle("textDocument/definition", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)

    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")
    result = find_definition(text, uri, line, char, Map.get(state, :position_encoding, :utf16))

    Transport.send_response(id, result)
    {state, []}
  end

  defp do_handle("textDocument/documentSymbol", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    symbols = compute_symbols(text, Map.get(state, :position_encoding, :utf16))
    Transport.send_response(id, symbols)
    {state, []}
  end

  defp do_handle("textDocument/codeAction", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    context = Map.get(params, "context", %{})
    diagnostics = Map.get(context, "diagnostics", [])

    actions = compute_code_actions(uri, diagnostics)
    Transport.send_response(id, actions)
    {state, []}
  end

  defp do_handle("textDocument/inlayHint", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")
    hints = compute_inlay_hints(text)
    Transport.send_response(id, hints)
    {state, []}
  end

  defp do_handle("textDocument/signatureHelp", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, compute_signature_help(text, line, char))
    {state, []}
  end

  defp do_handle("textDocument/formatting", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, compute_formatting_edits(text))
    {state, []}
  end

  defp do_handle("textDocument/prepareRename", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, prepare_rename(text, line, char))
    {state, []}
  end

  defp do_handle("textDocument/rename", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)
    new_name = Map.get(params, "newName", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, compute_rename(uri, text, line, char, new_name))
    {state, []}
  end

  defp do_handle("textDocument/codeLens", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, compute_code_lenses(uri, text))
    {state, []}
  end

  defp do_handle("textDocument/semanticTokens/full", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, %{"data" => compute_semantic_tokens(text)})
    {state, []}
  end

  defp do_handle("workspace/symbol", id, params, state) do
    query = Map.get(params, "query", "")
    docs = Map.get(state, :documents, %{})
    Transport.send_response(id, compute_workspace_symbols(query, docs, Map.get(state, :position_encoding, :utf16)))
    {state, []}
  end

  defp do_handle("textDocument/references", id, params, state) do
    {uri, text, line, char} = request_position(params, state)
    include_decl = get_in(params, ["context", "includeDeclaration"]) != false

    Transport.send_response(
      id,
      compute_references(uri, text, line, char, include_decl, Map.get(state, :position_encoding, :utf16))
    )

    {state, []}
  end

  defp do_handle("textDocument/documentHighlight", id, params, state) do
    {_uri, text, line, char} = request_position(params, state)
    Transport.send_response(id, compute_document_highlights(text, line, char))
    {state, []}
  end

  defp do_handle("textDocument/foldingRange", id, params, state) do
    {_uri, text, _line, _char} = request_position(params, state)
    Transport.send_response(id, compute_folding_ranges(text))
    {state, []}
  end

  defp do_handle("textDocument/rangeFormatting", id, params, state) do
    {_uri, text, _line, _char} = request_position(params, state)
    Transport.send_response(id, compute_formatting_edits(text))
    {state, []}
  end

  defp do_handle("textDocument/onTypeFormatting", id, params, state) do
    {_uri, text, _line, _char} = request_position(params, state)
    Transport.send_response(id, compute_formatting_edits(text))
    {state, []}
  end

  # `prepareCallHierarchy` returns the symbol at the cursor as a call-hierarchy
  # item; `incomingCalls`/`outgoingCalls` report the same-document callers and
  # callees. Cross-file resolution is out of scope (the server holds only open
  # buffers), so the item carries the current document's uri.
  defp do_handle("textDocument/prepareCallHierarchy", id, params, state) do
    {uri, text, line, char} = request_position(params, state)
    Transport.send_response(id, compute_prepare_call_hierarchy(uri, text, line, char))
    {state, []}
  end

  defp do_handle("callHierarchy/incomingCalls", id, params, state) do
    item = Map.get(params, "item", %{})
    {uri, text} = item_document(item, state)
    Transport.send_response(id, compute_incoming_calls(uri, text, item))
    {state, []}
  end

  defp do_handle("callHierarchy/outgoingCalls", id, params, state) do
    item = Map.get(params, "item", %{})
    {uri, text} = item_document(item, state)
    Transport.send_response(id, compute_outgoing_calls(uri, text, item))
    {state, []}
  end

  # A request the server does not implement MUST still be answered, or the client
  # blocks forever waiting for a reply. Only requests (those carrying an `id`) get
  # an error; notifications (no `id`) are silently ignored, per JSON-RPC 2.0.
  defp do_handle(method, id, _params, state) when is_binary(method) and not is_nil(id) do
    Transport.send_error(id, -32601, "Method not found: #{method}")
    {state, []}
  end

  defp do_handle(_method, _id, _params, state) do
    {state, []}
  end

  # Shared extraction of the (uri, text, line, char) a position-based request needs.
  defp request_position(params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)
    text = Map.get(Map.get(state, :documents, %{}), uri, "")
    {uri, text, line, char}
  end

  defp item_document(item, state) do
    uri = Map.get(item, "uri", "")
    {uri, Map.get(Map.get(state, :documents, %{}), uri, "")}
  end

  # -- Diagnostics -------------------------------------------------------------

  @doc """
  Compute LSP diagnostics for a document.

  Runs the SAME front-end pipeline `cure check` uses
  (`Cure.Compiler.check_source/2`: lex, parse, declaration-use expansion, lifted
  module validation, elaboration, totality certification), so the editor's
  diagnostics agree with the command line. Calling only
  `Elab.Program.elaborate/2` skipped the declaration-use expansion and lifted
  module validation, so a file could be clean in the editor and rejected by
  `cure check`.
  """
  def compute_diagnostics(uri, text, encoding \\ :utf16) do
    case Cure.Compiler.check_source(text, file: uri) do
      {:ok, _env} ->
        []

      {:error, reason} ->
        reason
        |> lsp_error_list()
        |> Enum.map(&source_diagnostic(&1, uri, text, encoding))
    end
  end

  defp lsp_error_list({:parse_error, errors}) when is_list(errors), do: errors
  defp lsp_error_list({:type_error, errors}) when is_list(errors), do: errors
  defp lsp_error_list(errors) when is_list(errors), do: errors
  defp lsp_error_list(error), do: [error]

  @doc false
  def diagnostic_to_lsp(%Cure.Diagnostic{} = diagnostic, registry \\ nil, encoding \\ :utf16) do
    Cure.Diagnostic.Renderer.lsp(diagnostic, registry, encoding)
  end

  defp source_diagnostic(error, uri, source, encoding) do
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, uri, source)
    diagnostic_to_lsp(diagnostic, registry, encoding)
  end

  defp negotiate_position_encoding(params) do
    offered = get_in(params, ["capabilities", "general", "positionEncodings"]) || []

    cond do
      "utf-8" in offered -> :utf8
      "utf-16" in offered -> :utf16
      "utf-32" in offered -> :utf32
      true -> :utf16
    end
  end

  defp position_encoding_name(:utf8), do: "utf-8"
  defp position_encoding_name(:utf16), do: "utf-16"
  defp position_encoding_name(:utf32), do: "utf-32"

  defp publish_diagnostics(uri, diagnostics) do
    Transport.send_notification("textDocument/publishDiagnostics", %{
      "uri" => uri,
      "diagnostics" => diagnostics
    })
  end

  # -- Hover -------------------------------------------------------------------

  @doc false
  def compute_hover(text, line, char) do
    # Try AST-based hover first, fall back to line-matching
    case parse_to_ast(text) do
      {:ok, ast} ->
        symbols = build_symbol_table(ast)
        lines = String.split(text, "\n")
        target_line = Enum.at(lines, line, "")
        word = extract_word_at(target_line, char)
        dotted_word = extract_dotted_word_at(target_line, char)

        selected =
          cond do
            word == "simplify" ->
              %{kind: :simplify_command}

            word in ["induction", "case"] ->
              %{kind: :induction_command}

            true ->
              named_argument_at(symbols, target_line, char, word) ||
                Enum.find(induction_binding_symbols(ast), &(&1.name == word)) ||
                Enum.find(equation_symbols(ast), &(&1.name == dotted_word)) ||
                Enum.find(proof_rule_symbols(ast), &(&1.name == word)) ||
                Enum.find(symbols, fn s -> s.name == word end)
          end

        case selected do
          %{kind: :simplify_command} ->
            hover_text = """
            ```cure
            simplify
            simplify using [rule, ...]
            ```

            *Builds a kernel-checked equality certificate using the audited beta/iota/zeta/certified-delta reductions, visible defining equations, and any explicit decreasing rules.*
            """

            %{"contents" => %{"kind" => "markdown", "value" => String.trim(hover_text)}}

          %{kind: :induction_command} ->
            hover_text = """
            ```cure
            induction value
              case Constructor(fields..., induction_hypothesis...) =>
                proof
            ```

            *Checks one constructor case at a time and supplies a specialized induction hypothesis after each structurally recursive field. It lowers to ordinary total recursion checked by the kernel and totality checker.*
            """

            %{"contents" => %{"kind" => "markdown", "value" => String.trim(hover_text)}}

          %{kind: :induction_hypothesis, name: name, constructor: constructor, recursive_field: field} ->
            hover_text =
              "```cure\n#{name}\n```\n\n*Specialized induction hypothesis for recursive field `#{field}` of constructor `#{constructor}`. Its proposition is the enclosing goal specialized to that structurally smaller value.*"

            %{"contents" => %{"kind" => "markdown", "value" => hover_text}}

          %{kind: :induction_field, name: name, constructor: constructor} ->
            hover_text = "```cure\n#{name}\n```\n\n*Field bound by induction constructor `#{constructor}`.*"
            %{"contents" => %{"kind" => "markdown", "value" => hover_text}}

          %{kind: :equation, proposition: proposition, line: fn_line, owner: owner, constructor_path: path} ->
            hover_text =
              "```cure\n#{proposition}\n```\n\n*Certified defining equation for function `#{owner}`, constructor case `#{Enum.join(path, ".")}` — not a module. Defined from the clause at line #{fn_line}.*"

            %{"contents" => %{"kind" => "markdown", "value" => hover_text}}

          %{kind: :function, signature: sig, line: fn_line} ->
            hover_text = "```cure\n#{sig}\n```\n\n*Defined at line #{fn_line}*"
            %{"contents" => %{"kind" => "markdown", "value" => hover_text}}

          %{kind: :named_argument, label: label, parameter: parameter, type: type, function: function} ->
            hover_text =
              "```cure\n#{function}(#{label}: value)\n```\n\n*Named argument `#{label}` fills parameter `#{parameter}: #{type}`. Named arguments may be reordered after any positional prefix.*"

            %{"contents" => %{"kind" => "markdown", "value" => hover_text}}

          %{kind: :proof_rule, proposition: proposition, line: rule_line} ->
            hover_text =
              "```cure\n#{proposition}\n```\n\n*Local equality proof available as an explicit simplification rule. Declared at line #{rule_line}.*"

            %{"contents" => %{"kind" => "markdown", "value" => hover_text}}

          _ ->
            compute_hover_fallback(target_line)
        end

      _ ->
        lines = String.split(text, "\n")
        target_line = Enum.at(lines, line, "")
        compute_hover_fallback(target_line)
    end
  end

  defp compute_hover_fallback(target_line) do
    cond do
      String.contains?(target_line, "fn ") ->
        effect_info = infer_hover_effects(target_line)

        hover_text =
          if effect_info != "" do
            "```cure\n#{String.trim(target_line)}\n```\n\n**Effects:** #{effect_info}"
          else
            "```cure\n#{String.trim(target_line)}\n```"
          end

        %{"contents" => %{"kind" => "markdown", "value" => hover_text}}

      String.contains?(target_line, "mod ") ->
        %{
          "contents" => %{
            "kind" => "markdown",
            "value" => "**Module definition**\n```cure\n#{String.trim(target_line)}\n```"
          }
        }

      Enum.any?(["actor ", "fsm ", "sup ", "app "], &String.contains?(target_line, &1)) ->
        %{
          "contents" => %{
            "kind" => "markdown",
            "value" => "**Standard-library macro**\n```cure\n#{String.trim(target_line)}\n```"
          }
        }

      true ->
        nil
    end
  end

  defp infer_hover_effects(line) do
    cond do
      String.contains?(line, "! ") ->
        case Regex.run(~r/!\s+(.+?)(?:\s+when|\s+=|$)/, line) do
          [_, effects] -> effects
          _ -> ""
        end

      Enum.any?(["println", "print", "put_chars"], &String.contains?(line, &1)) ->
        "Io"

      String.contains?(line, "throw") ->
        "Exception"

      String.contains?(line, "spawn") ->
        "Spawn"

      true ->
        ""
    end
  end

  # -- Go-to-Definition --------------------------------------------------------

  defp find_definition(text, uri, line, char, encoding) do
    lines = String.split(text, "\n")
    target_line = Enum.at(lines, line, "")
    word = extract_word_at(target_line, char)
    dotted_word = extract_dotted_word_at(target_line, char)

    if word != "" do
      # Try AST-based symbol table first
      definition_line =
        case parse_to_ast(text) do
          {:ok, ast} ->
            symbols = build_symbol_table(ast, text, encoding)

            case Enum.find(equation_symbols(ast), &(&1.name == dotted_word)) ||
                   Enum.find(symbols, fn s -> s.name == word and s.kind == :function end) do
              %{line: l} -> l - 1
              _ -> nil
            end

          _ ->
            nil
        end

      # Fall back to text search
      definition_line =
        definition_line ||
          Enum.find_index(lines, fn l ->
            String.contains?(l, "fn #{word}(") or String.contains?(l, "fn #{word} ")
          end)

      if definition_line do
        symbol_range =
          case parse_to_ast(text) do
            {:ok, ast} ->
              case Enum.find(build_symbol_table(ast, text, encoding), fn s -> s.name == word and s.kind == :function end) do
                %{span: span} -> Positions.range(span, text, encoding)
                _ -> Positions.line_range(definition_line + 1, text, encoding)
              end

            _ ->
              Positions.line_range(definition_line + 1, text, encoding)
          end

        %{
          "uri" => uri,
          "range" => symbol_range
        }
      else
        nil
      end
    else
      nil
    end
  end

  defp extract_word(line) do
    case Regex.run(~r/\b([a-z_][a-z0-9_]*)\s*\(/, line) do
      [_, word] ->
        word

      _ ->
        case Regex.run(~r/\b([a-z_][a-z0-9_]*)/, String.trim(line)) do
          [_, word] -> word
          _ -> ""
        end
    end
  end

  defp extract_word_at(line, char) do
    # Extract the identifier at the given character position
    graphemes = String.graphemes(line)
    # Walk backwards from char to find word start
    {before, _after} = Enum.split(graphemes, min(char, length(graphemes)))
    prefix = before |> Enum.reverse() |> Enum.take_while(&(&1 =~ ~r/[a-zA-Z0-9_]/)) |> Enum.reverse() |> Enum.join()

    suffix =
      graphemes |> Enum.drop(min(char, length(graphemes))) |> Enum.take_while(&(&1 =~ ~r/[a-zA-Z0-9_]/)) |> Enum.join()

    word = prefix <> suffix
    if word == "", do: extract_word(line), else: word
  end

  defp extract_dotted_word_at(line, char) do
    graphemes = String.graphemes(line)
    {before, after_cursor} = Enum.split(graphemes, min(char, length(graphemes)))
    allowed = &(&1 =~ ~r/[a-zA-Z0-9_.]/)
    prefix = before |> Enum.reverse() |> Enum.take_while(allowed) |> Enum.reverse() |> Enum.join()
    suffix = after_cursor |> Enum.take_while(allowed) |> Enum.join()
    prefix <> suffix
  end

  # -- Document Symbols --------------------------------------------------------

  defp compute_symbols(text, encoding) do
    with {:ok, tokens} <- Lexer.tokenize(text, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      Cure.LSP.Symbols.extract(ast, text, encoding)
    else
      _ -> []
    end
  end

  # -- Code Actions ------------------------------------------------------------

  @doc false
  def compute_code_actions(uri, diagnostics) do
    Enum.flat_map(diagnostics, fn diag ->
      message = Map.get(diag, "message", "")
      structured = structured_code_actions(uri, diag)

      cond do
        structured != [] ->
          structured

        String.contains?(message, "not exhaustive") ->
          range = Map.get(diag, "range", %{})
          end_line = get_in(range, ["end", "line"]) || 0

          [
            %{
              "title" => "Add wildcard pattern (_ -> ...)",
              "kind" => "quickfix",
              "diagnostics" => [diag],
              "edit" => %{
                "changes" => %{
                  uri => [
                    %{
                      "range" => %{
                        "start" => %{"line" => end_line + 1, "character" => 0},
                        "end" => %{"line" => end_line + 1, "character" => 0}
                      },
                      "newText" => "    | _ -> throw \"unhandled case\"\n"
                    }
                  ]
                }
              }
            }
          ]

        String.contains?(message, "undefined") or String.contains?(message, "unbound") ->
          # Try to suggest similar names
          case Regex.run(~r/'([^']+)'/, message) do
            [_, name] ->
              candidates = ~w(fn mod let pickup match type interface implementation use)

              case Cure.Compiler.Errors.suggest(name, candidates) do
                nil ->
                  []

                suggestion ->
                  [
                    %{
                      "title" => "Did you mean '#{suggestion}'?",
                      "kind" => "quickfix",
                      "diagnostics" => [diag]
                    }
                  ]
              end

            _ ->
              []
          end

        true ->
          []
      end
    end)
  end

  defp structured_code_actions(default_uri, diagnostic) do
    diagnostic
    |> get_in(["data", "suggestions"])
    |> List.wrap()
    |> Enum.flat_map(fn suggestion ->
      edits = Map.get(suggestion, "edits", [])

      if Map.get(suggestion, "applicability") == "machine_applicable" and edits != [] do
        changes =
          Enum.group_by(
            edits,
            fn edit -> Map.get(edit, "uri") |> present_uri(default_uri) end,
            &Map.take(&1, ["range", "newText"])
          )

        [
          %{
            "title" => Map.fetch!(suggestion, "message"),
            "kind" => "quickfix",
            "diagnostics" => [diagnostic],
            "edit" => %{"changes" => changes}
          }
        ]
      else
        []
      end
    end)
  end

  defp present_uri(uri, default_uri) when uri in [nil, ""], do: default_uri
  defp present_uri(uri, _default_uri), do: uri

  # -- Completions -------------------------------------------------------------

  @doc false
  def keyword_completions do
    keywords =
      ~w(fn mod rec actor fsm sup app interface implementation type typealias primitive let have proof because rewrite simplify induction case pickup else match return throw try catch finally use local when requires where deriving quote unsafe)

    Enum.map(keywords, fn kw ->
      %{
        "label" => kw,
        "kind" => 14,
        "detail" => "Cure keyword"
      }
    end)
  end

  @doc false
  def context_completions(text, prefix) do
    induction_completions = induction_case_completions(text, prefix)

    ast_completions =
      case parse_to_ast(text) do
        {:ok, ast} ->
          symbols = build_symbol_table(ast)
          named_arguments = named_argument_completions(symbols, prefix)

          ordinary =
            Enum.map(symbols, fn s ->
              kind = if s.kind == :function, do: 3, else: 2
              %{"label" => s.name, "kind" => kind, "detail" => s.signature}
            end)

          equations =
            Enum.map(equation_symbols(ast), fn equation ->
              %{
                "label" => equation.name,
                "kind" => 3,
                "detail" => "Defining equation rule — #{equation.proposition}"
              }
            end)

          local_rules =
            Enum.map(proof_rule_symbols(ast), fn rule ->
              %{"label" => rule.name, "kind" => 6, "detail" => "Local equality rule — #{rule.proposition}"}
            end)

          induction_bindings =
            Enum.map(induction_binding_symbols(ast), fn binding ->
              detail =
                if binding.kind == :induction_hypothesis,
                  do: "Specialized induction hypothesis for #{binding.constructor}.#{binding.recursive_field}",
                  else: "Field bound by induction case #{binding.constructor}"

              %{"label" => binding.name, "kind" => 6, "detail" => detail}
            end)

          cond do
            Regex.match?(~r/simplify\s+using\s+\[[^\]]*$/s, prefix) ->
              local_rules ++ equations

            Regex.match?(~r/simplify\s+using\s+[^\[\]\n]*$/s, prefix) ->
              local_rules ++ equations

            Regex.match?(~r/induction\s+[a-zA-Z_][a-zA-Z0-9_]*[\s\S]*case\s+[A-Z][^=]*=>[^\n]*$/s, prefix) ->
              induction_bindings ++ local_rules ++ equations

            true ->
              named_arguments ++ ordinary ++ equations ++ induction_bindings
          end

        _ ->
          []
      end

    induction_completions ++ ast_completions
  end

  defp induction_case_completions(text, prefix) do
    case Regex.run(~r/induction\s+([a-zA-Z_][a-zA-Z0-9_]*)[^\n]*\n([\s\S]*)$/, prefix) do
      [_, subject, case_text] ->
        existing = Regex.scan(~r/\bcase\s+([A-Z][a-zA-Z0-9_]*)/, case_text, capture: :all_but_first) |> List.flatten()
        repaired = Regex.replace(~r/induction\s+#{Regex.escape(subject)}[^\n]*\n[\s\S]*$/, text, subject)

        with {:ok, ast} <- parse_to_ast(repaired),
             type_name when is_binary(type_name) <- parameter_type_name(ast, subject),
             %{variants: variants} <- induction_family(ast, type_name) do
          missing = Enum.reject(variants, &(&1.name in existing))
          induction_completion_items(type_name, missing)
        else
          _ -> []
        end

      _ ->
        []
    end
  end

  defp parameter_type_name(ast, subject) do
    ast
    |> collect_function_params([])
    |> Enum.find_value(fn
      {:param, meta, ^subject} -> surface_type_name(Keyword.get(meta, :type))
      _ -> nil
    end)
  end

  defp collect_function_params({:function_def, meta, body}, acc),
    do: Keyword.get(meta, :params, []) ++ Enum.flat_map(body, &collect_function_params(&1, acc))

  defp collect_function_params({_tag, _meta, children}, acc) when is_list(children),
    do: Enum.flat_map(children, &collect_function_params(&1, acc))

  defp collect_function_params(list, acc) when is_list(list), do: Enum.flat_map(list, &collect_function_params(&1, acc))
  defp collect_function_params(_other, acc), do: acc

  defp surface_type_name({:variable, _meta, name}), do: name
  defp surface_type_name({:function_call, meta, _args}), do: Keyword.get(meta, :name)
  defp surface_type_name(_), do: nil

  defp induction_family(ast, type_name) do
    ast
    |> collect_induction_families([])
    |> Enum.find(&(&1.name == type_name))
  end

  defp collect_induction_families({:container, meta, variants}, acc) do
    own =
      if Keyword.get(meta, :container_type) == :enum do
        [
          %{
            name: Keyword.get(meta, :name),
            variants: Enum.map(variants, &induction_variant(&1, Keyword.get(meta, :name)))
          }
        ]
      else
        []
      end

    own ++ Enum.flat_map(variants, &collect_induction_families(&1, acc))
  end

  defp collect_induction_families({_tag, _meta, children}, acc) when is_list(children),
    do: Enum.flat_map(children, &collect_induction_families(&1, acc))

  defp collect_induction_families(list, acc) when is_list(list),
    do: Enum.flat_map(list, &collect_induction_families(&1, acc))

  defp collect_induction_families(_other, acc), do: acc

  defp induction_variant({:variable, _meta, name}, _family), do: %{name: name, fields: []}

  defp induction_variant({:function_def, meta, _body}, family) do
    fields = Keyword.get(meta, :params, [])
    %{name: Keyword.get(meta, :name), fields: Enum.map(fields, &%{recursive: surface_type_name(&1) == family})}
  end

  defp induction_completion_items(_type_name, []), do: []

  defp induction_completion_items(type_name, variants) do
    rendered = variants |> Enum.map(&render_induction_case/1) |> Enum.join("\n\n")

    [
      %{
        "label" => "Generate all #{type_name} induction cases",
        "kind" => 15,
        "detail" => "Complete constructor cases with recursive induction hypotheses",
        "insertText" => rendered,
        "insertTextFormat" => 2
      }
      | Enum.map(variants, fn variant ->
          %{
            "label" => "case #{variant.name}",
            "kind" => 15,
            "detail" => "#{type_name} induction case",
            "insertText" => render_induction_case(variant),
            "insertTextFormat" => 2
          }
        end)
    ]
  end

  defp render_induction_case(%{name: name, fields: fields}) do
    recursive_count = Enum.count(fields, & &1.recursive)

    {ordinary, _} =
      Enum.map_reduce(Enum.with_index(fields), 1, fn {field, index}, tab ->
        base = induction_field_name(field.recursive, index, length(fields), recursive_count)
        {"${#{tab}:#{base}}", tab + 1}
      end)

    {hypotheses, next_tab} =
      fields
      |> Enum.with_index()
      |> Enum.filter(fn {field, _index} -> field.recursive end)
      |> Enum.map_reduce(length(ordinary) + 1, fn {_field, index}, tab ->
        base =
          if recursive_count == 1, do: "induction_hypothesis", else: "#{induction_side(index)}_induction_hypothesis"

        {"${#{tab}:#{base}}", tab + 1}
      end)

    bindings = ordinary ++ hypotheses
    pattern = if bindings == [], do: name, else: "#{name}(#{Enum.join(bindings, ", ")})"
    "case #{pattern} =>\n  ${#{next_tab}:proof}"
  end

  defp induction_field_name(true, 0, _total, 1), do: "previous"
  defp induction_field_name(true, index, _total, _recursive_count), do: induction_side(index)

  defp induction_field_name(false, index, _total, _recursive_count),
    do: if(index == 0, do: "value", else: "value#{index + 1}")

  defp induction_side(0), do: "left"
  defp induction_side(1), do: "right"
  defp induction_side(index), do: "recursive#{index + 1}"

  @doc false
  def induction_binding_symbols(ast) do
    families = collect_induction_families(ast, [])
    params = collect_function_params(ast, [])
    collect_induction_bindings(ast, families, params)
  end

  defp collect_induction_bindings({:induction, _meta, [{:variable, _, subject} | cases]}, families, params) do
    type_name =
      Enum.find_value(params, fn
        {:param, meta, ^subject} -> surface_type_name(Keyword.get(meta, :type))
        _ -> nil
      end)

    family = Enum.find(families, &(&1.name == type_name))

    if family do
      Enum.flat_map(cases, &induction_case_bindings(&1, family))
    else
      []
    end
  end

  defp collect_induction_bindings({_tag, _meta, children}, families, params) when is_list(children),
    do: Enum.flat_map(children, &collect_induction_bindings(&1, families, params))

  defp collect_induction_bindings(list, families, params) when is_list(list),
    do: Enum.flat_map(list, &collect_induction_bindings(&1, families, params))

  defp collect_induction_bindings(_other, _families, _params), do: []

  defp induction_case_bindings({:induction_case, _meta, [pattern, _body]}, family) do
    {constructor, args} =
      case pattern do
        {:function_call, meta, args} -> {Keyword.get(meta, :name), args}
        {:variable, _meta, name} -> {name, []}
        _ -> {nil, []}
      end

    variant = Enum.find(family.variants, &(&1.name == constructor))

    if variant do
      ordinary_count = length(variant.fields)
      recursive = variant.fields |> Enum.with_index() |> Enum.filter(fn {field, _} -> field.recursive end)
      {ordinary_args, hypothesis_args} = Enum.split(args, ordinary_count)

      fields =
        ordinary_args
        |> Enum.with_index()
        |> Enum.flat_map(fn
          {{:variable, _meta, name}, _index} when name != "_" ->
            [%{kind: :induction_field, name: name, constructor: constructor}]

          _ ->
            []
        end)

      hypotheses =
        Enum.zip(hypothesis_args, recursive)
        |> Enum.flat_map(fn
          {{:variable, _meta, name}, {_field, field_index}} when name != "_" ->
            [
              %{
                kind: :induction_hypothesis,
                name: name,
                constructor: constructor,
                recursive_field: induction_side(field_index)
              }
            ]

          _ ->
            []
        end)

      fields ++ hypotheses
    else
      []
    end
  end

  defp document_prefix(text, line, character) do
    lines = String.split(text, "\n", trim: false)
    prior = lines |> Enum.take(line) |> Enum.join("\n")
    current = lines |> Enum.at(line, "") |> String.slice(0, character)
    if line == 0, do: current, else: prior <> "\n" <> current
  end

  @doc false
  def equation_symbols(ast) do
    ast
    |> collect_equation_symbols([])
    |> Enum.group_by(& &1.name)
    |> Enum.flat_map(fn
      {_name, [only]} -> [only]
      {_name, collisions} -> Enum.map(collisions, &%{&1 | name: &1.structural_name})
    end)
    |> Enum.sort_by(& &1.name)
  end

  @doc false
  def proof_rule_symbols(ast), do: collect_proof_rule_symbols(ast)

  defp collect_proof_rule_symbols(list) when is_list(list), do: Enum.flat_map(list, &collect_proof_rule_symbols/1)

  defp collect_proof_rule_symbols({:function_def, meta, body}) do
    params =
      meta
      |> Keyword.get(:params, [])
      |> Enum.flat_map(fn
        {:param, param_meta, name} ->
          case Keyword.get(param_meta, :type) do
            {:function_call, type_meta, _args} = type ->
              if Keyword.get(type_meta, :name) == "Equivalent" do
                [
                  %{
                    name: name,
                    kind: :proof_rule,
                    proposition: Printer.quoted_to_string(type),
                    line: Keyword.get(param_meta, :line, 1)
                  }
                ]
              else
                []
              end

            _ ->
              []
          end

        _ ->
          []
      end)

    params ++ collect_proof_rule_symbols(body)
  end

  defp collect_proof_rule_symbols({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &collect_proof_rule_symbols/1)

  defp collect_proof_rule_symbols(_other), do: []

  defp collect_equation_symbols(list, acc) when is_list(list),
    do: Enum.flat_map(list, &collect_equation_symbols(&1, acc))

  defp collect_equation_symbols({:function_def, meta, body}, _acc) do
    name = Keyword.get(meta, :name, "?")

    params =
      meta
      |> Keyword.get(:params, [])
      |> Enum.flat_map(fn
        {:param, _param_meta, param_name} -> [param_name]
        _type_parameter -> []
      end)

    info = Metadata.source_info(meta)
    collect_equation_paths(body, name, params, %{}, [], Keyword.get(meta, :line, 1), info && info.whole)
  end

  defp collect_equation_symbols({_tag, _meta, children}, acc) when is_list(children),
    do: Enum.flat_map(children, &collect_equation_symbols(&1, acc))

  defp collect_equation_symbols(_other, _acc), do: []

  defp collect_equation_paths([single], name, params, replacements, path, line, span),
    do: collect_equation_paths(single, name, params, replacements, path, line, span)

  defp collect_equation_paths(
         {:pattern_match, _meta, [{:variable, _scrutinee_meta, scrutinee} | arms]},
         name,
         params,
         replacements,
         path,
         line,
         span
       ) do
    Enum.flat_map(arms, fn
      {:match_arm, arm_meta, body} ->
        pattern = Keyword.get(arm_meta, :pattern)

        case equation_pattern_name(pattern) do
          nil ->
            []

          constructor ->
            info = Metadata.source_info(arm_meta)

            collect_equation_paths(
              body,
              name,
              params,
              Map.put(replacements, scrutinee, pattern),
              path ++ [constructor],
              (info && info.whole.start_line) || line,
              (info && info.whole) || span
            )
        end

      _ ->
        []
    end)
  end

  defp collect_equation_paths(_leaf, _name, _params, _replacements, [], _line, _span), do: []

  defp collect_equation_paths(leaf, name, params, replacements, path, line, span) do
    member = List.last(path)
    full_name = "#{name}.#{member}"
    arguments = Enum.map(params, &Map.get(replacements, &1, {:variable, [scope: :local], &1}))
    left = Printer.quoted_to_string({:function_call, [name: name], arguments})
    right = leaf |> single_equation_body() |> Printer.quoted_to_string()

    [
      %{
        name: full_name,
        structural_name: name <> "/" <> Enum.join(path, "/"),
        kind: :equation,
        owner: name,
        constructor_path: path,
        line: line,
        span: span,
        proposition: "#{full_name} : Equivalent(_, #{left}, #{right})"
      }
    ]
  end

  defp single_equation_body([body]), do: body
  defp single_equation_body(body), do: body

  defp equation_pattern_name({:variable, _meta, name}) when is_binary(name), do: name
  defp equation_pattern_name({:function_call, meta, _args}), do: Keyword.get(meta, :name)
  defp equation_pattern_name(_pattern), do: nil

  # -- AST Helpers for LSP -------------------------------------------------------

  defp parse_to_ast(text) do
    with {:ok, tokens} <- Lexer.tokenize(text, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      {:ok, ast}
    end
  end

  @doc false
  def build_symbol_table(ast, source \\ nil, encoding \\ :utf16) do
    extract_symbols(ast, [], source, encoding)
  end

  defp extract_symbols({:container, meta, body}, acc, source, encoding) do
    name = Keyword.get(meta, :name, "unknown")
    line = Keyword.get(meta, :line, 1)
    type = Keyword.get(meta, :container_type, :module)
    info = Metadata.source_info(meta)
    acc = [%{name: name, kind: :module, line: line, signature: "#{type} #{name}", span: info && info.whole} | acc]
    Enum.reduce(body, acc, &extract_symbols(&1, &2, source, encoding))
  end

  defp extract_symbols({:block, _, children}, acc, source, encoding) do
    Enum.reduce(children, acc, &extract_symbols(&1, &2, source, encoding))
  end

  defp extract_symbols({:function_def, meta, _body}, acc, _source, _encoding) do
    name = Keyword.get(meta, :name, "unknown")
    params = Keyword.get(meta, :params, [])
    line = Keyword.get(meta, :line, 1)

    param_str = Enum.map_join(params, ", ", &format_param/1)

    sig = "fn #{name}(#{param_str})"
    info = Metadata.source_info(meta)

    [
      %{
        name: name,
        kind: :function,
        line: line,
        signature: sig,
        parameters: Enum.map(params, &parameter_info/1),
        span: info && info.whole
      }
      | acc
    ]
  end

  defp extract_symbols(_, acc, _source, _encoding), do: acc

  # Parameter pretty-printer tolerant of the various AST shapes the parser
  # can emit (full `:param` tuples, bare `:variable` tuples in generic type
  # parameter position, raw identifiers, etc.). Any shape we don't know is
  # rendered with a safe fallback so inlay-hint / symbol requests cannot
  # crash the LSP server.
  defp format_param({:param, pm, pn}) when is_list(pm) do
    external = Keyword.get(pm, :label)
    name = to_string(pn)

    case Keyword.get(pm, :type) do
      nil -> if(external, do: "#{external} #{name}", else: name)
      type -> if(external, do: "#{external} #{name}: #{format_type(type)}", else: "#{name}: #{format_type(type)}")
    end
  end

  defp format_param({:variable, _, name}) when is_binary(name), do: name
  defp format_param({:variable, _, name}) when is_atom(name), do: Atom.to_string(name)
  defp format_param(name) when is_binary(name), do: name
  defp format_param(name) when is_atom(name), do: Atom.to_string(name)
  defp format_param(other), do: inspect(other)

  defp parameter_info({:param, meta, name}) do
    %{
      label: to_string(Keyword.get(meta, :label) || name),
      name: to_string(name),
      required: not is_nil(Keyword.get(meta, :label)),
      type: format_type(Keyword.get(meta, :type))
    }
  end

  defp parameter_info(other), do: %{label: format_param(other), name: format_param(other), required: false, type: "Any"}

  defp format_type({:variable, _, name}) when is_binary(name), do: name
  defp format_type({:variable, _, name}) when is_atom(name), do: Atom.to_string(name)

  defp format_type({:function_call, meta, _}) when is_list(meta),
    do: Keyword.get(meta, :name, "?") |> to_string()

  defp format_type(other) when is_binary(other), do: other
  defp format_type(other) when is_atom(other), do: Atom.to_string(other)
  defp format_type(_), do: "Any"

  defp named_argument_at(symbols, line, _char, word) when is_binary(word) and word != "" do
    escaped = Regex.escape(word)

    case Regex.run(~r/([a-z_][a-zA-Z0-9_]*)\s*\([^)]*\b#{escaped}\s*:/, line) do
      [_, function] ->
        with %{parameters: parameters} <- Enum.find(symbols, &(&1.kind == :function and &1.name == function)),
             %{label: ^word, name: name, type: type} <- Enum.find(parameters, &(&1.label == word)) do
          %{kind: :named_argument, label: word, parameter: name, type: type, function: function}
        else
          _ -> nil
        end

      _ ->
        nil
    end
  end

  defp named_argument_at(_symbols, _line, _char, _word), do: nil

  defp named_argument_completions(symbols, prefix) do
    case Regex.scan(~r/([a-z_][a-zA-Z0-9_]*)\s*\(([^()]*)$/s, prefix) |> List.last() do
      [_, function, written] ->
        supplied = Regex.scan(~r/\b([a-z_][a-zA-Z0-9_]*)\s*:/, written, capture: :all_but_first) |> List.flatten()

        case Enum.find(symbols, &(&1.kind == :function and &1.name == function)) do
          %{parameters: parameters} ->
            parameters
            |> Enum.reject(&(&1.label in supplied))
            |> Enum.map(fn parameter ->
              %{
                "label" => parameter.label <> ":",
                "kind" => 5,
                "detail" => "Named argument for #{parameter.name}: #{parameter.type}",
                "insertText" => parameter.label <> ": ${1:value}",
                "insertTextFormat" => 2
              }
            end)

          _ ->
            []
        end

      _ ->
        []
    end
  end

  # -- Inlay hints --------------------------------------------------------------

  @doc false
  def compute_inlay_hints(text) do
    case parse_to_ast(text) do
      {:ok, ast} ->
        symbols = build_symbol_table(ast)

        declaration_hints =
          Enum.flat_map(symbols, fn s ->
            case s do
              %{kind: :function, line: l, signature: sig} ->
                [
                  %{
                    "position" => %{"line" => l - 1, "character" => 0},
                    "label" => "# " <> sig,
                    "kind" => 2,
                    "paddingRight" => true
                  }
                ]

              _ ->
                []
            end
          end)

        declaration_hints ++ named_call_inlay_hints(ast, symbols)

      _ ->
        []
    end
  end

  defp named_call_inlay_hints(ast, symbols) do
    ast
    |> collect_function_calls()
    |> Enum.flat_map(fn {:function_call, meta, _args} ->
      name = Keyword.get(meta, :name)
      labels = Keyword.get(meta, :arg_labels)
      info = Metadata.source_info(meta)

      with %{parameters: parameters} <- Enum.find(symbols, &(&1.kind == :function and &1.name == name)),
           %Cure.MetaAST.SourceInfo{arguments: spans} <- info do
        labels = labels || List.duplicate(nil, length(spans))

        Enum.zip([spans, labels, parameters])
        |> Enum.flat_map(fn
          {%Cure.Diagnostic.Span{} = span, nil, parameter} ->
            [
              %{
                "position" => %{"line" => span.start_line - 1, "character" => span.start_column - 1},
                "label" => parameter.label <> ":",
                "kind" => 2,
                "paddingRight" => true
              }
            ]

          _ ->
            []
        end)
      else
        _ -> []
      end
    end)
  end

  defp collect_function_calls({:function_call, _meta, args} = call),
    do: [call | Enum.flat_map(args, &collect_function_calls/1)]

  defp collect_function_calls({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &collect_function_calls/1)

  defp collect_function_calls(list) when is_list(list), do: Enum.flat_map(list, &collect_function_calls/1)
  defp collect_function_calls(_other), do: []

  # -- Signature help -----------------------------------------------------------

  @doc false
  def compute_signature_help(text, line, char) do
    lines = String.split(text, "\n")
    target = Enum.at(lines, line, "")
    prefix = String.slice(target, 0, char)

    case Regex.scan(~r/([a-z_][a-zA-Z0-9_]*)\s*\(([^()]*)$/s, prefix) |> List.last() do
      [_, name, written] ->
        case parse_to_ast(text) do
          {:ok, ast} ->
            symbols = build_symbol_table(ast)

            case Enum.find(symbols, fn s -> s.name == name and s.kind == :function end) do
              %{signature: sig, parameters: parameters} ->
                active = active_named_parameter(parameters, written)

                %{
                  "signatures" => [
                    %{
                      "label" => sig,
                      "parameters" =>
                        Enum.map(parameters, fn parameter ->
                          %{
                            "label" => parameter.label,
                            "documentation" => "#{parameter.name}: #{parameter.type}"
                          }
                        end)
                    }
                  ],
                  "activeSignature" => 0,
                  "activeParameter" => active
                }

              _ ->
                nil
            end

          _ ->
            nil
        end

      _ ->
        nil
    end
  end

  defp active_named_parameter(parameters, written) do
    current = written |> String.split(",") |> List.last() |> String.trim()

    case Regex.run(~r/^([a-z_][a-zA-Z0-9_]*)\s*:/, current) do
      [_, label] -> Enum.find_index(parameters, &(&1.label == label)) || 0
      _ -> min(length(String.split(written, ",")) - 1, max(length(parameters) - 1, 0))
    end
  end

  # -- Formatting ---------------------------------------------------------------

  @doc """
  Compute formatting edits for a document.

  Delegates to `Cure.Compiler.Formatter`, which performs a small set
  of source-preserving transformations (line-ending normalisation,
  trailing-whitespace stripping, tab-to-space in indentation,
  blank-line collapsing, and operator spacing) and validates the
  result against a re-parse of the original AST. Returns a single
  whole-document `TextEdit` when the formatter produces a change, or
  an empty list otherwise.
  """
  @spec compute_formatting_edits(String.t()) :: [map()]
  def compute_formatting_edits(text) when is_binary(text) do
    Formatter.format_to_edits(text)
  end

  def compute_formatting_edits(_), do: []

  # -- Rename -------------------------------------------------------------------

  @doc false
  def prepare_rename(text, line, char) do
    lines = String.split(text, "\n")
    target = Enum.at(lines, line, "")
    word = extract_word_at(target, char)

    if word == "" do
      nil
    else
      %{
        "start" => %{"line" => line, "character" => max(char - String.length(word), 0)},
        "end" => %{"line" => line, "character" => char + String.length(word)}
      }
    end
  end

  @doc """
  Compute rename edits for the symbol under the cursor.

  The match is **scope-aware**: comments and string/char literals are masked out
  before scanning, so a rename never rewrites the symbol inside a comment or a
  string. (The previous implementation matched `\\bword\\b` on every raw line and
  happily renamed occurrences in `# rename foo here` and `"foo"`.)
  """
  def compute_rename(uri, text, line, char, new_name) do
    lines = String.split(text, "\n")
    target = Enum.at(lines, line, "")
    old = extract_word_at(target, char)

    edits =
      lines
      |> mask_non_code_lines()
      |> Enum.with_index()
      |> Enum.flat_map(fn {masked, i} ->
        case word_occurrences(masked, old) do
          [] ->
            []

          ranges ->
            Enum.map(ranges, fn {start_col, end_col} ->
              %{
                "range" => %{
                  "start" => %{"line" => i, "character" => start_col},
                  "end" => %{"line" => i, "character" => end_col}
                },
                "newText" => new_name
              }
            end)
        end
      end)

    %{"changes" => %{uri => edits}}
  end

  defp word_occurrences(line, word) when word != "" do
    pattern = Regex.compile!("\\b" <> Regex.escape(word) <> "\\b")

    Regex.scan(pattern, line, return: :index)
    |> Enum.map(fn [{start, len}] -> {start, start + len} end)
  end

  defp word_occurrences(_line, _word), do: []

  # -- References / highlights --------------------------------------------------

  @doc """
  Find every reference to the symbol under the cursor, as LSP `Location`s.

  Scope-aware (comments and string literals are excluded), and by default the
  declaration line is included unless the client sets
  `context.includeDeclaration` to false.
  """
  def compute_references(uri, text, line, char, include_declaration, _encoding \\ :utf16) do
    lines = String.split(text, "\n")
    target = Enum.at(lines, line, "")
    word = extract_word_at(target, char)

    if word == "" do
      []
    else
      declaration = declaration_line(lines, word)

      lines
      |> mask_non_code_lines()
      |> Enum.with_index()
      |> Enum.flat_map(fn {masked, i} ->
        if not include_declaration and i == declaration do
          []
        else
          Enum.map(word_occurrences(masked, word), fn {start_col, end_col} ->
            %{
              "uri" => uri,
              "range" => %{
                "start" => %{"line" => i, "character" => start_col},
                "end" => %{"line" => i, "character" => end_col}
              }
            }
          end)
        end
      end)
    end
  end

  @doc """
  Highlight every occurrence of the symbol under the cursor in the current
  document, as LSP `DocumentHighlight`s. The declaration is marked `Write`
  (kind 3), every other occurrence `Read` (kind 2).
  """
  def compute_document_highlights(text, line, char) do
    lines = String.split(text, "\n")
    target = Enum.at(lines, line, "")
    word = extract_word_at(target, char)

    if word == "" do
      []
    else
      declaration = declaration_line(lines, word)

      lines
      |> mask_non_code_lines()
      |> Enum.with_index()
      |> Enum.flat_map(fn {masked, i} ->
        kind = if i == declaration, do: 3, else: 2

        Enum.map(word_occurrences(masked, word), fn {start_col, end_col} ->
          %{
            "range" => %{
              "start" => %{"line" => i, "character" => start_col},
              "end" => %{"line" => i, "character" => end_col}
            },
            "kind" => kind
          }
        end)
      end)
    end
  end

  # The first line that declares `word` as a function, so references/highlights
  # can distinguish the definition site from its uses.
  defp declaration_line(lines, word) do
    Enum.find_index(lines, fn l ->
      String.contains?(l, "fn #{word}(") or String.contains?(l, "fn #{word} ")
    end)
  end

  # -- Folding ranges -----------------------------------------------------------

  @doc """
  Compute folding ranges from indentation: a run of deeper-indented lines folds
  under the shallower line that precedes it. Also folds consecutive comment
  blocks. Indentation-based folding needs no parse, so it works on a buffer that
  does not yet compile.
  """
  def compute_folding_ranges(text) do
    lines = String.split(text, "\n")

    indentation_folds(lines) ++ comment_folds(lines)
  end

  defp indentation_folds(lines) do
    lines
    |> Enum.with_index()
    |> Enum.reduce([], fn {line, i}, acc ->
      cond do
        String.trim(line) == "" ->
          acc

        true ->
          case block_end(lines, i) do
            nil -> acc
            end_i -> [%{"startLine" => i, "endLine" => end_i} | acc]
          end
      end
    end)
    |> Enum.reverse()
  end

  # The last line of the contiguous block of lines indented MORE than line `i`.
  # Returns nil when the next non-blank line is not deeper-indented (nothing to
  # fold). Blank lines inside the block are absorbed; a blank line followed by a
  # line at or below the header's indent ends the block.
  defp block_end(lines, i) do
    header_indent = indent_of(Enum.at(lines, i))
    first = next_non_blank(lines, i + 1)

    if first != nil and indent_of(Enum.at(lines, first)) > header_indent do
      find_block_end(lines, first, header_indent)
    else
      nil
    end
  end

  defp find_block_end(lines, i, header_indent) do
    cond do
      i >= length(lines) ->
        i - 1

      String.trim(Enum.at(lines, i)) == "" ->
        # A blank line may be interior or trailing; look past it.
        case next_non_blank(lines, i + 1) do
          nil ->
            i - 1

          next_i ->
            if indent_of(Enum.at(lines, next_i)) > header_indent,
              do: find_block_end(lines, next_i, header_indent),
              else: i - 1
        end

      indent_of(Enum.at(lines, i)) > header_indent ->
        find_block_end(lines, i + 1, header_indent)

      true ->
        i - 1
    end
  end

  defp next_non_blank(lines, i) do
    cond do
      i >= length(lines) -> nil
      String.trim(Enum.at(lines, i)) == "" -> next_non_blank(lines, i + 1)
      true -> i
    end
  end

  defp comment_folds(lines) do
    lines
    |> Enum.with_index()
    |> Enum.reduce({[], nil, nil}, fn {line, i}, {acc, start, prev} ->
      trimmed = String.trim_leading(line)

      if String.starts_with?(trimmed, "#") do
        start = start || i
        {acc, start, i}
      else
        {close_comment_fold(acc, start, prev), nil, nil}
      end
    end)
    |> then(fn {acc, start, prev} -> close_comment_fold(acc, start, prev) end)
    |> Enum.reverse()
  end

  defp close_comment_fold(acc, start, prev) when is_integer(start) and is_integer(prev) and prev > start,
    do: [%{"startLine" => start, "endLine" => prev, "kind" => "comment"} | acc]

  defp close_comment_fold(acc, _start, _prev), do: acc

  defp indent_of(line), do: line |> String.length() |> Kernel.-(String.trim_leading(line) |> String.length())

  # -- Call hierarchy -----------------------------------------------------------

  @doc """
  Return a single call-hierarchy item for the function under the cursor, or nil.
  """
  def compute_prepare_call_hierarchy(uri, text, line, char) do
    lines = String.split(text, "\n")
    target = Enum.at(lines, line, "")
    word = extract_word_at(target, char)

    with true <- word != "",
         {:ok, ast} <- parse_to_ast(text),
         %{kind: :function, line: l, span: span} <-
           Enum.find(build_symbol_table(ast), &(&1.kind == :function and &1.name == word)) do
      range =
        if span,
          do: Positions.range(span, text, :utf16),
          else: Positions.line_range(l, text, :utf16)

      [%{"name" => word, "kind" => 12, "uri" => uri, "range" => range, "selectionRange" => range}]
    else
      _ -> nil
    end
  end

  @doc """
  Same-document callers of the function named in `item`. Each entry is an LSP
  `CallHierarchyIncomingCall` (a caller item plus the ranges it calls from).
  """
  def compute_incoming_calls(uri, text, item) do
    name = Map.get(item, "name", "")

    with true <- name != "",
         {:ok, ast} <- parse_to_ast(text) do
      call_sites = call_sites(ast, name, text)

      call_sites
      |> Enum.group_by(& &1.caller)
      |> Enum.flat_map(fn {caller, sites} ->
        case Enum.find(build_symbol_table(ast), &(&1.kind == :function and &1.name == caller)) do
          nil ->
            []

          %{span: span, line: l} ->
            range = if span, do: Positions.range(span, text, :utf16), else: Positions.line_range(l, text, :utf16)

            [
              %{
                "from" => %{
                  "name" => caller,
                  "kind" => 12,
                  "uri" => uri,
                  "range" => range,
                  "selectionRange" => range
                },
                "fromRanges" => Enum.map(sites, & &1.range)
              }
            ]
        end
      end)
    else
      _ -> []
    end
  end

  @doc """
  Same-document callees of the function named in `item`.
  """
  def compute_outgoing_calls(uri, text, item) do
    name = Map.get(item, "name", "")

    with true <- name != "",
         {:ok, ast} <- parse_to_ast(text) do
      callees = outgoing_callees(ast, name, text)

      callees
      |> Enum.uniq()
      |> Enum.flat_map(fn callee ->
        case Enum.find(build_symbol_table(ast), &(&1.kind == :function and &1.name == callee)) do
          nil ->
            []

          %{span: span, line: l} ->
            range = if span, do: Positions.range(span, text, :utf16), else: Positions.line_range(l, text, :utf16)

            [
              %{
                "to" => %{
                  "name" => callee,
                  "kind" => 12,
                  "uri" => uri,
                  "range" => range,
                  "selectionRange" => range
                },
                "fromRanges" => []
              }
            ]
        end
      end)
    else
      _ -> []
    end
  end

  # Every call site of `name` in the AST, tagged with the enclosing function.
  defp call_sites(ast, name, text) do
    ast
    |> collect_functions()
    |> Enum.flat_map(fn {fn_name, body, _span} ->
      body
      |> collect_calls(text)
      |> Enum.filter(&(&1.name == name))
      |> Enum.map(fn call -> %{caller: fn_name, range: call.range} end)
    end)
  end

  defp outgoing_callees(ast, name, text) do
    ast
    |> collect_functions()
    |> Enum.filter(fn {fn_name, _body, _span} -> fn_name == name end)
    |> Enum.flat_map(fn {_fn_name, body, _span} -> body |> collect_calls(text) |> Enum.map(& &1.name) end)
  end

  defp collect_functions({:function_def, meta, body}) do
    name = Keyword.get(meta, :name)
    info = Metadata.source_info(meta)
    span = info && info.whole

    own = if name, do: [{name, body, span}], else: []
    own ++ Enum.flat_map(body, &collect_functions/1)
  end

  defp collect_functions({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &collect_functions/1)

  defp collect_functions(list) when is_list(list), do: Enum.flat_map(list, &collect_functions/1)
  defp collect_functions(_other), do: []

  defp collect_calls({:function_call, meta, args}, text) do
    name = Keyword.get(meta, :name)
    info = Metadata.source_info(meta)

    own =
      case {name, info && info.whole} do
        {nil, _} -> []
        {_, nil} -> []
        {name, span} -> [%{name: name, range: Positions.range(span, text, :utf16)}]
      end

    own ++ Enum.flat_map(args, &collect_calls(&1, text))
  end

  defp collect_calls({_tag, _meta, children}, text) when is_list(children),
    do: Enum.flat_map(children, &collect_calls(&1, text))

  defp collect_calls(list, text) when is_list(list), do: Enum.flat_map(list, &collect_calls(&1, text))
  defp collect_calls(_other, _text), do: []

  # -- Non-code masking ---------------------------------------------------------

  # Replace the contents of comments and string/char literals with spaces,
  # preserving character positions, so word matching never touches them. Takes a
  # list of lines (the callers have already split the document).
  defp mask_non_code_lines(lines) when is_list(lines), do: Enum.map(lines, &mask_line/1)

  defp mask_line(line), do: mask_line(String.graphemes(line), [], :code)

  defp mask_line([], acc, _mode), do: acc |> Enum.reverse() |> Enum.join()

  defp mask_line([g | rest], acc, :code) do
    cond do
      g == "#" -> mask_line(rest, [" " | acc], :comment)
      g in ["\"", "'"] -> mask_line(rest, [" " | acc], {:string, g})
      true -> mask_line(rest, [g | acc], :code)
    end
  end

  defp mask_line([_g | rest], acc, :comment), do: mask_line(rest, [" " | acc], :comment)

  defp mask_line([g | rest], acc, {:string, quote}) do
    if g == quote do
      mask_line(rest, [" " | acc], :code)
    else
      mask_line(rest, [" " | acc], {:string, quote})
    end
  end

  # -- Code lens ----------------------------------------------------------------

  @doc false
  def compute_code_lenses(_uri, text) do
    case parse_to_ast(text) do
      {:ok, ast} ->
        ast
        |> build_symbol_table()
        |> Enum.flat_map(fn
          %{kind: :function, line: l, signature: sig} ->
            [
              %{
                "range" => %{
                  "start" => %{"line" => l - 1, "character" => 0},
                  "end" => %{"line" => l - 1, "character" => 0}
                },
                # A code lens whose `command` is not a registered client command
                # is a dead reference the client cannot execute. The lens is
                # therefore self-describing: its title IS the type/effect
                # summary (the function's signature). A client that wants a
                # clickable action can resolve it via `codeLens/resolve` using
                # the `data` payload.
                "command" => %{"title" => "Type | Effects: " <> sig, "command" => ""},
                "data" => %{"cure" => "function", "signature" => sig}
              }
            ]

          _ ->
            []
        end)

      _ ->
        []
    end
  end

  # -- Semantic tokens ----------------------------------------------------------

  @doc """
  Compute the LSP semantic-token integer stream for a document.

  Emits the token types the legend declares — keywords, function names, type
  names, string literals, numbers, comments and operators — not just keywords.
  (The legend previously declared eight types while the scanner only ever emitted
  type 0, so functions/types/strings/numbers/comments got no semantic
  highlighting.) Comments and strings are masked out of the identifier scan so an
  identifier inside a comment or string is not mistaken for code.
  """
  def compute_semantic_tokens(text) do
    lines = String.split(text, "\n")

    {data, _} =
      lines
      |> Enum.with_index()
      |> Enum.reduce({[], {0, 0}}, fn {line, idx}, {acc, prev} ->
        line
        |> scan_semantic_tokens(idx)
        |> Enum.reduce({acc, prev}, fn {l, c, len, ttype}, {acc2, {pl, pc}} ->
          delta_line = l - pl
          delta_start = if delta_line == 0, do: c - pc, else: c
          # Prepend in reverse field order so the final Enum.reverse/1 produces
          # the LSP-required [delta_line, delta_start, length, token_type, mods].
          {[0, ttype, len, delta_start, delta_line | acc2], {l, c}}
        end)
      end)

    Enum.reverse(data)
  end

  defp scan_semantic_tokens(line, line_idx) do
    masked = mask_line(line)

    (comment_token(line, line_idx) ++ literal_tokens(line, line_idx) ++ identifier_tokens(masked, line_idx))
    |> Enum.sort()
  end

  # A trailing `#` comment (masked line blanks it, so we read it from the raw line).
  defp comment_token(line, line_idx) do
    masked = mask_line(line)

    case :binary.match(masked, "#") do
      {start, _} -> [{line_idx, start, String.length(line) - start, 6}]
      :nomatch -> []
    end
  end

  # String literals (double- or single-quoted) as type 4.
  defp literal_tokens(line, line_idx) do
    line
    |> String.graphemes()
    |> scan_quoted([], line_idx, 0)
  end

  defp scan_quoted([], acc, _line_idx, _col), do: Enum.reverse(acc)

  defp scan_quoted([g | rest], acc, line_idx, col) do
    cond do
      g in ["\"", "'"] ->
        {len, remaining} = take_until_quote(rest, g, 1)
        scan_quoted(remaining, [{line_idx, col, len, 4} | acc], line_idx, col + len)

      g == "#" ->
        Enum.reverse(acc)

      true ->
        scan_quoted(rest, acc, line_idx, col + 1)
    end
  end

  defp take_until_quote([], _quote, len), do: {len, []}

  defp take_until_quote([g | rest], quote, len) do
    if g == quote, do: {len + 1, rest}, else: take_until_quote(rest, quote, len + 1)
  end

  defp identifier_tokens(masked, line_idx) do
    keyword_set = keyword_set()

    ~r/[A-Za-z_][A-Za-z0-9_]*|\d+(?:\.\d+)?|[+\-*\/=<>!&|^%.,:;()\[\]{}]+/
    |> Regex.scan(masked, return: :index)
    |> Enum.map(fn [{start, len}] ->
      text = binary_part(masked, start, len)
      {line_idx, start, len, classify_token(text, masked, start, len, keyword_set)}
    end)
  end

  defp classify_token(text, masked, start, len, keyword_set) do
    cond do
      text in keyword_set -> 0
      Regex.match?(~r/^\d/, text) -> 5
      Regex.match?(~r/^[A-Z]/, text) -> 3
      Regex.match?(~r/^[a-z_]/, text) -> if(function_position?(masked, start + len), do: 1, else: 2)
      true -> 7
    end
  end

  # A lowercase identifier is a function name when it is immediately followed by
  # `(` (a call or definition) or preceded by the `fn` keyword.
  defp function_position?(masked, after_index) do
    next = String.slice(masked, after_index, 1)
    next == "("
  end

  defp keyword_set do
    ~w(fn mod rec actor fsm sup app interface implementation type typealias primitive let have proof because rewrite simplify induction case pickup else match return throw try catch finally use local when requires where deriving quote unsafe)
    |> MapSet.new()
  end

  # -- Workspace symbols --------------------------------------------------------

  @doc false
  def compute_workspace_symbols(query, documents, encoding \\ :utf16) do
    documents
    |> Enum.flat_map(fn {uri, text} ->
      case parse_to_ast(text) do
        {:ok, ast} ->
          ast
          |> build_symbol_table(text, encoding)
          |> Enum.filter(fn s -> query == "" or String.contains?(s.name, query) end)
          |> Enum.map(fn s ->
            %{
              "name" => s.name,
              "kind" => if(s.kind == :function, do: 12, else: 2),
              "location" => %{
                "uri" => uri,
                "range" =>
                  if(s.span,
                    do: Positions.range(s.span, text, encoding),
                    else: Positions.line_range(s.line, text, encoding)
                  )
              }
            }
          end)

        _ ->
          []
      end
    end)
  end

  # -- Stdin Reader (Content-Length aware) -------------------------------------

  defp lsp_reader_loop(server) do
    case read_lsp_message() do
      {:ok, message} ->
        send(server, {:lsp_message, message})
        lsp_reader_loop(server)

      :eof ->
        :ok

      {:error, _} ->
        :ok
    end
  end

  defp read_lsp_message do
    # Read headers until blank line (\r\n\r\n)
    case read_headers(%{}) do
      {:ok, headers} ->
        content_length = Map.get(headers, "content-length", "0") |> String.to_integer()

        if content_length > 0 do
          case IO.binread(:stdio, content_length) do
            data when is_binary(data) ->
              case safe_json_decode(data) do
                {:ok, msg} -> {:ok, msg}
                :error -> {:error, :json_decode}
              end

            _ ->
              :eof
          end
        else
          {:error, :no_content_length}
        end

      :eof ->
        :eof
    end
  end

  defp read_headers(acc) do
    case IO.binread(:stdio, :line) do
      line when is_binary(line) ->
        trimmed = String.trim_trailing(line, "\r\n") |> String.trim_trailing("\n")

        cond do
          # Blank line = end of headers
          trimmed == "" or trimmed == "\r" ->
            {:ok, acc}

          # Header line: Key: Value
          String.contains?(trimmed, ":") ->
            [key | rest] = String.split(trimmed, ":", parts: 2)
            value = Enum.join(rest, ":") |> String.trim()
            read_headers(Map.put(acc, String.downcase(String.trim(key)), value))

          true ->
            read_headers(acc)
        end

      _ ->
        :eof
    end
  end

  defp safe_json_decode(binary) do
    {:ok, :json.decode(binary)}
  rescue
    _ -> :error
  end
end

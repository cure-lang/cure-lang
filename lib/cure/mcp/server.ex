defmodule Cure.MCP.Server do
  @moduledoc """
  Model Context Protocol (MCP) server for the Cure programming language.

  Provides AI tool integration via JSON-RPC 2.0 over stdio (newline-delimited).

  ## Tools

  - `compile_cure` -- compile Cure source code, return result or errors
  - `parse_cure` -- parse source and return AST summary
  - `type_check_cure` -- type-check source, return errors/warnings
  - `validate_syntax` -- quick syntax validation (lex + parse only)
  - `get_syntax_help` -- get help on a Cure syntax topic
  - `get_examples` -- list or show example programs
  - `get_stdlib_docs` -- get documentation for a stdlib module

  ## Usage

      mix cure.mcp
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Sink

  @tools [
    %{
      "name" => "compile_cure",
      "description" =>
        "Compile Cure source code to BEAM bytecode. Returns the module name on success or error details.",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"source" => %{"type" => "string", "description" => "Cure source code"}},
        "required" => ["source"]
      }
    },
    %{
      "name" => "parse_cure",
      "description" => "Parse Cure source code and return a summary of the AST structure.",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"source" => %{"type" => "string", "description" => "Cure source code"}},
        "required" => ["source"]
      }
    },
    %{
      "name" => "type_check_cure",
      "description" => "Type-check Cure source code. Returns errors and warnings.",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"source" => %{"type" => "string", "description" => "Cure source code"}},
        "required" => ["source"]
      }
    },
    %{
      "name" => "validate_syntax",
      "description" => "Quick syntax validation -- lex and parse only, no type checking.",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"source" => %{"type" => "string", "description" => "Cure source code"}},
        "required" => ["source"]
      }
    },
    %{
      "name" => "get_syntax_help",
      "description" =>
        "Get help on a Cure syntax topic (functions, types, fsm, interfaces, pattern_matching, modules, records).",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"topic" => %{"type" => "string", "description" => "Syntax topic name"}},
        "required" => ["topic"]
      }
    },
    %{
      "name" => "get_stdlib_docs",
      "description" => "Get documentation for a Cure standard library module (Std.Core, Std.List, Std.Math, etc.).",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"module" => %{"type" => "string", "description" => "Module name, e.g. Std.List"}},
        "required" => ["module"]
      }
    }
  ]

  @tool_names Enum.map(@tools, & &1["name"])

  # -- Public API --------------------------------------------------------------

  @doc "Start the MCP server (blocking, reads from stdio)."
  def start do
    Application.ensure_all_started(:cure)
    :io.setopts(:standard_io, binary: true, encoding: :latin1)
    loop()
  end

  @doc """
  Handle a single JSON-RPC request map and return the response map.

  Used for testing without the stdio loop.
  """
  @spec handle_request(map()) :: map() | nil
  def handle_request(%{"method" => method, "id" => id} = req) do
    params = Map.get(req, "params", %{})
    result = dispatch(method, params)
    %{"jsonrpc" => "2.0", "id" => id, "result" => result}
  end

  def handle_request(%{"method" => method} = req) do
    params = Map.get(req, "params", %{})
    _result = dispatch(method, params)
    nil
  end

  # -- Stdio Loop --------------------------------------------------------------

  defp loop do
    case IO.gets("") do
      :eof ->
        :ok

      {:error, _} ->
        :ok

      line when is_binary(line) ->
        with <<_::utf8, _::binary>> = line <- String.trim(line),
             {:ok, request} <- safe_decode(line),
             %{} = response <- handle_request(request),
             do: send_response(response)

        loop()
    end
  end

  defp send_response(response) do
    json = :json.encode(response) |> IO.iodata_to_binary()
    IO.puts(json)
  end

  defp safe_decode(binary) do
    {:ok, :json.decode(binary)}
  rescue
    _ -> :error
  end

  # -- Method Dispatch ---------------------------------------------------------

  defp dispatch("initialize", _params) do
    %{
      "protocolVersion" => "2024-11-05",
      "capabilities" => %{"tools" => %{"listChanged" => false}},
      "serverInfo" => %{"name" => "cure-mcp", "version" => Cure.version()}
    }
  end

  defp dispatch("tools/list", _params) do
    %{"tools" => @tools}
  end

  defp dispatch("tools/call", %{"name" => name, "arguments" => args}) do
    call_tool(name, args)
  end

  defp dispatch("tools/call", %{"name" => name}) do
    call_tool(name, %{})
  end

  defp dispatch(_method, _params), do: %{"error" => "unknown method"}

  # -- Tool Implementations ----------------------------------------------------

  defp call_tool("compile_cure", %{"source" => source}) do
    case Cure.Compiler.compile_and_load(source, file: "mcp.cure", emit_events: false) do
      {:ok, module} ->
        exports =
          module.module_info(:exports)
          |> Enum.reject(fn {n, _} -> n == :module_info end)
          |> Enum.map(fn {n, a} -> "#{n}/#{a}" end)
          |> Enum.join(", ")

        text_result("Compiled successfully: #{module}\nExports: #{exports}")

      {:error, reason} ->
        diagnostic_result(reason, source)
    end
  end

  defp call_tool("parse_cure", %{"source" => source}) do
    with {:ok, tokens} <- Lexer.tokenize(source, file: "mcp.cure", emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, file: "mcp.cure", emit_events: false) do
      text_result(summarize_ast(ast))
    else
      {:error, reason} -> diagnostic_result(reason, source)
    end
  end

  defp call_tool("type_check_cure", %{"source" => source}) do
    with {:ok, tokens} <- Lexer.tokenize(source, file: "mcp.cure", emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, file: "mcp.cure", emit_events: false) do
      case Cure.Elab.Program.check_ast(ast) do
        {:ok, _env} -> text_result("Type check passed: no errors.")
        {:error, errors} -> diagnostic_result(errors, source)
      end
    else
      {:error, reason} -> diagnostic_result(reason, source)
    end
  end

  defp call_tool("validate_syntax", %{"source" => source}) do
    with {:ok, tokens} <- Lexer.tokenize(source, file: "mcp.cure", emit_events: false),
         {:ok, _ast} <- Parser.parse(tokens, file: "mcp.cure", emit_events: false) do
      text_result("Syntax is valid. #{length(tokens)} tokens parsed.")
    else
      {:error, reason} -> diagnostic_result(reason, source)
    end
  end

  defp call_tool("get_syntax_help", %{"topic" => topic}) do
    text_result(syntax_help(topic))
  end

  defp call_tool("get_stdlib_docs", %{"module" => module}) do
    text_result(stdlib_docs(module))
  end

  defp call_tool(name, _args) when name in @tool_names do
    diagnostic = Cure.Diagnostic.Operational.usage("Invalid arguments for MCP tool '#{name}'")
    diagnostic_result(diagnostic, nil)
  end

  defp call_tool(name, _args) do
    diagnostic = Cure.Diagnostic.Operational.usage("Unknown MCP tool '#{name}'")
    diagnostic_result(diagnostic, nil)
  end

  defp text_result(text) when is_binary(text) do
    %{"content" => [%{"type" => "text", "text" => text}], "isError" => false}
  end

  defp diagnostic_result(reason, source) do
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, "mcp.cure", source)

    text =
      Sink.new(format: :plain, color: :never, width: 80, registry: registry)
      |> Sink.render(diagnostic)

    machine =
      Sink.new(format: :json, registry: registry)
      |> Sink.render(diagnostic)

    %{
      "content" => [%{"type" => "text", "text" => text}],
      "isError" => true,
      "structuredContent" => %{"diagnostic" => machine}
    }
  end

  # -- AST Summary -------------------------------------------------------------

  defp summarize_ast({:container, meta, body}) do
    type = Keyword.get(meta, :container_type, :unknown)
    name = Keyword.get(meta, :name, "unnamed")

    items =
      Enum.map(body, fn
        {:function_def, m, _} -> "  fn #{Keyword.get(m, :name)}/#{Keyword.get(m, :arity, 0)}"
        {:container, m, _} -> "  #{Keyword.get(m, :container_type)} #{Keyword.get(m, :name)}"
        _ -> "  (other)"
      end)

    "#{type} #{name}\n#{Enum.join(items, "\n")}"
  end

  defp summarize_ast({:block, _, children}) do
    Enum.map_join(children, "\n\n", &summarize_ast/1)
  end

  defp summarize_ast(_), do: "(expression)"

  # -- Error Formatting --------------------------------------------------------

  # -- Syntax Help -------------------------------------------------------------

  defp syntax_help("functions") do
    """
    === Functions ===
    # Single-line function
    fn add(a: Int, b: Int) -> Int = a + b

    # Multi-line function body
    fn compute(x: Int) -> Int =
      let y = x * 2
      y + 1

    # Multi-clause function
    fn factorial(n: Int) -> Int
      | 0 -> 1
      | n -> n * factorial(n - 1)

    # Function with guard
    fn abs(x: Int) -> Int when x >= 0 = x

    # Private function
    local fn helper(x: Int) -> Int = x * 2

    # External function (FFI)
    @extern(:erlang, :abs, 1)
    fn abs(x: Int) -> Int
    """
  end

  defp syntax_help("types") do
    """
    === Types ===
    # ADT (sum type)
    type Color = Red | Green | Blue
    type Option(T) = Some(T) | None

    # Refinement type
    type NonZero = {x: Int | x != 0}
    type Positive = {x: Int | x > 0}

    # Type alias
    type Name = String
    """
  end

  defp syntax_help("fsm") do
    """
    === Finite State Machines ===

    ## Transition-table mode
    fsm TrafficLight with Int
      initial Red
      Red --Timer--> Green
      Green --Timer--> Yellow
      Yellow --Timer--> Red

    ## Structured mode
    fsm Turnstile
      state Int
      events
        Coin -> :keep_state_and_data

    # Transition rows are checked Cure ADT values and dispatch is an ordinary
    # recursive standard-library function. Callback bodies are reparsed under
    # the lifted module's GenStatem context.
    """
  end

  defp syntax_help(topic) when topic in ["interfaces", "protocols"] do
    """
    === Interfaces ===
    interface Show(t)
      fn show(x: t) -> String

    implementation Show for Int
      fn show(x: Int) -> String = Std.String.from_int(x)

    implementation Show for Bool
      fn show(x: Bool) -> String = pickup
        x -> "true"
        else -> "false"
    """
  end

  defp syntax_help("pattern_matching") do
    """
    === Pattern Matching ===
    # Match expression
    match x
      Ok(v)    -> v
      Error(e) -> default

    # List patterns
    match list
      []       -> "empty"
      [h | t]  -> "has head"

    # Boolean match
    match flag
      true  -> "yes"
      false -> "no"
    """
  end

  defp syntax_help("modules") do
    """
    === Modules ===
    mod MyApp.Math
      fn add(a: Int, b: Int) -> Int = a + b
      fn mul(a: Int, b: Int) -> Int = a * b

    # Modules use indentation (no do...end)
    # All functions are public by default
    # Use 'local fn' for private functions
    """
  end

  defp syntax_help(_topic) do
    "Available topics: functions, types, fsm, interfaces, pattern_matching, modules"
  end

  # -- Stdlib Docs -------------------------------------------------------------

  defp stdlib_docs("Std.Core"), do: read_stdlib_file("core")
  defp stdlib_docs("Std.List"), do: read_stdlib_file("list")
  defp stdlib_docs("Std.Math"), do: read_stdlib_file("math")
  defp stdlib_docs("Std.String"), do: read_stdlib_file("string")
  defp stdlib_docs("Std.Io"), do: read_stdlib_file("io")
  defp stdlib_docs("Std.Pair"), do: read_stdlib_file("pair")
  defp stdlib_docs("Std.Show"), do: read_stdlib_file("show")
  defp stdlib_docs("Std.System"), do: read_stdlib_file("system")
  defp stdlib_docs("Std.Fsm"), do: read_stdlib_file("fsm")

  defp stdlib_docs(_) do
    "Available modules: Std.Core, Std.List, Std.Math, Std.String, Std.Io, Std.Pair, Std.Show, Std.System, Std.Fsm"
  end

  defp read_stdlib_file(name) do
    path = Path.join(["lib", "std", "#{name}.cure"])

    case File.read(path) do
      {:ok, content} -> content
      {:error, _} -> "Source file not found: #{path}"
    end
  end
end

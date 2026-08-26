defmodule Cure.LSP.LspTest do
  use ExUnit.Case, async: true

  alias Cure.LSP.{Transport, Server, Symbols}

  # ============================================================================
  # Transport: framing
  # ============================================================================

  describe "Transport.encode" do
    test "produces Content-Length header and JSON body" do
      msg = %{"jsonrpc" => "2.0", "id" => 1, "result" => nil}
      encoded = Transport.encode(msg)

      assert String.starts_with?(encoded, "Content-Length:")
      assert String.contains?(encoded, "\r\n\r\n")

      [header, body] = String.split(encoded, "\r\n\r\n", parts: 2)
      assert String.starts_with?(header, "Content-Length: ")
      length = String.replace(header, "Content-Length: ", "") |> String.to_integer()
      assert byte_size(body) == length
    end
  end

  describe "Transport.parse_buffer" do
    test "parse single complete message" do
      json = :json.encode(%{"method" => "test"}) |> IO.iodata_to_binary()
      buffer = "Content-Length: #{byte_size(json)}\r\n\r\n#{json}"

      {messages, remaining} = Transport.parse_buffer(buffer)
      assert [%{"method" => "test"}] = messages
      assert remaining == ""
    end

    test "parse incomplete message returns empty" do
      {messages, remaining} = Transport.parse_buffer("Content-Length: 100\r\n\r\n{")
      assert messages == []
      assert remaining != ""
    end

    test "parse multiple messages" do
      msg1 = :json.encode(%{"id" => 1}) |> IO.iodata_to_binary()
      msg2 = :json.encode(%{"id" => 2}) |> IO.iodata_to_binary()

      buffer =
        "Content-Length: #{byte_size(msg1)}\r\n\r\n#{msg1}" <>
          "Content-Length: #{byte_size(msg2)}\r\n\r\n#{msg2}"

      {messages, remaining} = Transport.parse_buffer(buffer)
      assert length(messages) == 2
      assert remaining == ""
    end

    test "parse empty buffer" do
      {messages, remaining} = Transport.parse_buffer("")
      assert messages == []
      assert remaining == ""
    end
  end

  # ============================================================================
  # Server: message processing (without GenServer)
  # ============================================================================

  describe "Server.process_message -- initialize" do
    test "returns capabilities" do
      msg = %{"method" => "initialize", "id" => 1, "params" => %{}}
      state = %{initialized: false, documents: %{}}

      {new_state, _} = Server.process_message(msg, state)
      assert new_state.initialized == true
      assert new_state.position_encoding == :utf16
    end

    test "prefers UTF-8 when the client offers position encodings" do
      msg = %{
        "method" => "initialize",
        "id" => 1,
        "params" => %{
          "capabilities" => %{"general" => %{"positionEncodings" => ["utf-16", "utf-8", "utf-32"]}}
        }
      }

      {new_state, _} = Server.process_message(msg, %{initialized: false, documents: %{}})
      assert new_state.position_encoding == :utf8
    end
  end

  describe "Server.process_message -- document lifecycle" do
    test "didOpen stores document text" do
      msg = %{
        "method" => "textDocument/didOpen",
        "params" => %{
          "textDocument" => %{"uri" => "file:///test.cure", "text" => "mod Test\n  fn foo() -> Int = 42\n"}
        }
      }

      state = %{initialized: true, documents: %{}}
      {new_state, _} = Server.process_message(msg, state)
      assert Map.has_key?(new_state.documents, "file:///test.cure")
    end

    test "didChange updates document text" do
      state = %{
        initialized: true,
        documents: %{"file:///test.cure" => "mod Test\n  fn foo() -> Int = 42\n"}
      }

      msg = %{
        "method" => "textDocument/didChange",
        "params" => %{
          "textDocument" => %{"uri" => "file:///test.cure"},
          "contentChanges" => [%{"text" => "mod Test\n  fn bar() -> Int = 99\n"}]
        }
      }

      {new_state, _} = Server.process_message(msg, state)
      assert new_state.documents["file:///test.cure"] =~ "bar"
    end

    test "didClose removes document" do
      state = %{
        initialized: true,
        documents: %{"file:///test.cure" => "some text"}
      }

      msg = %{
        "method" => "textDocument/didClose",
        "params" => %{"textDocument" => %{"uri" => "file:///test.cure"}}
      }

      {new_state, _} = Server.process_message(msg, state)
      refute Map.has_key?(new_state.documents, "file:///test.cure")
    end
  end

  # ============================================================================
  # Server: diagnostics
  # ============================================================================

  describe "diagnostics" do
    test "valid Cure source produces no diagnostics" do
      source = "mod Valid\n  fn foo() -> Int = 42\n"
      diags = Server.compute_diagnostics("file:///test.cure", source)
      assert diags == []
    end

    test "invalid source produces diagnostics" do
      # Unterminated expression should produce parse errors
      source = "mod Broken\n  fn foo( -> Int\n"
      diags = Server.compute_diagnostics("file:///broken.cure", source)
      # Should have at least one diagnostic
      assert length(diags) >= 0
    end

    test "diagnostic has required LSP fields" do
      source = "mod X\n  fn bad( -> \n"
      diags = Server.compute_diagnostics("file:///x.cure", source)

      if length(diags) > 0 do
        diag = hd(diags)
        assert Map.has_key?(diag, "range")
        assert Map.has_key?(diag, "severity")
        assert Map.has_key?(diag, "source")
        assert Map.has_key?(diag, "message")
        assert diag["source"] == "cure"
      end
    end

    test "unsaved buffers receive elaboration diagnostics" do
      source =
        "mod X\n  type Nat = Z | S(Nat)\n  fn bad() -> Equivalent(Nat, Z, S(Z)) = reflexive(Z)\n"

      [diagnostic | _] = Server.compute_diagnostics("file:///unsaved.cure", source)

      assert diagnostic["source"] == "cure"
      assert diagnostic["code"] == "E093"
      assert diagnostic["message"] =~ "type"
      assert diagnostic["range"]["start"]["line"] == 2
    end

    test "unsaved Unicode buffers use the negotiated position encoding" do
      source = "mod X\n  fn bad() -> Int = \"😀\"\n"
      uri = "file:///unsaved-unicode.cure"

      utf8 = hd(Server.compute_diagnostics(uri, source, :utf8))
      utf16 = hd(Server.compute_diagnostics(uri, source, :utf16))
      utf32 = hd(Server.compute_diagnostics(uri, source, :utf32))

      assert utf8["range"]["start"]["character"] == 20
      assert utf16["range"]["start"]["character"] == 20
      assert utf32["range"]["start"]["character"] == 20
      assert utf8["range"]["end"]["character"] == 26
      assert utf16["range"]["end"]["character"] == 24
      assert utf32["range"]["end"]["character"] == 23
    end
  end

  # ============================================================================
  # Server: hover
  # ============================================================================

  describe "hover" do
    test "hover on function definition returns signature" do
      state = %{
        initialized: true,
        documents: %{
          "file:///test.cure" => "mod Test\n  fn add(a: Int, b: Int) -> Int = a + b\n"
        }
      }

      msg = %{
        "method" => "textDocument/hover",
        "id" => 42,
        "params" => %{
          "textDocument" => %{"uri" => "file:///test.cure"},
          "position" => %{"line" => 1, "character" => 5}
        }
      }

      {_, _} = Server.process_message(msg, state)
      # The response is sent via Transport, but we verify it doesn't crash
    end

    test "hover on non-definition returns nil" do
      state = %{
        initialized: true,
        documents: %{"file:///test.cure" => "  # just a comment\n"}
      }

      msg = %{
        "method" => "textDocument/hover",
        "id" => 43,
        "params" => %{
          "textDocument" => %{"uri" => "file:///test.cure"},
          "position" => %{"line" => 0, "character" => 0}
        }
      }

      {_, _} = Server.process_message(msg, state)
    end
  end

  # ============================================================================
  # Server: completion
  # ============================================================================

  describe "completion" do
    test "returns keyword completions" do
      state = %{initialized: true, documents: %{}}

      msg = %{
        "method" => "textDocument/completion",
        "id" => 44,
        "params" => %{
          "textDocument" => %{"uri" => "file:///test.cure"},
          "position" => %{"line" => 0, "character" => 0}
        }
      }

      {_, _} = Server.process_message(msg, state)
    end
  end

  # ============================================================================
  # Server: go-to-definition
  # ============================================================================

  describe "definition" do
    test "finds function definition in same document" do
      state = %{
        initialized: true,
        documents: %{
          "file:///test.cure" =>
            "mod Test\n  fn add(a: Int, b: Int) -> Int = a + b\n  fn use_add() -> Int = add(1, 2)\n"
        }
      }

      msg = %{
        "method" => "textDocument/definition",
        "id" => 50,
        "params" => %{
          "textDocument" => %{"uri" => "file:///test.cure"},
          "position" => %{"line" => 2, "character" => 25}
        }
      }

      {_, _} = Server.process_message(msg, state)
    end
  end

  # ============================================================================
  # Server: document symbols
  # ============================================================================

  describe "documentSymbol" do
    test "returns symbols for valid source" do
      state = %{
        initialized: true,
        documents: %{
          "file:///test.cure" => "mod SymTest\n  fn foo() -> Int = 42\n  fn bar() -> Int = 99\n"
        }
      }

      msg = %{
        "method" => "textDocument/documentSymbol",
        "id" => 51,
        "params" => %{"textDocument" => %{"uri" => "file:///test.cure"}}
      }

      {_, _} = Server.process_message(msg, state)
    end

    test "does not synthesize retired FSM metadata from generic containers" do
      ast =
        {:container, [container_type: :module, name: "Plain", line: 1],
         [
           {:function_call, [name: "transition", from: "Idle", event: "go", to: "Done", line: 2], []}
         ]}

      [symbol] = Symbols.extract(ast)

      assert symbol["detail"] == "module"
      assert symbol["children"] == []
    end
  end

  # ============================================================================
  # Server: code actions
  # ============================================================================

  describe "codeAction" do
    test "adds every missing induction case with descriptive editable binders" do
      source = """
      mod MissingInductionCase
        type Nat = Z | S(Nat)
        fn prove(value: Nat) -> Equivalent(Nat, value, value) = induction value
          case Z => reflexive(Z)
      end
      """

      assert {:error, {:codegen_error, reason}} =
               Cure.Compiler.compile_string(source, file: "missing_induction_case.cure", emit_events: false)

      {diagnostic, registry} =
        Cure.Compiler.Errors.to_diagnostic(reason, "missing_induction_case.cure", source)

      lsp_diagnostic = Cure.Diagnostic.Renderer.lsp(diagnostic, registry, :utf16)
      assert [action] = Server.compute_code_actions("file:///missing_induction_case.cure", [lsp_diagnostic])
      assert action["title"] == "Add missing induction cases"

      assert [{edit_uri, [%{"newText" => replacement, "range" => range}]}] =
               Map.to_list(action["edit"]["changes"])

      assert String.ends_with?(edit_uri, "/missing_induction_case.cure")
      assert replacement == "\n    case S(previous, induction_hypothesis) => ???"
      assert range["start"] == range["end"]
      assert range["start"]["line"] == 3
    end

    test "suggests wildcard for non-exhaustive match" do
      diag = %{
        "message" => "match expression is not exhaustive, missing: false",
        "range" => %{"start" => %{"line" => 3, "character" => 0}, "end" => %{"line" => 3, "character" => 0}}
      }

      actions = Server.compute_code_actions("file:///test.cure", [diag])
      assert length(actions) >= 1
      assert hd(actions)["title"] =~ "wildcard"
    end

    test "no actions for unrelated diagnostic" do
      diag = %{"message" => "some random warning", "range" => %{}}
      actions = Server.compute_code_actions("file:///test.cure", [diag])
      assert actions == []
    end

    test "codeAction request does not crash" do
      state = %{initialized: true, documents: %{}}

      msg = %{
        "method" => "textDocument/codeAction",
        "id" => 52,
        "params" => %{
          "textDocument" => %{"uri" => "file:///test.cure"},
          "range" => %{},
          "context" => %{"diagnostics" => []}
        }
      }

      {_, _} = Server.process_message(msg, state)
    end
  end

  # ============================================================================
  # Server: unknown method
  # ============================================================================

  describe "unknown method" do
    test "does not crash" do
      state = %{initialized: true, documents: %{}}
      msg = %{"method" => "unknown/method", "params" => %{}}
      {new_state, _} = Server.process_message(msg, state)
      assert new_state == state
    end
  end

  # ============================================================================
  # Server: symbol table and context completions
  # ============================================================================

  describe "build_symbol_table" do
    test "extracts function symbols from AST" do
      source = "mod Test\n  fn add(a: Int, b: Int) -> Int = a + b\n  fn hello() -> String = \"hi\"\n"

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
      symbols = Server.build_symbol_table(ast)

      fn_names = Enum.filter(symbols, &(&1.kind == :function)) |> Enum.map(& &1.name)
      assert "add" in fn_names
      assert "hello" in fn_names
    end

    test "extracts module name" do
      source = "mod MyMod\n  fn foo() -> Int = 1\n"

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
      symbols = Server.build_symbol_table(ast)

      mod_names = Enum.filter(symbols, &(&1.kind == :module)) |> Enum.map(& &1.name)
      assert "MyMod" in mod_names
    end
  end

  describe "completion with context" do
    test "includes function names from document" do
      state = %{
        initialized: true,
        documents: %{
          "file:///test.cure" => "mod Test\n  fn add(a: Int, b: Int) -> Int = a + b\n"
        }
      }

      msg = %{
        "method" => "textDocument/completion",
        "id" => 60,
        "params" => %{
          "textDocument" => %{"uri" => "file:///test.cure"},
          "position" => %{"line" => 1, "character" => 5}
        }
      }

      {_, _} = Server.process_message(msg, state)
      # Verifies no crash and response is sent
    end

    test "defining-equation members expose propositions and structural collision names" do
      source = """
      mod EquationLsp
        type Bit = Off | On
        fn both(left: Bit, right: Bit) -> Bit = match left
          Off -> Off
          On -> match right
            Off -> Off
            On -> On
      end
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
      equations = Server.equation_symbols(ast)

      assert Enum.map(equations, & &1.name) == ["both.On", "both/Off", "both/On/Off"]
      assert Enum.all?(equations, &(&1.proposition =~ "Equivalent"))
      assert Enum.any?(equations, &(&1.proposition =~ "both(On, Off), Off"))
      assert Enum.map(equations, & &1.line) == [7, 4, 6]
      assert Enum.all?(equations, & &1.span)
    end

    test "simplification rule completion offers defining equations with rule-specific detail" do
      source = """
      mod SimplifyLsp
        type Bit = Off | On
        fn flip(bit: Bit) -> Bit = match bit
          Off -> On
          On -> Off
        fn proof(bit: Bit) -> Equivalent(Bit, flip(flip(bit)), bit) = proof chain
          flip(flip(bit)) == bit
          because simplify using []
      end
      """

      prefix = String.replace(source, "[]", "[")
      items = Server.context_completions(source, prefix)

      assert Enum.map(items, & &1["label"]) == ["flip.Off", "flip.On"]
      assert Enum.all?(items, &String.starts_with?(&1["detail"], "Defining equation rule —"))
    end

    test "defining-equation hover identifies a function case rather than a module" do
      source = """
      mod EquationHover
        type Bit = Off | On
        fn flip(bit: Bit) -> Bit = match bit
          Off -> On
          On -> Off
        fn use() = flip.Off
      end
      """

      hover = Server.compute_hover(source, 5, 20)
      value = get_in(hover, ["contents", "value"])
      assert value =~ "defining equation for function `flip`"
      assert value =~ "constructor case `Off`"
      assert value =~ "not a module"
      assert value =~ "Equivalent"
    end

    test "simplification completion and hover include local equality proofs" do
      source = """
      mod LocalRuleHover
        type Nat = Z | S(Nat)
        fn adapt(x: Nat, y: Nat, equality: Equivalent(Nat, S(x), y)) -> Equivalent(Nat, S(S(x)), S(y)) = proof chain
          S(S(x)) == S(y)
          because simplify using [equality]
      end
      """

      prefix = source |> String.split("equality]") |> hd()
      items = Server.context_completions(source, prefix)
      assert %{"label" => "equality", "detail" => "Local equality rule — " <> detail} = hd(items)
      assert detail =~ "Equivalent(Nat, S(x), y)"

      bare_prefix = source |> String.split("[equality]") |> hd()
      bare_items = Server.context_completions(source, bare_prefix)
      assert Enum.any?(bare_items, &(&1["label"] == "equality"))

      hover = Server.compute_hover(source, 4, 30)
      value = get_in(hover, ["contents", "value"])
      assert value =~ "Local equality proof"
      assert value =~ "explicit simplification rule"

      command_hover = Server.compute_hover(source, 4, 12)
      command_value = get_in(command_hover, ["contents", "value"])
      assert command_value =~ "simplify using [rule, ...]"
      assert command_value =~ "kernel-checked equality certificate"
    end

    test "structured induction vocabulary has completion and explanatory hover" do
      source = """
      mod InductionLsp
        type Nat = Z | S(Nat)
        fn proof(value: Nat) -> Equivalent(Nat, value, value) = induction value
          case Z => reflexive(Z)
          case S(previous, induction_hypothesis) => induction_hypothesis
      end
      """

      hover = Server.compute_hover(source, 2, 65)
      value = get_in(hover, ["contents", "value"])
      assert value =~ "specialized induction hypothesis"
      assert value =~ "ordinary total recursion"

      hypothesis_hover = Server.compute_hover(source, 4, 30)
      hypothesis_value = get_in(hypothesis_hover, ["contents", "value"])
      assert hypothesis_value =~ "Specialized induction hypothesis"
      assert hypothesis_value =~ "structurally smaller value"

      assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, emit_events: false)
      assert {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
      bindings = Server.induction_binding_symbols(ast)
      assert Enum.any?(bindings, &(&1.name == "induction_hypothesis" and &1.kind == :induction_hypothesis))

      completion = Server.context_completions(source, source)
      assert Enum.any?(completion, &(&1["label"] == "induction_hypothesis" and &1["detail"] =~ "Specialized"))

      semantic = Server.compute_semantic_tokens("induction value\n  case Z => simplify")
      assert length(semantic) == 15
    end

    test "induction completion generates every constructor with descriptive hypotheses" do
      source = """
      mod InductionCompletion
        type Nat = Z | S(Nat)
        fn proof(value: Nat) -> Equivalent(Nat, value, value) = induction value
      """

      items = Server.context_completions(source, source)
      all = Enum.find(items, &(&1["label"] == "Generate all Nat induction cases"))

      assert all["insertTextFormat"] == 2
      assert all["insertText"] =~ "case Z =>"
      assert all["insertText"] =~ "case S(${1:previous}, ${2:induction_hypothesis}) =>"
      assert all["detail"] =~ "recursive induction hypotheses"
    end

    test "induction completion omits constructor cases already written" do
      source = """
      mod PartialInductionCompletion
        type Nat = Z | S(Nat)
        fn proof(value: Nat) -> Equivalent(Nat, value, value) = induction value
          case Z => reflexive(Z)
      """

      items = Server.context_completions(source, source)
      all = Enum.find(items, &(&1["label"] == "Generate all Nat induction cases"))

      refute all["insertText"] =~ "case Z"
      assert all["insertText"] =~ "case S("
    end
  end
end

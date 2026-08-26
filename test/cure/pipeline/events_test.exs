defmodule Cure.Pipeline.EventsTest do
  use ExUnit.Case, async: false

  alias Cure.Pipeline.Events

  describe "subscribe/1 and emit/4" do
    test "subscriber receives events from the subscribed stage" do
      Events.subscribe(:lexer)
      meta = Events.meta("test.cure", 1)
      Events.emit(:lexer, :token_produced, :some_token, meta)

      assert_receive {Events, :lexer, :token_produced, :some_token, ^meta}
    end

    test "subscriber does not receive events from other stages" do
      Events.subscribe(:parser)
      meta = Events.meta("test.cure", 1)
      Events.emit(:lexer, :token_produced, :some_token, meta)

      refute_receive {Events, :lexer, _, _, _}, 50
    end

    test "subscriber with :all filter receives all event types for that stage" do
      Events.subscribe(:codegen)
      meta = Events.meta("test.cure", 1)

      Events.emit(:codegen, :form_generated, :form1, meta)
      Events.emit(:codegen, :error, :bad, meta)

      assert_receive {Events, :codegen, :form_generated, :form1, _}
      assert_receive {Events, :codegen, :error, :bad, _}
    end
  end

  describe "subscribe/2 with event_type filter" do
    test "subscriber only receives matching event types" do
      Events.subscribe(:lexer, :error)
      meta = Events.meta("test.cure", 1)

      Events.emit(:lexer, :token_produced, :tok, meta)
      Events.emit(:lexer, :error, :bad, meta)

      refute_receive {Events, :lexer, :token_produced, _, _}, 50
      assert_receive {Events, :lexer, :error, :bad, _}
    end
  end

  describe "emit_events option gates per-token lexer events" do
    test "tokenizing with emit_events: false delivers no token_produced events" do
      Events.subscribe(:lexer)
      {:ok, _toks} = Cure.Compiler.Lexer.tokenize("fn add(x, y) -> x + y", emit_events: false)
      refute_receive {Events, :lexer, :token_produced, _, _}, 100
    end

    test "tokenizing with emit_events: true still delivers token_produced events" do
      Events.subscribe(:lexer)
      {:ok, _toks} = Cure.Compiler.Lexer.tokenize("fn add", emit_events: true)
      assert_receive {Events, :lexer, :token_produced, _, _}, 200
    end
  end

  describe "meta/2" do
    test "builds metadata map with file, line, and timestamp" do
      meta = Events.meta("hello.cure", 42)

      assert meta.file == "hello.cure"
      assert meta.line == 42
      assert is_integer(meta.timestamp)
    end
  end
end

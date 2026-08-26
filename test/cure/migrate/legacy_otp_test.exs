defmodule Cure.Migrate.LegacyOtpTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.Migrate.LegacyOtp

  test "normalises the old inline application header" do
    source = "app Cure.Demo root Cure.Root\n"

    assert {migrated, true} = LegacyOtp.normalize(source)
    assert migrated == "app Cure.Demo\n  root Cure.Root\n"
    assert reparses?(migrated)
  end

  test "normalises inline supervisor child specs" do
    source = "sup Cure.Demo children [child_spec Cure.Worker :worker, child_spec Cure.Echo :echo]\n"

    assert {migrated, true} = LegacyOtp.normalize(source)
    assert migrated =~ "sup Cure.Demo\n  children\n    actor Cure.Worker as worker\n    actor Cure.Echo as echo\n"
    assert reparses?(migrated)
  end

  test "normalises inline actor lifecycle fields and preserves its callback" do
    source = """
    actor Cure.Worker state Int initial 0 messages Atom handle_cast
      pickup
        message == :inc -> %[:noreply, state + 1]
        else -> %[:noreply, state]
    """

    assert {migrated, true} = LegacyOtp.normalize(source)
    assert migrated =~ "actor Cure.Worker\n  state Int\n  initial 0\n  messages Atom\n  handle_cast\n"
    assert migrated =~ "    pickup\n      message == :inc"
    assert reparses?(migrated)
    assert prints_and_reparses?(migrated)
  end

  test "normalises callback-only FSM showcases" do
    source = """
    # legacy showcase
    fsm Cure.Pipeline with 0
      fn initial_state() -> Atom = :idle
    """

    assert {migrated, true} = LegacyOtp.normalize(source)
    assert migrated =~ "fsm Cure.Pipeline\n  state Atom\n  initial :idle\n  event_type Atom\n  events\n"
    assert reparses?(migrated)
  end

  defp reparses?(source) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, _ast} <- Parser.parse(tokens, emit_events: false) do
      true
    else
      _ -> false
    end
  end

  defp prints_and_reparses?(source) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false),
         printed <- Printer.quoted_to_string(ast),
         {:ok, printed_tokens} <- Lexer.tokenize(printed, emit_events: false),
         {:ok, _printed_ast} <- Parser.parse(printed_tokens, emit_events: false) do
      true
    else
      _ -> false
    end
  end
end

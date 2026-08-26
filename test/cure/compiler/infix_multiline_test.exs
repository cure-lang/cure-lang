defmodule Cure.Compiler.InfixMultilineTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse(source) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false) do
      Parser.parse(tokens, emit_events: false, prelude_macros: false)
    end
  end

  test "builtin infix operators accept an indented right operand on the next line" do
    for source <- [
          "true or\n  false",
          "true and\n  false",
          "1 +\n  2",
          "1 ==\n  2",
          "1 ..\n  2",
          "value.\n  field"
        ] do
      assert {:ok, _ast} = parse(source), "failed to parse:\n#{source}"
    end
  end

  test "a multiline expression may chain operators inside one continuation layout" do
    assert {:ok, _ast} =
             parse("""
             true or
               false or
               true
             """)
  end

  test "user-defined infix operators receive the same newline continuation" do
    assert {:ok, _ast} =
             parse("""
             precedencegroup Join
               associativity: left
             infix `<?>` : Join
             fn combine(left: Int, right: Int) -> Int = left
             fn example() -> Int = 1 <?>
               2
             """)
  end

  # `<-|` keeps a dedicated lexer token — it gives both the ASCII and envelope
  # spellings good spans — but it is an ordinary library-defined operator: the
  # `Melquiades` precedence group is ambient (`lib/std/operators.cure`) while the
  # fixity `infix `<-|` : Melquiades` lives in `Std.Otp`. So only the fixity has
  # to be written out here; redeclaring the group is a conflict, not a setup step.
  test "the melquiades send takes the continuation from its declaration" do
    source = """
    infix `<-|` : Melquiades
    fn send(mailbox: Int, message: Int) -> Int = mailbox
    """

    assert {:ok, _ast} = parse(source <> "fn trailing() -> Int = 1 <-|\n  2\n")
    assert {:ok, _ast} = parse(source <> "fn leading() -> Int = 1\n  <-| 2\n")
  end

  test "operators beginning a continuation line are also declaration-driven" do
    assert {:ok, _ast} =
             parse("""
             precedencegroup Join
               associativity: left
             infix `<?>` : Join
             fn combine(left: Int, right: Int) -> Int = left
             fn example() -> Int = 1
               <?> 2
             """)
  end
end

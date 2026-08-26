defmodule Cure.Elab.EnvOwnerTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  test "the elaborated environment records the source module owner" do
    source = "mod Client\n  fn answer() -> Int = 7\nend\n"
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env} = Program.check_ast(ast)
    assert env.module_owner == "Client"
  end

  test "an unwrapped source gets the stable Main owner" do
    source = "fn answer() -> Int = 7\n"
    assert {:ok, env} = Program.elaborate(source)
    assert env.module_owner == "Main"
  end
end

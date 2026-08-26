defmodule Cure.Migrate.ProtoToInterfaceTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate

  defp migrate(src) do
    {:ok, toks, trivia} = Lexer.tokenize(src, trivia: true)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    {:ok, out, warns} = Migrate.run_to_fixpoint(Trivia.attach(ast, trivia))
    {Printer.quoted_to_string(out), warns}
  end

  defp reparses?(src) do
    match?({:ok, _}, with({:ok, t} <- Lexer.tokenize(src, emit_events: false), do: Parser.parse(t, emit_events: false)))
  end

  test "proto/impl are rewritten to interface/implementation and the output reparses" do
    src = "mod M\n  proto P(t)\n    fn e(a: t) -> Bool\n  impl P for Int\n    fn e(a: Int) -> Bool = true\n"
    {out, warns} = migrate(src)
    assert out =~ ~r/\binterface\s+P\(t\)/
    assert out =~ ~r/\bimplementation\s+P\s+for\s+Int/
    refute out =~ ~r/\bproto\s+P/
    refute out =~ ~r/\bimpl\s+P\s+for/
    proto_warnings = Enum.filter(warns, &(&1.rule == :W_proto_to_interface))

    assert Enum.map(proto_warnings, fn warning ->
             {warning.span.start_line, warning.span.start_column, warning.span.end_column}
           end) == [{2, 3, 8}, {4, 3, 7}]

    assert reparses?(out)
  end
end

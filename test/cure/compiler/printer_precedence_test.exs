defmodule Cure.Compiler.PrinterPrecedenceTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.Compiler.Parser.BuiltinFixity

  # The printer used to drop grouping parentheses unconditionally, so a
  # sub-expression whose precedence is LOWER than its surrounding operator was
  # reprinted without the parens the parser needs to recover it — silently
  # changing the program's meaning on every `cure fmt` / `cure migrate`. E.g.
  # `(x + 1) * 2` was reprinted as `x + 1 * 2`, which reparses as `x + (1 * 2)`.
  #
  # These tests pin the fix: parse -> print -> parse must recover a structurally
  # identical AST (parentheses may be added/removed, but never in a way that
  # changes the parse). We compare meta-stripped trees so that only shape and
  # operators — not line/col — are asserted.

  defp strip(node) do
    case node do
      {tag, _meta, kids} when is_list(kids) -> {tag, Enum.map(kids, &strip/1)}
      {tag, _meta, kid} -> {tag, strip(kid)}
      list when is_list(list) -> Enum.map(list, &strip/1)
      other -> other
    end
  end

  defp parse!(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    ast
  end

  # Each entry is the RHS expression of a `fn` body.
  @exprs [
    "(x + 1) * 2",
    "x * (x + 1)",
    "1 - (2 - x)",
    "(x - 1) - 2",
    "(if x > 0 then 1 else 2) + 1",
    "1 + (if x > 0 then 1 else 2)",
    "a or (b and c)",
    "(a or b) and c",
    "-(x + 1)",
    "not (a and b)",
    "(a <> b) <> c",
    "a <> (b <> c)",
    # Non-`:binary_op` infix nodes the parser lowers specially — range (`..`),
    # send (`<-|`), and dot access (`.`) — must also parenthesise their operands
    # (as parents) and be parenthesised (as operands) by precedence.
    "(1..2) + 3",
    "3 + (1..2)",
    "(a == b)..c",
    "(pid <-| msg) + 1",
    "(a + b).x",
    "a.b + c",
    "Std.Map.put(k, v, m)",
    # `|>` lowers to a pipe-tagged :function_call (not :binary_op) and binds
    # loosest (level 10); the right-extending prefix keywords (`throw`, `yield`,
    # …) grab everything to their right. Both must be parenthesised as operands.
    "(a |> f) + b",
    "b + (a |> f)",
    "(a |> f) < b",
    "(a |> f).x",
    "a |> f |> g",
    "(a <-| b) |> f",
    "(throw x) + 1",
    "(yield x) + 1"
  ]

  # A user-declared operator has no entry in the printer's hardcoded precedence
  # table, so the printer used to treat it as :unknown and defensively wrap every
  # operand of (and every operand that was) such an operator in parentheses. Given
  # the session `FixityTable` the parser assembled, the printer must instead
  # parenthesise a custom operator by its real precedence — no redundant parens.
  test "a custom operator reprints by its declared precedence, not over-parenthesised" do
    src = """
    mod M
      use Std.Operators
      precedencegroup Weighted
        associativity: left
        higher_than: Additive
      infix `<+>` : Weighted
      fn `<+>`(a: Int, b: Int) -> Int = a
      fn f(x: Int) -> Int = x + x <+> x
    end
    """

    ast = parse!(src)
    table = BuiltinFixity.extend(BuiltinFixity.table(), ast)
    out = Printer.quoted_to_string(ast, fixity: table)

    # `<+>` binds tighter than `+`, so `x + x <+> x` needs no parentheses.
    assert out =~ "x + x <+> x", "expected minimal parens, got:\n#{out}"
    refute out =~ "(x <+> x)", "custom operator was over-parenthesised:\n#{out}"
    # And the reprint must still recover the same parse.
    assert strip(ast) == strip(parse!(out))
  end

  for expr <- @exprs do
    @expr expr
    test "precedence-preserving reprint: #{expr}" do
      src =
        "mod M\n  use Std.Otp\n  fn f(x: Int, a: Int, b: Int, c: Int, pid: Int, msg: Int, k: Int, v: Int, m: Int) -> Int = #{@expr}\n"

      ast = parse!(src)
      out = Printer.quoted_to_string(ast)
      reparsed = parse!(out)

      assert strip(ast) == strip(reparsed),
             "reprint changed the parse.\n  in:  #{@expr}\n  out: #{out}"
    end
  end
end

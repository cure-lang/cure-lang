defmodule Cure.Compiler.DotPatternParseTest do
  @moduledoc """
  Surface syntax for forced (dot) patterns (forced-patterns plan, Task 5).

  A leading `.` in expression-prefix position produces a
  `{:forced_pattern, meta, expr}` AST node — the pattern-position surface for a
  forced equation (`.x`, `.(S(k))`). Parsing succeeds in ANY position by design;
  using a dot pattern OUTSIDE a pattern is rejected at elaboration time with
  `{:forced_pattern_not_in_pattern, _}`.

  Infix `.` (module paths like `Std.String`) is a different grammar position and
  is unaffected (non-regression case (d)).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # (a) A bare identifier dot pattern `.a` in a constructor-argument position
  #     parses to `{:forced_pattern, _, {:variable, _, "a"}}` — the confirmed
  #     surface shape for a bare identifier (constructor_pattern/1 matches
  #     {:variable, _m, _v}).
  test "(a) `same(.a)` parses the ctor arg as a bare-identifier forced pattern" do
    ast = parse!("match x { same(.a) -> 1 }")
    assert {:pattern_match, _, [_scrutinee, arm]} = ast
    assert {:match_arm, ameta, _body} = arm
    assert {:function_call, _cmeta, [arg]} = Keyword.get(ameta, :pattern)
    assert {:forced_pattern, _, [{:variable, _, "a"}]} = arg
  end

  # (b) A parenthesised compound dot pattern `.(S(k))` parses the inner
  #     expression as a constructor application.
  test "(b) `.(S(k))` parses the parenthesised compound forced pattern" do
    ast = parse!("match x { same(.(S(k))) -> 1 }")
    assert {:pattern_match, _, [_scrutinee, arm]} = ast
    assert {:match_arm, ameta, _body} = arm
    assert {:function_call, _cmeta, [arg]} = Keyword.get(ameta, :pattern)
    assert {:forced_pattern, _, [inner]} = arg
    assert {:function_call, _, [{:variable, _, "k"}]} = inner
  end

  # (c) NEGATIVE: a dot pattern used as an ordinary expression (a function body /
  #     let RHS, not a pattern) is rejected at ELABORATION time. Parsing `.x`
  #     itself succeeds by design, so this drives the fixture through the full
  #     pipeline via Cure.Elab.Program.elaborate/1.
  test "(c) a forced pattern in ordinary expression position is rejected" do
    src = """
    type Nat = Z | S(Nat)
    fn f() -> Nat = .x
    """

    assert {:error, {:source_context, {:forced_pattern_not_in_pattern, _meta}, _}} = Program.elaborate(src)
  end

  # (d) NON-REGRESSION: infix `.` (module paths) is unaffected. A bare module
  #     path `Std.String` still builds the `{:attribute_access, …}` chain, and a
  #     qualified call `Std.String.from_int(5)` still parses to its existing
  #     dotted-name `:function_call` form — neither yields a forced pattern.
  test "(d) infix `.` module paths still parse to attribute_access / dotted call" do
    ast = parse!("Std.String")
    assert {:attribute_access, meta, [{:variable, _, "Std"}]} = ast
    assert Keyword.get(meta, :attribute) == "String"
    refute inspect(ast, limit: :infinity) =~ ":forced_pattern"

    call = parse!("Std.String.from_int(5)")
    assert {:function_call, cmeta, [_arg]} = call
    assert Keyword.get(cmeta, :name) == "Std.String.from_int"
    refute inspect(call, limit: :infinity) =~ ":forced_pattern"
  end
end

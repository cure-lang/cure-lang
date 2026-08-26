defmodule Cure.Std.OperatorBootstrapTest do
  @moduledoc """
  Phase-3 bootstrap gate: `operators.cure` must parse WITHOUT relying, in a body,
  on an infix/prefix operator — it is the source the built-in operator table is
  bootstrapped from, so it is parsed before that table exists.

  Fixity comes from `operators.cure` alone: it declares every precedence group
  and operator fixity. The interface modules (`equatable`/`comparable`/
  `arithmetic`/`bool`) supply the backing *methods*, and parsing needs methods
  from no one — by the time they are parsed the table is already baked. So they
  are under no bootstrap obligation and may use the operators they define as
  ordinary infix expressions, exactly as a Swift module may use an operator it
  declares. `Std.Comparable.min` is written `x <= y`, not `` `<=`(x, y) ``.

  ## What "against an empty fixity table" means here, honestly

  `Cure.Compiler.Parser.parse/2` always seeds its Pratt binding-power table from
  the memoized built-in table (`BuiltinFixity.table()`); there is no `opts`
  switch to hand it a custom/empty table. The compiler DOES have one genuine
  empty-table seam — the `:cure_building_fixity_table` process flag, which makes
  `session_builtin_fixity_table/0` return `FixityTable.new()` — but it is only
  clean for `operators.cure`, whose body is entirely inert declarations. For the
  interface modules that flag is *too* aggressive: it also strips the
  non-overloadable **builtin** operators `operators.cure` declares (notably the
  `.` module/field projection those modules use in `Std.Builtin.int_eq(...)`),
  which none of these modules *defines*. Under it, `Std.Builtin.int_eq` silently
  mis-parses (`Std` as a variable, `.Builtin`/`.int_eq(...)` as stray forced
  patterns) yet still returns `{:ok, _}` — a false pass. So an `{:ok, _}`
  assertion under that flag would not actually verify anything for four of the
  five modules.

  In real compilation the ordering is: `operators.cure` is harvested FIRST
  against an empty table — at Elixir compile time, when `BuiltinFixity` bakes its
  `@builtin_fixity_table` constant via `Parser.harvest/4` seeded with an explicit
  empty base — to build the table; the four interface modules are then parsed
  against the FULL built-in table. (The bake seeds the empty base directly rather
  than through the `:cure_building_fixity_table` flag, but the obligation is the
  same, and this test injects that empty base via the flag.) So the only module
  with a hard empty-table obligation is `operators.cure`, and both tests below
  scope to it: it must parse with no table, and its AST must contain ZERO
  infix/prefix operator nodes (`:binary_op`/`:unary_op`), since an operator
  expression there would need the very table it is being read to produce.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}

  # Only `operators.cure` is parsed before the fixity table exists, so it is the
  # only module that cannot use an operator expression. The interface modules
  # that supply the backing methods are parsed against the full table.
  @operator_defining_modules ~w(operators.cure)

  defp std_source(file), do: File.read!(Path.join([File.cwd!(), "lib", "std", file]))

  defp parse_default(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    Parser.parse(tokens, file: file, emit_events: false)
  end

  # Count `:binary_op` / `:unary_op` nodes anywhere in a MetaAST tree. A
  # hand-rolled walk (MetaAST nodes are not standard Elixir AST).
  defp operator_nodes(node) when is_tuple(node) do
    here =
      case node do
        {tag, _meta, _} when tag in [:binary_op, :unary_op] -> [node]
        _ -> []
      end

    here ++ (node |> Tuple.to_list() |> Enum.flat_map(&operator_nodes/1))
  end

  defp operator_nodes(list) when is_list(list), do: Enum.flat_map(list, &operator_nodes/1)
  defp operator_nodes(_other), do: []

  test "operators.cure parses against a genuinely empty fixity table" do
    # The load-bearing bootstrap obligation: `operators.cure` is harvested to
    # BUILD the built-in table (at `BuiltinFixity`'s compile time), so it must
    # parse with NO table present. It is all inert precedence/fixity
    # declarations, so an empty table parses it faithfully (no false-pass risk).
    prev = Process.put(:cure_building_fixity_table, true)

    try do
      assert {:ok, _ast} = parse_default(std_source("operators.cure"), "operators.cure"),
             "operators.cure must parse against an empty fixity table — it is the source " <>
               "the built-in table is bootstrapped from"
    after
      case prev do
        nil -> Process.delete(:cure_building_fixity_table)
        _ -> Process.put(:cure_building_fixity_table, prev)
      end
    end
  end

  test "operators.cure uses no infix/prefix operator in any body" do
    for f <- @operator_defining_modules do
      assert {:ok, ast} = parse_default(std_source(f), f), "#{f} must parse"

      nodes = operator_nodes(ast)

      assert nodes == [],
             "#{f} uses an infix/prefix operator in a body (found #{length(nodes)} operator " <>
               "node(s): #{inspect(nodes, limit: 5)}). It is parsed to BUILD the fixity table, " <>
               "so it must call operators only in backtick prefix-call form (`` `==`(a, b) ``), " <>
               "via `Std.Builtin.<op>`/`Std.Bool.<op>`, or via `match`/`pickup` — never as an " <>
               "operator expression that would need the very fixity table it defines."
    end
  end

  # The converse of the gate above: modules that merely supply an operator's
  # backing methods are parsed against the full table, so an infix use in one of
  # their bodies is legal. `Std.Comparable` defines `<=` and `min` uses it.
  test "a module may use infix an operator whose method it defines" do
    assert {:ok, ast} = parse_default(std_source("comparable.cure"), "comparable.cure")

    assert operator_nodes(ast) != [],
           "comparable.cure should parse its infix operator uses as operator nodes"
  end
end

defmodule Cure.QuoteTest do
  use ExUnit.Case, async: true

  # Helper: quote and assert success
  defp quote!(source) do
    {:ok, ast} = Cure.quote(source)
    ast
  end

  # Helper: round-trip through quote -> print -> re-quote, assert AST equality.
  #
  # The comparison is performed modulo position metadata (`line`, `col`,
  # `column`). Canonical block forms for `match` and `pickup` (per
  # `docs/MATCH.md` §9 and `docs/PICKUP.md` §8) introduce newlines that
  # shift positions even when the structural AST is identical, so a
  # strict `==` would mistake those layout-only differences for round-
  # trip failures.
  defp assert_round_trip(source) do
    {:ok, ast} = Cure.quote(source)
    printed = Cure.quoted_to_string(ast)
    {:ok, re_ast} = Cure.quote(printed)

    assert strip_positions(ast) == strip_positions(re_ast),
           "Round-trip failed for: #{source}\nPrinted: #{printed}"

    printed
  end

  # Strip source-location and diagnostic-provenance keys from every meta keyword
  # list in the tree. They do not affect quoted syntax semantics or printing.
  defp strip_positions({type, meta, children}) when is_list(meta) do
    {type, drop_position_keys(meta), strip_positions(children)}
  end

  defp strip_positions(list) when is_list(list), do: Enum.map(list, &strip_positions/1)

  defp strip_positions(tuple) when is_tuple(tuple) do
    tuple |> Tuple.to_list() |> Enum.map(&strip_positions/1) |> List.to_tuple()
  end

  defp strip_positions(other), do: other

  defp drop_position_keys(meta) do
    meta
    |> Keyword.delete(:line)
    |> Keyword.delete(:col)
    |> Keyword.delete(:column)
    |> Keyword.delete(:span)
    |> Keyword.delete(:construct_span)
    |> Keyword.delete(:source_info)
    |> Keyword.delete(:provenance)
    |> Enum.map(fn {k, v} -> {k, strip_positions(v)} end)
  end

  # ── Cure.quote/2 ─────────────────────────────────────────────────────

  describe "Cure.quote/2" do
    test "returns {:ok, ast} for valid source" do
      assert {:ok, {:literal, _, 42}} = Cure.quote("42")
    end

    test "returns {:error, _} for invalid source" do
      assert {:error, _} = Cure.quote("\t invalid")
    end

    test "accepts :file option" do
      {:ok, ast} = Cure.quote("x", file: "test.cure")
      assert {:variable, _, "x"} = ast
    end

    test "does not emit events by default" do
      # Just verify it doesn't crash with events disabled
      assert {:ok, _} = Cure.quote("42")
    end

    test "can emit events when requested" do
      Cure.Pipeline.Events.subscribe(:parser, :parse_complete)
      {:ok, _} = Cure.quote("42", emit_events: true)
      assert_receive {Cure.Pipeline.Events, :parser, :parse_complete, _, _}
    end
  end

  # ── Cure.quoted_to_string/2 ──────────────────────────────────────────

  describe "Cure.quoted_to_string/2 literals" do
    test "integer" do
      ast = quote!("42")
      assert Cure.quoted_to_string(ast) == "42"
    end

    test "float" do
      ast = quote!("3.14")
      assert Cure.quoted_to_string(ast) == "3.14"
    end

    test "string" do
      ast = quote!(~s("hello"))
      assert Cure.quoted_to_string(ast) == ~s("hello")
    end

    test "boolean true" do
      ast = quote!("true")
      assert Cure.quoted_to_string(ast) == "true"
    end

    test "boolean false" do
      ast = quote!("false")
      assert Cure.quoted_to_string(ast) == "false"
    end

    test "nil" do
      ast = quote!("nil")
      assert Cure.quoted_to_string(ast) == "nil"
    end

    test "atom" do
      ast = quote!(":ok")
      assert Cure.quoted_to_string(ast) == ":ok"
    end

    test "regex" do
      ast = quote!("/[a-z]+/i")
      assert Cure.quoted_to_string(ast) == "/[a-z]+/i"
    end

    test "char" do
      ast = quote!("'x'")
      assert Cure.quoted_to_string(ast) == "'x'"
    end
  end

  describe "Cure.quoted_to_string/2 operators" do
    test "binary arithmetic" do
      assert_round_trip("x + y")
      assert_round_trip("a * b")
    end

    test "comparison" do
      assert_round_trip("x == 42")
      assert_round_trip("a >= b")
    end

    test "boolean operators" do
      assert_round_trip("a and b")
      assert_round_trip("a or b")
    end

    test "string concat" do
      assert_round_trip(~s("a" <> "b"))
    end

    test "unary negation" do
      assert_round_trip("-x")
    end

    test "unary not" do
      assert_round_trip("not p")
    end
  end

  describe "Cure.quoted_to_string/2 bindings" do
    test "let binding" do
      printed = assert_round_trip("let x = 42")
      assert printed == "let x = 42"
    end

    test "bare assignment" do
      printed = assert_round_trip("x = 42")
      assert printed == "x = 42"
    end

    test "let with type annotation" do
      assert_round_trip("let x: Int = 42")
    end
  end

  describe "Cure.quoted_to_string/2 conditionals" do
    test "inline if-then-else" do
      assert_round_trip("if x then 1 else 2")
    end

    test "if with comparison" do
      assert_round_trip("if x > 0 then x else 0")
    end
  end

  describe "Cure.quoted_to_string/2 pattern matching" do
    test "inline match" do
      assert_round_trip("match x { 0 -> 1, _ -> 2 }")
    end

    test "match with guard" do
      assert_round_trip("match x { x when x > 0 -> x, _ -> 0 }")
    end
  end

  describe "Cure.quoted_to_string/2 collections" do
    test "empty list" do
      assert_round_trip("[]")
    end

    test "list" do
      assert_round_trip("[1, 2, 3]")
    end

    test "cons list" do
      assert_round_trip("[h | t]")
    end

    test "empty tuple" do
      assert_round_trip("%[]")
    end

    test "tuple" do
      assert_round_trip("%[1, 2]")
    end

    test "empty map" do
      assert_round_trip("%{}")
    end

    test "map with atom key shorthand" do
      assert_round_trip("%{name: 42}")
    end

    test "map with explicit key" do
      assert_round_trip(~s(%{"key" => 42}))
    end
  end

  describe "Cure.quoted_to_string/2 ranges" do
    test "exclusive range" do
      assert_round_trip("1..10")
    end

    test "inclusive range" do
      assert_round_trip("1..=10")
    end
  end

  describe "Cure.quoted_to_string/2 pipe" do
    test "pipe to bare function" do
      assert_round_trip("x |> f")
    end

    test "pipe to function with args" do
      assert_round_trip("x |> f(y)")
    end
  end

  describe "Cure.quoted_to_string/2 attribute access" do
    test "simple access" do
      assert_round_trip("person.name")
    end

    test "chained access" do
      assert_round_trip("a.b.c")
    end
  end

  describe "Cure.quoted_to_string/2 function calls" do
    test "zero-arg call" do
      assert_round_trip("f()")
    end

    test "multi-arg call" do
      assert_round_trip("add(x, y)")
    end
  end

  describe "Cure.quoted_to_string/2 lambda" do
    test "simple lambda" do
      assert_round_trip("fn(x) -> x")
    end

    test "multi-param lambda" do
      assert_round_trip("fn(x, y) -> x")
    end

    test "zero-param lambda" do
      assert_round_trip("fn() -> 42")
    end
  end

  describe "Cure.quoted_to_string/2 keyword unary" do
    test "return" do
      assert_round_trip("return 42")
    end

    test "throw" do
      assert_round_trip("throw x")
    end

    test "yield" do
      assert_round_trip("yield x")
    end
  end

  describe "Cure.quoted_to_string/2 comprehensions" do
    test "simple comprehension" do
      assert_round_trip("[x for x <- list]")
    end

    test "comprehension with filter" do
      assert_round_trip("[x for x <- list, x > 0]")
    end
  end

  describe "Cure.quoted_to_string/2 string interpolation" do
    test "simple interpolation" do
      assert_round_trip(~s("hello \#{name}"))
    end

    test "interpolation with expression" do
      assert_round_trip(~s("result: \#{x + 1}"))
    end
  end

  # ── Structural Round-trips ──────────────────────────────────────────

  describe "Cure.quoted_to_string/2 function definitions" do
    test "simple fn" do
      assert_round_trip("fn add(x: Int, y: Int) -> Int = x + y")
    end

    test "private fn" do
      assert_round_trip("local fn helper(x: Int) -> Int = x + 1")
    end

    test "fn signature only" do
      assert_round_trip("fn show(x: T) -> String")
    end
  end

  describe "Cure.quoted_to_string/2 type definitions" do
    test "ADT" do
      assert_round_trip("type Option(T) = Some(T) | None")
    end

    test "nullary constructors" do
      assert_round_trip("type Color = Red | Green | Blue")
    end

    test "type alias" do
      assert_round_trip("type Name = String")
    end
  end

  describe "Cure.quoted_to_string/2 imports" do
    test "use all" do
      printed = assert_round_trip("use Std.List")
      assert printed == "use Std.List"
    end

    test "selective import" do
      printed = assert_round_trip("use Std.List.{map, filter}")
      assert printed == "use Std.List.{map, filter}"
    end

    test "aliased import" do
      printed = assert_round_trip("use Std.Io as IO")
      assert printed == "use Std.Io as IO"
    end
  end
end

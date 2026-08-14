defmodule Cure.Compiler.ParserTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  describe "binder grade decorators" do
    test "precede the binder and preserve external labels" do
      ast = parse!("mod M\n  fn f(@linear label c : Box, @affine h : Handle) -> Box = c\n")

      {:container, _, [{:function_def, meta, _}]} = ast
      [{:param, linear_meta, "c"}, {:param, affine_meta, "h"}] = meta[:params]

      assert linear_meta[:grade] == :linear
      assert linear_meta[:label] == "label"
      assert affine_meta[:grade] == :affine
    end

    test "supports graded implicit binders" do
      ast = parse!("mod M\n  fn f({@erased n : Nat}) -> Nat = n\n")

      {:container, _, [{:function_def, meta, _}]} = ast
      [{:param, param_meta, "n"}] = meta[:params]
      assert param_meta[:implicit]
      assert param_meta[:grade] == :erased
    end

    test "supports graded local bindings" do
      ast = parse!("mod M\n  fn f() -> Int =\n    let @linear c : Int = 1\n    c\n")

      assert {:container, _, [{:function_def, _, [{:block, _, _}]}]} = ast
    end
  end

  # ── Literals ──────────────────────────────────────────────────────────

  describe "literals" do
    test "integer" do
      assert {:literal, meta, 42} = parse!("42")
      assert meta[:subtype] == :integer
    end

    test "float" do
      assert {:literal, meta, 3.14} = parse!("3.14")
      assert meta[:subtype] == :float
    end

    test "string" do
      assert {:literal, meta, "hello"} = parse!(~s("hello"))
      assert meta[:subtype] == :string
    end

    test "boolean true" do
      assert {:literal, meta, true} = parse!("true")
      assert meta[:subtype] == :boolean
    end

    test "boolean false" do
      assert {:literal, meta, false} = parse!("false")
      assert meta[:subtype] == :boolean
    end

    test "nil" do
      assert {:literal, meta, nil} = parse!("nil")
      assert meta[:subtype] == :null
    end

    test "atom" do
      assert {:literal, meta, :ok} = parse!(":ok")
      assert meta[:subtype] == :symbol
    end

    test "regex" do
      assert {:computed_use, meta, [_expander, {:macro_input, input_meta, [pattern, flags]}]} =
               parse!("/[a-z]+/i")

      assert meta[:keyword] == "regex"
      assert input_meta[:keyword] == "regex"
      assert {:literal, pattern_meta, "[a-z]+"} = pattern
      assert pattern_meta[:subtype] == :string
      assert pattern_meta[:source_info].whole.start_column == 2
      assert pattern_meta[:source_info].whole.end_column == 8
      assert {:literal, flags_meta, "i"} = flags
      assert flags_meta[:subtype] == :string
      assert flags_meta[:source_info].whole.start_column == 9
      assert flags_meta[:source_info].whole.end_column == 10
    end

    test "bare slash regex expands to the pure Cure Regex literal macro" do
      assert {:computed_use, meta, [_expander, {:macro_input, _input_meta, [pattern, flags]}]} =
               parse!("/[A-z]*/")

      assert meta[:keyword] == "regex"

      assert {:literal, pattern_meta, "[A-z]*"} = pattern
      assert pattern_meta[:subtype] == :string
      assert {:literal, flags_meta, ""} = flags
      assert flags_meta[:subtype] == :string
    end

    test "preserves the complete Elixir modifier string for the pure macro" do
      assert {:computed_use, meta,
              [_expander, {:macro_input, _input_meta, [_pattern, {:literal, _flags_meta, "imsxurfUE"}]}]} =
               parse!("/foo/imsxurfUE")

      assert meta[:keyword] == "regex"
    end

    test "char" do
      assert {:literal, meta, ?x} = parse!("'x'")
      assert meta[:subtype] == :char
    end
  end

  describe "match-chain function definitions" do
    test "parses unguarded pattern clauses without an equals body" do
      ast =
        parse!("""
        fn factorial(n: Nat) -> Nat
          | 0 -> 1
          | n -> n * factorial(n - 1)
        """)

      assert {:function_def, meta, []} = ast
      assert meta[:name] == "factorial"
      assert [%{guard: nil, params: [zero], body: [{:literal, _, 1}]}, second] = meta[:clauses]
      assert {:literal, _, 0} = zero
      assert second.guard == nil
      assert [{:binary_op, _, _}] = second.body
    end

    test "parses guarded clauses and preserves the fallback pattern" do
      ast =
        parse!("""
        fn classify(x: Int) -> Sign
          | x when x > 0 -> Positive
          | x when x < 0 -> Negative
          | _             -> Zero
        """)

      assert {:function_def, meta, []} = ast
      [positive, negative, fallback] = meta[:clauses]
      assert positive.guard != nil
      assert negative.guard != nil
      assert fallback.guard == nil
      assert [{:variable, _, "_"}] = fallback.params
    end
  end

  # ── Variables ─────────────────────────────────────────────────────────

  describe "variables" do
    test "simple variable" do
      assert {:variable, meta, "x"} = parse!("x")
      assert meta[:scope] == :local
    end

    test "underscore wildcard" do
      assert {:variable, meta, "_"} = parse!("_")
      assert meta[:scope] == :local
    end

    test "PascalCase identifier" do
      assert {:variable, meta, "MyModule"} = parse!("MyModule")
      assert meta[:scope] == :local
    end
  end

  describe "type definitions" do
    test "accepts newline between ADT name and assign" do
      ast =
        parse!("""
        type Literal
          = LInt(Int)
          | LFloat(Float)
          | LString(String)
        """)

      assert {:container, meta, variants} = ast
      assert meta[:container_type] == :enum
      assert meta[:name] == "Literal"

      assert Enum.map(variants, fn {:function_def, meta, []} -> meta[:name] end) == [
               "LInt",
               "LFloat",
               "LString"
             ]
    end
  end

  # ── Binary Operators ──────────────────────────────────────────────────

  describe "binary operators" do
    test "addition" do
      ast = parse!("x + y")
      assert {:binary_op, meta, [left, right]} = ast
      assert Keyword.get(meta, :operator) == :+
      assert Keyword.get(meta, :category) == :arithmetic
      assert {:variable, _, "x"} = left
      assert {:variable, _, "y"} = right
    end

    test "precedence: * binds tighter than +" do
      ast = parse!("a + b * c")
      assert {:binary_op, meta, [_a, rhs]} = ast
      assert Keyword.get(meta, :operator) == :+
      assert {:binary_op, inner_meta, [_b, _c]} = rhs
      assert Keyword.get(inner_meta, :operator) == :*
    end

    test "precedence: parentheses override" do
      ast = parse!("(a + b) * c")
      assert {:binary_op, meta, [lhs, _c]} = ast
      assert Keyword.get(meta, :operator) == :*
      assert {:binary_op, inner_meta, [_a, _b]} = lhs
      assert Keyword.get(inner_meta, :operator) == :+
    end

    test "comparison" do
      ast = parse!("x == 42")
      assert {:binary_op, meta, _} = ast
      assert Keyword.get(meta, :operator) == :==
      assert Keyword.get(meta, :category) == :comparison
    end

    test "boolean and" do
      ast = parse!("a and b")
      assert {:binary_op, meta, _} = ast
      assert Keyword.get(meta, :operator) == :and
    end

    test "boolean or" do
      ast = parse!("a or b")
      assert {:binary_op, meta, _} = ast
      assert Keyword.get(meta, :operator) == :or
    end

    test "string concatenation" do
      ast = parse!(~s("a" <> "b"))
      assert {:binary_op, meta, _} = ast
      assert Keyword.get(meta, :operator) == :<>
    end
  end

  # ── Unary Operators ──────────────────────────────────────────────────

  describe "unary operators" do
    test "negation" do
      ast = parse!("-x")
      assert {:unary_op, meta, [{:variable, _, "x"}]} = ast
      assert Keyword.get(meta, :operator) == :-
      assert Keyword.get(meta, :category) == :arithmetic
    end

    test "not" do
      ast = parse!("not p")
      assert {:unary_op, meta, [{:variable, _, "p"}]} = ast
      assert Keyword.get(meta, :operator) == :not
      assert Keyword.get(meta, :category) == :boolean
    end
  end

  # ── Function Calls ───────────────────────────────────────────────────

  describe "function calls" do
    test "zero-arg call" do
      ast = parse!("f()")
      assert {:function_call, meta, []} = ast
      assert Keyword.get(meta, :name) == "f"
    end

    test "multi-arg call" do
      ast = parse!("add(x, y)")
      assert {:function_call, meta, [_, _]} = ast
      assert Keyword.get(meta, :name) == "add"
    end

    test "nested call" do
      ast = parse!("f(g(x))")
      assert {:function_call, _, [{:function_call, _, [{:variable, _, "x"}]}]} = ast
    end

    test "constructor call (PascalCase)" do
      ast = parse!("Ok(value)")
      assert {:function_call, meta, [{:variable, _, "value"}]} = ast
      assert Keyword.get(meta, :name) == "Ok"
    end
  end

  # ── Let Bindings ─────────────────────────────────────────────────────

  describe "let bindings" do
    test "simple let" do
      ast = parse!("let x = 42")
      assert {:assignment, _meta, [{:variable, _, "x"}, {:literal, _, 42}]} = ast
    end

    test "let with type annotation" do
      ast = parse!("let x: Int = 42")
      assert {:assignment, meta, [{:variable, _, "x"}, {:literal, _, 42}]} = ast
      assert Keyword.has_key?(meta, :type_annotation)
    end

    test "function expression body can start with let chain" do
      ast =
        parse!("""
        fn f() -> Int = let x = 1
          x
        """)

      assert {:function_def, _, [{:block, _, [assignment, {:variable, _, "x"}]}]} = ast
      assert {:assignment, meta, [{:variable, _, "x"}, {:literal, _, 1}]} = assignment
      assert Keyword.get(meta, :let)
    end
  end

  # ── Conditionals ─────────────────────────────────────────────────────

  describe "conditionals" do
    test "inline if-then-else" do
      ast = parse!("if x then 1 else 2")
      assert {:conditional, _, [cond, then_br, else_br]} = ast
      assert {:variable, _, "x"} = cond
      assert {:literal, _, 1} = then_br
      assert {:literal, _, 2} = else_br
    end

    test "if with comparison condition" do
      ast = parse!("if x > 0 then x else 0")
      assert {:conditional, _, [{:binary_op, _, _}, _, _]} = ast
    end
  end

  # ── Pattern Matching ─────────────────────────────────────────────────

  describe "match" do
    test "inline match" do
      ast = parse!("match x { 0 -> 1, _ -> 2 }")
      assert {:pattern_match, _, [scrutinee | arms]} = ast
      assert {:variable, _, "x"} = scrutinee
      assert [_, _] = arms
    end

    test "match arm has pattern metadata" do
      ast = parse!("match x { 0 -> 1 }")
      assert {:pattern_match, _, [_, arm]} = ast
      assert {:match_arm, meta, [{:literal, _, 1}]} = arm
      assert {:literal, _, 0} = Keyword.get(meta, :pattern)
    end

    test "a `-> impossible` arm body is marked impossible in arm meta" do
      ast = parse!("match x { bar() -> impossible }")
      assert {:pattern_match, _, [_, arm]} = ast
      assert {:match_arm, meta, _body} = arm
      assert Keyword.get(meta, :impossible) == true
    end

    test "`impossible` is still usable as a normal identifier in an arm body" do
      ast = parse!("match x { bar() -> impossible + 1 }")
      assert {:pattern_match, _, [_, arm]} = ast
      assert {:match_arm, meta, _body} = arm
      refute Keyword.get(meta, :impossible) == true
    end
  end

  # ── Collections ──────────────────────────────────────────────────────

  describe "collections" do
    test "empty list" do
      assert {:list, _, []} = parse!("[]")
    end

    test "list with elements" do
      ast = parse!("[1, 2, 3]")
      assert {:list, _, [_, _, _]} = ast
    end

    test "cons list" do
      ast = parse!("[h | t]")
      assert {:list, meta, [{:variable, _, "h"}, {:variable, _, "t"}]} = ast
      assert Keyword.get(meta, :cons) == true
    end

    test "empty tuple" do
      assert {:tuple, _, []} = parse!("%[]")
    end

    test "tuple with elements" do
      ast = parse!("%[1, 2]")
      assert {:tuple, _, [_, _]} = ast
    end

    test "empty map" do
      assert {:map, _, []} = parse!("%{}")
    end

    test "map with atom key shorthand" do
      ast = parse!("%{name: 42}")
      assert {:map, _, [{:pair, _, [{:literal, [subtype: :symbol], :name}, {:literal, _, 42}]}]} = ast
    end

    test "map with explicit key" do
      ast = parse!(~s(%{"key" => 42}))
      assert {:map, _, [{:pair, _, [key, val]}]} = ast
      assert {:literal, key_meta, "key"} = key
      assert key_meta[:subtype] == :string
      assert {:literal, _, 42} = val
    end
  end

  # ── Ranges ───────────────────────────────────────────────────────────

  describe "ranges" do
    test "exclusive range" do
      ast = parse!("1..10")
      assert {:range, meta, [{:literal, _, 1}, {:literal, _, 10}]} = ast
      assert Keyword.get(meta, :inclusive) == false
    end

    test "inclusive range" do
      ast = parse!("1..=10")
      assert {:range, meta, [{:literal, _, 1}, {:literal, _, 10}]} = ast
      assert Keyword.get(meta, :inclusive) == true
    end
  end

  # ── Pipe ─────────────────────────────────────────────────────────────

  describe "pipe" do
    test "pipe to bare function" do
      ast = parse!("x |> f")
      assert {:function_call, meta, [{:variable, _, "x"}]} = ast
      assert Keyword.get(meta, :name) == "f"
      assert Keyword.get(meta, :pipe) == true
    end

    test "pipe to function with args" do
      ast = parse!("x |> f(y)")
      assert {:function_call, meta, [{:variable, _, "x"}, {:variable, _, "y"}]} = ast
      assert Keyword.get(meta, :name) == "f"
      assert Keyword.get(meta, :pipe) == true
    end

    test "multi-step pipe" do
      ast = parse!("x |> f |> g")
      assert {:function_call, meta, [{:function_call, _, _}]} = ast
      assert Keyword.get(meta, :name) == "g"
    end
  end

  # ── Attribute Access ─────────────────────────────────────────────────

  describe "attribute access" do
    test "simple access" do
      ast = parse!("person.name")
      assert {:attribute_access, meta, [{:variable, _, "person"}]} = ast
      assert Keyword.get(meta, :attribute) == "name"
    end

    test "chained access" do
      ast = parse!("a.b.c")
      assert {:attribute_access, meta, [{:attribute_access, _, _}]} = ast
      assert Keyword.get(meta, :attribute) == "c"
    end
  end

  # ── Return / Throw / Yield ──────────────────────────────────────────

  describe "keyword unary" do
    test "return" do
      ast = parse!("return 42")
      assert {:early_return, _, [{:literal, _, 42}]} = ast
    end

    test "throw" do
      ast = parse!("throw x")
      assert {:throw, _, [{:variable, _, "x"}]} = ast
    end

    test "yield" do
      ast = parse!("yield x")
      assert {:yield, _, [{:variable, _, "x"}]} = ast
    end
  end

  # ── Lambda ──────────────────────────────────────────────────────────

  describe "lambda" do
    test "simple lambda" do
      ast = parse!("fn(x) -> x")
      assert {:lambda, meta, [{:variable, _, "x"}]} = ast
      assert [{:param, param_meta, "x"}] = Keyword.get(meta, :params)
      assert %Cure.MetaAST.SourceInfo{} = Keyword.fetch!(param_meta, :source_info)
    end

    test "multi-param lambda" do
      ast = parse!("fn(x, y) -> x")
      assert {:lambda, meta, _} = ast
      params = Keyword.get(meta, :params)
      assert [_, _] = params
    end

    test "zero-param lambda" do
      ast = parse!("fn() -> 42")
      assert {:lambda, meta, [{:literal, _, 42}]} = ast
      assert [] = Keyword.get(meta, :params)
    end
  end

  # ── String Interpolation ────────────────────────────────────────────

  describe "string interpolation" do
    test "simple interpolation" do
      ast = parse!(~s("hello \#{name}"))
      assert {:string_interpolation, _, parts} = ast
      assert [{:literal, [subtype: :string], "hello "}, {:variable, _, "name"}] = parts
    end

    test "interpolation with expression" do
      ast = parse!(~s("result: \#{x + 1}"))
      assert {:string_interpolation, _, [_, {:binary_op, _, _}]} = ast
    end
  end

  # ── Comprehensions ──────────────────────────────────────────────────

  describe "comprehensions" do
    test "simple comprehension" do
      ast = parse!("[x for x <- list]")
      assert {:comprehension, _, [body, gen]} = ast
      assert {:variable, _, "x"} = body
      assert {:generator, _, [{:variable, _, "x"}, {:variable, _, "list"}]} = gen
    end

    test "comprehension with filter" do
      ast = parse!("[x for x <- list, x > 0]")
      assert {:comprehension, _, [_body, _gen, filter]} = ast
      assert {:filter, _, [{:binary_op, _, _}]} = filter
    end
  end

  # ── Blocks (multi-expression) ──────────────────────────────────────

  describe "blocks" do
    test "multiple top-level expressions" do
      ast = parse!("x\ny")
      assert {:block, _, [{:variable, _, "x"}, {:variable, _, "y"}]} = ast
    end
  end

  # ── Position Tracking ──────────────────────────────────────────────

  describe "position tracking" do
    test "line and col in metadata" do
      ast = parse!("42")
      assert {:literal, meta, 42} = ast
      assert Keyword.get(meta, :line) == 1
      assert Keyword.get(meta, :col) == 1
    end
  end

  # ── Pipeline Events ────────────────────────────────────────────────

  describe "pipeline events" do
    test "parse_complete event is emitted" do
      Cure.Pipeline.Events.subscribe(:parser, :parse_complete)
      {:ok, tokens} = Lexer.tokenize("42", emit_events: false)
      Parser.parse(tokens, emit_events: true)

      assert_receive {Cure.Pipeline.Events, :parser, :parse_complete, _, _}
    end
  end
end

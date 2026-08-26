defmodule Cure.Compiler.UnionParseTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.MetaAST.Metadata

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Metadata.strip_diagnostics(ast)
  end

  # Collect every {tag, meta, children} 3-tuple in the AST.
  defp collect(node, acc) do
    acc = if is_tuple(node) and tuple_size(node) == 3, do: [node | acc], else: acc

    cond do
      is_tuple(node) -> Enum.reduce(Tuple.to_list(node), acc, &collect/2)
      is_list(node) -> Enum.reduce(node, acc, &collect/2)
      true -> acc
    end
  end

  defp find_union(ast) do
    collect(ast, []) |> Enum.find(&match?({:union_type, _, _}, &1))
  end

  describe "union types in type-expression position" do
    test "parses a two-member union in a parameter annotation" do
      ast = parse!("mod M\n  fn f(x: Int | String) -> Int = 1\nend\n")

      assert {:union_type, [], [a, b]} = find_union(ast)
      assert {:variable, _, "Int"} = a
      assert {:variable, _, "String"} = b
    end

    test "parses a three-member union in a return annotation" do
      ast = parse!("mod M\n  fn f(x: Int) -> Int | String | Bool = 1\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 3
    end

    test "parses literal members" do
      ast = parse!("mod M\n  fn f(x: 3 | :north | \"s\") -> Int = 1\nend\n")

      assert {:union_type, [], [i, s, str]} = find_union(ast)
      assert {:literal, m1, 3} = i
      assert m1[:subtype] == :integer
      assert {:literal, m2, :north} = s
      assert m2[:subtype] == :symbol
      assert {:literal, m3, "s"} = str
      assert m3[:subtype] == :string
    end

    test "parses an applied type as a member" do
      ast = parse!("mod M\n  fn f(x: List(Int) | Int) -> Int = 1\nend\n")
      assert {:union_type, [], [{:function_call, fm, _}, {:variable, _, "Int"}]} = find_union(ast)
      assert fm[:name] == "List"
    end

    test "allows a leading bar" do
      ast = parse!("mod M\n  typealias P = | Int | String\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 2
    end

    test "binds LOOSER than -> : `A -> B | C` is `(A -> B) | C`" do
      ast = parse!("mod M\n  typealias P = Int -> Bool | String\nend\n")

      assert {:union_type, [], [arrow, {:variable, _, "String"}]} = find_union(ast)
      assert {:function_call, am, _} = arrow
      assert am[:function_type] == true
    end

    test "parses a union nested in a type argument" do
      ast = parse!("mod M\n  fn f(m: Map(String, Int | Bool)) -> Int = 1\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 2
    end

    test "parses a parenthesised union in domain position" do
      ast = parse!("mod M\n  typealias P = (Int | String) -> Bool\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 2
    end
  end

  describe "regression: `|` in ADT declaration bodies still means constructor alternatives" do
    test "plain enum is unaffected" do
      ast = parse!("mod M\n  type Color = Red | Green | Blue\nend\n")
      assert find_union(ast) == nil
    end

    test "enum whose first variant is parenthesised-arrow-shaped is unaffected" do
      ast = parse!("mod M\n  type Handler = Cb(Int) | Nope\nend\n")
      assert find_union(ast) == nil

      assert {:container, meta, variants} =
               ast |> collect([]) |> Enum.find(&match?({:container, _, _}, &1))

      assert meta[:container_type] == :enum
      assert length(variants) == 2
    end

    test "the empty type `type Empty = |` still parses" do
      ast = parse!("mod M\n  type Empty = |\nend\n")
      assert find_union(ast) == nil
    end
  end

  # Guards the highest-severity risk in this feature: literal-token recognition must
  # be scoped to union members only. A bare numeral in a type INDEX (not followed by
  # `|`) must keep parsing to {:variable, _, "N"} — idx_to_core recovers the integer
  # from that via numeric_index_value/1 and has NO clause for {:literal, ...}, so
  # emitting a literal node here would silently break every dependent numeral index
  # in the tree, including `typealias Char = Bounded(1114112)` in lib/std/char.cure.
  describe "regression: a numeral in type-index position is NOT a literal node" do
    test "Bounded(1114112) — the real Std.Char definition — stays a :variable" do
      ast = parse!("mod M\n  typealias Char = Bounded(1114112)\nend\n")

      assert {:function_call, fm, [arg]} =
               collect(ast, [])
               |> Enum.find(&match?({:function_call, m, _} when m != [], &1))

      assert fm[:name] == "Bounded"
      assert {:variable, [scope: :local], "1114112"} = arg
      assert collect(ast, []) |> Enum.find(&match?({:literal, _, _}, &1)) == nil
    end

    test "a multi-argument literal index telescope stays :variable" do
      ast = parse!("mod M\n  typealias E = Equivalent(Int, 3, 3)\nend\n")

      assert collect(ast, []) |> Enum.find(&match?({:literal, _, _}, &1)) == nil
      assert collect(ast, []) |> Enum.any?(&match?({:variable, _, "3"}, &1))
    end
  end

  describe "typed patterns in match arms" do
    defp arm_patterns(ast) do
      ast
      |> collect([])
      |> Enum.filter(&match?({:match_arm, _, _}, &1))
      |> Enum.map(fn {:match_arm, meta, _} -> meta[:pattern] end)
    end

    test "binds a name at a member type" do
      ast =
        parse!("""
        mod M
          fn f(x: Int | String) -> Int = match x
            n: Int -> 1
            s: String -> 2
        end
        """)

      pats = arm_patterns(ast) |> Enum.sort_by(fn {_, _, [n, _]} -> n end)

      assert [
               {:typed_pattern, _, ["n", {:variable, _, "Int"}]},
               {:typed_pattern, _, ["s", {:variable, _, "String"}]}
             ] = pats
    end

    test "a typed pattern's annotation may itself be a union (sub-union branch)" do
      ast =
        parse!("""
        mod M
          fn f(x: Int | String | Bool) -> Int = match x
            n: Int -> 1
            rest: String | Bool -> 2
        end
        """)

      assert Enum.any?(arm_patterns(ast), fn
               {:typed_pattern, _, ["rest", {:union_type, [], ms}]} -> length(ms) == 2
               _ -> false
             end)
    end

    test "literal patterns in match arms are untouched" do
      ast =
        parse!("""
        mod M
          fn f(x: Int) -> Int = match x
            3 -> 1
            _ -> 2
        end
        """)

      assert collect(ast, []) |> Enum.find(&match?({:typed_pattern, _, _}, &1)) == nil
    end

    test "a typed pattern also parses inside a constructor-pattern argument list" do
      # Cons(n: Int, rest) — NOT a separate parser change: parse_call_args/1 and
      # parse_more_args/1 already call maybe_wrap_as/2 on every parsed argument,
      # the same helper parse_match_arm/1 uses, so this comes free.
      ast = parse!("mod M\n  fn f(x) -> Int = match x\n    Cons(n: Int, rest) -> 1\n    _ -> 2\nend\n")

      assert collect(ast, [])
             |> Enum.any?(&match?({:typed_pattern, _, ["n", {:variable, _, "Int"}]}, &1))
    end

    test "a typed pattern's annotation may be a QUALIFIED (dotted) type name" do
      # `parse_pattern_type_member` restricts to `parse_type_atom/1` (bare `Name`
      # / `Name(args)`) so it never swallows the arm's `->` — but that grammar
      # alone does not know about `.`, so `n: Std.Nat.Nat -> ...` used to fail
      # with a hard parse error (`{:expected, :arrow, :got, :dot, ...}`) even
      # though the identical qualified name parses fine as an ordinary parameter
      # annotation via parse_type_arrow/1's maybe_parse_type_projection/2.
      ast =
        parse!("""
        mod M
          fn f(x: Int) -> Int = match x
            n: Std.Nat.Nat -> 1
            _ -> 2
        end
        """)

      assert {:typed_pattern, _, ["n", type_ast]} =
               collect(ast, []) |> Enum.find(&match?({:typed_pattern, _, _}, &1))

      assert {:attribute_access, [attribute: "Nat"], [{:attribute_access, [attribute: "Nat"], [{:variable, _, "Std"}]}]} =
               type_ast
    end

    test "a typed pattern's annotation may be a qualified type applied to arguments" do
      ast =
        parse!("""
        mod M
          fn f(x: Int) -> Int = match x
            n: Std.List.List(Int) -> 1
            _ -> 2
        end
        """)

      assert {:typed_pattern, _, ["n", type_ast]} =
               collect(ast, []) |> Enum.find(&match?({:typed_pattern, _, _}, &1))

      assert {:function_call, [name: "Std.List.List", qualified: true], [{:variable, _, "Int"}]} =
               type_ast
    end
  end
end

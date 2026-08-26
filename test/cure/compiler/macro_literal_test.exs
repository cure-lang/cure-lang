# test/cure/compiler/macro_literal_test.exs
defmodule Cure.Compiler.MacroLiteralTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "a literal rule parses to a :literal-kind rule with a hole, a suffix, and a template" do
    node = parse!("macro Dur\n  literal <n: Number> ms becomes Duration.ms(n)\n")
    assert {:macro_def, _meta, [rule]} = node
    assert rule.kind == :literal
    assert rule.suffix == "ms"
    assert [{:hole, %{name: "n", kind: "Number"}}, {:lit, "ms"}] = rule.segments
    assert {:function_call, _, _} = rule.template
  end

  test "a number use-site with a registered suffix expands the literal rule" do
    node =
      parse!("macro Dur\n  literal <n: Number> ms becomes Duration.ms(n)\n\nfn f() -> Int = 500ms\n")

    body = find_fn_body(node, "f")
    # 500ms  ==>  Duration.ms(500)
    assert {:function_call, meta, [arg]} = body
    assert Keyword.get(meta, :name) in ["Duration.ms", "ms"]
    assert {:literal, _, 500} = arg
  end

  test "a float number use-site with a registered suffix expands the literal rule" do
    node =
      parse!("macro Dur\n  literal <n: Number> s becomes Duration.s(n)\n\nfn f() -> Float = 3.5s\n")

    body = find_fn_body(node, "f")
    # 3.5s  ==>  Duration.s(3.5)  — the :float parse_prefix clause dispatches
    # through the same maybe_literal_macro/2 as :integer.
    assert {:function_call, meta, [arg]} = body
    assert Keyword.get(meta, :name) in ["Duration.s", "s"]
    assert {:literal, _, 3.5} = arg
  end

  test "a bare number without a registered suffix is unaffected" do
    node = parse!("fn f() -> Int = 500\n")
    body = find_fn_body(node, "f")
    assert {:literal, _, 500} = body
  end

  test "an unrelated numeric expression is unaffected even when a literal macro IS registered elsewhere in the file" do
    # state.literal_macros is NON-empty (has an "ms" entry), so this exercises
    # the real Map.fetch-miss path, not just the trivially-empty-map case.
    node =
      parse!("macro Dur\n  literal <n: Number> ms becomes Duration.ms(n)\n\nfn f() -> Int = 500 + 3\n")

    body = find_fn_body(node, "f")
    assert {:binary_op, meta, [left, right]} = body
    assert Keyword.get(meta, :operator) == :+
    assert {:literal, _, 500} = left
    assert {:literal, _, 3} = right
  end

  test "a computed token-class literal becomes a deferred compile-time use" do
    node =
      parse!("""
      macro RegexLiteral
        literal regex <pattern: String> <flags: String> computed by build_regex

      fn f() = /[a-z]+/im
      """)

    assert {:computed_use, meta, [elab, {:macro_input, _, [pattern, flags]}]} =
             find_fn_body(node, "f")

    assert meta[:keyword] == "regex"
    assert {:variable, _, "build_regex"} = elab
    assert {:literal, pattern_meta, "[a-z]+"} = pattern
    assert pattern_meta[:subtype] == :string
    assert {:literal, flags_meta, "im"} = flags
    assert flags_meta[:subtype] == :string
  end

  defp find_fn_body({:function_def, meta, [body]}, name),
    do: if(to_string(Keyword.get(meta, :name)) == name, do: body)

  defp find_fn_body({_t, _m, ch}, name) when is_list(ch), do: Enum.find_value(ch, &find_fn_body(&1, name))
  defp find_fn_body(_, _), do: nil
end

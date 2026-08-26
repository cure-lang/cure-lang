# test/cure/compiler/macro_computed_test.exs
defmodule Cure.Compiler.MacroComputedTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp rules({:macro_def, _, rs}), do: rs
  defp rules({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &rules/1)
  defp rules(_), do: nil

  test "a `computed by` rule parses to a :computed rule capturing the elab reference" do
    [rule] = rules(parse!("macro Mk\n  syntax mk <x: Code> computed by build_it\n"))
    assert rule.kind == :computed
    assert rule.keyword == "mk"
    assert [{:hole, %{name: "x", kind: "Code"}}] = rule.segments
    assert {:variable, _, "build_it"} = rule.elab
  end

  test "a `becomes` rule still parses to a :syntax rule (non-breaking)" do
    [rule] = rules(parse!("macro Now\n  syntax now becomes Clock.now()\n"))
    assert rule.kind == :syntax
    assert {:function_call, _, _} = rule.template
  end

  test "a :computed rule dispatches to a deferred use-site node" do
    node = parse!("mod M\n  macro Mk\n    syntax mk computed by build_it\n  fn f() = mk\n")

    find = fn find, n ->
      case n do
        {:function_def, meta, [body]} -> if(to_string(Keyword.get(meta, :name)) == "f", do: body)
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end

    assert {:computed_use, meta, _} = find.(find, node)

    assert Keyword.take(meta, [
             :keyword,
             :syntax_type,
             :syntax_fields,
             :syntax_repeated_fields,
             :syntax_field_types,
             :file
           ]) ==
             [
               keyword: "mk",
               syntax_type: "MkSyntax",
               syntax_fields: [],
               syntax_repeated_fields: [],
               syntax_field_types: %{},
               file: "nofile"
             ]
  end

  test "computed rules can delimit one parsed code hole before a following literal" do
    [rule] =
      rules(parse!("macro Mk\n  syntax mk <body: Code until call> (call <other: Code>)? computed by build\n"))

    assert rule.kind == :computed
    assert [{:code_hole, %{name: "body", delimiter: "call"}}, {:optional, segments}] = rule.segments
    assert [{:lit, "call"}, {:hole, %{name: "other", kind: "Code"}}] = segments
  end

  test "computed rules can capture a positional declarations block hole" do
    [rule] =
      rules(
        parse!("macro Mk\n  syntax mk state <t: Type> <body: Declarations until dedent> computed directly by build\n")
      )

    assert rule.kind == :computed

    assert [
             {:lit, "state"},
             {:hole, %{name: "t", kind: "Type"}},
             {:declarations_hole, %{name: "body", delimiter: "dedent"}}
           ] = rule.segments
  end

  test "a declarations block hole does not shadow a sibling rule on a single-line use" do
    # `<body: Declarations until dedent>` must only match a real indented block.
    # On a single-line use-site sharing the `mk state <t>` prefix, the trailing
    # sibling literal (`with`) has to win — otherwise the declarations hole
    # matches an empty block and swallows the rest as leftover.
    node =
      parse!("""
      mod M
        macro Mk
          syntax mk state <t: Type> <body: Declarations until dedent> computed directly by build_body
          syntax mk state <t: Type> with <p: Code> computed directly by build_with
        fn f() -> Syntax = mk state Int with 0
      """)

    find = fn find, n ->
      case n do
        {:computed_use, _, [{:variable, _, name}, _]} -> name
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end

    assert find.(find, node) == "build_with"
  end

  test "a declarations block hole still matches a real indented body" do
    node =
      parse!("""
      mod M
        macro Mk
          syntax mk state <t: Type> <body: Declarations until dedent> computed directly by build_body
          syntax mk state <t: Type> with <p: Code> computed directly by build_with
        fn f() -> Syntax =
          mk state Int
            fn helper() -> Int = 0
      """)

    find = fn find, n ->
      case n do
        {:computed_use, _, [{:variable, _, name}, _]} -> name
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end

    assert find.(find, node) == "build_body"
  end

  test "a declarations block hole matches a bodyless use whose form ends after the prefix" do
    # `mk state Int` with nothing after (the form ends at the newline/eof) is a
    # legitimate empty-body use of the declarations-hole rule; it must still
    # match that rule (empty block), not fall through.
    node =
      parse!("""
      mod M
        macro Mk
          syntax mk state <t: Type> <body: Declarations until dedent> computed directly by build_body
          syntax mk state <t: Type> with <p: Code> computed directly by build_with
        fn f() -> Syntax = mk state Int
      """)

    find = fn find, n ->
      case n do
        {:computed_use, _, [{:variable, _, name}, {:macro_input, _, inputs}]} -> {name, inputs}
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end

    assert {"build_body", [_t, {:declarations_block, _, []}]} = find.(find, node)
  end

  test "computed dispatch tries later rules after an earlier grammar mismatch" do
    node =
      parse!("""
      mod M
        macro Mk
          syntax mk first <x: Code> computed by build_first
          syntax mk second <x: Code> computed by build_second
        fn f() -> Syntax = mk second 1
      """)

    find = fn find, n ->
      case n do
        {:computed_use, _, [{:variable, _, "build_second"}, _]} -> true
        {_tag, _meta, children} when is_list(children) -> Enum.any?(children, &find.(find, &1))
        _ -> false
      end
    end

    assert find.(find, node)
  end

  test "a zero-hole computed use is deferred with its elab and synthetic input" do
    node =
      parse!("""
      mod M
        macro Mk
          syntax mk computed by build_it
        fn build_it(input: Syntax) -> Syntax = input
        fn f() -> Syntax = mk
      """)

    find = fn find, n ->
      case n do
        {:function_def, meta, [body]} ->
          if Keyword.get(meta, :name) == "f", do: body

        {_t, _m, ch} when is_list(ch) ->
          Enum.find_value(ch, &find.(find, &1))

        _ ->
          nil
      end
    end

    assert {:computed_use, meta, [{:variable, _, "build_it"}, {:macro_input, [keyword: "mk"], []}]} =
             find.(find, node)

    assert Keyword.take(meta, [
             :keyword,
             :syntax_type,
             :syntax_fields,
             :syntax_repeated_fields,
             :syntax_field_types,
             :file
           ]) ==
             [
               keyword: "mk",
               syntax_type: "MkSyntax",
               syntax_fields: [],
               syntax_repeated_fields: [],
               syntax_field_types: %{},
               file: "nofile"
             ]
  end

  test "a computed use preserves matched hole inputs in segment order" do
    node =
      parse!("""
      mod M
        macro Mk
          syntax mk <first: Code> then <second: Code> computed by build_it
        fn f(a: Int, b: Int) -> Syntax = mk a then b
      """)

    find = fn find, n ->
      case n do
        {:function_def, meta, [body]} ->
          if Keyword.get(meta, :name) == "f", do: body

        {_t, _m, ch} when is_list(ch) ->
          Enum.find_value(ch, &find.(find, &1))

        _ ->
          nil
      end
    end

    assert {:computed_use, _, [{:variable, _, "build_it"}, {:macro_input, _, [first, second]}]} =
             find.(find, node)

    assert {:variable, _, "a"} = first
    assert {:variable, _, "b"} = second
  end

  test "computed rules derive a typed record name and ordered hole fields" do
    [rule] = rules(parse!("macro Mk\n  syntax mk <first: Code> then <second: Code> computed by build_it\n"))

    assert rule.syntax_type == "MkSyntax"
    assert rule.syntax_fields == ["first", "second"]
  end

  test "a plain `computed by` rule does not opt into direct (multi-arg) inputs" do
    [rule] = rules(parse!("macro Mk\n  syntax mk <x: Code> computed by build_it\n"))
    assert rule.kind == :computed
    assert Map.get(rule, :direct_inputs, false) == false
  end

  test "`computed directly by` opts the rule into direct (multi-arg) inputs" do
    [rule] = rules(parse!("macro Mk\n  syntax mk <x: Code> then <y: Code> computed directly by build_it\n"))
    assert rule.kind == :computed
    assert rule.direct_inputs == true
    # the opt-in must not disturb the rest of the rule
    assert rule.syntax_fields == ["x", "y"]
    assert {:variable, _, "build_it"} = rule.elab
  end

  test "the direct opt-in propagates to the deferred use-site node meta" do
    node =
      parse!(
        "mod M\n  macro Mk\n    syntax mk <x: Code> computed directly by build_it\n  fn f(a: Int) -> Syntax = mk a\n"
      )

    find = fn find, n ->
      case n do
        {:function_def, meta, [body]} -> if(to_string(Keyword.get(meta, :name)) == "f", do: body)
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end

    assert {:computed_use, meta, _} = find.(find, node)
    assert Keyword.get(meta, :direct_inputs) == true
  end
end

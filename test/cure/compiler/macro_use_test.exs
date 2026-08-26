# test/cure/compiler/macro_use_test.exs
defmodule Cure.Compiler.MacroUseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.ProvenanceFrame
  alias Cure.MetaAST.Metadata

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "two-phase parse still returns the macro def unchanged (no regression from single-pass)" do
    # A module with only a macro def: the harvest pass must not alter the
    # authoritative parse's output for the def itself.
    node = parse!("mod M\n  macro Now\n    syntax now becomes Clock.now()\n")
    # The macro def survives inside the module container.
    assert has_macro_def?(node)
  end

  defp has_macro_def?({:macro_def, _, _}), do: true
  defp has_macro_def?({_t, _m, children}) when is_list(children), do: Enum.any?(children, &has_macro_def?/1)
  defp has_macro_def?(_), do: false

  test "a zero-hole local macro use-site expands to its template" do
    # `now` is defined as a macro; a later `now` use-site expands to Clock.now().
    node =
      parse!("mod M\n  macro Now\n    syntax now becomes Clock.now()\n  fn f() = now\n")

    # Find `f`'s body; it must be the expanded Clock.now() call, not a bare
    # `{:variable, _, "now"}`.
    body = find_fn_body(node, "f")
    assert {:function_call, meta, _} = body
    # Clock.now() call shape
    assert Keyword.get(meta, :name) in ["Clock.now", "now"]
    refute match?({:variable, _, "now"}, body)
  end

  # Walk to a function_def's body by name.
  defp find_fn_body({:function_def, meta, [body]}, name) do
    if to_string(Keyword.get(meta, :name)) == name, do: body, else: nil
  end

  defp find_fn_body({_t, _m, children}, name) when is_list(children),
    do: Enum.find_value(children, &find_fn_body(&1, name))

  defp find_fn_body(_, _), do: nil

  defp slice(source, span), do: binary_part(source, span.start_byte, span.end_byte - span.start_byte)

  test "a one-hole local macro use-site binds the hole and substitutes it" do
    node =
      parse!("mod M\n  macro Every\n    syntax every <t: Code> becomes Timer.repeat(t)\n  fn f() = every 500\n")

    body = find_fn_body(node, "f")
    # every 500  ==>  Timer.repeat(500)
    assert {:function_call, meta, [arg]} = body
    assert Keyword.get(meta, :name) in ["Timer.repeat", "repeat"]
    assert {:literal, _, 500} = arg
  end

  test "template copies and substituted captures retain authored identity plus expansion provenance" do
    source =
      "mod M\n  macro Wrap\n    syntax wrap <x: Code> becomes id(x)\n  fn f() = wrap 42\n"

    node = parse!(source)
    {:container, _, [{:macro_def, _, [rule]}, _function]} = node
    body = find_fn_body(node, "f")

    {:function_call, body_meta, [{:literal, argument_meta, 42}]} = body
    template_info = rule.template |> elem(1) |> Metadata.source_info()
    body_info = Metadata.source_info(body_meta)
    argument_info = Metadata.source_info(argument_meta)

    assert %{template_info | provenance: body_info.provenance} == body_info
    assert slice(source, body_info.whole) == "id(x)"
    assert slice(source, argument_info.whole) == "42"

    assert [%ProvenanceFrame{} = body_frame] = body_info.provenance
    assert body_frame.name == "wrap"
    assert slice(source, body_frame.invocation) == "wrap 42"
    assert slice(source, body_frame.definition) == "syntax wrap <x: Code> becomes id(x)"

    assert [%ProvenanceFrame{} = argument_frame] = argument_info.provenance
    assert argument_frame.invocation == body_frame.invocation
    assert argument_frame.definition == body_frame.definition
  end

  test "nested macro provenance links the inner expansion to its parent invocation" do
    source = """
    mod M
      macro Inner
        syntax inner <x: Code> becomes id(x)
      macro Outer
        syntax outer <x: Code> becomes x
      fn f() = outer inner 1
    """

    body = source |> parse!() |> find_fn_body("f")
    {:function_call, meta, [_argument]} = body

    assert [inner, outer] = Metadata.source_info(meta).provenance
    assert inner.name == "inner"
    assert outer.name == "outer"
    assert inner.parent == %{kind: :macro_expansion, name: "outer", invocation: outer.invocation}
  end

  test "a two-literal-segment local macro use-site matches both literals" do
    # `say hello` has no hole: keyword "say", one literal segment "hello".
    # Without segment matching, "hello" is left unconsumed and becomes a stray
    # third sibling; segment matching must consume it so the container has
    # exactly the two real top-level forms (macro_def and fn f()).
    node =
      parse!("mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say hello\n")

    {:container, _meta, children} = node
    assert length(children) == 2
    body = find_fn_body(node, "f")
    assert {:function_call, meta, []} = body
    assert Keyword.get(meta, :name) in ["Clock.now", "now"]
  end

  test "repeated and optional grammar segments expand as list and single bindings" do
    source = """
    macro Grammar
      syntax list <item: Nat>... becomes item
      syntax maybe (<value: Nat>)? becomes value
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, rules}} = Parser.parse(tokens, emit_events: false)

    list_rule = Enum.find(rules, &(&1.keyword == "list"))
    assert {:ok, use_site} = Lexer.tokenize("list 1 2", emit_events: false)

    assert {:list, [generated_by: :macro_repeat], [_one, _two]} =
             [list_rule]
             |> Parser.expand_example(use_site)
             |> Metadata.strip_diagnostics()

    maybe_rule = Enum.find(rules, &(&1.keyword == "maybe"))
    assert {:ok, optional_use} = Lexer.tokenize("maybe (1)", emit_events: false)
    assert {:literal, _meta, 1} = Parser.expand_example([maybe_rule], optional_use)
  end

  test "a macro use-site literal-segment mismatch records a :macro_use_mismatch error" do
    # `say` expects the literal "hello" next; using it with "goodbye" must fail
    # the segment match and record an error rather than silently mis-expanding.
    {:ok, tokens} =
      Lexer.tokenize(
        "mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say goodbye\n",
        emit_events: false
      )

    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    assert Enum.any?(errors, &match?({:macro_use_mismatch, %{keyword: "say", expected: {:literal, "hello"}}}, &1))
  end

  test "a hole referenced inside a template match-arm's guard is substituted" do
    # `match_arm`'s pattern/guard live in the node's *meta* keyword list, not
    # its children list. subst_holes/2 must still reach them: a hole bound at
    # the use-site referenced from a guard must not survive expansion as a
    # dangling {:variable, _, "x"}.
    node =
      parse!(
        "mod M\n  macro Check\n    syntax check <x: Code> becomes match 1 { y when x -> 1, _ -> 0 }\n  fn f() = check true\n"
      )

    body = find_fn_body(node, "f")
    assert {:pattern_match, _, [_scrutinee, first_arm, _second_arm]} = body
    assert {:match_arm, arm_meta, _} = first_arm

    guard = Keyword.fetch!(arm_meta, :guard)
    refute match?({:variable, _, "x"}, guard)
    assert {:literal, _, true} = guard
  end
end

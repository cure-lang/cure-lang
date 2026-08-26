defmodule Cure.Compiler.TupleTypeSigilTest do
  @moduledoc """
  Tuple TYPES may be written with the `%[A, B]` sigil, mirroring the value tuple `%[a, b]` and removing the
  long-standing inconsistency where values were `%[a, b]` but their types were `(A, B)`. `%[A, B]` produces the
  same `{:tuple_type, …}` node as `Tuple(A, B)` (including optional per-position binders for a dependent
  telescope), so resolution, display, and codegen are unchanged; `(A, B)` still parses (now soft-deprecated).

  Original `%[A, B]` proposal: Aleksei Matiushkin (am-kantox); re-implemented here against the dependent parser.
  """
  use ExUnit.Case, async: true

  test "%[A, B] is a tuple type, identical to Tuple(A, B) in value and projection" do
    src = """
    mod M
      fn sig() -> %[Int, Bool] = %[1, true]
      fn named() -> Tuple(Int, Bool) = %[1, true]
      fn proj(p: %[Int, Bool]) -> Int = p.1
      fn three() -> %[Int, Int, Int] = %[1, 2, 3]
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    # %[A, B] and Tuple(A, B) produce the identical flat BEAM tuple.
    assert apply(mod, :sig, []) == {1, true}
    assert apply(mod, :sig, []) == apply(mod, :named, [])
    assert apply(mod, :proj, [{7, true}]) == 7
    assert apply(mod, :three, []) == {1, 2, 3}
  end

  test "%[A, B] accepts per-position binders like Tuple(x: A, B) — a dependent telescope" do
    # The binder syntax `x: T` is retained (same node as `Tuple(x: A, B)`); here the binder is unused, but the
    # form is what lets a later position depend on an earlier one.
    src = """
    mod D
      fn f(p: %[x: Int, Bool]) -> Int = p.1
      fn g(p: Tuple(x: Int, Bool)) -> Int = p.1
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :f, [{5, true}]) == 5
    assert apply(mod, :f, [{5, true}]) == apply(mod, :g, [{5, true}])
  end

  test "legacy (A, B) is definitionally and operationally identical to %[A, B]" do
    src = """
    mod L
      fn legacy() -> (Int, Bool) = %[7, true]
      fn canonical() -> %[Int, Bool] = %[7, true]
      fn first(p: (Int, Bool)) -> Int = p.1
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :legacy, []) == {7, true}
    assert apply(mod, :legacy, []) == apply(mod, :canonical, [])
    assert apply(mod, :first, [{9, false}]) == 9
  end

  test "legacy (A, B) emits registered E086 deprecation metadata" do
    Cure.Pipeline.Events.subscribe(:parser, :deprecation)
    src = "mod L\n  fn legacy(p: (Int, Bool)) -> Int = p.1\n"
    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, file: "legacy_tuple.cure", emit_events: false)
    assert {:ok, _ast} = Cure.Compiler.Parser.parse(tokens, file: "legacy_tuple.cure", emit_events: true)

    assert_receive {
      Cure.Pipeline.Events,
      :parser,
      :deprecation,
      %{code: "E086", arity: 2, message: message},
      %{file: "legacy_tuple.cure"}
    }

    assert message =~ "E-TYPE-TUPLE-PAREN"
    assert message =~ "%[A, B]"
    assert {:ok, explanation} = Cure.Compiler.Errors.explain("E086")
    assert explanation =~ "mechanical"
    assert Cure.Compiler.Errors.explain("e086") == {:ok, explanation}
  end

  test "canonical, grouped, and function-domain types do not emit E086" do
    Cure.Pipeline.Events.subscribe(:parser, :deprecation)

    for {name, source} <- [
          canonical: "mod C\n  fn f(p: %[Int, Bool]) -> Int = p.1\n",
          grouped: "mod G\n  fn f(p: (Int)) -> Int = p\n",
          function_domain: "mod F\n  fn apply(f: (Int, Bool) -> Int) -> Int = f(1, true)\n"
        ] do
      file = "#{name}.cure"
      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, file: file, emit_events: false)
      assert {:ok, _ast} = Cure.Compiler.Parser.parse(tokens, file: file, emit_events: true)
    end

    refute_receive {
      Cure.Pipeline.Events,
      :parser,
      :deprecation,
      %{code: "E086"},
      _meta
    }
  end

  test "tuple type spellings retain exact authored delimiters and argument ranges" do
    src = "mod M\n  typealias P = Tuple(Int, Bool)\n  typealias Q = %[Int, Bool]\n"
    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, file: "tuple_meta.cure", emit_events: false)
    assert {:ok, {:container, _, declarations}} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

    infos =
      Enum.map(declarations, fn {:type_annotation, _, [{:tuple_type, meta, _}]} ->
        Keyword.fetch!(meta, :source_info)
      end)

    assert [named, sigil] = infos

    assert {named.whole.start_column, named.whole.end_column} == {17, 33}
    assert {named.name.start_column, named.name.end_column} == {17, 22}
    assert {named.opener.start_column, named.opener.end_column} == {22, 23}
    assert {named.closer.start_column, named.closer.end_column} == {32, 33}
    assert Enum.map(named.arguments, &{&1.start_column, &1.end_column}) == [{23, 26}, {28, 32}]

    assert {sigil.whole.start_column, sigil.whole.end_column} == {17, 29}
    assert sigil.name == nil
    assert {sigil.opener.start_column, sigil.opener.end_column} == {17, 19}
    assert {sigil.closer.start_column, sigil.closer.end_column} == {28, 29}
  end
end

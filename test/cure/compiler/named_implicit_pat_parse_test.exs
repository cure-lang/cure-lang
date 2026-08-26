defmodule Cure.Compiler.NamedImplicitPatParseTest do
  @moduledoc """
  Surface syntax for named-implicit dot patterns (`{ name = <expr> }`) — the
  Lean/Idris-style annotation of a constructor's erased implicit index in a
  pattern-argument position, e.g. `vcons({k = .m}, h, r)`.

  Parsing a `{ IDENT = … }` in expression-prefix position produces a canonical
  `{:named_implicit_pat, [name: name, …], [inner_expr]}` node (the annotated name
  is data in `meta[:name]`, the inner expression the single child); the inner
  expression is parsed with the full grammar, so a leading `.` yields a
  `{:forced_pattern,…}`.
  Using a named-implicit OUTSIDE a pattern is rejected at elaboration with
  `{:named_implicit_not_in_pattern, _}`.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp diagnostic(source, file, matcher) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    error = Enum.find(errors, matcher)
    assert error
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  # (a) `{k = .m}` as a ctor arg parses to a named-implicit whose inner is a
  #     bare-identifier forced pattern.
  test "(a) `vcons({k = .m}, h, r)` parses the named-implicit dot pattern" do
    ast = parse!("match v { vcons({k = .m}, h, r) -> h }")
    assert {:pattern_match, _, [_scrutinee, arm]} = ast
    assert {:match_arm, ameta, _body} = arm
    assert {:function_call, _cmeta, [arg0, arg1, arg2]} = Keyword.get(ameta, :pattern)
    assert {:named_implicit_pat, nmeta, [inner]} = arg0
    assert Keyword.get(nmeta, :name) == "k"
    assert {:forced_pattern, _, [{:variable, _, "m"}]} = inner
    assert {:variable, _, "h"} = arg1
    assert {:variable, _, "r"} = arg2
  end

  # (b) The inner expression uses the full grammar: `{k = .(Z())}` parses the
  #     compound forced pattern `.(Z())` as a constructor application.
  test "(b) `{k = .(Z())}` parses the compound forced inner" do
    ast = parse!("match v { vcons({k = .(Z())}, h, r) -> h }")
    assert {:pattern_match, _, [_scrutinee, arm]} = ast
    assert {:match_arm, ameta, _body} = arm
    assert {:function_call, _cmeta, [arg0 | _]} = Keyword.get(ameta, :pattern)
    assert {:named_implicit_pat, nmeta, [inner]} = arg0
    assert Keyword.get(nmeta, :name) == "k"
    assert {:forced_pattern, _, [{:function_call, zmeta, []}]} = inner
    assert Keyword.get(zmeta, :name) == "Z"
  end

  # (c) NEGATIVE: a named-implicit used as an ordinary expression (a function
  #     body, not a pattern) is rejected at ELABORATION time. Parsing succeeds by
  #     design, so this drives the fixture through the full pipeline.
  test "(c) a named-implicit in ordinary expression position is rejected" do
    src = """
    type Nat = Z | S(Nat)
    fn f() -> Nat = {k = .m}
    """

    assert {:error, {:source_context, {:named_implicit_not_in_pattern, _meta}, _}} = Program.elaborate(src)
  end

  test "a missing equals sign labels the opener and binder and offers an exact edit" do
    source = "match v { vcons({k .m}, h, r) -> h }"

    {error, {diagnostic, registry}} =
      diagnostic(source, "implicit_assign.cure", fn
        {:declaration_separator_missing, %{kind: :named_implicit_pattern_assign_missing}} -> true
        _ -> false
      end)

    assert {:declaration_separator_missing, %{kind: :named_implicit_pattern_assign_missing, binder: "k", observed: "."}} =
             error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NAMED IMPLICIT PATTERN NEEDS AN EQUALS SIGN [E094] ----- implicit_assign.cure

             The named implicit pattern for `k` needs `=` before the pattern that fixes its
             value.

             A valid continuation here starts with '='.

             at implicit_assign.cure:1:20
             1 | match v { vcons({k .m}, h, r) -> h }
               |                 -- ^ this named implicit pattern starts here; this is the implicit binder; insert `=` before this implicit pattern

             Hint: Insert `=` before the implicit pattern
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "= ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 20}
    assert insertion.start_byte == insertion.end_byte
  end

  test "a missing closing brace is inserted before the next constructor argument" do
    source = "match v { vcons({k = .m, h, r) -> h }"

    {error, {diagnostic, registry}} =
      diagnostic(source, "implicit_close.cure", fn
        {:container_elements_syntax, %{container: :named_implicit_pattern}} -> true
        _ -> false
      end)

    assert {:container_elements_syntax,
            %{
              kind: :container_unclosed,
              container: :named_implicit_pattern,
              binder: "k",
              observed: ","
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NAMED IMPLICIT PATTERN IS NOT CLOSED [E094] ------------- implicit_close.cure

             The named implicit pattern for `k` reaches the end of its value without the
             closing '}'.

             at implicit_close.cure:1:24
             1 | match v { vcons({k = .m, h, r) -> h }
               |                 --    -^ this named implicit pattern starts here; this is the implicit binder; the implicit pattern ends here; close this named implicit pattern with `}`

             Hint: Insert `}` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "}", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 24}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => "}", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 23},
             "end" => %{"line" => 0, "character" => 23}
           }
  end
end

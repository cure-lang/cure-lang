# test/cure/compiler/macro_example_check_test.exs
defmodule Cure.Compiler.MacroExampleCheckTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp macro_def!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)

    find = fn find, n ->
      case n do
        {:macro_def, _, _} = m -> m
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end

    find.(find, ast)
  end

  test "expand_example runs an example's captured use-site through the rule" do
    {:macro_def, _, rules} =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(500)\n"
      )

    rule = Enum.find(rules, &(&1[:kind] == :syntax))
    [ex] = rule.examples

    result = Parser.expand_example(rules, ex.use_site)
    # every 500  ==>  Timer.repeat(500)
    assert {:function_call, meta, [{:literal, _, 500}]} = result
    assert Keyword.get(meta, :name) == "Timer.repeat"
  end

  alias Cure.Compiler.{MacroValidate, Errors}
  alias Cure.Elab.Program

  test "an example whose expansion matches its pin checks clean" do
    md =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(500)\n"
      )

    assert :ok = MacroValidate.check_examples(md)
  end

  test "an example whose pin is WRONG is example_mismatch" do
    md =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(999)\n"
      )

    assert {:error, {:example_mismatch, [m]}} = MacroValidate.check_examples(md)
    assert m.keyword == "every"

    rendered = Errors.format_error({:example_mismatch, [m]}, "m.cure")
    assert rendered =~ "every"
    refute rendered =~ ":example_mismatch"
  end

  test "a matching example modulo source position still checks clean (α: positions ignored)" do
    md =
      macro_def!("macro M\n  syntax m <x: Code> becomes f(x)\n    example m 1 expands f(1)\n")

    assert :ok = MacroValidate.check_examples(md)
  end

  test "example validation is invariant under recursive source decoration" do
    md =
      macro_def!("macro M\n  syntax m <x: Code> becomes f(x)\n    example m 1 expands f(1)\n")

    decorated = Cure.MetaAST.SourceDecorator.decorate(md)
    stripped = Cure.MetaAST.Metadata.strip_diagnostics(decorated)

    assert :ok = MacroValidate.check_examples(md)
    assert :ok = MacroValidate.check_examples(decorated)
    assert :ok = MacroValidate.check_examples(stripped)
  end

  test "a correct example pinning a <fresh> BINDER (not just a reference) checks clean" do
    # The template's `<fresh h>` marker sits in BINDER position (the LHS of
    # `let`). Its own {:fresh_name, meta, name} node was parsed with only
    # line/col in its meta (no `scope: :local` -- that key only gets attached
    # by the ordinary-identifier parse path, e.g. `variable/1`). freshen/2's
    # apply_freshening reuses that meta verbatim when rewriting the marker to
    # {:variable, meta, gensym}, so the *binder* occurrence in the actual
    # expansion has no `scope` key at all, while the hand-written pin's `h`
    # (an ordinary identifier) always carries `scope: :local` from normal
    # parsing. Comparing full variable meta (as normalize/1 did) makes every
    # <fresh>-as-binder example spuriously mismatch, even when perfectly
    # pinned -- this defeats the headline <fresh> self-proving case.
    md =
      macro_def!(
        "macro FreshBinder\n  syntax fb <e: Code> becomes let <fresh h> = 100 in e + h\n    example fb 1 expands let h = 100 in 1 + h\n"
      )

    assert :ok = MacroValidate.check_examples(md)
  end

  test "an example whose use-site has unconsumed trailing tokens is example_mismatch, not a false :ok" do
    # The rule has a single hole and no trailing literal segment, so
    # match_segments is satisfied the moment the hole is bound -- it does not
    # require the use-site's captured tokens to be fully consumed. Before the
    # fix, expand_example silently dropped "wrong garbage" (leftover after the
    # hole) and returned the same AST as a clean `every2 500` use-site, so a
    # broken/garbage-suffixed example checked :ok instead of being caught.
    md =
      macro_def!(
        "macro Every2\n  syntax every2 <t: Duration> becomes Timer.repeat(t)\n    example every2 500 wrong garbage expands Timer.repeat(500)\n"
      )

    assert {:error, {:example_mismatch, [m]}} = MacroValidate.check_examples(md)
    assert m.keyword == "every2"
  end

  test "a computed example executes against the module environment" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        syntax mk <x: Code> computed by build_it
          example mk 1 expands 1

      fn build_it(a: MkSyntax) -> Syntax = a.x
    """

    md = macro_def!(source)
    assert {:ok, env} = Program.elaborate(source)
    assert :ok = MacroValidate.check_computed_examples(md, env)
  end

  test "a computed example with the wrong pin is example_mismatch" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        syntax mk <x: Code> computed by build_it
          example mk 1 expands 2

      fn build_it(a: MkSyntax) -> Syntax = a.x
    """

    md = macro_def!(source)
    env_source = String.replace(source, "example mk 1 expands 2", "example mk 1 expands 1")
    assert {:ok, env} = Program.elaborate(env_source)
    assert {:error, {:example_mismatch, [m]}} = MacroValidate.check_computed_examples(md, env)
    assert m.keyword == "mk"
  end

  test "a computed example reports an elab execution failure" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        syntax mk computed by build_it
          example mk expands 1

      fn build_it(a: MkSyntax) -> Int = 0
    """

    md = macro_def!(source)

    env_source = """
    mod M
      use Std.Syntax

      rec MkSyntax
        x: Syntax

      fn build_it(a: MkSyntax) -> Int = 0
    """

    assert {:ok, env} = Program.elaborate(env_source)

    assert {:error, {:computed_example_error, [failure]}} =
             MacroValidate.check_computed_examples(md, env)

    assert failure.keyword == "mk"
    rendered = Errors.format_error({:computed_example_error, [failure]}, "m.cure")
    assert rendered =~ "computed macro example failed"
    assert rendered =~ "mk"

    assert {:error,
            {:source_context, {:computed_example_error, [%{keyword: "mk", source_span: %Cure.Diagnostic.Span{}}]},
             %{span: %Cure.Diagnostic.Span{}, rule_spans: [%Cure.Diagnostic.Span{}]}} = reason} =
             MacroValidate.check_program(md, env)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "computed_example.cure", source)

    assert Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- COMPUTED MACRO EXAMPLE FAILED [E092] ------------------ computed_example.cure

             A computed macro example failed while being checked: mk.

             at computed_example.cure:6:7
             5 |     syntax mk computed by build_it
               |     ------------------------------ this rule owns the failing example
             6 |       example mk expands 1
               |       ^^^^^^^^^^^^^^^^^^^^ this computed example could not be checked

             Hint: Fix the computed expander or its worked example
             """)

    assert Cure.Diagnostic.Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 5, "character" => 6},
             "end" => %{"line" => 5, "character" => 26}
           }
  end
end

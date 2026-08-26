defmodule Cure.Migrate.RuleRegistryTest do
  use ExUnit.Case, async: true
  alias Cure.Migrate
  alias Cure.Migrate.Rule

  # Synthetic rules local to this test. They prove the ordered-fold mechanism
  # (a rule's rewrite is threaded to the next rule, and a `{:rewrite, _}` return
  # produces one warning) without depending on Tasks 8/9's real seed rules,
  # which do not exist yet at this point in the plan.
  #
  # NB: for a multi-item file, `Parser.parse/2` returns a `{:block, meta, exprs}`
  # node -- NOT a bare list -- so these rules append to the block's children
  # rather than to the AST value itself. (The plan's original draft assumed a
  # list and did `ast ++ [marker]`; that would crash on the real tuple AST. This
  # is the only deviation from the plan's verbatim test and it strengthens, not
  # weakens, the assertion: a second rule now proves the fold threads output.)
  @marker1 {:literal, [subtype: :string, injected: 1], "marker-1"}
  @marker2 {:literal, [subtype: :string, injected: 2], "marker-2"}

  defp append_marker_rule do
    %Rule{
      id: :W_test_append_marker,
      description: "test-only: appends marker-1 to the top-level block",
      phase: :syntactic,
      tier: :machine,
      since: "2026",
      detect_and_rewrite: fn {:block, m, exprs}, _ctx ->
        {:rewrite, {:block, m, exprs ++ [@marker1]}}
      end,
      warning_template: "marker-1 appended"
    }
  end

  # Only rewrites when it SEES marker-1 already present -> proves it received the
  # first rule's output, i.e. the fold threads rewrites in declaration order.
  defp require_marker_rule do
    %Rule{
      id: :W_test_require_marker,
      description: "test-only: appends marker-2 iff marker-1 is present",
      phase: :syntactic,
      tier: :machine,
      since: "2026",
      detect_and_rewrite: fn {:block, m, exprs}, _ctx ->
        if @marker1 in exprs do
          {:rewrite, {:block, m, exprs ++ [@marker2]}}
        else
          :no_change
        end
      end,
      warning_template: "marker-2 appended"
    }
  end

  defp parse!(src, file) do
    {:ok, toks} = Cure.Compiler.Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(toks, file: file, emit_events: false)
    ast
  end

  test "run threads rules as an ordered fold and collects one warning per rewrite" do
    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n", "r.cure")
    {:block, m, exprs} = ast

    {new_ast, warnings} =
      Migrate.run(ast, file: "r.cure", rules: [append_marker_rule(), require_marker_rule()])

    # rule 2 fired only because it saw rule 1's appended marker -> ordered fold
    assert new_ast == {:block, m, exprs ++ [@marker1, @marker2]}
    assert Enum.any?(warnings, &(&1.rule == :W_test_append_marker))
    assert Enum.any?(warnings, &(&1.rule == :W_test_require_marker))
  end

  test "a rule returning :no_change contributes no warning and leaves the AST untouched" do
    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n", "n.cure")

    # require_marker_rule alone sees no marker-1 -> :no_change
    {new_ast, warnings} = Migrate.run(ast, file: "n.cure", rules: [require_marker_rule()])

    assert new_ast == ast
    assert warnings == []
  end
end

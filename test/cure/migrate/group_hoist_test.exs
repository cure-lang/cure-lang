defmodule Cure.Migrate.GroupHoistTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate

  defp reparses?(src, file) do
    with {:ok, toks} <- Lexer.tokenize(src, file: file, emit_events: false),
         {:ok, _ast} <- Parser.parse(toks, file: file, emit_events: false) do
      true
    else
      _ -> false
    end
  end

  defp migrate(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {new_ast, warns} = Migrate.run(Trivia.attach(ast, trivia), file: file)
    {Printer.quoted_to_string(new_ast), warns}
  end

  # Drives the real `cure migrate` path: `run_to_fixpoint` threads the AST
  # between passes WITHOUT reparsing, so an AST-level non-idempotent rewrite
  # corrupts here even when a single `run/2` pass (or a reparse-between-passes
  # loop) looks correct.
  defp migrate_fixpoint(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {:ok, final, _warns} = Migrate.run_to_fixpoint(Trivia.attach(ast, trivia), edition: "2026")
    Printer.quoted_to_string(final)
  end

  test "in-body @group is hoisted to directly above mod and output reparses" do
    {out, warns} = migrate("mod M\n@group(:core)\nfn f() -> Int = 1\n", "a.cure")
    # decorator now appears before `mod`, and not after it
    assert out =~ ~r/@group\(:core\)\s*\n\s*mod\s+M/
    refute out =~ ~r/mod\s+M[\s\S]*@group\(:core\)/
    warning = Enum.find(warns, &(&1.rule == :W_group_hoist))
    assert %Cure.Diagnostic.Span{start_line: 2, start_column: 2, end_column: 7} = warning.span
    assert reparses?(out, "a.cure")
  end

  test "a file already in above-mod form is unchanged and does not warn" do
    src = "@group(:core)\nmod M\nfn f() -> Int = 1\n"
    {out, warns} = migrate(src, "b.cure")
    assert out =~ ~r/@group\(:core\)\s*\n\s*mod\s+M/
    refute Enum.any?(warns, &(&1.rule == :W_group_hoist))
  end

  test "a comment on the @group line travels with the hoisted decorator (never dropped or orphaned)" do
    {out, _} = migrate("mod M\n@group(:core)  # grouping tag\nfn f() -> Int = 1\n", "c.cure")
    # the comment survives...
    assert out =~ "grouping tag"
    # ...and rides above mod with the decorator, not left stranded below it
    assert out =~ ~r/@group\(:core\).*grouping tag[\s\S]*mod\s+M/
    refute out =~ ~r/mod\s+M[\s\S]*grouping tag/
    assert reparses?(out, "c.cure")
  end

  test "a @group under a later module hoists above THAT module, not the first" do
    # Multi-module files parse and compile; migrate runs on source syntactically.
    # The `@group(:core)` belongs to `Second` (it trails Second's `mod`), so it
    # must hoist above `Second`. The rule keyed every mover to the FIRST module,
    # silently re-associating the group with `First` — a semantic corruption that
    # `verify/3` accepts (the output reparses, comments preserved).
    src = "mod First\nfn f() -> Int = 1\nmod Second\n@group(:core)\nfn g() -> Int = 2\n"
    {out, warns} = migrate(src, "multi.cure")

    assert Enum.any?(warns, &(&1.rule == :W_group_hoist))
    # @group sits directly above Second...
    assert out =~ ~r/@group\(:core\)\s*\n\s*mod\s+Second/
    # ...and NOT above First (no @group between the start and `mod First`).
    refute out =~ ~r/@group\(:core\)[\s\S]*mod\s+First/
    assert reparses?(out, "multi.cure")
  end

  test "each @group hoists above its own module in a two-module, two-group file" do
    src =
      "mod First\n@group(:a)\nfn f() -> Int = 1\nmod Second\n@group(:b)\nfn g() -> Int = 2\n"

    {out, _} = migrate(src, "two.cure")

    assert out =~ ~r/@group\(:a\)\s*\n\s*mod\s+First/
    assert out =~ ~r/@group\(:b\)\s*\n\s*mod\s+Second/
    # neither group landed above the wrong module (both stacked above First was
    # the bug symptom)
    refute out =~ ~r/@group\(:b\)[\s\S]*mod\s+First/
    assert reparses?(out, "two.cure")
  end

  test "under run_to_fixpoint a later module's @group hoists above THAT module, not the first" do
    # `cure migrate` runs `run_to_fixpoint`, which threads the AST between passes
    # WITHOUT reparsing. `@group(:core)` is in-body of `Second`; pass 1 correctly
    # hoists it directly above `Second`, but the AST-level decorator now sits
    # after `mod First`, so the nearest-preceding-module heuristic re-flags it on
    # pass 2 and drags it above `First`. Single-pass `run/2` looks right; the
    # fixpoint the CLI actually uses corrupts.
    src = "mod First\nfn f() -> Int = 1\nmod Second\n@group(:core)\nfn g() -> Int = 2\n"
    out = migrate_fixpoint(src, "fp.cure")

    # @group ends up directly above Second...
    assert out =~ ~r/@group\(:core\)\s*\n+\s*mod\s+Second/
    # ...and is NOT dragged above First.
    refute out =~ ~r/@group\(:core\)[\s\S]*mod\s+First/
    assert reparses?(out, "fp.cure")
  end

  test "cure migrate is text-idempotent — a hoisted @group does not shift whitespace on re-run" do
    # `cure migrate` reparses its own output on a second run. The printer's
    # top-level rule blanks every item, so a hoisted @group *standalone sibling*
    # rendered `@group(:g)\n\nmod A` — but on reparse the decorator is absorbed
    # into the module container and re-renders tight (`@group(:g)\nmod A`). So a
    # second `cure migrate` silently changed whitespace: the tool advertises
    # idempotence but was not text-idempotent. A decorator must hug the item it
    # decorates, matching the absorbed form.
    src = "mod A\nfn a() -> Int = 1\n@group(:g)\n"
    out1 = migrate_fixpoint(src, "ti.cure")
    out2 = migrate_fixpoint(out1, "ti.cure")
    assert out1 == out2

    # and the same for two stacked groups on one module
    src2 = "mod A\nfn a() -> Int = 1\n@group(:g1)\n@group(:g2)\n"
    s1 = migrate_fixpoint(src2, "ti2.cure")
    s2 = migrate_fixpoint(s1, "ti2.cure")
    assert s1 == s2
  end

  test "under run_to_fixpoint each module's @group stays above its own module" do
    # Two in-body groups. The non-idempotent rewrite walked every non-first-module
    # group one module toward the top each pass, so both ended stacked above the
    # FIRST module.
    src =
      "mod First\n@group(:a)\nfn f() -> Int = 1\nmod Second\n@group(:b)\nfn g() -> Int = 2\n"

    out = migrate_fixpoint(src, "fp2.cure")

    assert out =~ ~r/@group\(:a\)\s*\n+\s*mod\s+First/
    assert out =~ ~r/@group\(:b\)\s*\n+\s*mod\s+Second/
    # @group(:b) must not have been dragged above First
    refute out =~ ~r/@group\(:b\)[\s\S]*mod\s+First/
    assert reparses?(out, "fp2.cure")
  end
end

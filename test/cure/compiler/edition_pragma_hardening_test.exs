# Hardening tests for the @edition pragma placement/validation guard.
# Red-green coverage for audit findings F1 (decorator-led bypass), F3 (multiple
# pragmas), and F7 (malformed value silently accepted).
defmodule Cure.Compiler.EditionPragmaHardeningTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse(src) do
    {:ok, toks} = Lexer.tokenize(src, file: "t.cure", emit_events: false)
    Parser.parse(toks, file: "t.cure", emit_events: false)
  end

  defp placement_error?(errors),
    do: Enum.any?(errors, &match?({:edition_pragma_placement, %{span: %Cure.Diagnostic.Span{}}}, &1))

  defp malformed_error?(errors),
    do: Enum.any?(errors, &match?({:edition_pragma_malformed, %{span: %Cure.Diagnostic.Span{}}}, &1))

  defp unknown_error?(errors),
    do: Enum.any?(errors, &match?({:edition_pragma_unknown, %{span: %Cure.Diagnostic.Span{}}}, &1))

  # F1 — a decorator-led definition (@extern/@derive/@builtin...) is substantive;
  # a later @edition is therefore misplaced and must be a hard error.
  test "F1: @edition after a @derive-led definition is a placement error" do
    src = "@derive(Show)\nrec R\n  x: Int\n@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n"
    assert {:error, errors} = parse(src)
    assert placement_error?(errors)
  end

  test "F1: @edition after an @extern-led fn is a placement error" do
    src =
      "@extern(:erlang, :length, 1)\nfn len(x: Int) -> Int\n@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n"

    assert {:error, errors} = parse(src)
    assert placement_error?(errors)
  end

  # F3 — only the first @edition can be file-leading; a second is misplaced.
  test "F3: a second @edition pragma is a placement error" do
    src = "@edition(\"2026\")\n@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n"
    assert {:error, errors} = parse(src)
    assert placement_error?(errors)
  end

  # F7 — the pragma argument must be a 4-digit year string; anything else errors
  # rather than silently falling back to the default edition.
  test "F7: an unquoted-integer @edition value is a malformed-pragma error" do
    src = "@edition(2026)\nmod M\n  fn f() -> Int = 1\n"
    assert {:error, errors} = parse(src)
    assert malformed_error?(errors)
  end

  test "F7: a non-year string @edition value is a malformed-pragma error" do
    src = "@edition(\"abc\")\nmod M\n  fn f() -> Int = 1\n"
    assert {:error, errors} = parse(src)
    assert malformed_error?(errors)
  end

  test "F7: a bare @edition with no argument is a malformed-pragma error" do
    src = "@edition\nmod M\n  fn f() -> Int = 1\n"
    assert {:error, errors} = parse(src)
    assert malformed_error?(errors)
  end

  # F-A LIVE (audit iteration 3): a well-formed but UNKNOWN edition (`"9999"` is
  # not on the allow-list) must fail loudly at parse — spec §3.1 ("a typo'd
  # edition must fail loudly") / §3.3 ("its argument is validated as an edition").
  # The build pipeline (compiler.ex lex/parse) never calls Cure.Edition.resolve,
  # so the parser's format-only check let an unknown edition compile silently.
  # This is a DISTINCT error from :edition_pragma_malformed (the value is a valid
  # 4-digit year in shape, just not a minted edition).
  test "F-A: a well-formed but unknown @edition value is an unknown-edition error" do
    src = "@edition(\"9999\")\nmod M\n  fn f() -> Int = 1\n"
    assert {:error, errors} = parse(src)
    assert unknown_error?(errors)
    refute malformed_error?(errors)
  end

  # F1 (audit iteration 4) — the pre-parse resolver (Cure.Edition.pragma_edition)
  # reads the pragma with a single-line regex, so a pragma split across lines is
  # invisible to it (returns nil → resolve falls back to project/default). The
  # token-based parser must NOT honour a form the resolver can't see, or the two
  # disagree: the file would LEX under the resolver's (default) edition while the
  # parser accepts a different DECLARED edition — a silent wrong-edition compile
  # once a second edition is minted. The canonical pragma is a single line, so a
  # multi-line pragma is a malformed-pragma error.
  test "F1: a multi-line @edition pragma is rejected (parser agrees with the resolver)" do
    src = "@edition(\n\"2026\")\nmod M\n  fn f() -> Int = 1\n"
    # The pre-parse resolver cannot see a multi-line pragma:
    assert Cure.Edition.pragma_edition(src) == nil
    # ...so the parser must reject it rather than silently honour a declared edition
    # the resolver never selected for lexing:
    assert {:error, errors} = parse(src)
    assert malformed_error?(errors)
  end

  # Guard against over-correction: the happy path must still parse.
  test "a well-placed valid @edition still parses cleanly" do
    assert {:ok, _ast} = parse("@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n")
  end
end

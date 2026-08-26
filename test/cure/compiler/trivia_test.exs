defmodule Cure.Compiler.TriviaTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Lexer

  test "lexer collects every comment and blank run as positioned trivia" do
    src = """
    mod M

    # leading comment
    fn f() -> Int = 1  # trailing comment
    """

    {:ok, _tokens, trivia} = Lexer.tokenize(src, file: "t.cure", trivia: true)

    texts = for {:comment, t, _l, _c} <- trivia, do: String.trim(t)
    assert "leading comment" in texts
    assert "trailing comment" in texts
    assert Enum.any?(trivia, &match?({:blank, _, _}, &1))
  end

  test "a blank line that contains only indentation whitespace still counts as blank" do
    # Pins the fix for reusing lex_indentation/1's own blank-line branch
    # (lexer.ex:210-231, which strips leading whitespace via measure_indent/1
    # BEFORE checking for end-of-line) rather than a fresh "newline-only line"
    # definition that would miss this case. The blank line between `x` and `y`
    # below has two leading spaces (mirroring the block's own indent), which a
    # naive "line is exactly empty" check would fail to classify as blank.
    src = "mod M\nfn f() -> Int =\n  let x = 1\n  \n  x\n"

    {:ok, _tokens, trivia} = Lexer.tokenize(src, file: "t2.cure", trivia: true)

    assert Enum.any?(trivia, &match?({:blank, _, _}, &1)),
           "a whitespace-only blank line was not collected as trivia: #{inspect(trivia)}"
  end

  # ── Attachment pass (Task 5) ─────────────────────────────────────────────

  alias Cure.Compiler.{Parser, Trivia}
  alias Cure.Compiler.Trivia.UnplacedTriviaError

  defp attach(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    Trivia.attach(ast, trivia)
  end

  test "leading comment attaches to the following definition" do
    ast = attach("mod M\n\n# doc\nfn f() -> Int = 1\n", "a.cure")

    leadings =
      ast
      |> collect_meta(:leading)
      |> List.flatten()
      |> Enum.filter(&match?({kind, _, _, _} when kind in [:comment, :doc_comment], &1))
      |> Enum.map(&elem(&1, 1))
      |> Enum.map(&String.trim/1)

    assert "doc" in leadings
  end

  test "comment after last statement of a nested block lands in that block's trailer" do
    src = """
    mod M
    fn f() -> Int =
      let x = 1
      x
      # nested trailer
    """

    ast = attach(src, "b.cure")

    trailers =
      ast |> collect_meta(:trailer) |> List.flatten() |> Enum.map(&elem(&1, 1)) |> Enum.map(&String.trim/1)

    assert "nested trailer" in trailers
  end

  test "trailing comment on a map-literal pair attaches correctly (pair nodes carry no line/col of their own)" do
    # Exercises the recursive-children span fallback: `:pair` (parser.ex:932,
    # 944, 954) has empty meta, so its effective end must be derived from its
    # value child's position, not read off the pair node itself.
    src = "mod M\nfn f() -> Int =\n  let m = %{x: 1, y: 2}  # tail comment\n  1\n"
    ast = attach(src, "pair.cure")

    trailings =
      ast |> collect_meta(:trailing) |> List.flatten() |> Enum.map(&elem(&1, 1)) |> Enum.map(&String.trim/1)

    assert "tail comment" in trailings
  end

  test "a comment near a lambda with a positionless param leaf does not crash attach/2" do
    # Exercises the transparent-leaf fallback: a lambda `:param` node
    # (parser.ex:2648, `{:param, [], name}`) has no meta AND no children list
    # (its 3rd element is a bare string), so it contributes no position of its
    # own and must not be recursed into.
    src = "mod M\nfn f() -> Int =\n  let g = fn (x) -> x\n  # after the let\n  g(1)\n"
    ast = attach(src, "lambda.cure")

    texts =
      ((ast |> collect_meta(:trailer) |> List.flatten()) ++ (ast |> collect_meta(:leading) |> List.flatten()))
      |> Enum.map(&elem(&1, 1))
      |> Enum.map(&String.trim/1)

    assert "after the let" in texts
  end

  test "attachment is total: an item that cannot be placed raises, never drops" do
    # `Trivia.attach([], ...)` is a direct unit test of attach/2's recursive
    # contract: zero nodes exist for the item to become a `:leading` on, and
    # there is no container node's `meta` to hold it as a `:trailer` either --
    # genuinely nothing to attach to, hence the raise. (A real Parser.parse/2
    # never returns a bare list at top level, so this is defense-in-depth.)
    assert_raise UnplacedTriviaError, fn ->
      Trivia.attach([], [{:comment, "orphan", 1, 1}])
    end
  end

  alias Cure.Compiler.Printer

  defp reprint(src) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: "d.cure", trivia: true)
    {:ok, ast} = Parser.parse(toks, file: "d.cure", emit_events: false)
    ast |> Trivia.attach(trivia) |> Printer.quoted_to_string()
  end

  # A fenced doc comment with no blank body line (`### tail\n###`) carries a
  # trailing "\n" in its token text (the opening-tail prepend over an empty
  # body). Splitting on "\n" naively yielded a spurious empty `## ` line, which
  # reparses as an extra doc comment the source never had. The reprint must not
  # invent that empty line, and formatting must be idempotent.
  test "a fenced doc comment with no blank body line does not gain a spurious empty ## line" do
    out = reprint("### tail\n###\nmod M\n  fn f() -> Int = 1\n")

    refute out |> String.split("\n") |> Enum.any?(&(String.trim_trailing(&1) == "##")),
           "reprint invented an empty `## ` doc line: #{inspect(out)}"

    assert reprint(out) == out, "doc-comment reprint is not idempotent"
  end

  # Two-or-more trailing blank body lines leave two-or-more trailing "\n" in the
  # token text. Dropping only ONE (String.replace_suffix) still leaves a trailing
  # "\n", so the split yields a spurious empty `## ` line — the same defect as the
  # single-newline case, one blank line deeper. Trailing blanks carry no meaning
  # in a doc comment, so every trailing newline must be dropped.
  test "a fenced doc comment with multiple trailing blank body lines gains no spurious ## line" do
    out = reprint("### tail\nline1\n\n\n###\nmod M\n  fn f() -> Int = 1\n")

    refute out |> String.split("\n") |> Enum.any?(&(String.trim_trailing(&1) == "##")),
           "reprint invented an empty `## ` doc line: #{inspect(out)}"

    assert reprint(out) == out, "doc-comment reprint is not idempotent"
  end

  # A function call's argument list is the one comma-separated construct whose
  # delimiters can span newlines and still reparse, so a comment CAN legally sit
  # inside it. The single-line span form has nowhere to put such a comment and
  # dropped it silently — a lossless-reprint violation (and, in `cure migrate`,
  # a spurious `:comment_dropped` rejection). A leading comment on an argument
  # must survive the round-trip and reprint idempotently.
  test "a leading comment on a call argument survives the reprint" do
    src = "mod M\n  fn g(a: Int, b: Int) -> Int = a\n  fn f() -> Int = g(\n    # keep me\n    1,\n    2)\n"
    out = reprint(src)

    assert out =~ "keep me", "call-argument comment was dropped: #{inspect(out)}"
    assert reparses?(out), "reprint no longer parses: #{inspect(out)}"
    assert reprint(out) == out, "call-argument-comment reprint is not idempotent"
  end

  # A trailing comment attaches to the PRECEDING argument, so the separating
  # comma must be emitted before the comment — otherwise the `#` swallows the
  # comma and the argument list reparses one element short.
  test "a trailing comment on a call argument survives without eating the comma" do
    src = "mod M\n  fn g(a: Int, b: Int) -> Int = a\n  fn f() -> Int = g(1, # inline\n    2)\n"
    out = reprint(src)

    assert out =~ "inline", "trailing call-argument comment was dropped: #{inspect(out)}"
    assert reparses?(out), "reprint no longer parses (comma likely eaten): #{inspect(out)}"
    assert reprint(out) == out, "trailing-comment reprint is not idempotent"
  end

  # A comment between `=` and an inline body attaches as a LEADING comment on the
  # body. Rendered inline (`= # note`) the `#` comments out the body, so the
  # printer shoved the body to the next line and the comment drifted — from
  # body-leading, to `=`-trailing, to fn-leading — across successive reprints
  # (non-idempotent, and a relocation `cure fmt` must never do). When the body
  # carries a leading comment the whole body must break to the next line, exactly
  # as the source wrote it.
  test "a comment between = and an inline body round-trips idempotently without relocating" do
    src = "mod M\n  fn f() -> Int =\n    # note\n    1\n"
    out = reprint(src)

    assert out =~ "# note", "body-leading comment was dropped: #{inspect(out)}"
    assert reparses?(out), "reprint no longer parses: #{inspect(out)}"
    assert reprint(out) == out, "= / inline-body comment reprint is not idempotent: #{inspect(out)}"
  end

  defp reparses?(src) do
    with {:ok, toks} <- Lexer.tokenize(src, file: "r.cure", emit_events: false),
         {:ok, _ast} <- Parser.parse(toks, file: "r.cure", emit_events: false) do
      true
    else
      _ -> false
    end
  end

  # helper: collect all values of a given meta key across the AST
  defp collect_meta(ast, key, acc \\ [])

  defp collect_meta({_k, m, ch}, key, acc) when is_list(m) and is_list(ch) do
    acc = if v = Keyword.get(m, key), do: [v | acc], else: acc
    Enum.reduce(ch, acc, &collect_meta(&1, key, &2))
  end

  defp collect_meta({_k, m, _v}, key, acc) when is_list(m) do
    if v = Keyword.get(m, key), do: [v | acc], else: acc
  end

  defp collect_meta(l, key, acc) when is_list(l), do: Enum.reduce(l, acc, &collect_meta(&1, key, &2))
  defp collect_meta(_, _key, acc), do: acc
end

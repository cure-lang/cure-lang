defmodule Cure.LSP.ServerV17Test do
  use ExUnit.Case, async: true

  alias Cure.LSP.Server

  @sample """
  mod Demo
    fn add(a: Int, b: Int) -> Int = a + b
    fn double(x: Int) -> Int = x * 2
  """

  describe "compute_inlay_hints/1" do
    test "does not repeat a declaration's own signature" do
      assert Server.compute_inlay_hints(@sample) == []
    end

    test "gives constructor calls no hints and places call hints on their line" do
      source = """
      mod Payload
        type Callback = On(Int -> Int) | Off
        fn apply(cb: Callback, x: Int) -> Int = x
        fn main() -> Int = apply(On(fn(n) -> n + 1), 10)
      """

      hints = Server.compute_inlay_hints(source)
      assert Enum.map(hints, & &1["label"]) == ["cb:", "x:"]
      assert Enum.all?(hints, &(&1["position"]["line"] == 3))
    end

    test "offers parameter-name hints for positional calls but not already named arguments" do
      source = "mod Hints\n  fn add(left x: Int, y: Int) -> Int = x + y\n  fn go() -> Int = add(left: 1, 2)\n"
      labels = Server.compute_inlay_hints(source) |> Enum.map(& &1["label"])
      assert "y:" in labels
      refute Enum.count(labels, &(&1 == "left:")) > 0
    end
  end

  describe "compute_signature_help/3" do
    test "returns nil away from a call site" do
      assert nil == Server.compute_signature_help("not a function", 0, 5)
    end

    test "shows declaration labels and follows a reordered active named argument" do
      source =
        "mod Help\n  fn move(to dest: Int, from src: Int) -> Int = dest\n  fn go() -> Int = move(from: 1, to: 2)\n"

      help = Server.compute_signature_help(source, 2, 38)
      assert hd(help["signatures"])["label"] =~ "move(to dest: Int, from src: Int)"
      assert help["activeParameter"] == 0
      assert Enum.map(hd(help["signatures"])["parameters"], & &1["label"]) == ["to", "from"]
    end
  end

  test "named-argument completion and hover expose parameter meaning" do
    source =
      "mod Tools\n  fn move(to dest: Int, from src: Int) -> Int = dest\n  fn go() -> Int = move(from: 1, to: 2)\n"

    prefix = "mod Tools\n  fn move(to dest: Int, from src: Int) -> Int = dest\n  fn go() -> Int = move(from: 1, "
    items = Server.context_completions(source, prefix)
    assert Enum.any?(items, &(&1["label"] == "to:" and &1["detail"] =~ "dest: Int"))
    refute Enum.any?(items, &(&1["label"] == "from:"))

    hover = Server.compute_hover(source, 2, 24)
    assert hover["contents"]["value"] =~ "Named argument `from`"
    assert hover["contents"]["value"] =~ "src: Int"
  end

  test "keyword completion exposes the canonical 0.34 surface" do
    items = Server.keyword_completions()
    assert Enum.any?(items, &(&1["label"] == "interface"))
    assert Enum.any?(items, &(&1["label"] == "pickup"))

    refute Enum.any?(items, &(&1["label"] in ["proto", "impl", "if", "elif"]))
  end

  describe "compute_formatting_edits/1" do
    # LSP formatting delegates to `Cure.Compiler.Formatter`, a
    # source-preserving formatter whose output is round-trip-validated
    # against the original AST. The LSP handler returns a single
    # whole-document `TextEdit` when the formatter produces a change,
    # or `[]` otherwise.
    test "returns an empty edit list on canonical text" do
      assert [] = Server.compute_formatting_edits(@sample)
    end

    test "returns a whole-document TextEdit for dirty input" do
      dirty = "mod Demo\n  fn add(a: Int, b: Int) -> Int = a+b\n"
      assert [edit] = Server.compute_formatting_edits(dirty)
      assert %{"range" => range, "newText" => new_text} = edit
      assert %{"start" => %{"line" => 0, "character" => 0}} = range
      assert new_text =~ "a + b"
    end

    test "degrades to [] on unparseable input" do
      # Unterminated string: lexer error, so the formatter refuses to
      # modify the buffer.
      assert [] = Server.compute_formatting_edits(~s|mod D\n  fn f() -> String = "oops|)
    end

    test "returns [] on empty input" do
      assert [] = Server.compute_formatting_edits("")
    end
  end

  describe "prepare_rename/3" do
    test "returns the word range under the cursor" do
      result = Server.prepare_rename("  fn add(a: Int, b: Int) -> Int = a + b", 0, 6)
      assert %{"start" => _, "end" => _} = result
    end
  end

  describe "compute_rename/5" do
    test "produces a workspace edit set" do
      result = Server.compute_rename("file://x", @sample, 1, 6, "plus")
      assert %{"changes" => %{"file://x" => edits}} = result
      assert is_list(edits)
    end
  end

  describe "compute_code_lenses/2" do
    test "offers no lenses without a command behind them" do
      assert Server.compute_code_lenses("file://x", @sample) == []
    end
  end

  describe "compute_semantic_tokens/1" do
    test "classifies contextual have at a local-fact head as a keyword" do
      # One token encoded as [delta line, delta column, UTF-16 length, keyword, modifiers].
      assert [0, 0, 4, 0, 0 | _] = Server.compute_semantic_tokens("have fact = 1")
    end

    test "classifies proof-chain vocabulary as keywords" do
      data = Server.compute_semantic_tokens("proof chain\n  x == x because evidence")
      assert Enum.chunk_every(data, 5) |> Enum.count(fn [_dl, _dc, length, 0, 0] -> length in [5, 7] end) >= 2
    end

    test "classifies canonical interface and pickup vocabulary as keywords" do
      data = Server.compute_semantic_tokens("interface Show(a)\npickup\n  else -> true")
      keyword_lengths = for [_dl, _dc, length, 0, 0] <- Enum.chunk_every(data, 5), do: length
      assert 9 in keyword_lengths
      assert 6 in keyword_lengths
    end

    test "ignores keywords inside comments and strings" do
      source = """
      mod Demo
        ###
        any type expression
        ###
        ## identity when Off
        fn f() -> String = "type match"
      """

      words =
        for [dl, dc, len, 0, 0] <- Enum.chunk_every(Server.compute_semantic_tokens(source), 5), reduce: {[], 0, 0} do
          {acc, line, col} ->
            {line, col} = if dl == 0, do: {line, col + dc}, else: {line + dl, dc}
            text = source |> String.split("\n") |> Enum.at(line) |> String.slice(col, len)
            {[text | acc], line, col}
        end
        |> elem(0)
        |> Enum.reverse()

      assert words == ["mod", "fn"]
    end

    test "marks contextual words only where they are keywords" do
      keywords = fn source ->
        for [_dl, _dc, len, 0, 0] <- Enum.chunk_every(Server.compute_semantic_tokens(source), 5), do: len
      end

      # `fn` only: `proof`, `case` and `app` stand as names here.
      assert keywords.("fn proof(x: Int) -> Int = x") == [2]
      assert keywords.("let case = 1") == [3]
      assert keywords.("let app = start(app)") == [3]
      assert keywords.("fn prefix(s: String) -> String = s") == [2]

      assert keywords.("behavior Store") == [8]
      assert keywords.("infix `<+>`") == [5]
    end

    test "counts columns in UTF-16 units" do
      # `if` starts at byte 7 but UTF-16 unit 5: the emoji is 4 bytes, 2 units.
      assert [0, 5, 2, 0, 0] = Server.compute_semantic_tokens(~s("😀" if))
      assert [0, 4, 2, 0, 0] = Server.compute_semantic_tokens(~s("😀" if), :utf32)
    end

    test "produces an LSP token integer stream" do
      tokens = Server.compute_semantic_tokens(@sample)
      assert is_list(tokens)
      assert rem(length(tokens), 5) == 0
    end
  end

  describe "compute_workspace_symbols/2" do
    test "filters by query" do
      docs = %{"file://demo.cure" => @sample}
      assert symbols = Server.compute_workspace_symbols("add", docs)
      assert Enum.any?(symbols, fn s -> s["name"] == "add" end)
    end
  end
end

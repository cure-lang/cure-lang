defmodule Cure.Compiler.FormatterTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Formatter

  # A fixture buffer that is intentionally messy along every axis the
  # formatter touches. Individual tests pull out sub-slices or assert
  # on the final round-trip.
  @dirty ~S"""
  mod Demo


    fn add(a: Int,b: Int) -> Int = a+b
    fn mul(a: Int,b: Int) -> Int = a*b

    # trailing whitespace follows
    fn id(x: Int) -> Int = x

    fn neg() -> Int = -1
  """

  describe "format/2 -- idempotence" do
    test "canonical buffer is a no-op" do
      canonical = "mod Demo\n  fn add(a: Int, b: Int) -> Int = a + b\n"
      assert {:ok, ^canonical} = Formatter.format(canonical)
    end

    test "formatting is a fixed point" do
      {:ok, once} = Formatter.format(@dirty)
      {:ok, twice} = Formatter.format(once)
      assert once == twice
    end

    test "named-argument order and labels survive formatting at a fixed point" do
      source = "mod NamedFmt\n  fn f(a: Int, b: Int) -> Int = a + b\n  fn g() -> Int = f(b: 2, a: 1)\n"
      assert {:ok, once} = Formatter.format(source)
      assert once =~ "f(b: 2, a: 1)"
      assert {:ok, ^once} = Formatter.format(once)
    end
  end

  describe "format/2 -- trailing whitespace" do
    test "strips trailing spaces from code lines" do
      src = "mod Demo\n  fn f() -> Int = 1   \n"
      assert {:ok, "mod Demo\n  fn f() -> Int = 1\n"} = Formatter.format(src)
    end

    test "strips trailing spaces from comment lines" do
      src = "mod Demo\n  fn f() -> Int = 1 # trailing   \n"
      assert {:ok, "mod Demo\n  fn f() -> Int = 1 # trailing\n"} = Formatter.format(src)
    end

    test "does not touch content inside string literals" do
      src = ~s|mod Demo\n  fn f() -> String = "hello   "\n|
      assert {:ok, ^src} = Formatter.format(src)
    end
  end

  describe "format/2 -- tab handling" do
    test "expands leading tabs to two spaces each" do
      src = "mod Demo\n\tfn f() -> Int = 1\n"
      assert {:ok, "mod Demo\n  fn f() -> Int = 1\n"} = Formatter.format(src)
    end

    test "double-tab indentation becomes four spaces" do
      src = "mod Demo\n\t\tfn f() -> Int = 1\n"
      assert {:ok, "mod Demo\n    fn f() -> Int = 1\n"} = Formatter.format(src)
    end
  end

  describe "format/2 -- blank-line collapsing" do
    test "collapses any run of >=2 blanks to a single blank" do
      src = "mod Demo\n\n\n\n  fn f() -> Int = 1\n"
      assert {:ok, "mod Demo\n\n  fn f() -> Int = 1\n"} = Formatter.format(src)
    end

    test "preserves a single blank line" do
      src = "mod Demo\n\n  fn f() -> Int = 1\n"
      assert {:ok, ^src} = Formatter.format(src)
    end
  end

  describe "format/2 -- line endings" do
    test "rewrites CRLF to LF" do
      src = "mod Demo\r\n  fn f() -> Int = 1\r\n"
      assert {:ok, "mod Demo\n  fn f() -> Int = 1\n"} = Formatter.format(src)
    end
  end

  describe "format/2 -- final newline" do
    test "adds a trailing newline when missing" do
      src = "mod Demo\n  fn f() -> Int = 1"
      assert {:ok, "mod Demo\n  fn f() -> Int = 1\n"} = Formatter.format(src)
    end

    test "collapses multiple trailing newlines to one" do
      src = "mod Demo\n  fn f() -> Int = 1\n\n\n"
      assert {:ok, "mod Demo\n  fn f() -> Int = 1\n"} = Formatter.format(src)
    end
  end

  describe "format/2 -- operator spacing" do
    test "spaces around +, -, *, /" do
      src = "mod Demo\n  fn f(a: Int, b: Int) -> Int = a+b-a*b/1\n"
      assert {:ok, out} = Formatter.format(src)
      assert out =~ "a + b - a * b / 1"
    end

    test "spaces around comparison operators" do
      src = "mod Demo\n  fn f(a: Int, b: Int) -> Bool = a==b\n"
      assert {:ok, out} = Formatter.format(src)
      assert out =~ "a == b"
    end

    test "spaces around pipe" do
      src = "mod Demo\n  fn f(x: Int) -> Int = x|>inc|>dbl\n"
      assert {:ok, out} = Formatter.format(src)
      assert out =~ "x |> inc |> dbl"
    end

    test "leaves unary minus alone" do
      src = "mod Demo\n  fn f() -> Int = -1\n"
      assert {:ok, ^src} = Formatter.format(src)
    end

    test "leaves unary minus after return alone" do
      src = "mod Demo\n  fn f(x: Int) -> Int = return -1\n"
      assert {:ok, ^src} = Formatter.format(src)
    end

    test "leaves variadic *args alone" do
      src = "mod Demo\n  fn many(*args: Int) -> Int = 0\n"
      assert {:ok, ^src} = Formatter.format(src)
    end

    test "leaves content inside strings alone" do
      src = ~s|mod Demo\n  fn f() -> String = "1+2=3"\n|
      assert {:ok, ^src} = Formatter.format(src)
    end

    test "leaves content inside regex alone" do
      src = "mod Demo\n  fn f() -> Regex = /a+b/i\n"
      assert {:ok, ^src} = Formatter.format(src)
    end

    test "leaves content inside line comments alone" do
      src = "mod Demo\n  fn f() -> Int = 1 # 1+2=3\n"
      assert {:ok, ^src} = Formatter.format(src)
    end

    test "leaves exponent signs inside numbers alone" do
      src = "mod Demo\n  fn f() -> Float = 1.5e-3\n"
      assert {:ok, ^src} = Formatter.format(src)
    end
  end

  describe "format/2 -- non-destructiveness" do
    test "preserves plain line comments exactly" do
      src = """
      mod Demo
        # this is a top comment
        fn f() -> Int = 1 # trailing
        # bottom comment
      """

      {:ok, out} = Formatter.format(src)
      assert out =~ "# this is a top comment"
      assert out =~ "# trailing"
      assert out =~ "# bottom comment"
    end

    test "preserves doc comments exactly" do
      src = """
      mod Demo
        ## doc for f
        fn f() -> Int = 1
      """

      assert {:ok, out} = Formatter.format(src)
      assert out =~ "## doc for f"
    end

    test "degrades to original on unparseable input" do
      # Unterminated string literal: lexer error, no AST to validate.
      src = ~s|mod Demo\n  fn f() -> String = "unterminated|
      assert {:ok, ^src} = Formatter.format(src)
    end

    test "handles the empty string" do
      assert {:ok, ""} = Formatter.format("")
    end
  end

  describe "format_to_edits/1" do
    test "returns [] for a canonical buffer" do
      canonical = "mod Demo\n  fn f() -> Int = 1\n"
      assert [] = Formatter.format_to_edits(canonical)
    end

    test "returns a single whole-document edit for dirty input" do
      src = "mod Demo\n  fn f() -> Int = 1+2\n"
      assert [edit] = Formatter.format_to_edits(src)
      assert %{"range" => range, "newText" => new_text} = edit

      assert %{"start" => %{"line" => 0, "character" => 0}, "end" => _} = range
      assert new_text =~ "1 + 2"
    end

    test "returns [] for unparseable input (degrades safely)" do
      src = ~s|mod Demo\n  fn f() -> String = "unterminated|
      assert [] = Formatter.format_to_edits(src)
    end
  end
end

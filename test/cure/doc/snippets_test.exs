defmodule Cure.Doc.SnippetsTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.Snippets

  test "extracts backtick and tilde Cure fences with authored line numbers" do
    markdown = """
    prose

    ```cure
    fn answer() -> Int = 42
    ```

    ~~~~cure expr
    40 + 2
    ~~~~

    ```elixir
    :ignored
    ```
    """

    assert [
             %Snippets{line: 4, info: "cure", code: "fn answer() -> Int = 42"},
             %Snippets{line: 8, info: "cure expr", code: "40 + 2"}
           ] = Snippets.extract(markdown, "guide.md")
  end

  test "does not mistake longer language names for Cure" do
    assert [] = Snippets.extract("```curescript\nvalue\n```\n")
  end

  test "extracts Cure fences from ## docstrings with source line numbers" do
    source = """
    mod Demo
      ## ## Examples
      ##
      ## ```cure expr
      ## 40 + 2
      ## ```
      fn answer() -> Int = 42
    """

    assert [%Snippets{path: "demo.cure", line: 5, info: "cure expr", code: "40 + 2"}] =
             Snippets.extract_cure(source, "demo.cure")
  end

  test "extracts fences inside ### docstring bodies" do
    source = """
    mod Demo
      ###
      Examples:

      ```cure expr
      40 + 2
      ```
      ###
      fn answer() -> Int = 42
    """

    assert [%Snippets{path: "demo.cure", line: 6, info: "cure expr", code: "40 + 2"}] =
             Snippets.extract_cure(source, "demo.cure")
  end

  test "parses tags separately from fence attributes" do
    [snippet] =
      Snippets.extract("""
      ```cure E091,expr path=broken.cure start=4
      missing
      ```
      """)

    assert Snippets.tags(snippet) == MapSet.new(["E091", "expr"])
    assert Snippets.expected_diagnostic(snippet) == {:ok, "E091"}
    refute Snippets.tagged?(snippet, "path=broken.cure")
  end

  test "reads a warning code as an expected diagnostic" do
    [snippet] = Snippets.extract("```cure W000\nfn answer() -> Int = 42\n```\n")

    assert Snippets.expected_diagnostic(snippet) == {:ok, "W000"}
  end

  test "ignores tags that are not diagnostic codes" do
    [snippet] = Snippets.extract("```cure expr declarations\nmissing\n```\n")

    assert Snippets.expected_diagnostic(snippet) == nil
  end

  test "rejects multiple expected diagnostic tags" do
    [snippet] = Snippets.extract("```cure E091 E093\nmissing\n```\n")

    assert Snippets.expected_diagnostic(snippet) == {:error, ["E091", "E093"]}
  end

  test "rejects an error code and a warning code on the same fence" do
    [snippet] = Snippets.extract("```cure E091 W000\nmissing\n```\n")

    assert Snippets.expected_diagnostic(snippet) == {:error, ["E091", "W000"]}
  end

  test "wraps declarations and expressions at their authored lines" do
    declaration = %Snippets{
      path: "guide.md",
      line: 8,
      info: "cure",
      code: "fn answer() -> Int = 42"
    }

    expression = %{declaration | line: 12, info: "cure expr", code: "40 + 2"}

    declaration_source = Snippets.source(declaration)
    expression_source = Snippets.source(expression)

    assert Enum.at(String.split(declaration_source, "\n"), 7) == "  fn answer() -> Int = 42"
    assert Enum.at(String.split(expression_source, "\n"), 11) == "    40 + 2"
  end

  test "treats attributed declarations as declarations" do
    snippet = %Snippets{
      path: "ffi.md",
      line: 3,
      info: "cure E056",
      code: "@extern(:erlang, :abs, 1)\nfn abs(x)"
    }

    source = Snippets.source(snippet)

    assert source =~ "mod DocSnippet_"
    assert source =~ "  @extern(:erlang, :abs, 1)\n  fn abs(x)"
    refute source =~ "fn snippet()"
  end

  # A fence of unindented lines is ambiguous: it is either several independent
  # example expressions, or one block that happens to start flush left. The
  # `let` tells them apart -- a `let` has no value without the body that follows
  # it, so a fence containing one cannot be a list of independent expressions.
  test "several independent expressions each become their own function" do
    snippet = %Snippets{
      path: "guide.md",
      line: 3,
      info: "cure expr",
      code: "1 + 1\n2 + 2"
    }

    source = Snippets.source(snippet)

    assert source =~ "fn snippet_1() = 1 + 1"
    assert source =~ "fn snippet_2() = 2 + 2"
  end

  test "a let sequence is one expression body rather than one function per line" do
    snippet = %Snippets{
      path: "guide.md",
      line: 3,
      info: "cure expr",
      code: "let x = 40\nlet y = 2\nx + y"
    }

    source = Snippets.source(snippet)

    refute source =~ "fn snippet_1() = let",
           "a `let` is not a whole function body; splitting the block strands it without one"

    assert {:ok, _module, []} = Snippets.compile(snippet)
  end

  test "compiles complete modules, declarations, and expressions" do
    snippets = [
      %Snippets{path: "one.md", line: 1, info: "cure", code: "mod Complete\n  fn value() = 1"},
      %Snippets{path: "two.md", line: 3, info: "cure", code: "fn value() -> Int = 1"},
      %Snippets{path: "three.md", line: 5, info: "cure expr", code: "1 + 1"}
    ]

    for snippet <- snippets do
      assert {:ok, _module, []} = Snippets.compile(snippet)
    end
  end

  test "appended support declarations are available without shifting snippet source" do
    snippet = %Snippets{
      path: "support.md",
      line: 7,
      info: "cure expr",
      code: "documented_helper(42)"
    }

    support = "fn documented_helper(value: Int) -> Int = value"

    assert Enum.at(String.split(Snippets.source(snippet, support), "\n"), 6) ==
             "    documented_helper(42)"

    assert {:ok, _module, []} = Snippets.compile(snippet, support: support)
  end

  # A fence opening with `use` and then declaring top-level forms is a whole
  # compilation unit already. Wrapping it would nest those declarations inside
  # the synthetic module, where siblings can no longer name each other — which
  # is exactly how a doc page shows client code driving an `fsm`.
  test "a fence that opens with use and declares top-level forms is left unwrapped" do
    snippet = %Snippets{
      path: "unit.md",
      line: 1,
      info: "cure",
      code: "use Std.List\n\nmod Doc.Lib\n  fn f() -> Int = 1\n\nmod Doc.Driver\n  fn run() -> Int = Doc.Lib.f()"
    }

    refute Snippets.source(snippet, "") =~ "DocSnippet_"
    assert {:ok, _module, []} = Snippets.compile(snippet)
  end

  test "a fence that opens with use but only continues with expressions is still wrapped" do
    snippet = %Snippets{path: "expr.md", line: 1, info: "cure", code: "use Std.List\n\nfn f() -> Int = 1"}

    assert Snippets.source(snippet, "") =~ "DocSnippet_"
  end

  # The classifier reads the fence's first meaningful line to choose between a
  # module body and a `fn snippet() =` expression body. A declaration head it
  # does not recognise silently picks the expression body, where a declaration
  # cannot appear — the fence then fails on the shape of the wrapper rather than
  # on anything the page wrote.
  for {head, code} <- [
        {"rec", "rec Point\n  x: Int\n  y: Int\n\nfn origin() -> Point = Point{x: 0, y: 0}"},
        {"opaque", "opaque type Handle\n\nfn describe(_h: Handle) -> Atom = :handle"},
        {"local", "local fn helper() -> Int = 1\n\nfn call() -> Int = helper()"}
      ] do
    test "a fence headed by `#{head}` is compiled as declarations" do
      snippet = %Snippets{path: "decl.md", line: 1, info: "cure", code: unquote(code)}

      refute Snippets.source(snippet, "") =~ "fn snippet()"
      assert {:ok, _module, []} = Snippets.compile(snippet)
    end
  end
end

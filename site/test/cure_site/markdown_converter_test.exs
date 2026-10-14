defmodule CureSite.MarkdownConverterTest do
  use ExUnit.Case, async: true

  alias CureSite.MarkdownConverter

  test "renders brace interpolation inside fenced cure blocks" do
    html =
      MarkdownConverter.to_html(~S"""
      ```cure
      "hello #{name}"
      "result: #{compute(42)}"
      ```
      """)

    assert html =~ ~S|#{|
    assert html =~ "compute"
    refute html =~ "&lbrace;"
    refute html =~ "&rbrace;"
  end

  test "wraps fenced blocks in a reusable code window" do
    html = MarkdownConverter.to_html("```cure\nfn answer() -> Int = 42\n```")

    assert html =~ ~s(class="cure-code-window")
    assert html =~ ~s(class="cure-code-window-bar")
    assert html =~ ~s(class="cure-code-window-dots")
    assert html =~ ~s(class="cure-code-window-label">cure</span>)
    assert html =~ ~s(<pre><code class="makeup cure">)
  end

  describe "math" do
    test "marks inline dollar math for the client-side KaTeX pass" do
      html = MarkdownConverter.to_html(~S|Graded functions ($\Pi$) carry usage grades.|)

      assert html =~ ~S|<span data-math-style="inline">\Pi</span>|
    end

    test "keeps TeX backslash escapes intact" do
      # Without the math extension CommonMark would eat the escaped braces,
      # leaving KaTeX with an unbalanced set literal.
      html = MarkdownConverter.to_html(~S|QTT grades $\{0, 1, \le 1, \omega\}$.|)

      assert html =~ ~S|<span data-math-style="inline">\{0, 1, \le 1, \omega\}</span>|
    end

    test "marks display math" do
      html = MarkdownConverter.to_html(~S|$$a^2 + b^2 = c^2$$|)

      assert html =~ ~S|<span data-math-style="display">a^2 + b^2 = c^2</span>|
    end

    test "marks GFM math code spans" do
      html = MarkdownConverter.to_html(~S|Inline: $`\sqrt{3}`$|)

      assert html =~ ~S|<code data-math-style="inline">\sqrt{3}</code>|
    end

    test "marks math fences and keeps them out of the Makeup pass" do
      html = MarkdownConverter.to_html("```math\n\\sum_{i=0}^n i\n```")

      assert html =~ ~s(data-math-style="display")
      assert html =~ ~S|\sum_{i=0}^n i|
      refute html =~ ~s(class="cure-code-window")
    end

    test "leaves dollar signs inside code spans alone" do
      html = MarkdownConverter.to_html(~S|Open `$EDITOR` / `$VISUAL` on the buffer.|)

      assert html =~ ~s(<code>$EDITOR</code>)
      assert html =~ ~s(<code>$VISUAL</code>)
      refute html =~ "data-math-style"
    end
  end
end

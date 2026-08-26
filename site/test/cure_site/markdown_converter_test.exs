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
end

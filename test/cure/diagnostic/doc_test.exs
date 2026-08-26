defmodule Cure.Diagnostic.DocTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Doc

  test "paragraphs wrap deterministically at display width" do
    doc = Doc.paragraph(["Cure diagnostics explain", Doc.emphasis(:name, "the authored name"), "without noise."])

    assert Doc.plain(doc, width: 28) ==
             "Cure diagnostics explain the\nauthored name without noise."
  end

  test "stacks, indentation, notes, hints, and lists compose as blocks" do
    doc =
      Doc.stack([
        Doc.paragraph("A short explanation."),
        Doc.indent(2, Doc.bullet_list(["first choice", Doc.paragraph("second choice")])),
        Doc.note("Names are case-sensitive."),
        Doc.hint("Import the module first.")
      ])

    assert Doc.plain(doc, width: 40) ==
             """
             A short explanation.

               - first choice
               - second choice

             Note: Names are case-sensitive.

             Hint: Import the module first.
             """
             |> String.trim_trailing()
  end

  test "code is unwrapped and explicit blank lines stack once" do
    doc = Doc.concat([Doc.code("some very long authored_code(value)"), Doc.blank_line(), Doc.text("after")])

    assert Doc.plain(doc, width: 12) == "some very long authored_code(value)\n\nafter"
  end

  test "ANSI is emitted only by the ANSI encoder and semantic roles survive wrapping" do
    doc = Doc.paragraph(["Expected", Doc.emphasis(:expected, "Int"), "but found", Doc.emphasis(:observed, "Bool")])

    plain = Doc.plain(doc, width: 80)
    ansi = Doc.ansi(doc, width: 80)

    assert plain == "Expected Int but found Bool"
    refute plain =~ "\e["
    assert ansi =~ IO.ANSI.green() <> "Int" <> IO.ANSI.reset()
    assert ansi =~ IO.ANSI.red() <> "Bool" <> IO.ANSI.reset()
    assert Regex.replace(~r/\e\[[0-9;]*m/, ansi, "") == plain
  end

  test "display width handles combining marks, wide characters, emoji clusters, and tabs" do
    assert Doc.display_width("e\u0301") == 1
    assert Doc.display_width("界") == 2
    assert Doc.display_width("👩‍💻") == 2
    assert Doc.display_width("a\tb", 1, tab_width: 4) == 5
    assert Doc.display_width("\tb", 3, tab_width: 4) == 3
  end

  test "invalid emphasis roles are rejected" do
    assert_raise ArgumentError, fn -> Doc.emphasis(:internal_core_term, "bad") end
  end
end

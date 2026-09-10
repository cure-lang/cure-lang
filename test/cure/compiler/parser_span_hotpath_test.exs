defmodule Cure.Compiler.ParserSpanHotpathTest do
  use ExUnit.Case, async: true

  test "source-span folding avoids intermediate child-span lists" do
    source = File.read!("lib/cure/compiler/parser.ex")

    assert source =~ "defp merge_ast_children"
    refute source =~ "children |> Enum.map(&ast_source_span/1)"
  end
end

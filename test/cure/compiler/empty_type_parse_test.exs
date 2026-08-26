defmodule Cure.Compiler.EmptyTypeParseTest do
  # `type Empty = |` declares a constructor-less (uninhabited) type: a leading
  # `|` with no variant following it parses to a 0-ctor `:enum` container.
  use ExUnit.Case, async: true

  # Find the parsed node for the type/declaration named `name`, anywhere in the
  # AST (the `mod` container wraps the declarations in its body).
  defp find_named(ast, name) do
    ast
    |> List.wrap()
    |> Enum.flat_map(&walk/1)
    |> Enum.find(fn
      {_tag, meta, _ch} when is_list(meta) -> Keyword.get(meta, :name) == name
      _ -> false
    end)
  end

  defp walk({_tag, _meta, ch} = node) when is_list(ch), do: [node | Enum.flat_map(ch, &walk/1)]
  defp walk(node), do: [node]

  test "`type Empty = |` parses to a 0-constructor enum container" do
    {:ok, ast} = Cure.Compiler.parse_source("mod X\n  type Empty = |\n")

    assert {:container, meta, []} = find_named(ast, "Empty")
    assert Keyword.get(meta, :container_type) == :enum
  end

  test "a `## doc` on the NEXT declaration is not slurped as a variant of `type Empty = |`" do
    # Regression: a doc (or line) comment can never begin a variant, so it must
    # end the empty type's variant list. Omitting comment tokens from the
    # end-of-variants check turned `type Empty = |` followed by a documented
    # sibling into the bogus alias `type Empty = <docword>`, which then broke
    # downstream elaboration (`:bad_motive`) for any type referencing `Empty`.
    src = """
    mod X
      type Empty = |
      ## the decision type
      type Decision(a) =
        | Yes(a)
        | No(a -> Empty)
    """

    {:ok, ast} = Cure.Compiler.parse_source(src)

    # `Empty` stays a 0-ctor enum container — NOT a `:type_annotation` alias
    # whose RHS is the doc text.
    assert {:container, empty_meta, []} = find_named(ast, "Empty")
    assert Keyword.get(empty_meta, :container_type) == :enum

    # And the doc attaches to `Decision`, where it belongs.
    assert {_tag, dec_meta, _ch} = find_named(ast, "Decision")
    assert Keyword.get(dec_meta, :doc) =~ "decision type"
  end

  test "a plain `#` line comment on the next declaration is likewise not a variant" do
    src = """
    mod X
      type Empty = |
      # a comment
      type Decision(a) =
        | Yes(a)
        | No(a -> Empty)
    """

    {:ok, ast} = Cure.Compiler.parse_source(src)

    assert {:container, meta, []} = find_named(ast, "Empty")
    assert Keyword.get(meta, :container_type) == :enum
  end
end

defmodule Cure.MetaAST.MetadataLintTest do
  use ExUnit.Case, async: true

  alias Cure.MetaAST.MetadataLint

  test "reports exact metadata lists in semantic function patterns" do
    source = "def bad({:sigma_type, [binder: binder], children}), do: {binder, children}\n"
    [site] = MetadataLint.scan_source(source, "fixture.ex")

    assert site.file == "fixture.ex"
    assert site.line == 1
    assert site.node == :sigma_type
  end

  test "reports exact empty metadata lists in semantic patterns" do
    source = "def bad({:variable, [], name}), do: name\n"
    [site] = MetadataLint.scan_source(source, "empty.ex")

    assert site.file == "empty.ex"
    assert site.line == 1
    assert site.node == :variable
  end

  test "identifies legacy source keys in semantic metadata patterns" do
    source = "def bad({:variable, [span: span], name}), do: {span, name}\n"
    [site] = MetadataLint.scan_source(source, "legacy.ex")

    assert site.node == :variable
    assert site.legacy_source_keys == [:span]
  end

  test "accepts metadata bindings and ignores construction sites" do
    source = """
    def good({:sigma_type, meta, children}), do: {Keyword.fetch!(meta, :binder), children}
    def build(binder, children), do: {:sigma_type, [binder: binder], children}
    """

    assert MetadataLint.scan_source(source, "fixture.ex") == []
  end

  test "reports case-clause patterns" do
    source = "def check(ast), do: case ast do\n  {:pi_type, [binders: binders], children} -> {binders, children}\nend\n"
    assert [%{node: :pi_type}] = MetadataLint.scan_source(source, "case.ex")
  end

  test "the elaborator and compiler semantic trees have no exact metadata patterns" do
    paths = Path.wildcard("lib/cure/**/*.ex")
    assert :ok = MetadataLint.validate(paths)
  end
end

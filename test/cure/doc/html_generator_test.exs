defmodule Cure.Doc.HTMLGeneratorTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.HTMLGenerator

  @moduletag :tmp_dir

  defp sample_modules do
    [
      %{
        module: "Std.Core",
        module_doc: "Core combinators.\n\nSome prose.\n\n```cure\nfn id(x: T) -> T = x\n```",
        functions: [
          %{
            name: "identity",
            params: [{"x", "T"}],
            return_type: "T",
            effects: [],
            visibility: :public,
            doc: "Identity.\n\n## Examples\n\n```cure\nidentity(1)\n```",
            clauses: 1,
            extern: false,
            guards: false
          },
          %{
            name: "helper",
            params: [],
            return_type: "Int",
            effects: [],
            visibility: :private,
            doc: nil,
            clauses: 1,
            extern: false,
            guards: false
          }
        ],
        protocols: [
          %{
            name: "Show",
            type_params: ["t"],
            methods: [%{name: "show"}],
            doc: "Values which can be displayed."
          }
        ],
        types: []
      },
      %{
        module: "Std.List",
        module_doc: "Eager lists.",
        functions: [
          %{
            name: "map",
            params: [{"list", "List(T)"}, {"f", "T -> U"}],
            return_type: "List(U)",
            effects: [],
            visibility: :public,
            doc: "Map `f` over every element.",
            clauses: 1,
            extern: false,
            guards: false
          }
        ],
        protocols: [],
        types: []
      }
    ]
  end

  test "writes index, per-module pages, CSS, and JS bundle", %{tmp_dir: tmp} do
    HTMLGenerator.generate(sample_modules(), tmp, title: "Demo")

    assert File.regular?(Path.join(tmp, "index.html"))
    assert File.regular?(Path.join(tmp, "style.css"))
    assert File.regular?(Path.join(tmp, "assets.js"))
    assert File.regular?(Path.join(tmp, "std_core.html"))
    assert File.regular?(Path.join(tmp, "std_list.html"))
  end

  test "sidebar lists every module", %{tmp_dir: tmp} do
    HTMLGenerator.generate(sample_modules(), tmp, title: "Demo")

    index = File.read!(Path.join(tmp, "index.html"))
    assert index =~ ~s(class="cure-doc-sidebar")
    assert index =~ ~s(data-slug="std_core")
    assert index =~ ~s(data-slug="std_list")
    assert index =~ "Std.Core"
    assert index =~ "Std.List"
  end

  test "groups modules when groups_for_modules is provided", %{tmp_dir: tmp} do
    doc_config = %{
      groups_for_modules: [{"Core", ["Std.Core"]}, {"Collections", ["Std.List"]}]
    }

    HTMLGenerator.generate(sample_modules(), tmp, title: "Demo", doc_config: doc_config)

    index = File.read!(Path.join(tmp, "index.html"))
    assert index =~ ">Core</h2>"
    assert index =~ ">Collections</h2>"
  end

  test "module page carries anchored function entries", %{tmp_dir: tmp} do
    HTMLGenerator.generate(sample_modules(), tmp, title: "Demo")

    page = File.read!(Path.join(tmp, "std_core.html"))
    assert page =~ ~s(id="fn-identity")
    assert page =~ ~s(href="#fn-identity")
    refute page =~ "helper"
  end

  test "module page renders interfaces using canonical syntax", %{tmp_dir: tmp} do
    HTMLGenerator.generate(sample_modules(), tmp, title: "Demo")

    page = File.read!(Path.join(tmp, "std_core.html"))
    assert page =~ ~s(id="interface-Show")
    assert page =~ ~s(href="#interface-Show")
    assert page =~ "<h2>Interfaces</h2>"
    assert page =~ "<code>interface Show(t)</code>"
    refute page =~ "<code>proto Show"
  end

  test "function doc is rendered as HTML (not escaped markdown)", %{tmp_dir: tmp} do
    HTMLGenerator.generate(sample_modules(), tmp, title: "Demo")

    page = File.read!(Path.join(tmp, "std_core.html"))
    assert page =~ "<h2>\n  Examples\n</h2>"
    # The `identity(1)` example was fenced as `cure`, so it should be
    # syntax-highlighted (or at least end up inside a <pre><code>).
    assert page =~ ~s(<pre)
    assert page =~ ~s(class="language-cure")
  end

  test "extras pages are generated and appear in the sidebar", %{tmp_dir: tmp} do
    extra = Path.join(tmp, "overview.md")
    File.write!(extra, "# Overview\n\nHello, Cure doc.\n")

    HTMLGenerator.generate(sample_modules(), tmp,
      title: "Demo",
      doc_config: %{extras: [extra]},
      project_root: tmp
    )

    assert File.regular?(Path.join(tmp, "overview.html"))
    index = File.read!(Path.join(tmp, "index.html"))
    assert index =~ ">Pages</h2>"
    assert index =~ ~s(data-slug="overview")
    assert index =~ ">Overview</a>"
  end

  test "--main switch picks which page index.html mirrors", %{tmp_dir: tmp} do
    extra = Path.join(tmp, "README.md")
    File.write!(extra, "# Landing\n\nWelcome.\n")

    HTMLGenerator.generate(sample_modules(), tmp,
      title: "Demo",
      doc_config: %{extras: [extra], main: "README"},
      project_root: tmp
    )

    index = File.read!(Path.join(tmp, "index.html"))
    assert index =~ "Welcome."
    assert index =~ ~s(data-active="readme")
  end
end

defmodule Cure.Refactor.AnalysisTest do
  use ExUnit.Case, async: false

  alias Cure.Refactor.Analysis

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_refactor_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)

    on_exit(fn -> File.rm_rf!(dir) end)

    {:ok, dir: dir}
  end

  test "reports declarations, visibility, spans, and source order", %{dir: dir} do
    path = Path.join(dir, "demo.cure")

    source = """
    mod Demo
      ## public entry
      fn answer() -> Int = helper(41)

      local fn helper(value: Int) -> Int = value + 1
    end
    """

    File.write!(path, source)

    assert {:ok, report} = Analysis.analyze(path)
    assert report.module == "Demo"
    assert report.path == Path.expand(path)
    assert report.line_count == 7
    assert report.declaration_count == 2
    assert report.imports == []

    assert [%{name: "answer"} = answer, %{name: "helper"} = helper] = report.declarations
    assert answer.kind == :function
    assert answer.arity == 0
    assert answer.visibility == :public
    assert answer.span.start_line == 3
    assert answer.span.end_line == 3
    assert helper.kind == :function
    assert helper.arity == 1
    assert helper.visibility == :private
    assert helper.span.start_line == 5
    assert helper.span.end_line == 5
  end

  test "analysis is deterministic and has a stable JSON projection", %{dir: dir} do
    path = Path.join(dir, "stable.cure")
    File.write!(path, "mod Stable\n  fn z() -> Int = 1\n  fn a() -> Int = z()\n")

    assert {:ok, first} = Analysis.analyze(path)
    assert {:ok, second} = Analysis.analyze(path)
    assert first == second
    assert Analysis.to_json(first) == Analysis.to_json(second)

    assert {:ok, decoded} = Jason.decode(Analysis.to_json(first))
    assert decoded["module"] == "Stable"
    assert decoded["declaration_count"] == 2
    assert Enum.map(decoded["declarations"], & &1["name"]) == ["z", "a"]
  end

  test "checked mode runs the canonical module pipeline", %{dir: dir} do
    path = Path.join(dir, "checked.cure")
    File.write!(path, "mod Checked\n  fn value() -> Int = 7\n")

    assert {:ok, report} = Analysis.analyze(path, checked: true)
    assert report.checked?
  end

  test "warns when parser recovery leaves declarations outside the module", %{dir: dir} do
    path = Path.join(dir, "recovered.cure")

    File.write!(path, "mod Recovered\n  fn inside() -> Int = 1\n fn outside() -> Int = 2\n")

    assert {:ok, report} = Analysis.analyze(path)
    assert report.declaration_count == 1

    assert [%{kind: "declarations_outside_module", count: 1, first_name: "outside"}] = report.warnings
  end

  test "recursively reports nested declarations with canonical parents and stats", %{dir: dir} do
    path = Path.join(dir, "nested.cure")

    File.write!(
      path,
      "mod Nested\n  interface Marker(t)\n    fn mark(value: t) -> Bool\n"
    )

    assert {:ok, report} = Analysis.analyze(path, recursive: true, stats: true)
    assert report.declaration_count == 1

    assert [%{name: "Marker", kind: :interface, depth: 0, children: [member]} = marker] =
             report.declarations

    assert marker.identity == :"Nested#Marker"
    assert member.name == "mark"
    assert member.kind == :function
    assert member.identity == :"Nested#mark"
    assert member.depth == 1
    assert member.parent == marker.identity

    assert report.stats["top_level_declarations"] == 1
    assert report.stats["total_declarations"] == 2
    assert report.stats["nested_declarations"] == 1
    assert report.stats["max_depth"] == 1
    assert report.stats["declarations_by_kind"] == %{"function" => 1, "interface" => 1}

    assert {:ok, shallow} = Analysis.analyze(path, recursive: true, max_depth: 0)
    assert [%{children: []}] = shallow.declarations

    rendered = Analysis.format(report, recursive: true)
    assert rendered =~ "Nested#Marker"
    assert rendered =~ "  2. Nested#mark/1"
  end

  test "records canonical local and unresolved dependency references", %{dir: dir} do
    path = Path.join(dir, "dependencies.cure")

    File.write!(
      path,
      "mod Deps\n  fn answer() -> Int = helper() + external()\n  fn helper() -> Int = 41\n"
    )

    assert {:ok, report} = Analysis.analyze(path, dependencies: true, stats: true)
    assert [%{name: "answer", references: references}, _helper] = report.declarations

    assert [%{name: "helper", identity: :"Deps#helper", kind: :call}, %{name: "external", identity: nil, kind: :call}] =
             references

    assert report.stats["references"] == 2
    assert report.stats["unresolved_references"] == 1
    assert report.stats["references_by_kind"] == %{"call" => 2}

    rendered = Analysis.format(report, dependencies: true)
    assert rendered =~ "references: Deps#helper (call), external (call)"
  end
end

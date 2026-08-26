defmodule Cure.Compiler.CanonicalModulePipelineBoundaryRedTest do
  use ExUnit.Case, async: true

  @moduletag :canonical_module_pipeline_red

  @forbidden [
    {"env_with_generated_dependencies", "stamped-AST dependency recovery"},
    {":code.is_loaded(module)", "loaded-BEAM semantic resolution"},
    {"compile_missing_from_sources", "recursive source/provider compilation"}
  ]

  @semantic_boundary_files [
    "lib/cure/elab/program.ex",
    "lib/cure/stdlib/preload.ex"
  ]

  @bulk_compiler_routes [
    "lib/cure/cli.ex",
    "lib/cure/project.ex",
    "lib/mix/tasks/cure.compile.ex"
  ]

  test "the canonical module pipeline has no alternate resolution backdoors" do
    offenders =
      for path <- source_files(),
          {needle, reason} <- @forbidden,
          occurrence <- occurrences(path, needle),
          do: %{path: path, line: occurrence.line, call: needle, reason: reason}

    assert offenders == [], """
    The canonical module pipeline must not depend on alternate semantic resolution paths.
    Remove these calls while replacing their behavior with manifest/interface contracts:

    #{Enum.map_join(offenders, "\n", &"  #{&1.path}:#{&1.line} #{&1.call} — #{&1.reason}")}
    """
  end

  test "bulk compiler routes do not construct a legacy dependency plan" do
    offenders =
      for path <- @bulk_compiler_routes,
          needle <- ["Cure.Compiler.prepare_files"],
          occurrence <- occurrences(path, needle),
          do: %{path: path, line: occurrence.line, call: needle}

    assert offenders == [], """
    Bulk compilation must obtain ordering, cycles, Prelude providers, and module
    identities from the canonical module pipeline alone:

    #{Enum.map_join(offenders, "\n", &"  #{&1.path}:#{&1.line} #{&1.call}")}
    """
  end

  defp source_files do
    Enum.filter(@semantic_boundary_files, &File.regular?/1)
  end

  defp occurrences(path, needle) do
    path
    |> File.stream!()
    |> Stream.with_index(1)
    |> Enum.flat_map(fn {line, line_number} ->
      if String.contains?(line, needle), do: [%{line: line_number}], else: []
    end)
  end
end

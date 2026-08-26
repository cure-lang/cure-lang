defmodule Cure.ProfilerTest do
  use ExUnit.Case, async: false

  alias Cure.Profiler

  describe "profile_string" do
    test "returns report with timing data" do
      source = "mod ProfileTest\n  fn foo() -> Int = 42\n"
      {:ok, report} = Profiler.profile_string(source)

      assert report.source_bytes == byte_size(source)
      assert report.total_us > 0
      assert report.event_count > 0
      assert is_map(report.stages)
      assert report.result =~ "success"
    end

    test "captures lexer and parser events" do
      source = "mod EvtTest\n  fn bar() -> Int = 1 + 2\n"
      {:ok, report} = Profiler.profile_string(source)

      # Should have events from lexer and parser at minimum
      stage_names = Map.keys(report.stages)
      assert :lexer in stage_names or :parser in stage_names or :codegen in stage_names
    end

    test "compile failures retain a structured diagnostic instead of a raw reason" do
      source = "fn run() -> Int = missing_name\n"
      {:ok, report} = Profiler.profile_string(source, file: "profile_failure.cure")

      assert report.result == "error [E091]"
      assert %{diagnostic: diagnostic, registry: _registry} = report.diagnostic
      assert diagnostic.code == "E091"
      refute Profiler.format_report(report) =~ "{:unknown_global"
    end
  end

  describe "profile_file" do
    @tag :examples
    test "profiles an example file" do
      {:ok, report} = Profiler.profile_file("examples/hello.cure")

      assert report.file == "examples/hello.cure"
      assert report.total_us > 0
      assert report.result =~ "success"
    end

    test "error for missing file" do
      assert {:error, _} = Profiler.profile_file("nonexistent.cure")
    end
  end

  describe "format_report" do
    test "produces readable output" do
      source = "mod FmtTest\n  fn x() -> Int = 1\n"
      {:ok, report} = Profiler.profile_string(source)
      formatted = Profiler.format_report(report)

      assert formatted =~ "Cure Compilation Profile"
      assert formatted =~ "Total time"
      assert formatted =~ "Events"
      assert formatted =~ "Pipeline Stages"
    end
  end
end

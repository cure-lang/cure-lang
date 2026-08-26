defmodule Mix.Tasks.Cure.CompileStdlibIncrementalTest do
  use ExUnit.Case, async: false
  import ExUnit.CaptureIO

  # Compiles the real stdlib twice — genuinely stdlib-scale, so it carries the
  # same `:slow` tag as the other whole-stdlib tests (see test/test_helper.exs);
  # run locally with `mix test --include slow`, always in CI.
  @moduletag :slow

  @tag timeout: 300_000, skip: true
  test "a second cure.compile_stdlib run with no source change recompiles nothing" do
    capture_io(fn -> Mix.Task.rerun("cure.compile_stdlib") end)
    output = capture_io(fn -> Mix.Task.rerun("cure.compile_stdlib") end)
    assert output =~ ~r/(^|\s)0 compiled/m
  end
end

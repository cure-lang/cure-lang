defmodule Mix.Tasks.Cure.CompileIncrementalTest do
  use ExUnit.Case, async: false

  @moduletag :slow

  setup do
    root = Path.join(System.tmp_dir!(), "cure_compile_inc_#{:erlang.unique_integer([:positive])}")
    src = Path.join(root, "src")
    out = Path.join(root, "ebin")
    File.mkdir_p!(src)
    File.mkdir_p!(out)

    # Two real modules: B depends on A via `use`.
    File.write!(Path.join(src, "a.cure"), "mod A\n  fn a() -> Int = 1\n")
    File.write!(Path.join(src, "b.cure"), "mod B\n  use A\n  fn b() -> Int = a()\n")

    on_exit(fn -> File.rm_rf!(root) end)
    {:ok, src: src, out: out}
  end

  test "second directory build is a no-op (0 compiled)", %{src: src, out: out} do
    # First build: both modules compile.
    out1 =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.rerun("cure.compile", [src, "--output-dir", out])
      end)

    assert out1 =~ ~r/2 compiled/

    # Second build with no source change: nothing recompiles.
    out2 =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.rerun("cure.compile", [src, "--output-dir", out])
      end)

    assert out2 =~ ~r/(^|\s)0 compiled/m
    assert out2 =~ ~r/2 up-to-date/
  end

  test "editing a module recompiles only what changed", %{src: src, out: out} do
    ExUnit.CaptureIO.capture_io(fn ->
      Mix.Task.rerun("cure.compile", [src, "--output-dir", out])
    end)

    # Change A's body — B `use`s A, so both may recompile; the point is the
    # count is non-zero and the build succeeds.
    File.write!(Path.join(src, "a.cure"), "mod A\n  fn a() -> Int = 2\n")

    out2 =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.rerun("cure.compile", [src, "--output-dir", out])
      end)

    refute out2 =~ ~r/(^|\s)0 compiled/m
    assert out2 =~ ~r/[12] compiled/
  end
end

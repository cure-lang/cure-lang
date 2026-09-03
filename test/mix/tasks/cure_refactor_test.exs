defmodule Mix.Tasks.Cure.RefactorTest do
  use ExUnit.Case, async: false

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_refactor_task_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)

    on_exit(fn ->
      File.rm_rf!(dir)
      Mix.Task.reenable("cure.refactor")
    end)

    {:ok, dir: dir}
  end

  test "JSON mode prints a report without changing the source", %{dir: dir} do
    path = Path.join(dir, "task.cure")
    source = "mod Task\n  fn value() -> Int = 7\n"
    File.write!(path, source)
    Mix.Task.reenable("cure.refactor")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        assert :ok = Mix.Task.run("cure.refactor", ["--json", path])
      end)

    assert output =~ "\"module\":\"Task\""
    assert output =~ "\"declaration_count\":1"
    assert File.read!(path) == source
  end

  test "plan mode exposes dependency components in JSON", %{dir: dir} do
    path = Path.join(dir, "planned_task.cure")
    source = "mod PlannedTask\n  fn entry() -> Int = 1\n"
    File.write!(path, source)
    Mix.Task.reenable("cure.refactor")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        assert :ok = Mix.Task.run("cure.refactor", ["--json", "--plan", path])
      end)

    assert output =~ "\"plan\":{"
    assert output =~ "\"component_count\":1"
    assert File.read!(path) == source
  end

  test "split mode applies the verified structural rewrite", %{dir: dir} do
    path = Path.join(dir, "split_task.cure")
    target = Path.join(dir, "helpers.cure")
    File.write!(path, "mod SplitTask\n  fn keep() -> Int = 2\n  fn move() -> Int = 1\nend\n")
    Mix.Task.reenable("cure.refactor")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        assert :ok =
                 Mix.Task.run("cure.refactor", [
                   "--split",
                   "helpers.cure:Extracted:move",
                   "--output-directory",
                   dir,
                   path
                 ])
      end)

    assert output =~ "(written)"
    assert File.exists?(target)
    assert File.read!(target) =~ "mod Extracted"
    refute File.read!(path) =~ "fn move()"
  end
end

defmodule Mix.Tasks.Cure.StoryTest do
  use ExUnit.Case, async: false

  setup do
    previous_shell = Mix.shell()
    previous_cwd = File.cwd!()
    Mix.shell(Mix.Shell.IO)

    dir = Path.join(System.tmp_dir!(), "cure_story_#{System.unique_integer([:positive])}")
    File.mkdir_p!(Path.join(dir, "lib"))
    File.cd!(dir)

    on_exit(fn ->
      File.cd!(previous_cwd)
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.story")
      File.rm_rf!(dir)
    end)

    {:ok, dir: dir}
  end

  test "unknown options fail through the shared E099 diagnostic" do
    Mix.Task.reenable("cure.story")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.story", ["--unknown"])) == {:shutdown, 1}
      end)

    assert output =~ "INVALID COMMAND USAGE [E099]"
    assert output =~ "Invalid arguments for mix cure.story"
    refute output =~ "wrote STORY.md"
  end

  test "unknown formats report the spelling and valid choices" do
    Mix.Task.reenable("cure.story")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.story", ["--format", "markdown"])) == {:shutdown, 1}
      end)

    assert output =~ "INVALID COMMAND USAGE [E099]"
    assert output =~ "Unknown story format 'markdown'"
    assert output =~ "Supported formats: md, html"
  end

  test "write failures render one unwrapped operational diagnostic", %{dir: dir} do
    output_path = Path.join([dir, "missing", "STORY.md"])
    Mix.Task.reenable("cure.story")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.story", ["--out", output_path])) == {:shutdown, 1}
      end)

    assert output =~ "COULD NOT WRITE FILE [E096]"
    assert output =~ output_path
    refute output =~ "cure.story: --"
    refute output =~ "{:file_write_error"
    refute output =~ "1 |"
  end
end

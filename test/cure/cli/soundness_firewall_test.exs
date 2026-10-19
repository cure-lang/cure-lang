defmodule Cure.CLI.SoundnessFirewallTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  @moduletag :tmp_dir
  @moduletag timeout: 600_000

  test "compile reports E014 and publishes no artifact for a reachable hole", %{tmp_dir: tmp} do
    source = Path.join(tmp, "holed.cure")
    output = Path.join(tmp, "ebin")

    File.write!(source, """
    mod SoundnessFirewallHoled
      pub fn probe(x: Int) -> Int = ?probe
    """)

    diagnostic =
      capture_io(:stderr, fn ->
        assert catch_exit(Cure.CLI.main(["compile", source, "-o", output])) == {:shutdown, 1}
      end)

    assert diagnostic =~ "[E014]"
    assert diagnostic =~ "probe"
    refute File.exists?(Path.join(output, "current"))
    assert [] = Path.wildcard(Path.join(output, "**/*.beam"))
  end

  test "the same compile publication path accepts a hole-free definition", %{tmp_dir: tmp} do
    source = Path.join(tmp, "clean.cure")
    output = Path.join(tmp, "ebin")

    File.write!(source, """
    mod SoundnessFirewallClean
      pub fn probe(x: Int) -> Int = x
    """)

    message = capture_io(fn -> Cure.CLI.main(["compile", source, "-o", output]) end)

    assert message =~ "Cure.SoundnessFirewallClean"
    artifact_root = Cure.Compiler.Artifacts.Writer.resolve(output)
    assert File.exists?(Path.join(artifact_root, "Cure.SoundnessFirewallClean.beam"))
  end
end

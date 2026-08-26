defmodule Mix.Tasks.Cure.VerifyTest do
  use ExUnit.Case, async: false

  setup do
    previous_shell = Mix.shell()
    Mix.shell(Mix.Shell.IO)

    dir = Path.join(System.tmp_dir!(), "cure_mix_verify_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    File.write!(Path.join(dir, "broken.cureproof"), <<0, 1, 2, 3>>)

    on_exit(fn ->
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.verify")
      File.rm_rf!(dir)
    end)

    {:ok, dir: dir}
  end

  test "corrupt proof artifacts use the structured verification diagnostic", %{dir: dir} do
    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        Mix.Task.reenable("cure.verify")
        assert catch_exit(Mix.Task.run("cure.verify", [dir])) == {:shutdown, 1}
      end)

    assert output =~ "[E066]"
    assert output =~ "Proof verification failed"
    assert output =~ "broken.cureproof"
  end

  test "unknown options fail as E099 before proof collection" do
    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        Mix.Task.reenable("cure.verify")
        assert catch_exit(Mix.Task.run("cure.verify", ["--unknown"])) == {:shutdown, 1}
      end)

    assert output =~ "INVALID COMMAND USAGE [E099]"
    assert output =~ "Usage: mix cure.verify"
    refute output =~ "Collecting proofs"
  end

  test "failed certificate details do not expose Core or raw reason terms", %{dir: dir} do
    proof_dir = Path.join(dir, "failed")
    File.mkdir_p!(proof_dir)

    certificate = %{
      module: "Demo.Proof",
      kind: :equality,
      statement: {:data, :SecretType, [], []},
      witness: {:forged_witness, {:global, :secret}}
    }

    File.write!(Path.join(proof_dir, "failed.cureproof"), Cure.Project.Proof.serialize([certificate]))

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        Mix.Task.reenable("cure.verify")
        assert catch_exit(Mix.Task.run("cure.verify", [proof_dir])) == {:shutdown, 1}
      end)

    assert output =~ "PROOF VERIFICATION FAILED [E066]"
    assert output =~ "certificate from Demo.Proof failed"
    assert output =~ "certificate witness was rejected"
    refute output =~ "SecretType"
    refute output =~ "forged_witness"
    refute output =~ "{:data"
    refute output =~ "{:global"
  end
end

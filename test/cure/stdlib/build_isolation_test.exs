defmodule Cure.Stdlib.BuildIsolationTest do
  use ExUnit.Case, async: true

  alias Cure.Stdlib.Paths

  test "test VMs share one immutable-generation publication root" do
    first = Paths.build_beam_dir(:test, "vm-a")
    second = Paths.build_beam_dir(:test, "vm-b")

    assert first == second
    assert first == Path.join(["_build", "cure", "test", "ebin"])
    assert String.ends_with?(first, "/ebin")
  end

  test "non-test builds retain the canonical development output" do
    assert Paths.build_beam_dir(:dev, "ignored") == Path.join(["_build", "cure", "ebin"])
    assert Paths.build_beam_dir(:prod, "ignored") == Path.join(["_build", "cure", "ebin"])
  end

  test "the test compile gate does not mutate packaged bundles or the shared escript" do
    compile_alias = Mix.Project.config() |> Keyword.fetch!(:aliases) |> Keyword.fetch!(:compile)

    assert "cure.compile_stdlib" in compile_alias
    refute "cure.bundle_stdlib" in compile_alias
    refute "cure.bundle_stdlib_beams" in compile_alias
    refute "cure.escript" in compile_alias
  end

  @tag timeout: 120_000
  test "two OS compiler VMs converge on one verified immutable generation" do
    root =
      Path.join(
        System.tmp_dir!(),
        "cure_cross_process_isolation_#{System.unique_integer([:positive])}"
      )

    File.mkdir_p!(root)
    on_exit(fn -> File.rm_rf!(root) end)

    source_root = Path.join(root, "source")
    output_root = Path.join(root, "output")
    File.mkdir_p!(source_root)
    File.write!(Path.join(source_root, "isolated.cure"), "mod Isolated\n  fn value() -> Int = 1\n")

    runs =
      for suffix <- ["A", "B"] do
        report = Path.join(root, "report_#{suffix}.etf")
        {suffix, source_root, output_root, report}
      end

    results =
      runs
      |> Enum.map(fn run -> Task.async(fn -> external_sweep(run) end) end)
      |> Enum.map(&Task.await(&1, 120_000))

    for {{_suffix, _source_root, _output_root, report}, {output, 0}} <- Enum.zip(runs, results) do
      assert output =~ "ok"
      {artifact_root, modules} = report |> File.read!() |> :erlang.binary_to_term([:safe])
      assert File.dir?(artifact_root)
      assert "Isolated" in modules
    end

    [{root_a, _}, {root_b, _}] =
      Enum.map(runs, fn {_suffix, _source_root, _output_root, report} ->
        report |> File.read!() |> :erlang.binary_to_term([:safe])
      end)

    assert root_a == root_b
  end

  defp external_sweep({_suffix, source_root, output_root, report}) do
    expression = """
    Application.ensure_all_started(:cure)
    output = System.fetch_env!("CURE_ISOLATION_OUTPUT")
    {:ok, result} = Cure.Compiler.Artifacts.sweep(
      kind: :stdlib,
      source_roots: [System.fetch_env!("CURE_ISOLATION_SOURCE")],
      output_dir: output,
      repair: true,
      compile_opts: [emit_events: false]
    )
    {:ok, set} = Cure.Compiler.Artifacts.open_verified_set(result.artifact_root)
    File.write!(System.fetch_env!("CURE_ISOLATION_REPORT"),
      :erlang.term_to_binary({result.artifact_root, Map.keys(set.modules)}))
    IO.puts("ok " <> result.artifact_root)
    """

    args =
      :code.get_path()
      |> Enum.flat_map(fn path -> ["-pa", List.to_string(path)] end)
      |> Kernel.++(["-e", expression])

    System.cmd(System.find_executable("elixir"), args,
      env: [
        {"CURE_ISOLATION_SOURCE", source_root},
        {"CURE_ISOLATION_OUTPUT", output_root},
        {"CURE_ISOLATION_REPORT", report}
      ],
      stderr_to_stdout: true
    )
  end
end

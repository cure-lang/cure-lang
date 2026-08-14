defmodule Cure.Compiler.InterfaceBenchmarkTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.InterfaceBenchmark

  test "ranks and bounds declaration hotspots deterministically" do
    timings = [
      %{module: "B", declaration: "slow", elapsed_us: 20},
      %{module: "A", declaration: "tie", elapsed_us: 10},
      %{module: "A", declaration: "also_tie", elapsed_us: 10},
      %{module: "A", declaration: "fast", elapsed_us: 1}
    ]

    assert InterfaceBenchmark.slowest(timings, 3) == [
             %{module: "B", declaration: "slow", elapsed_us: 20},
             %{module: "A", declaration: "also_tie", elapsed_us: 10},
             %{module: "A", declaration: "tie", elapsed_us: 10}
           ]
  end

  test "reports cold and warm module-interface timings separately" do
    root = Path.join(System.tmp_dir!(), "cure_interface_benchmark_#{System.unique_integer([:positive])}")
    path = Path.join(root, "bench.cure")
    File.mkdir_p!(root)
    suffix = System.unique_integer([:positive])
    File.write!(path, "mod Bench#{suffix}\n  fn answer() -> Int = 42\n")

    on_exit(fn -> File.rm_rf!(root) end)
    expected_module = "Bench#{suffix}"

    assert {:ok, report} = InterfaceBenchmark.run([path], warm_iterations: 2)
    assert report.pipeline == :canonical
    assert report.source_count == 1
    assert report.cold.total_us >= 0
    assert report.cold.call_attempts == []
    assert report.cold.rebuilt_modules == [expected_module]
    assert report.cold.phases.module_check >= 0
    assert Enum.any?(report.cold.totality_metrics, &(&1.operation == :direct_summary and &1.cache == :miss))
    assert Enum.any?(report.cold.totality_metrics, &(&1.operation == :scc_proposal))
    assert Enum.any?(report.cold.totality_metrics, &(&1.operation == :partition_verification))
    assert [%{modules: [^expected_module], elapsed_us: elapsed}] = report.cold.components
    assert elapsed >= 0

    assert [%{module: ^expected_module, declaration: "answer", elapsed_us: declaration_elapsed}] =
             report.cold.declarations

    assert declaration_elapsed >= 0

    assert Enum.map(report.cold.declaration_stages, & &1.stage) == [
             :macro_expansion,
             :signature,
             :induction,
             :typed_elaboration,
             :relevance,
             :core_packaging,
             :environment_publication,
             :totality,
             :equations
           ]

    assert Enum.all?(report.cold.declaration_stages, fn stage ->
             stage.module == expected_module and stage.declaration == "answer" and stage.elapsed_us >= 0
           end)

    # Component certification consumes the checked body's trusted direct-call
    # summary. It must not re-enter the legacy per-definition `check_def/2`
    # timing path and repeat type/body validation.
    assert report.cold.kernel_certificate_stages == []

    assert length(report.warm) == 2

    assert Enum.all?(report.warm, fn sample ->
             sample.total_us >= 0 and sample.call_attempts == [] and sample.rebuilt_modules == [] and
               sample.phases.module_check >= 0 and sample.totality_metrics == []
           end)
  end
end

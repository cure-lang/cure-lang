defmodule Mix.Tasks.Cure.Bench.Interfaces do
  @moduledoc """
  Measure cold and cached runs through the canonical module pipeline.

      mix cure.bench.interfaces
      mix cure.bench.interfaces lib/std/regex.cure --warm-iterations 5
      mix cure.bench.interfaces --top 30
  """

  use Mix.Task

  @shortdoc "Benchmarks cold/warm canonical module checking"

  @impl Mix.Task
  def run(args) do
    {opts, paths, invalid} =
      OptionParser.parse(args,
        strict: [warm_iterations: :integer, top: :integer],
        aliases: [n: :warm_iterations, t: :top]
      )

    if invalid != [], do: Mix.raise("invalid arguments: #{inspect(invalid)}")

    paths = if paths == [], do: Path.wildcard("lib/std/**/*.cure"), else: paths
    iterations = Keyword.get(opts, :warm_iterations, 3)
    top = Keyword.get(opts, :top, 20)

    if top < 0, do: Mix.raise("--top must be non-negative")

    case Cure.Compiler.InterfaceBenchmark.run(paths, warm_iterations: iterations) do
      {:ok, report} -> print_report(report, top)
      {:error, reason} -> Mix.raise("interface benchmark failed: #{inspect(reason)}")
    end
  end

  defp print_report(report, top) do
    Mix.shell().info(
      "pipeline=#{report.pipeline} sources=#{report.source_count} " <>
        "cold_ms=#{ms(report.cold.total_us)} rebuilt=#{length(report.cold.rebuilt_modules)}"
    )

    Mix.shell().info("component_ms\tmodules")

    report.cold.components
    |> Enum.sort_by(&{-&1.elapsed_us, &1.modules})
    |> Enum.take(top)
    |> Enum.each(fn component ->
      Mix.shell().info("#{ms(component.elapsed_us)}\t#{Enum.join(component.modules, ",")}")
    end)

    Mix.shell().info("declaration_ms\tmodule\tdeclaration")

    report.cold.declarations
    |> Cure.Compiler.InterfaceBenchmark.slowest(top)
    |> Enum.each(fn declaration ->
      Mix.shell().info("#{ms(declaration.elapsed_us)}\t#{declaration.module}\t#{declaration.declaration}")
    end)

    Mix.shell().info("declaration_stage_ms\tmodule\tdeclaration\tstage")

    report.cold.declaration_stages
    |> Cure.Compiler.InterfaceBenchmark.slowest(top)
    |> Enum.each(fn stage ->
      Mix.shell().info("#{ms(stage.elapsed_us)}\t#{stage.module}\t#{stage.declaration}\t#{stage.stage}")
    end)

    Mix.shell().info("kernel_certificate_stage_ms\tdefinition\tstage")

    report.cold.kernel_certificate_stages
    |> Cure.Compiler.InterfaceBenchmark.slowest(top)
    |> Enum.each(fn stage ->
      Mix.shell().info("#{ms(stage.elapsed_us)}\t#{stage.definition}\t#{stage.stage}")
    end)

    report.warm
    |> Enum.with_index(1)
    |> Enum.each(fn {sample, index} ->
      Mix.shell().info(
        "warm_#{index}_ms=#{ms(sample.total_us)} rebuilt=#{length(sample.rebuilt_modules)} " <>
          "module_check_ms=#{ms(Map.get(sample.phases, :module_check, 0))}"
      )
    end)
  end

  defp ms(microseconds), do: :erlang.float_to_binary(microseconds / 1_000, decimals: 3)
end

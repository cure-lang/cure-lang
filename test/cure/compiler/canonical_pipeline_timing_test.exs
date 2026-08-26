defmodule Cure.Compiler.CanonicalPipelineTimingTest do
  use ExUnit.Case, async: false

  @moduletag :tmp_dir

  test "reports canonical phase and component timings through the request event sink", %{tmp_dir: dir} do
    provider = Path.join(dir, "provider.cure")
    consumer = Path.join(dir, "consumer.cure")
    File.write!(provider, "mod Timing.Provider\n  fn value() -> Int = 41\n")
    File.write!(consumer, "mod Timing.Consumer\n  use Timing.Provider\n  fn result() -> Int = value() + 1\n")

    owner = self()

    assert {:ok, _checked} =
             Cure.Compiler.ModulePipeline.check([consumer, provider],
               module_pipeline: :canonical,
               package: "timing",
               source_roots: [dir],
               event_sink: &send(owner, {:pipeline_event, &1})
             )

    events = drain_events([])

    for phase <- [:interface_load, :manifest, :expansion, :module_check] do
      assert Enum.any?(events, &match?({:module_pipeline_timing, ^phase, elapsed, _} when elapsed >= 0, &1))
    end

    components =
      for {:module_pipeline_timing, :component, elapsed, %{modules: modules}} <- events do
        assert elapsed >= 0
        modules
      end

    assert components == [["Timing.Provider"], ["Timing.Consumer"]]

    preparations =
      for {:module_pipeline_preparation, module, declaration_count} <- events do
        assert declaration_count >= 1
        module
      end

    assert preparations == ["Timing.Provider", "Timing.Consumer"]

    for phase <- [:component_register, :component_merge, :component_bodies, :component_freeze] do
      assert Enum.count(
               events,
               &match?({:module_pipeline_timing, ^phase, elapsed, %{modules: [_]}} when elapsed >= 0, &1)
             ) == 2
    end

    declarations =
      for {:module_pipeline_timing, :declaration, elapsed, %{module: module, declaration: declaration}} <- events do
        assert elapsed >= 0
        {module, declaration}
      end

    assert declarations == [{"Timing.Provider", "value"}, {"Timing.Consumer", "result"}]

    for stage <- [:macro_expansion, :signature, :induction, :typed_elaboration] do
      assert Enum.count(
               events,
               &match?(
                 {:module_pipeline_timing, :declaration_stage, elapsed, %{module: _, declaration: _, stage: ^stage}}
                 when elapsed >= 0,
                 &1
               )
             ) == 2
    end
  end

  defp drain_events(events) do
    receive do
      {:pipeline_event, event} -> drain_events([event | events])
    after
      0 -> Enum.reverse(events)
    end
  end
end

defmodule Antigen.CoverageBaselineRefreshTest do
  use ExUnit.Case, async: false
  import ExUnit.CaptureIO
  alias Antigen.{Challenge, Corpus, Cover, CoverageBaseline}

  @moduletag :cover_machinery

  setup do
    cwd = File.cwd!()
    root = Path.join(System.tmp_dir!(), "antigen-floor-refresh-#{System.unique_integer([:positive])}")
    File.mkdir_p!(Path.join(root, "test/antigen"))
    File.cd!(root)

    on_exit(fn ->
      File.cd!(cwd)
      File.rm_rf!(root)
    end)

    for path <- CoverageBaseline.replay_paths(), do: File.write!(path, "")

    record =
      Challenge.new(
        kind: :malformed,
        assay: "term/rejection",
        label: :ill_typed,
        payload: %{sig: :v1, ctx: [], term: {:app, {:atom_lit, :ok}, {:atom_lit, :ok}}}
      )
      |> Corpus.encode_record()

    File.write!(CoverageBaseline.coverage_path(), record <> "\n")
    floor = Map.new(Cover.cover_modules(), &{&1, %{covered: 0, total: 0}})
    CoverageBaseline.write_baseline(floor)
    %{floor: floor}
  end

  test "the explicit task refreshes real totals without changing thresholds or records", %{floor: old_floor} do
    before = corpus_bytes()

    output =
      capture_io(fn ->
        Mix.Tasks.Antigen.run(["cover", "--refresh-existing-coverage-baseline"])
      end)

    assert output =~ "Antigen existing replay: 1 records preserved"
    assert before == corpus_bytes()
    assert {:ok, floor} = CoverageBaseline.read_baseline()
    assert MapSet.new(Map.keys(floor)) == MapSet.new(Cover.cover_modules())
    assert Enum.all?(floor, fn {_, entry} -> entry.total > 0 end)

    assert Map.new(floor, fn {module, entry} -> {module, entry.covered} end) ==
             Map.new(old_floor, fn {module, entry} -> {module, entry.covered} end)

    refute output =~ "observed 0 covered lines"
  end

  test "no covered-line floor can be lowered", %{floor: floor} do
    CoverageBaseline.write_baseline(Map.put(floor, Cure.Core.Kernel, %{covered: 1_000_000, total: 1_000_000}))
    before = File.read!(CoverageBaseline.baseline_path())

    assert_raise RuntimeError, ~r/cannot lower/, fn ->
      CoverageBaseline.refresh_existing!()
    end

    assert File.read!(CoverageBaseline.baseline_path()) == before
  end

  test "bad replay or an incomplete floor cannot produce a new baseline", %{floor: floor} do
    before = File.read!(CoverageBaseline.baseline_path())
    File.write!(CoverageBaseline.coverage_path(), "not-a-record\n")

    assert_raise RuntimeError, ~r/replay failures/, fn ->
      CoverageBaseline.refresh_existing!()
    end

    assert File.read!(CoverageBaseline.baseline_path()) == before
    CoverageBaseline.write_baseline(Map.take(floor, [Cure.Core.Kernel]))
    incomplete = File.read!(CoverageBaseline.baseline_path())

    assert_raise RuntimeError, ~r/module set/, fn ->
      CoverageBaseline.refresh_existing!()
    end

    assert File.read!(CoverageBaseline.baseline_path()) == incomplete
  end

  test "refresh cannot accidentally select a sampling or banking command" do
    for args <- [
          ["--refresh-existing-coverage-baseline"],
          ["cover", "--refresh-existing-coverage-baseline", "--count", "10"],
          ["cover", "--refresh-existing-coverage-baseline", "--unknown"],
          ["cover", "--no-refresh-existing-coverage-baseline"],
          ["cover", "--refresh-existing-coverage-baseline", "--no-refresh-existing-coverage-baseline"],
          ["cover", "--refresh-existing-coverage-baseline", "--refresh-existing-coverage-baseline"],
          ["cover", "--refresh-existing-coverage-baseline=false", "--refresh-existing-coverage-baseline"],
          ["cover", "--refresh-existing-coverage-baseline", "--refresh-existing-coverage-baseline=true"],
          ["cover", "--refresh-existing-coverage-baseline", "--record-new-coverage-baseline"]
        ] do
      assert_raise Mix.Error, fn -> Mix.Tasks.Antigen.run(args) end
    end
  end

  test "a transient lower floor cannot replace the captured authorization", %{floor: floor} do
    CoverageBaseline.write_baseline(Map.put(floor, Cure.Core.Kernel, %{covered: 1_000_000, total: 1_000_000}))
    original = File.read!(CoverageBaseline.baseline_path())

    assert_raise RuntimeError, ~r/cannot lower/, fn ->
      CoverageBaseline.refresh_existing!(
        on_checkpoint: fn
          :snapshot_captured -> CoverageBaseline.write_baseline(floor)
          :measurement_complete -> File.write!(CoverageBaseline.baseline_path(), original)
        end
      )
    end

    assert File.read!(CoverageBaseline.baseline_path()) == original
  end

  test "captured records, not transient replacement bytes, are the measured inputs" do
    before = corpus_bytes()

    assert %{records: 1, floor: persisted, measured: observed} =
             CoverageBaseline.refresh_existing!(
               on_checkpoint: fn
                 :snapshot_captured ->
                   File.write!(CoverageBaseline.coverage_path(), "not-the-captured-record\n")

                 :measurement_complete ->
                   File.write!(CoverageBaseline.coverage_path(), Map.fetch!(before, CoverageBaseline.coverage_path()))
               end
             )

    assert corpus_bytes() == before

    for module <- Cover.cover_modules() do
      assert persisted[module].covered == 0
      assert persisted[module].total == observed[module].total
    end

    assert observed[Cure.Core.Kernel].covered > 0
  end

  test "a decoded challenge that fails under instrumentation cannot ratchet the floor" do
    challenge =
      Challenge.new(
        kind: :malformed,
        assay: "term/rejection",
        label: :ill_typed,
        payload: %{sig: :v1, ctx: [], term: {:ctor, :Z, []}}
      )

    File.write!(CoverageBaseline.coverage_path(), Corpus.encode_record(challenge) <> "\n")
    original = File.read!(CoverageBaseline.baseline_path())

    assert_raise RuntimeError, ~r/instrumented replay failures/, fn ->
      CoverageBaseline.refresh_existing!()
    end

    assert File.read!(CoverageBaseline.baseline_path()) == original
  end

  defp corpus_bytes, do: Map.new(CoverageBaseline.replay_paths(), &{&1, File.read!(&1)})
end

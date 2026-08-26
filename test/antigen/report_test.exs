defmodule Antigen.ReportTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Report}

  @tmp "tmp/antigen_report_test"
  setup do
    File.rm_rf!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "write_infection writes a full report and updates latest.txt before returning" do
    c =
      Challenge.new(
        kind: :stub,
        assay: "totality/diverging",
        label: :diverging,
        payload: %{term: {:type, 0}},
        seed: 12345
      )

    assert {:ok, path} = Report.write_infection(@tmp, c, {:violation, :wrongly_certified}, %{discard_rate: 0.0})
    assert File.exists?(path)
    body = File.read!(path)
    assert body =~ "totality/diverging"
    assert body =~ "12345"
    assert body =~ "wrongly_certified"
    assert File.read!(Path.join(@tmp, "latest.txt")) =~ Path.basename(path)
  end

  test "breadcrumb is a single grep-surviving line naming the assay, seed, and file" do
    c =
      Challenge.new(
        kind: :stub,
        assay: "totality/diverging",
        label: :diverging,
        payload: %{term: {:type, 0}},
        seed: 999
      )

    line = Report.breadcrumb(c, "tmp/antigen/failure-999-totality_diverging-1.txt")
    refute line =~ "\n"
    assert line =~ "ANTIGEN INFECTION" and line =~ "totality/diverging" and line =~ "seed=999"
  end
end

defmodule Antigen.ReportTest.TriageLine do
  use ExUnit.Case, async: false
  alias Antigen.{Report, Challenge}

  defp ch, do: Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:ctor, :Z, []}}, seed: 3)

  test "render includes a triage line when the health map carries :triage" do
    tmp = Path.join(System.tmp_dir!(), "antigen-report-#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)

    health = %{
      discard_rate: 0.0,
      coverage: MapSet.new(),
      triage: %{orig_size: 27, min_size: 9, bisect_drops: 2, shrink_rewrites: 11}
    }

    {:ok, path} = Report.write_infection(tmp, ch(), {:boom, :x}, health)
    body = File.read!(path)
    # Assert the DISTINCTIVE formatted triage line, not substrings that `inspect(health)`
    # would already emit for the map's `triage:` key (`orig_size: 27, bisect_drops: 2, …`).
    # `size 27→9`, `bisect −2 elems`, `shrink −11 rewrites` are produced ONLY by
    # `triage_line/1` — so this genuinely pins the dedicated line, not the inspected map.
    assert body =~ "triage:"
    assert body =~ "size 27→9"
    assert body =~ "bisect −2 elems"
    assert body =~ "shrink −11 rewrites"
  end

  test "render omits the triage line when :triage absent" do
    tmp = Path.join(System.tmp_dir!(), "antigen-report-#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)
    {:ok, path} = Report.write_infection(tmp, ch(), {:boom, :x}, %{discard_rate: 0.0, coverage: MapSet.new()})
    refute File.read!(path) =~ "triage:"
  end
end

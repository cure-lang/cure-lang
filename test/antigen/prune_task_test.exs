defmodule Mix.Tasks.Antigen.PruneTest do
  use ExUnit.Case, async: true
  import ExUnit.CaptureIO
  alias Antigen.{Challenge, Corpus}

  @tmp "tmp/antigen_prune_task_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "runs prune on the given paths and prints a tally" do
    corpus = Path.join(@tmp, "corpus.sexp")
    retired = Path.join(@tmp, "retired.sexp")
    keep = Corpus.encode_record(Challenge.stub({:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}}))

    original = Corpus.encode_record(Challenge.stub({:type, Cure.Core.Sort.finite_closed(1)}))

    bad_piece =
      [["term", "(cure-core 2 (zzz_unknown_node 1))"]] |> :json.encode() |> IO.iodata_to_binary() |> Base.encode64()

    bad = Regex.replace(~r/pieces64=[^\t]*$/, original, "pieces64=" <> bad_piece)
    refute bad == original
    assert {:error, _} = Corpus.decode_record(bad)

    File.write!(corpus, keep <> "\n" <> bad <> "\n")

    out =
      capture_io(fn ->
        Mix.Tasks.Antigen.Prune.run(["--corpus", corpus, "--retired", retired])
      end)

    assert out =~ "antigen prune: 1 kept, 1 retired"
    assert File.read!(corpus) |> String.split("\n", trim: true) == [keep]
    assert File.read!(retired) =~ "# retired:"
  end
end

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
    keep = Corpus.encode_record(Challenge.stub({:type, 0}))

    bad =
      Regex.replace(~r/pieces=.*$/, Corpus.encode_record(Challenge.stub({:type, 1})), "pieces=t::(zzz_unknown_node 1)")

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

defmodule Antigen.PruneTest do
  @moduledoc """
  `Antigen.Prune.prune/3` — re-check antibody records against the live kernel via
  the shared replay registry; keep the ones that decode and replay `:ok`, move the
  rest verbatim to a retirement store with a reason. Never rewrites a term; a run
  that retires nothing leaves the corpus byte-identical. All I/O is on tmp copies
  (the committed stores are never touched).
  """
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus, Prune, Runner}

  @tmp "tmp/antigen_prune_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  defp path(name), do: Path.join(@tmp, name)
  defp stub_rec(term), do: Corpus.encode_record(Challenge.stub(term))

  # A record that decodes cleanly but whose term uses a head the grammar rejects —
  # surgically swap the pieces field of a valid stub record (key= precedes pieces=
  # in the encoding, so the stored key stays intact).
  defp undecodable_rec do
    Regex.replace(~r/pieces=.*$/, stub_rec({:type, 7}), "pieces=t::(zzz_unknown_node 1)")
  end

  defp write(name, lines) do
    p = path(name)
    File.write!(p, Enum.join(lines, "\n") <> "\n")
    p
  end

  test "keeps a replay-:ok record and retires an undecodable one, with a reason" do
    keep = stub_rec({:type, 0})
    bad = undecodable_rec()
    corpus = write("corpus.sexp", [keep, bad])
    retired = path("retired.sexp")

    tally = Prune.prune(corpus, retired)

    assert tally.kept == 1
    assert tally.retired == 1
    assert [{:decode_error, _}] = tally.reasons

    # kept record survives byte-identically; the bad one is gone
    got = corpus |> File.read!() |> String.split("\n", trim: true)
    assert got == [keep]

    # the retired store carries the reason and the verbatim record
    retired_text = File.read!(retired)
    assert retired_text =~ "# retired: {:decode_error"
    assert retired_text =~ bad
  end

  test "retires a label-drift record (decodes, replays a non-:ok verdict)" do
    defmodule DriftAssay do
      def run(_c), do: {:violation, :drift}
    end

    rec = stub_rec({:type, 0})
    corpus = write("corpus.sexp", [rec])
    retired = path("retired.sexp")

    tally = Prune.prune(corpus, retired, %{"stub" => DriftAssay})

    assert tally.kept == 0
    assert [{:label_drift, :drift}] = tally.reasons
    assert File.read!(retired) =~ "# retired: {:label_drift, :drift}"
    assert File.read!(corpus) == ""
  end

  test "leaves an all-green corpus byte-identical and writes no retirement file" do
    a = stub_rec({:type, 1})
    b = stub_rec({:type, 2})
    corpus = write("corpus.sexp", [a, b])
    retired = path("retired.sexp")
    before = File.read!(corpus)

    tally = Prune.prune(corpus, retired, Runner.replay_registry())

    assert tally == %{kept: 2, retired: 0, reasons: []}
    assert File.read!(corpus) == before
    refute File.exists?(retired)
  end
end

defmodule Antigen.CorpusMergeTest do
  @moduledoc """
  `Antigen.Corpus.merge/2` — fold scattered record files into a master, deduplicating
  by each record's embedded key, byte-preserving. Guards the recovery path for replay
  values banked to a scratch/tmp directory (see `mix antigen.merge`).
  """
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus}

  @tmp "tmp/antigen_corpus_merge_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  defp path(name), do: Path.join(@tmp, name)
  defp rec(term), do: Corpus.encode_record(Challenge.stub(term))

  defp write(name, lines) do
    p = path(name)
    File.write!(p, Enum.join(lines, "\n") <> "\n")
    p
  end

  defp lines_of(p), do: p |> File.read!() |> String.split("\n", trim: true)

  test "merges only records whose key is not already in dest (union, not concat)" do
    a = rec({:type, 0})
    b = rec({:type, 1})
    c = rec({:type, 2})

    dest = write("dest.sexp", [a, b])
    src = write("src.sexp", [b, c])

    assert %{added: 1, duplicate: 1, keyless: 0} = Corpus.merge(dest, [src])

    got = lines_of(dest)
    assert length(got) == 3
    # verbatim copy — the new record is byte-identical to the source line
    assert c in got
    # b was already present and not re-appended
    assert Enum.count(got, &(&1 == b)) == 1
  end

  test "deduplicates across multiple sources within one call" do
    a = rec({:type, 0})
    c = rec({:type, 2})

    dest = write("dest.sexp", [a])
    s1 = write("s1.sexp", [c])
    s2 = write("s2.sexp", [c])

    # c is new the first time it is seen, a duplicate the second — even though dest
    # never contained it before this call.
    assert %{added: 1, duplicate: 1} = Corpus.merge(dest, [s1, s2])
    assert Enum.count(lines_of(dest), &(&1 == c)) == 1
  end

  test "skips and counts keyless lines (no dedup identity)" do
    a = rec({:type, 0})
    dest = write("dest.sexp", [a])
    src = write("src.sexp", ["this line has no key= field", rec({:type, 3})])

    assert %{added: 1, keyless: 1} = Corpus.merge(dest, [src])
    refute Enum.any?(lines_of(dest), &(&1 =~ "no key="))
  end

  test "a missing source contributes nothing (no crash)" do
    a = rec({:type, 0})
    dest = write("dest.sexp", [a])

    assert %{added: 0, duplicate: 0, keyless: 0} = Corpus.merge(dest, [path("does_not_exist.sexp")])
    assert lines_of(dest) == [a]
  end

  test "merging into a non-existent dest creates it with the source's records" do
    c = rec({:type, 2})
    src = write("src.sexp", [c])
    dest = path("fresh.sexp")

    assert %{added: 1} = Corpus.merge(dest, [src])
    assert lines_of(dest) == [c]
  end

  test "a dest without a trailing newline is not glued onto by the appended record" do
    a = rec({:type, 0})
    c = rec({:type, 2})
    dest = path("dest.sexp")
    # no trailing newline
    File.write!(dest, a)
    src = write("src.sexp", [c])

    assert %{added: 1} = Corpus.merge(dest, [src])
    got = lines_of(dest)
    assert got == [a, c]
  end
end

defmodule Antigen.UniverseCorpusFormatTest do
  use ExUnit.Case, async: true

  alias Antigen.{Challenge, Corpus}
  alias Cure.Core.{Serialize, UniverseCodec, UniverseLevel}

  test "current JSON pieces64 round-trip closed, open, limit and primitive level syntax" do
    for term <- [
          {:type, {:finite, UniverseLevel.closed(37)}},
          {:type, {:finite, UniverseLevel.atom({:var, 0})}},
          {:type, {:omega, Integer.pow(10, 100)}},
          {:level_type},
          {:level_value, UniverseLevel.succ(UniverseLevel.atom({:var, 0}))}
        ] do
      original = Challenge.stub(term)
      line = Corpus.encode_record(original)
      assert line =~ "\tformat=2\t"
      assert line =~ "\tuniverse=#{Corpus.universe_epoch()}\t"
      assert fields(line)["pieces64"] |> Base.decode64!() |> :json.decode() == [["term", Serialize.encode(term)]]
      assert {:ok, ^original} = Corpus.decode_record(line)
    end
  end

  test "family result sorts are hash-visible and survive the whole current corpus carrier" do
    challenge = fn sort ->
      family = %{name: :F, params: [{:u, {:level_type}}], indices: [], sort: sort}
      Challenge.new(kind: :family, assay: "universes", label: :positive, payload: %{family: family, ctors: []})
    end

    low = challenge.({:finite, UniverseLevel.closed(0)})
    high = challenge.({:finite, UniverseLevel.closed(37)})
    refute Corpus.dedup_key(low, :antibody) == Corpus.dedup_key(high, :antibody)

    for original <- [low, high, challenge.({:finite, UniverseLevel.atom({:var, 0})}), challenge.({:omega, 0})] do
      assert {:ok, ^original} = original |> Corpus.encode_record() |> Corpus.decode_record()
    end
  end

  test "piece data containing old delimiters, quotes, Unicode and newlines remains one record" do
    original = Challenge.stub({:hole, "old;;piece::delimiters\tand\nquotes\" café %"})
    line = Corpus.encode_record(original)
    refute String.contains?(line, "\n")
    assert {:ok, ^original} = Corpus.decode_record(line)
  end

  test "all dedup identities include the universe checker epoch, including zero-piece challenges" do
    ordinary = Challenge.stub({:atom_type})
    empty = Challenge.new(kind: :kernel_probe, assay: "kernel", label: :none, payload: %{probe: :infer_absurd})
    prefix = "antigen/2|" <> Corpus.universe_epoch() <> "|"

    for challenge <- [ordinary, empty], kind <- [:seed, :antibody] do
      assert String.starts_with?(Corpus.dedup_key(challenge, kind), prefix)
    end

    line = Corpus.encode_record(ordinary, "caller-key")
    assert Corpus.raw_key(line) == prefix <> "caller-key"
    refute Corpus.raw_key(line) == "caller-key"
  end

  test "format, checker identity, duplicate fields and obsolete carrier names fail closed" do
    line = Corpus.encode_record(Challenge.stub({:atom_type}))

    for bad <- [
          delete_field(line, "format"),
          set_field(line, "format", "1"),
          set_field(line, "universe", "fixed-ceiling"),
          line <> "\tformat=2",
          line <> "\tunknown=ignored",
          line <> "\tpieces=term::(atom-type)",
          set_field(line, "key", Base.encode64("unversioned")),
          "antigen-record\tkind=stub\tpieces=term::(type 0)"
        ] do
      assert {:error, _} = Corpus.decode_record(bad)
      assert is_nil(Corpus.raw_key(bad))
    end
  end

  test "missing, duplicate, unknown and malformed JSON piece IDs never get overwritten or ignored" do
    line = Corpus.encode_record(Challenge.stub({:atom_type}))
    wire = Serialize.encode({:atom_type})

    for rows <- [
          [],
          [["term", wire], ["term", wire]],
          [["term", wire], ["ignored", wire]],
          [["other", wire]],
          [["term"]],
          [["term", 0]],
          [["term", "(type 0)"]],
          %{"term" => wire}
        ] do
      assert {:error, _} = Corpus.decode_record(set_field(line, "pieces64", json64(rows)))
    end
  end

  test "record and JSON budgets reject before unbounded current reconstruction" do
    line = Corpus.encode_record(Challenge.stub({:atom_type}))
    assert {:error, _} = Corpus.decode_record(String.duplicate("x", UniverseCodec.max_bytes() + 1))
    nested = String.duplicate("[", 300) <> String.duplicate("]", 300)
    assert {:error, _} = Corpus.decode_record(set_field(line, "pieces64", Base.encode64(nested)))
    assert {:error, _} = Corpus.decode_record(set_field(line, "pieces64", "not-base64"))
    assert {:error, _} = Corpus.decode_record(set_field(line, "pieces64", Base.encode64(:erlang.term_to_binary([]))))
  end

  test "opaque scaffold decoder refuses compressed ETF and runtime host values" do
    compressed = :erlang.term_to_binary(%{"data" => String.duplicate("x", 1000)}, [:compressed])
    assert <<131, 80, _::binary>> = compressed
    assert_raise ArgumentError, fn -> Corpus.decode_scaffold(Base.encode64(compressed)) end

    for value <- [%{"pid" => self()}, %{"struct" => UniverseLevel.zero()}, []] do
      assert_raise ArgumentError, fn ->
        Corpus.decode_scaffold(Base.encode64(:erlang.term_to_binary(value)))
      end
    end
  end

  @tag :tmp_dir
  test "append rejects non-whitelist-independent decoding errors and never writes the bad record", %{tmp_dir: root} do
    path = Path.join(root, "bad.sexp")
    invalid = %{Challenge.stub({:atom_type}) | seed: "not-an-integer"}
    assert {:rejected, _} = Corpus.append(path, invalid, "bad")
    refute File.exists?(path)
  end

  @tag :tmp_dir
  test "merge preserves current bytes but does not silently import historical record identity", %{tmp_dir: root} do
    current = Corpus.encode_record(Challenge.stub({:atom_type}))
    historical = "antigen-record\tkey=" <> Base.encode64("old") <> "\tpieces=term::(type 0)"
    source = Path.join(root, "source.sexp")
    destination = Path.join(root, "merged.sexp")
    File.write!(source, historical <> "\n" <> current <> "\n")
    assert %{added: 1, duplicate: 0, keyless: 1} = Corpus.merge(destination, [source])
    assert File.read!(destination) == current <> "\n"
    assert File.read!(source) == historical <> "\n" <> current <> "\n"
  end

  test "fault64 preserves all supported diagnostic value shapes without minting atoms" do
    fault = %{
      kind: :universe,
      witness: :level,
      expected_head: {:type, {:finite, UniverseLevel.closed(0)}},
      injected_head: {:type, {:finite, UniverseLevel.closed(37)}},
      scope: {2, 2},
      depth: 2,
      wrap_path: [:app_arg, :pair],
      reduction: :required,
      required: true,
      carrier: :conv_index,
      expected_index: 0,
      actual_index: 1
    }

    for fault <- [fault, %{fault | scope: nil, expected_head: :Nat, injected_head: :Vec}] do
      original = mutant(fault)
      line = Corpus.encode_record(original)
      refute line =~ "\tfault="
      assert line =~ "\tfault64="
      assert {:ok, ^original} = Corpus.decode_record(line)
    end
  end

  test "unknown fault atoms, wrappers, depths, fields and extra value tags fail closed" do
    line = Corpus.encode_record(mutant(%{kind: :universe, depth: 0, wrap_path: []}))
    base = fields(line)["fault64"] |> Base.decode64!() |> :json.decode()
    unknown = "not_a_known_fault_atom_#{System.unique_integer([:positive])}"
    assert_raise ArgumentError, fn -> String.to_existing_atom(unknown) end

    for bad <- [
          Map.put(base, "kind", %{"tag" => "atom", "value" => unknown}),
          Map.put(base, "depth", %{"tag" => "integer", "value" => -1}),
          Map.put(base, "depth", %{"tag" => "integer", "value" => 257}),
          Map.put(base, "wrap_path", %{"tag" => "list", "value" => ["Nat"]}),
          Map.put(base, "wrap_path", %{"tag" => "list", "value" => [unknown]}),
          Map.put(base, "kind", %{"tag" => "atom", "value" => "universe", "trusted" => true}),
          Map.put(base, "expected_head", %{"tag" => "core_syntax", "value" => "(type 0)"}),
          Map.put(base, "expected_head", %{"tag" => "checked_core", "value" => "(cure-core 2 (atom-type))"}),
          Map.put(base, "Nat", %{"tag" => "nil"})
        ] do
      assert {:error, _} = Corpus.decode_record(set_field(line, "fault64", json64(bad)))
    end

    assert_raise ArgumentError, fn -> String.to_existing_atom(unknown) end
    assert {:error, _} = Corpus.decode_record(line <> "\tfault=((kind universe))")
    duplicate_keys = ~s({"kind":{"tag":"atom","value":"universe"},"kind":{"tag":"atom","value":"scope"}})
    assert {:error, _} = Corpus.decode_record(set_field(line, "fault64", Base.encode64(duplicate_keys)))
  end

  @tag :tmp_dir
  test "malformed diagnostic metadata cannot be banked or recast as canonical Core evidence", %{tmp_dir: root} do
    path = Path.join(root, "invalid-fault.sexp")

    for fault <- [%{depth: -1}, %{wrap_path: [:Nat]}, %{expected_head: {:type, 0}}, %{scope: self()}] do
      assert {:rejected, _} = Corpus.append(path, mutant(fault), "invalid")
      refute File.exists?(path)
    end
  end

  @tag :tmp_dir
  test "fresh replay VM decodes current fault64 and fixed universe primitive names", %{tmp_dir: root} do
    original = mutant(%{kind: :universe, expected_head: {:global, :universe_succ}, depth: 0, wrap_path: []})
    path = Path.join(root, "current.sexp")
    File.write!(path, Corpus.encode_record(original))
    paths = :code.get_path() |> Enum.flat_map(fn path -> ["-pa", path |> List.to_string() |> Path.expand()] end)

    script =
      "case Antigen.Corpus.decode_record(File.read!(hd(System.argv()))) do {:ok, _} -> IO.inspect(:ok); error -> IO.inspect(error) end"

    {output, 0} = System.cmd(System.find_executable("elixir"), paths ++ ["-e", script, "--", path])
    assert String.trim(output) == ":ok"
  end

  defp mutant(fault) do
    Challenge.new(
      kind: :mutant_term,
      assay: "mutation/rejection",
      label: :ill_typed,
      payload: %{sig: :v1, ctx: [], type: {:atom_type}, term: {:atom_lit, :ok}, fault: fault}
    )
  end

  defp fields(line) do
    [_marker | rest] = String.split(line, "\t")

    Map.new(rest, fn field ->
      [key, value] = String.split(field, "=", parts: 2)
      {key, value}
    end)
  end

  defp set_field(line, key, value) do
    [marker | rest] = String.split(line, "\t")

    rest =
      Enum.map(rest, fn field -> if String.starts_with?(field, key <> "="), do: key <> "=" <> value, else: field end)

    Enum.join([marker | rest], "\t")
  end

  defp delete_field(line, key),
    do: line |> String.split("\t") |> Enum.reject(&String.starts_with?(&1, key <> "=")) |> Enum.join("\t")

  defp json64(value), do: value |> :json.encode() |> IO.iodata_to_binary() |> Base.encode64()
end

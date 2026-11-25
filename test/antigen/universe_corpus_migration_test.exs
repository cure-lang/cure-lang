defmodule Antigen.UniverseCorpusMigrationTest do
  use ExUnit.Case, async: false
  alias Antigen.Corpus
  alias Antigen.Corpus.{LegacyImport, Migration}
  alias Cure.Core.Sort

  @fixture "test/antigen/fixtures/pre_universe_corpus_v2"
  @era [from: :fixed_ceiling_v1]

  defp legacy(opts \\ []) do
    fields = [
      {"kind", "stub"},
      {"assay", "stub"},
      {"label", "none"},
      {"seed", "-"},
      {"note", "-"},
      {"scaffold", "-"},
      {"key", Base.encode64("historical-key")},
      {"pieces", "term::(type 0)"}
    ]

    "antigen-record\t" <>
      Enum.map_join(fields, "\t", fn {key, default} ->
        key <> "=" <> Keyword.get(opts, String.to_existing_atom(key), default)
      end)
  end

  test "unknown text and safe ETF symbols never grow the atom table" do
    name = "antigen_migration_poison_#{System.unique_integer([:positive])}"
    assert_raise ArgumentError, fn -> :erlang.binary_to_existing_atom(name, :utf8) end
    assert {:error, _} = LegacyImport.decode_record(legacy(pieces: "term::(global #{name})"), @era)
    etf = <<131, 116, 1::32, 109, 1::32, "x", 119, byte_size(name), name::binary>>
    assert {:error, _} = LegacyImport.decode_record(legacy(scaffold: Base.encode64(etf)), @era)
    assert_raise ArgumentError, fn -> :erlang.binary_to_existing_atom(name, :utf8) end
  end

  defp opaque(value), do: value |> :erlang.term_to_binary([:deterministic]) |> Base.encode64()

  setup do
    tmp = Path.join(System.tmp_dir!(), "antigen-migration-test-#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)
    %{tmp: tmp}
  end

  test "all five archived preimage files exist, including the exact empty reach store" do
    inventory = Path.join(@fixture, "inventory.json") |> File.read!() |> :json.decode()
    records = inventory["files"] ++ inventory["inactive_preimages"]

    for name <- ~w(corpus.sexp seeds.sexp coverage.sexp reach.sexp retired.sexp) do
      path = Path.join(@fixture, name)
      assert File.exists?(path), "missing archived preimage #{name}"
      bytes = File.read!(path)
      assert %{"sha256" => sha} = Enum.find(records, &(&1["name"] == name))
      assert digest(bytes) == sha
    end

    assert File.read!(Path.join(@fixture, "reach.sexp")) == ""
  end

  test "historical import requires an explicit era and current markers prohibit fallback" do
    assert {:error, :explicit_historical_era_required} = LegacyImport.decode_record(legacy())
    assert {:error, _} = Corpus.decode_record(legacy())
    assert {:ok, %{challenge: c}} = LegacyImport.decode_record(legacy(), @era)
    assert c.payload.term == {:type, Sort.finite_closed(0)}

    for marker <- ["format=2", "universe=stale", "pieces64=broken"] do
      assert {:error, {:current_record_rejected, _}} = LegacyImport.decode_record(legacy() <> "\t" <> marker, @era)
    end
  end

  test "already interned arbitrary Core and ETF symbols are rejected" do
    assert {:error, _} = LegacyImport.decode_record(legacy(pieces: "term::(global erlang)"), @era)
    assert {:error, _} = LegacyImport.decode_record(legacy(scaffold: opaque(%{"unexpected" => :erlang})), @era)
    assert {:error, _} = LegacyImport.decode_record(legacy(scaffold: opaque(%{"unexpected" => %URI{}})), @era)
  end

  test "unsafe or noncanonical historical metadata is refused before reconstruction" do
    cases = [
      opaque(%{"x" => self()}),
      opaque(%{"x" => make_ref()}),
      opaque(%{"x" => fn -> :ok end}),
      opaque(%{"x" => [1 | 2]}),
      Base.encode64(:erlang.term_to_binary(%{"x" => String.duplicate("a", 4096)}, [:compressed])),
      Base.encode64(:erlang.term_to_binary(%{}) <> "trailing"),
      opaque(%{"x" => Enum.reduce(1..260, [], fn _, acc -> [acc] end)}),
      opaque(%{"x" => Enum.to_list(1..100_001)})
    ]

    for scaffold <- cases do
      assert {:error, _} = LegacyImport.decode_record(legacy(scaffold: scaffold), @era)
    end

    assert {:error, _} = LegacyImport.decode_record(String.duplicate("x", 1_048_577), @era)
  end

  test "orphan pieces, unknown scaffold fields, duplicate faults and oversized fault integers fail" do
    assert {:error, _} = LegacyImport.decode_record(legacy(pieces: "term::(type 0);;extra::(var 0)"), @era)
    assert {:error, _} = LegacyImport.decode_record(legacy(scaffold: opaque(%{"extra" => 1})), @era)
    family = %{"families" => [], "def_name" => "u"}

    assert {:error, _} =
             LegacyImport.decode_record(
               legacy(
                 kind: "indexed_case",
                 scaffold: opaque(family),
                 pieces: "fam:999:sort::(type 0);;def_type::(type 1);;def_body::(type 0)"
               ),
               @era
             )

    for fault <- [
          "((kind head_swap) (kind head_swap))",
          "((unknown head_swap))",
          "((depth #{String.duplicate("9", 4097)}))"
        ] do
      assert {:error, _} = LegacyImport.decode_record(legacy() <> "\tfault=" <> fault, @era)
    end
  end

  test "fixed-ceiling family import refuses unreviewed level3 and only migration retires the exact row", %{tmp: tmp} do
    row = @fixture |> Path.join("corpus.sexp") |> Corpus.record_lines() |> Enum.at(32)
    assert {:error, _} = LegacyImport.decode_record(row, @era)
    assert String.contains?(row, "kind=family")
    path = Path.join(tmp, "corpus.sexp")
    File.write!(path, row <> "\n")
    assert {:error, report, _} = Migration.audit([path], @era)
    assert [%{"disposition" => "preserved", "error" => error}] = report["rows"]
    assert error =~ "outside fixed-ceiling era"
  end

  test "all rows map explicitly, full seed duplicates and mutants survive, and current rerun is idempotent", %{tmp: tmp} do
    paths = for name <- ~w(corpus seeds coverage reach), do: Path.join(@fixture, name <> ".sexp")

    opts =
      @era ++
        [
          archive_dir: Path.join(tmp, "archive"),
          out_dir: Path.join(tmp, "stage"),
          inventory: Path.join(tmp, "inventory.json")
        ]

    assert {:ok, report, _state} = Migration.stage(paths, opts)
    assert report["complete"]
    assert report["failures"] == []
    assert report["replay_failures"] == []
    assert report["mutants_before"] == report["mutants_after"]
    assert report["mutants_after"]["count"] == 93
    counts = Map.new(report["files"], &{&1["name"], &1["output_records"]})
    assert counts == %{"corpus.sexp" => 63, "seeds.sexp" => 419, "coverage.sexp" => 167, "reach.sexp" => 0}
    assert [%{"fresh_replay" => "ok", "source_sha256" => source_sha}] = report["additions"]
    assert byte_size(source_sha) == 64
    assert length(report["rows"]) == 645
    assert Enum.count(report["rows"], &(&1["disposition"] == "retired_obsolete_ceiling")) == 2
    assert Enum.count(report["rows"], &(&1["disposition"] == "archived_obsolete_positive_claim")) == 5
    for path <- paths, do: assert(File.read!(path) == File.read!(Path.join(opts[:archive_dir], Path.basename(path))))
    assert Enum.any?(report["collisions"], &(&1["store"] == "seeds.sexp" and &1["semantic_payloads"] > 1))
    assert Enum.count(report["collisions"], &(&1["store"] == "seeds.sexp")) == 67
    refute Enum.any?(report["collisions"], &(&1["store"] == "coverage.sexp"))

    for {kind, count} <- [{"kernel_probe", 48}, {"decode_probe", 19}] do
      rows = Enum.filter(report["rows"], &(&1["source"] == "coverage.sexp" and &1["old_kind"] == kind))
      assert length(rows) == count
      keys = for row <- rows, output <- row["outputs"], do: output["key"]
      assert keys |> Enum.uniq() |> length() == count
    end

    current_preimages =
      for path <- paths, line <- Corpus.record_lines(path), String.contains?(line, "\tformat=2\t"), do: digest(line)

    assert length(current_preimages) == 14

    for sha <- current_preimages do
      assert %{"outputs" => [_], "error" => nil} = Enum.find(report["rows"], &(&1["sha256"] == sha))
    end

    current_paths = Enum.map(paths, &Path.join(opts[:out_dir], Path.basename(&1)))
    assert {:ok, rerun, state} = Migration.audit(current_paths, @era)

    for input <- state.inputs do
      file = Enum.find(rerun["files"], &(&1["name"] == input.name))
      assert file["sha256"] == file["output_sha256"]
    end
  end

  test "audit does not publish, staging keeps unresolved evidence, write refuses errors", %{tmp: tmp} do
    path = Path.join(tmp, "bad.sexp")
    File.write!(path, "not-a-record\n")
    assert {:error, report, _} = Migration.audit([path], @era)
    refute report["complete"]
    assert File.read!(path) == "not-a-record\n"

    opts =
      @era ++
        [
          archive_dir: Path.join(tmp, "archive"),
          out_dir: Path.join(tmp, "stage"),
          inventory: Path.join(tmp, "inventory.json"),
          write: true
        ]

    assert_raise RuntimeError, ~r/unresolved/, fn -> Migration.stage([path], opts) end
    assert File.read!(path) == File.read!(Path.join(opts[:archive_dir], "bad.sexp"))
    refute File.exists?(opts[:inventory] <> ".publish.json")
  end

  test "publication uses source hashes and retains an inspectable per-file journal", %{tmp: tmp} do
    path = Path.join(tmp, "source.sexp")
    File.write!(path, legacy() <> "\n")

    opts =
      @era ++
        [
          archive_dir: Path.join(tmp, "archive"),
          out_dir: Path.join(tmp, "stage"),
          inventory: Path.join(tmp, "inventory.json")
        ]

    assert {:ok, report, state} = Migration.stage([path], opts)
    File.write!(path, "changed\n")
    assert_raise RuntimeError, ~r/compare-and-swap/, fn -> Migration.publish!(state, report, opts) end
    File.write!(path, legacy() <> "\n")
    assert :ok = Migration.publish!(state, report, opts)
    journal = File.read!(opts[:inventory] <> ".publish.json") |> :json.decode()
    assert journal["status"] == "published"
    assert [%{"status" => "published"}] = journal["files"]
    assert {:ok, _} = path |> Corpus.record_lines() |> hd() |> Corpus.decode_record()
    assert_raise RuntimeError, ~r/journal already exists/, fn -> Migration.publish!(state, report, opts) end
  end

  test "lexical/symlink aliases and basename collisions fail before any writes", %{tmp: tmp} do
    path = Path.join(tmp, "one.sexp")
    File.write!(path, legacy() <> "\n")
    File.ln_s!(tmp, Path.join(tmp, "alias"))

    for archive <- [tmp, Path.join(tmp, "alias")] do
      assert_raise ArgumentError, ~r/alias/, fn ->
        Migration.stage(
          [path],
          @era ++
            [archive_dir: archive, out_dir: Path.join(tmp, "out"), inventory: Path.join(tmp, "i.json")]
        )
      end
    end

    assert_raise ArgumentError, ~r/basename/, fn -> Migration.audit([path, Path.join(tmp, "other/one.sexp")], @era) end
    refute File.exists?(Path.join(tmp, "out"))
    assert_raise Mix.Error, fn -> Mix.Tasks.Antigen.Migrate.run([path]) end
  end

  test "historical keys must be canonical Base64 carrying nonempty inert single-line bytes" do
    for key <- ["not_base64", "", Base.encode64("bad\nkey"), Base.encode64(<<0>>)] do
      assert {:error, :malformed_historical_key} = LegacyImport.decode_record(legacy(key: key), @era)
    end
  end

  test "hard-linked inputs, archives and staged outputs are rejected before writes", %{tmp: tmp} do
    for relation <- [:inputs, :archive, :staged, :archive_and_staged] do
      root = Path.join(tmp, Atom.to_string(relation))
      File.mkdir_p!(root)
      path = Path.join(root, "source.sexp")
      File.write!(path, legacy() <> "\n")
      archive = Path.join(root, "archive")
      out = Path.join(root, "stage")
      opts = @era ++ [archive_dir: archive, out_dir: out, inventory: Path.join(root, "inventory.json")]

      case relation do
        :inputs ->
          linked = Path.join(root, "linked.sexp")
          File.ln!(path, linked)
          assert_raise ArgumentError, ~r/inode aliases/, fn -> Migration.audit([path, linked], @era) end

        :archive ->
          File.mkdir_p!(archive)
          File.ln!(path, Path.join(archive, "source.sexp"))
          assert_raise ArgumentError, ~r/inode aliases/, fn -> Migration.stage([path], opts) end

        :staged ->
          File.mkdir_p!(out)
          File.ln!(path, Path.join(out, "source.sexp"))
          assert_raise ArgumentError, ~r/inode aliases/, fn -> Migration.stage([path], opts) end

        :archive_and_staged ->
          File.mkdir_p!(archive)
          File.mkdir_p!(out)
          File.write!(Path.join(archive, "source.sexp"), legacy() <> "\n")
          File.ln!(Path.join(archive, "source.sexp"), Path.join(out, "source.sexp"))
          assert_raise ArgumentError, ~r/inode aliases/, fn -> Migration.stage([path], opts) end
      end

      refute File.exists?(opts[:inventory])
      assert File.read!(path) == legacy() <> "\n"
    end
  end

  test "a staged-file change after earlier publication is never copied live and the journal permits recovery", %{
    tmp: tmp
  } do
    first = Path.join(tmp, "first.sexp")
    second = Path.join(tmp, "second.sexp")
    original = legacy() <> "\n"
    for path <- [first, second], do: File.write!(path, original)

    opts =
      @era ++
        [
          archive_dir: Path.join(tmp, "archive"),
          out_dir: Path.join(tmp, "stage"),
          inventory: Path.join(tmp, "inventory.json")
        ]

    assert {:ok, report, state} = Migration.stage([first, second], opts)
    second_staged = Path.join(opts[:out_dir], "second.sexp")

    observer = fn entry ->
      if entry["source"] == first, do: File.write!(second_staged, "tampered after preflight\n")
    end

    assert_raise RuntimeError, ~r/staged output changed/, fn ->
      Migration.publish!(state, report, Keyword.put(opts, :on_checkpoint, observer))
    end

    assert File.read!(second) == original
    assert File.read!(first) == File.read!(Path.join(opts[:out_dir], "first.sexp"))
    refute File.read!(second) == File.read!(second_staged)
    journal = File.read!(opts[:inventory] <> ".publish.json") |> :json.decode()
    assert [%{"status" => "published"}, %{"status" => "prepared"}] = journal["files"]

    for entry <- journal["files"] do
      assert digest(File.read!(entry["archive"])) == entry["input_sha256"]
      File.cp!(entry["archive"], entry["source"])
      assert digest(File.read!(entry["source"])) == entry["input_sha256"]
    end

    refute File.exists?(second <> ".antigen-migration")
  end

  test "pre-existing symlink, dangling symlink and hardlink publication temporaries are never followed", %{tmp: tmp} do
    for kind <- [:symlink, :dangling, :hardlink] do
      root = Path.join(tmp, Atom.to_string(kind))
      File.mkdir_p!(root)
      path = Path.join(root, "source.sexp")
      original = legacy() <> "\n"
      File.write!(path, original)

      opts =
        @era ++
          [
            archive_dir: Path.join(root, "archive"),
            out_dir: Path.join(root, "stage"),
            inventory: Path.join(root, "inventory.json")
          ]

      assert {:ok, report, state} = Migration.stage([path], opts)
      victim = Path.join(root, "victim")
      File.write!(victim, "untouched\n")

      case kind do
        :symlink -> File.ln_s!(victim, path <> ".antigen-migration")
        :dangling -> File.ln_s!(victim <> ".absent", path <> ".antigen-migration")
        :hardlink -> File.ln!(victim, path <> ".antigen-migration")
      end

      assert_raise RuntimeError, ~r/temporary already exists/, fn -> Migration.publish!(state, report, opts) end
      assert File.read!(victim) == "untouched\n"
      assert File.read!(path) == original
      refute File.exists?(opts[:inventory] <> ".publish.json")
    end
  end

  test "late symlink and hardlink temporary injection cannot overwrite unrelated bytes", %{tmp: tmp} do
    for kind <- [:symlink, :hardlink] do
      root = Path.join(tmp, "late-#{kind}")
      File.mkdir_p!(root)
      first = Path.join(root, "first.sexp")
      second = Path.join(root, "second.sexp")
      original = legacy() <> "\n"
      for path <- [first, second], do: File.write!(path, original)

      opts =
        @era ++
          [
            archive_dir: Path.join(root, "archive"),
            out_dir: Path.join(root, "stage"),
            inventory: Path.join(root, "inventory.json")
          ]

      assert {:ok, report, state} = Migration.stage([first, second], opts)
      victim = Path.join(root, "victim")
      File.write!(victim, "untouched\n")

      observer = fn entry ->
        if entry["source"] == first do
          case kind do
            :symlink -> File.ln_s!(victim, second <> ".antigen-migration")
            :hardlink -> File.ln!(victim, second <> ".antigen-migration")
          end
        end
      end

      assert_raise File.Error, fn -> Migration.publish!(state, report, Keyword.put(opts, :on_checkpoint, observer)) end
      assert File.read!(victim) == "untouched\n"
      assert File.read!(second) == original
      journal = File.read!(opts[:inventory] <> ".publish.json") |> :json.decode()
      assert [%{"status" => "published"}, %{"status" => "prepared"}] = journal["files"]
    end
  end

  defp digest(bytes), do: :crypto.hash(:sha256, bytes) |> Base.encode16(case: :lower)
end

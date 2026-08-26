defmodule Antigen.CorpusTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus}

  @tmp "tmp/antigen_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "encode → decode round-trips a stub challenge identically (C2 stability)" do
    c =
      Challenge.new(
        kind: :stub,
        assay: "stub",
        label: :none,
        payload: %{term: {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:type, 0}}},
        seed: 42,
        note: "hi"
      )

    line = Corpus.encode_record(c)
    refute String.contains?(line, "\n")
    assert {:ok, c2} = Corpus.decode_record(line)
    assert c2.payload.term == c.payload.term
    assert c2.assay == "stub" and c2.seed == 42 and c2.note == "hi"
  end

  test "append is idempotent on the dedup key" do
    path = Path.join(@tmp, "corpus.sexp")
    c = Challenge.stub({:type, 0})
    key = Corpus.dedup_key(c, :antibody)
    assert :appended == Corpus.append(path, c, key)
    assert :duplicate == Corpus.append(path, c, key)
    assert File.read!(path) |> String.split("\n", trim: true) |> length() == 1
  end

  test "stream surfaces a decode error as a distinct entry and keeps going" do
    path = Path.join(@tmp, "corpus.sexp")
    Corpus.append(path, Challenge.stub({:type, 0}), Corpus.dedup_key(Challenge.stub({:type, 0}), :antibody))
    File.write!(path, File.read!(path) <> "this-is-not-a-record\n")
    results = Corpus.stream(path) |> Enum.to_list()
    assert Enum.any?(results, &match?({:ok, %Challenge{}}, &1))
    assert Enum.any?(results, &match?({:decode_error, _, _}, &1))
  end

  test "scaffold round-trips non-Term metadata through the record line (proves Phase-2 def_group/family carry-through)" do
    scaffold = %{"focus" => ["f", "g"], "arity" => 2}
    line = Corpus.encode_scaffold(scaffold)
    refute String.contains?(line, "\t") or String.contains?(line, "\n")
    assert Corpus.decode_scaffold(line) == scaffold
  end

  test "an empty scaffold encodes to the `-` sentinel and decodes back to an empty map" do
    assert Corpus.encode_scaffold(%{}) == "-"
    assert Corpus.decode_scaffold("-") == %{}
  end

  alias Cure.Core.Serialize

  test "term pieces are stored as readable s-expressions, not Base64" do
    c =
      Challenge.new(
        kind: :stub,
        assay: "stub",
        label: :none,
        payload: %{term: {:ctor, :vcons, [{:ctor, :Z, []}, {:ctor, :Z, []}, {:ctor, :vnil, []}]}},
        seed: 7,
        note: "n"
      )

    line = Corpus.encode_record(c)
    # the piece is the literal Serialize s-expr, inline in the line
    assert line =~ "term::(ctor vcons (ctor Z) (ctor Z) (ctor vnil))"
    refute line =~ "term::" <> Base.encode64(Serialize.encode(c.payload.term))
    assert {:ok, c2} = Corpus.decode_record(line)
    assert c2.payload.term == c.payload.term
  end

  test "decode_record still reads a legacy Base64 piece (dual-read)" do
    term = {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:type, 0}}
    # hand-build a legacy record: pieces = id::Base64(Serialize.encode(term))
    legacy =
      Enum.join(
        [
          "antigen-record",
          "kind=stub",
          "assay=stub",
          "label=none",
          "seed=1",
          "note=aGk=",
          "scaffold=-",
          "key=" <> Base.encode64("k"),
          "pieces=term::" <> Base.encode64(Serialize.encode(term))
        ],
        "\t"
      )

    assert {:ok, c} = Corpus.decode_record(legacy)
    assert c.payload.term == term
  end

  test "note is stored as readable plaintext and round-trips special chars" do
    for note <- ["negative occurrence: Bad left of an arrow", "has\ttab and % and\nnewline", "-", "plain", nil] do
      c = Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:type, 0}}, seed: 1, note: note)
      line = Corpus.encode_record(c)
      refute String.contains?(line, "\n"), "record must stay one line for note=#{inspect(note)}"
      assert {:ok, c2} = Corpus.decode_record(line)
      assert c2.note == note
    end
  end

  test "a real (non-nil) note is human-readable in the line (not Base64)" do
    c =
      Challenge.new(
        kind: :stub,
        assay: "stub",
        label: :none,
        payload: %{term: {:type, 0}},
        seed: 1,
        note: "negative occurrence"
      )

    line = Corpus.encode_record(c)
    assert line =~ "note=negative occurrence"
    refute line =~ "note=" <> Base.encode64("negative occurrence")
  end

  test "legacy Base64 note decodes to the original text (format inferred from Base64 pieces)" do
    term = {:type, 0}

    legacy =
      Enum.join(
        [
          "antigen-record",
          "kind=stub",
          "assay=stub",
          "label=none",
          "seed=1",
          "note=" <> Base.encode64("hello world"),
          "scaffold=-",
          "key=" <> Base.encode64("k"),
          "pieces=term::" <> Base.encode64(Serialize.encode(term))
        ],
        "\t"
      )

    assert {:ok, c} = Corpus.decode_record(legacy)
    assert c.note == "hello world"
    assert c.payload.term == term
  end

  defp mutant(fault, term \\ {:ctor, :Z, []}) do
    Challenge.new(
      kind: :mutant_term,
      assay: "mutation/rejection",
      label: :ill_typed,
      payload: %{sig: :v1, ctx: [], type: {:type, 0}, term: term, fault: fault}
    )
  end

  test "mutant fault round-trips every value shape and is readable in the line" do
    faults = [
      # atom/integer/nil/list (head_swap + deepen)
      %{
        kind: :head_swap,
        witness: :head,
        expected_head: :Nat,
        injected_head: :Vec,
        scope: nil,
        depth: 3,
        wrap_path: [:app_arg, :case_branch]
      },
      # integer-pair scope (out_of_scope_var)
      %{
        kind: :out_of_scope_var,
        witness: :scope,
        expected_head: nil,
        injected_head: nil,
        scope: {2, 2},
        depth: 0,
        wrap_path: []
      },
      # Core-term head values (universe)
      %{
        kind: :universe,
        witness: :level,
        expected_head: {:type, 0},
        injected_head: {:type, 1},
        scope: nil,
        depth: 1,
        wrap_path: [:pair]
      },
      # conversion carrier fault (integers + atoms)
      %{
        kind: :conv_index,
        witness: :conv,
        expected_index: 2,
        actual_index: 3,
        reduction: :required,
        depth: 2,
        carrier: :conv_index
      }
    ]

    for f <- faults do
      line = Corpus.encode_record(mutant(f))
      refute String.contains?(line, "\n")
      assert line =~ "fault=((", "fault must be an inline assoc-sexpr for #{inspect(f)}"
      assert {:ok, c2} = Corpus.decode_record(line)
      assert c2.payload.fault == f, "fault mismatch for #{inspect(f)}"
    end
  end

  test "non-mutant records carry no fault= field" do
    c = Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:type, 0}}, seed: 1, note: "n")
    refute Corpus.encode_record(c) =~ "\tfault="
  end

  test "legacy fault-in-scaffold still decodes (dual-read)" do
    # a legacy mutant: Base64 pieces + fault inside the Base64 scaffold, no fault= field
    fault = %{
      kind: :head_swap,
      witness: :head,
      expected_head: :Nat,
      injected_head: :Vec,
      scope: nil,
      depth: 0,
      wrap_path: []
    }

    scaffold = %{"sig" => "v1", "ctx_len" => 0, "fault" => fault}

    legacy =
      Enum.join(
        [
          "antigen-record",
          "kind=mutant_term",
          "assay=mutation/rejection",
          "label=ill_typed",
          "seed=1",
          "note=-",
          "scaffold=" <> Corpus.encode_scaffold(scaffold),
          "key=" <> Base.encode64("k"),
          "pieces=type::" <>
            Base.encode64(Serialize.encode({:type, 0})) <>
            ";;term::" <> Base.encode64(Serialize.encode({:ctor, :Z, []}))
        ],
        "\t"
      )

    assert {:ok, c} = Corpus.decode_record(legacy)
    assert c.payload.fault == fault
  end

  test "migration is lossless and idempotent (keys, challenges, bytes)" do
    path = Path.join(@tmp, "mig.sexp")

    challenges = [
      Challenge.new(
        kind: :stub,
        assay: "stub",
        label: :none,
        payload: %{term: {:ctor, :S, [{:ctor, :Z, []}]}},
        seed: 1,
        note: "one"
      ),
      mutant(%{
        kind: :out_of_scope_var,
        witness: :scope,
        expected_head: nil,
        injected_head: nil,
        scope: {1, 1},
        depth: 0,
        wrap_path: []
      })
    ]

    for c <- challenges, do: Corpus.append(path, c, Corpus.dedup_key(c, :antibody))
    before_bytes = File.read!(path)
    keys_before = corpus_keys(path)

    Mix.Tasks.Antigen.Migrate.run([path])

    after_bytes = File.read!(path)
    assert after_bytes == before_bytes, "already-new-format file must migrate byte-identically (idempotent)"
    assert corpus_keys(path) == keys_before, "dedup keys must be identical after migration"

    decoded = Corpus.stream(path) |> Enum.map(fn {:ok, c} -> c end)
    assert length(decoded) == length(challenges)
    assert Enum.at(decoded, 1).payload.fault.scope == {1, 1}
  end

  defp corpus_keys(path) do
    path |> File.stream!() |> Enum.map(&Corpus.raw_key/1) |> Enum.sort()
  end

  @looks_base64 ~r/\A[A-Za-z0-9+\/]{16,}={0,2}\z/

  test "a banked mutant record in seeds.sexp is fully human-readable" do
    seeds = "test/antigen/seeds.sexp"

    line =
      seeds
      |> File.stream!()
      |> Enum.find(fn l -> String.contains?(l, "kind=mutant_term") end)

    assert line, "expected at least one mutant_term in #{seeds}"
    # drop the leading "antigen-record" marker (no `=`) before building the map —
    # `Map.new`/`:maps.from_list` cannot mix its 1-tuple with the other fields' 2-tuples
    fields = line |> String.trim_trailing("\n") |> String.split("\t") |> tl()
    m = Map.new(fields, fn f -> List.to_tuple(String.split(f, "=", parts: 2)) end)

    # readable, not Base64, in the three human-facing fields
    assert m["pieces"] =~ "(", "pieces must be s-expr"
    refute Regex.match?(@looks_base64, m["note"] || "-")
    assert m["fault"] =~ "((", "mutant must carry a readable fault field"
    refute Regex.match?(@looks_base64, m["fault"])
    # and it still decodes
    assert {:ok, c} = Corpus.decode_record(line)
    assert c.kind == :mutant_term
  end

  alias Antigen.Generators.{Mutation, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.Context, as: CoreCtx

  test "fault codec round-trips every fault shape the generators actually emit (§4a lock)" do
    ctx = CoreCtx.empty(SigMenu.env_of(:v1))

    # one static fault per operator (build/2's fault map is deterministic)
    op_faults = Enum.map(Mutation.operators(), fn op -> elem(Mutation.build(ctx, op), 1) end)

    # a deepened fault (adds :depth + :wrap_path list) — take one concrete draw;
    # "fst on a Nat" spelled inductively (D2, projection case over mk_pair).
    fault_term =
      {:case, {:ctor, :Z, []},
       {:lam, Cure.Core.Grade.unrestricted(),
        {:data, :Sigma,
         [{:data, :Nat, [], []}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}}],
         []}, {:data, :Nat, [], []}}, [{:mk_pair, 2, {:var, 1}}]}

    {_deep, path} = B.interp(Mutation.deepen(ctx, fault_term, 3)) |> Enum.at(0)
    deep_fault = Map.merge(hd(op_faults), %{depth: 3, wrap_path: path})

    # a conversion carrier fault (:expected_index/:actual_index/:carrier/:reduction ints+atoms)
    conv = B.interp(Antigen.Generators.Conversion.conv_reject()) |> Enum.at(0)
    conv_fault = conv.payload.fault

    for fault <- [deep_fault, conv_fault | op_faults] do
      c =
        Challenge.new(
          kind: :mutant_term,
          assay: "mutation/rejection",
          label: :ill_typed,
          payload: %{sig: :v1, ctx: [], type: {:type, 0}, term: {:ctor, :Z, []}, fault: fault}
        )

      assert {:ok, c2} = Corpus.decode_record(Corpus.encode_record(c))
      assert c2.payload.fault == fault, "fault codec lost a generator-emitted shape: #{inspect(fault)}"
    end
  end
end

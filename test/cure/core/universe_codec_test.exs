defmodule Cure.Core.UniverseCodecTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Serialize, Term, UniverseCodec, UniverseLevel}

  test "current S-expression syntax round-trips finite, open, limit and level nodes" do
    open =
      UniverseLevel.max(
        UniverseLevel.atom({:var, 0}),
        UniverseLevel.succ(UniverseLevel.atom({:var, 1}))
      )

    huge = Integer.pow(10, 100)

    terms = [
      {:level_type},
      {:level_value, UniverseLevel.closed(huge)},
      {:type, {:finite, UniverseLevel.closed(37)}},
      {:type, {:omega, huge}},
      {:pi, :erased, {:level_type}, {:type, {:finite, open}}},
      {:level_value, open},
      {:ctor, :ok, [{:level_value, open}, {:type, {:omega, 0}}]}
    ]

    for term <- terms do
      wire = Serialize.encode(term)
      assert String.starts_with?(wire, "(cure-core 2 ")
      assert {:ok, ^term} = Serialize.decode(wire)
      assert %{"format" => "cure-core", "version" => 2} = external = Term.to_external(term)
      assert ^term = Term.from_external(external)
    end

    assert Serialize.encode({:type, {:finite, UniverseLevel.closed(37)}}) ==
             "(cure-core 2 (type (finite (level-nf 37))))"
  end

  test "external tagged level and sort helpers round-trip without normalizing" do
    level = UniverseLevel.succ(UniverseLevel.atom({:var, 0}))
    tagged = UniverseCodec.public_nf(level)
    assert {:level_nf, 0, [{{:var, 0}, 1}]} = tagged
    assert {:ok, ^level} = UniverseCodec.internal_nf(tagged)

    encode = &Term.to_external_node/1
    decode = &Term.from_external_node/1
    wire = UniverseCodec.encode_level(level, encode)
    assert {:ok, ^level} = UniverseCodec.decode_level(wire, decode)

    for sort <- [{:finite, level}, {:omega, 0}, {:omega, Integer.pow(10, 100)}] do
      assert {:ok, ^sort} =
               UniverseCodec.decode_sort(UniverseCodec.encode_sort(sort, encode), decode)
    end

    framed = UniverseCodec.frame(%{"node" => "level_type"})
    assert {:ok, %{"node" => "level_type"}} = UniverseCodec.unframe(framed)
    assert {:error, _} = UniverseCodec.unframe(Map.put(framed, "version", 1))
    assert {:error, _} = UniverseCodec.unframe(Map.put(framed, "extra", nil))
  end

  test "current decoders reject legacy, mixed, malformed and noncanonical level encodings" do
    bad_nodes = [
      "(type 0)",
      "(type (finite 0))",
      "(type (omega -1))",
      "(type (omega (var 0)))",
      "(type (limit 0))",
      "(level-value (level-nf -1))",
      "(level-value (level-nf 0 (atom (var 0) -1)))",
      "(level-value (level-nf 1 (atom (var 0) 1)))",
      "(level-value (level-nf 0 (atom (var 0) 0) (atom (var 0) 2)))",
      "(level-value (level-nf 0 (atom (var 1) 0) (atom (var 0) 0)))",
      "(level-value (level-nf 0 (atom (hole \"hidden\") 0)))",
      "(level-value (level-nf 0 (atom (meta 0) 0)))",
      "(level-value (level-nf 0 (atom (level-value (level-nf 1)) 0)))"
    ]

    for node <- bad_nodes do
      assert {:error, _} = Serialize.decode("(cure-core 2 #{node})"), node
    end

    assert {:error, _} = Serialize.decode("(type 0)")
    assert {:error, _} = Serialize.decode("(cure-core 1 (type 0))")
    assert {:error, _} = Serialize.decode("(cure-core 2 (var 0)) (var 1)")
    assert {:error, _} = Serialize.decode("(cure-core 2 (var -1))")

    duplicate = %{
      "tag" => "level_nf",
      "constant" => 0,
      "atoms" => [
        %{"term" => %{"node" => "var", "index" => 0}, "offset" => 0},
        %{"term" => %{"node" => "var", "index" => 0}, "offset" => 1}
      ]
    }

    assert {:error, _} = UniverseCodec.decode_level(duplicate, &Term.from_external_node/1)

    assert {:error, _} =
             UniverseCodec.decode_level(
               Map.put(duplicate, "extra", true),
               &Term.from_external_node/1
             )

    assert {:error, _} =
             UniverseCodec.decode_sort(
               %{"tag" => "omega", "index" => -1},
               &Term.from_external_node/1
             )
  end

  test "historical import is explicit, bounded to its original universes and always re-encodes current" do
    for n <- 0..2 do
      expected = {:type, {:finite, UniverseLevel.closed(n)}}
      assert {:ok, ^expected} = Serialize.decode_legacy("(type #{n})")
      assert String.starts_with?(Serialize.encode(expected), "(cure-core 2 ")
      assert {:error, _} = Serialize.decode("(type #{n})")
    end

    assert {:ok, {:lam, :erased, {:type, {:finite, _}}, {:var, 0}}} =
             Serialize.decode_legacy("(lam erased (type 0) (var 0))")

    for node <- ["(type -1)", "(type 3)", "(level-type)", "(type (omega 0))"] do
      assert {:error, _} = Serialize.decode_legacy(node)
    end
  end

  test "depth, collection, bytes and numeric budgets refuse input before reconstruction" do
    assert {:error, _} =
             Serialize.decode(String.duplicate("(", 300) <> String.duplicate(")", 300))

    assert {:error, _} =
             Serialize.decode("(cure-core 2 (type (omega " <> String.duplicate("9", 4097) <> ")))")

    assert {:error, _} = Serialize.decode(String.duplicate(" ", UniverseCodec.max_bytes() + 1))

    assert {:error, _} =
             UniverseCodec.internal_nf({:level_nf, 0, List.duplicate({{:var, 0}, 0}, 10_001)})

    assert {:error, _} =
             UniverseCodec.budget(Enum.reduce(1..300, nil, fn _, child -> [child] end))

    assert {:error, _} = Serialize.decode(nil)
    chunk = String.duplicate("x", div(UniverseCodec.max_bytes(), 2) + 1)
    assert {:error, _} = UniverseCodec.budget([chunk, chunk])

    for value <- [
          {:type, 0},
          UniverseLevel.zero(),
          self(),
          make_ref(),
          fn -> :ok end,
          :unknown_wire_atom,
          %{atom_key: 0}
        ] do
      assert {:error, _} = UniverseCodec.budget(value)
    end
  end

  test "external current decoding preserves ArgumentError and refuses competing legacy fields" do
    for node <- [
          %{"node" => "type", "level" => 0},
          %{"node" => "type", "sort" => %{"tag" => "omega", "index" => 0}, "level" => 0},
          %{"node" => "level_type", "meta" => 0},
          %{"node" => "var", "index" => -1},
          %{"node" => "unknown"}
        ] do
      assert_raise ArgumentError, fn -> Term.from_external(UniverseCodec.frame(node)) end
    end

    for n <- 0..2 do
      term = {:type, {:finite, UniverseLevel.closed(n)}}
      assert ^term = Term.from_legacy_external(%{"node" => "type", "level" => n})
      assert_raise ArgumentError, fn -> Term.from_external(%{"node" => "type", "level" => n}) end
    end
  end

  test "canonical ordering is portable serialized bytes, not host ETF ordering" do
    assert UniverseCodec.atom_order_key({:var, 10}) == "(var 10)"
    assert UniverseCodec.atom_order_key({:var, 10}) < UniverseCodec.atom_order_key({:var, 2})
    refute :erlang.term_to_binary({:var, 10}) < :erlang.term_to_binary({:var, 2})
    assert {:cure_universe, 1, :max_plus_finite_omega} = UniverseCodec.identity()

    refute UniverseCodec.semantic_hash(:unchanged) ==
             :crypto.hash(:sha256, :erlang.term_to_binary(:unchanged, [:deterministic]))
  end
end

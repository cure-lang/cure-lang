defmodule Cure.Core.SerializeTest do
  @moduledoc """
  Commitment C2 (design spec §9): Core proof terms serialize to a stable,
  host-independent form so an independent checker can re-validate the same
  artifacts. Round-trip must be exact, and a deserialized term must earn the
  same kernel verdict as the original.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Kernel, Serialize}

  @terms [
    {:type, 0},
    # `Universe.ceiling()` is 2, and `Term.term?/1` bounds a universe level by it. This row
    # used to read `{:type, 3}` — a term the Core's own grammar rejects, which round-tripped
    # only because `decode/1` never checked the shape it rebuilt.
    {:type, 2},
    {:var, 5},
    {:absurd},
    {:global, :compose},
    {:int_type},
    {:float_type},
    {:data, :Bool, [], []},
    {:int_lit, 42},
    {:int_lit, -7},
    {:float_lit, 3.5},
    {:ctor, :True, []},
    {:ctor, :False, []},
    {:hole, "body"},
    {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:type, 0}},
    {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:var, 0}},
    {:app, {:global, :f}, {:int_lit, 3}},
    # Inductive Sigma (D2): the dependent pair round-trips as `{:data, :Sigma}` /
    # `{:ctor, :mk_pair}` / projection-`:case` (covered by the data/ctor/case rows).
    # Primitive sigma/pair/fst/snd nodes no longer encode; their *rejection* on
    # decode is pinned as a negative test once the codec clauses are stripped.
    {:data, :Sigma, [{:int_type}, {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:type, 0}}], []},
    {:ctor, :mk_pair, [{:int_lit, 1}, {:ctor, :True, []}]},
    # K2: arithmetic round-trips as builtin-op GLOBAL spines (ordinary app
    # chains); the {:prim} wire tag no longer decodes (negative test below).
    {:app, {:app, {:global, :int_add}, {:int_lit, 3}}, {:int_lit, 5}},
    {:ctor, :seq, [{:global, :l}, {:global, :r}]},
    {:data, :SF, [{:global, :a}], [{:global, :b}, {:global, :c}]},
    {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:type, 0}},
     [{:prim, 2, {:ctor, :True, []}}, {:seq, 7, {:global, :x}}]}
  ]

  test "every Core term round-trips through encode/decode exactly" do
    for term <- @terms do
      encoded = Serialize.encode(term)
      assert is_binary(encoded)
      assert {:ok, ^term} = Serialize.decode(encoded), "round-trip failed for #{inspect(term)}"
    end
  end

  test "encoding is deterministic" do
    for term <- @terms, do: assert(Serialize.encode(term) == Serialize.encode(term))
  end

  test "a deserialized term earns the same kernel verdict as the original" do
    ctx = Context.empty(Cure.Core.Builtins.seed(Cure.Core.Env.empty()))

    well_typed = {:app, {:app, {:global, :int_add}, {:int_lit, 1}}, {:int_lit, 2}}
    {:ok, decoded} = Serialize.decode(Serialize.encode(well_typed))
    assert Kernel.infer(ctx, decoded) == Kernel.infer(ctx, well_typed)
    assert {:ok, {:vdata, :"Std.Int#Int", []}} = Kernel.infer(ctx, decoded)

    ill_typed = {:app, {:app, {:global, :int_add}, {:int_lit, 1}}, {:type, 0}}
    {:ok, decoded_bad} = Serialize.decode(Serialize.encode(ill_typed))
    assert {:error, _} = Kernel.infer(ctx, decoded_bad)
  end

  test "decode rejects malformed input" do
    assert {:error, _} = Serialize.decode("(type")
    assert {:error, _} = Serialize.decode("(nonsense 1 2)")
    assert {:error, _} = Serialize.decode("")
  end

  # D2: the primitive Sigma nodes are retired from the codec. Their wire tags no
  # longer decode — a stronger guarantee than the former positive round-trip rows.
  # K2: the {:prim} node is retired from the codec — its wire tag no longer
  # decodes (mirrors the D2 Sigma precedent below).
  test "decode rejects the retired (prim ...) tag" do
    assert {:error, :unknown_node} = Serialize.decode("(prim add (int 3) (int 5))")
    assert {:error, :unknown_node} = Serialize.decode("(prim not (ctor True))")
  end

  test "decode rejects the retired primitive Sigma tags" do
    for wire <- [
          "(sigma (int-type) (var 0))",
          "(pair (int 1) (ctor True))",
          "(fst (var 0))",
          "(snd (var 0))"
        ] do
      assert {:error, :unknown_node} = Serialize.decode(wire)
    end
  end
end

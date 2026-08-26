defmodule Antigen.ChallengeTest do
  use ExUnit.Case, async: true
  alias Antigen.Challenge

  test "a stub challenge holds a single Core term and defaults" do
    c = Challenge.stub({:type, 0})
    assert %Challenge{kind: :stub, assay: "stub", label: :none} = c
    assert c.payload == %{term: {:type, 0}}
    assert c.seed == nil
  end

  test "new/1 fills fields from a keyword list" do
    c = Challenge.new(kind: :stub, assay: "stub", label: :none, payload: %{term: {:var, 0}}, seed: 7)
    assert c.seed == 7
    assert c.payload.term == {:var, 0}
  end

  test "indexed_case challenge round-trips through to_pieces/from_pieces" do
    dec = {:data, :Dec, [], []}
    fam = Cure.Core.Inductive.family(:Dec, [], [], 0)
    ctors = [Cure.Core.Inductive.ctor(:Dcoupled, [], []), Cure.Core.Inductive.ctor(:Causal, [], [])]

    payload = %{
      families: [{fam, ctors}],
      def_name: :probe,
      def_type: dec,
      def_body:
        {:case, {:ctor, :Causal, []}, {:lam, Cure.Core.Grade.unrestricted(), dec, dec},
         [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}
    }

    c = Antigen.Challenge.new(kind: :indexed_case, assay: "indexed/case", label: :well_typed, payload: payload)
    {scaffold, pieces} = Antigen.Challenge.to_pieces(c)
    back = Antigen.Challenge.from_pieces(:indexed_case, "indexed/case", :well_typed, nil, nil, scaffold, pieces)

    assert back.kind == :indexed_case
    assert back.payload.def_name == :probe
    assert back.payload.def_type == dec
    assert back.payload.def_body == payload.def_body
    assert back.payload.families == [{fam, ctors}]
  end

  test ":mutant_term round-trips through to_pieces/from_pieces incl the fault map" do
    fault = %{kind: :proj_non_pair, witness: :head, expected_head: :Sigma, injected_head: :Nat, scope: nil}

    c =
      Challenge.new(
        kind: :mutant_term,
        assay: "mutation/rejection",
        label: :ill_typed,
        payload: %{
          sig: :v1,
          ctx: [{:data, :Nat, [], []}],
          type: {:data, :Nat, [], []},
          # "fst on a Nat" spelled inductively (D2): projection case over
          # mk_pair scrutinising a Nat — same :proj_non_pair fault.
          term:
            {:case, {:ctor, :Z, []},
             {:lam, Cure.Core.Grade.unrestricted(),
              {:data, :Sigma,
               [
                 {:data, :Nat, [], []},
                 {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}}
               ], []}, {:data, :Nat, [], []}}, [{:mk_pair, 2, {:var, 1}}]},
          fault: fault
        }
      )

    {scaffold, pieces} = Challenge.to_pieces(c)
    # simulate the corpus scaffold codec (term_to_binary → binary_to_term [:safe])
    scaffold2 = Antigen.Corpus.decode_scaffold(Antigen.Corpus.encode_scaffold(scaffold))
    c2 = Challenge.from_pieces(:mutant_term, c.assay, c.label, nil, nil, scaffold2, pieces)

    assert c2.kind == :mutant_term
    assert c2.payload.fault == fault
    assert c2.payload.term == c.payload.term
    assert c2.payload.ctx == c.payload.ctx
    assert c2.payload.type == c.payload.type
  end

  # A deep-propagation fault map (7 keys incl. :depth/:wrap_path and wrapper-kind
  # values :app_arg/:case_branch/:pair) serialized OUTSIDE this module, so those
  # atoms appear ONLY in these opaque bytes — never as literals in the test source
  # that would pre-intern them. `binary_to_term [:safe]` can therefore decode it
  # only if Challenge.@known_atoms interns the new wrapper/field atoms. This is the
  # genuine file-decode guard; an in-source round-trip test cannot be (its own
  # literals defeat the red state — exactly the v1 key-atom false-green).
  @deep_fault_blob "g3QAAAAHdwVzY29wZXcDbmlsdwVkZXB0aGEDdwRraW5kdwloZWFkX3N3YXB3B3dpdG5lc3N3BGhlYWR3DWV4cGVjdGVkX2hlYWR3A05hdHcNaW5qZWN0ZWRfaGVhZHcDVmVjdwl3cmFwX3BhdGhsAAAAA3cHYXBwX2FyZ3cLY2FzZV9icmFuY2h3BHBhaXJq"

  test "deep-fault wrapper/field atoms are interned for [:safe] file decode" do
    _ = Antigen.Challenge.__known_atoms__()
    decoded = :erlang.binary_to_term(Base.decode64!(@deep_fault_blob), [:safe])
    assert is_map(decoded) and map_size(decoded) == 7
  end

  # Conversion-at-depth (sub-project B) fault map (7 keys incl :expected_index/
  # :actual_index/:carrier and values :conv_index/:conv), serialized OUTSIDE this
  # module so those atoms live only in the opaque bytes — the [:safe] decode can
  # succeed only if Challenge.@known_atoms interns them (same guard as A's).
  @conv_fault_blob "g3QAAAAHdwVkZXB0aGEDdwRraW5kdwpjb252X2luZGV4dwd3aXRuZXNzdwRjb252dw5leHBlY3RlZF9pbmRleGEDdwxhY3R1YWxfaW5kZXhhBHcJcmVkdWN0aW9udwhyZXF1aXJlZHcHY2FycmllcncKY29udl9pbmRleA=="

  test "conversion fault atoms are interned for [:safe] file decode" do
    _ = Antigen.Challenge.__known_atoms__()
    decoded = :erlang.binary_to_term(Base.decode64!(@conv_fault_blob), [:safe])
    assert is_map(decoded) and map_size(decoded) == 7
  end
end

defmodule Cure.Core.ProofWireTest do
  @moduledoc """
  Producer-side vectors for the wire format formalised in
  `proof/Core/Wire.agda`.

  These tests pin the CHARACTERS this producer emits for concrete terms. The
  Agda side independently proves the codec inverts the encoder
  (`Core.Wire.decode-encode`) and pins the same grammar
  (`Proof.WireExamples`); the vectors here are the shared hand-checked
  cross-language artifact. Nothing here establishes typing, admission or
  coverage, and no byte-for-byte fixture claim is made yet.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.ProofWire

  # The empty name of the non-name code nodes is part of the table.
  @table ["", "a", "Boundary#Packed", "Boundary#Pack"]

  describe "unary atoms and child lists" do
    test "an atom is a unary run terminated by ';'" do
      # tag 1 (var), name index 0, number 0, no children
      assert {:ok, chars} = ProofWire.encode_term({:var, 0}, @table)
      assert chars == "(" <> "1;" <> ";" <> ";" <> ")"
    end

    test "a larger natural repeats '1'" do
      # tag 1, name index 0, NUMBER 3: the number is the unary run
      assert {:ok, chars} = ProofWire.encode_term({:var, 3}, @table)
      assert chars == "(" <> "1;" <> ";" <> "111;" <> ")"
    end

    test "a list node brackets its children" do
      # tag 5 (app) with two children: var 0 and atom_type
      assert {:ok, chars} = ProofWire.encode_term({:app, {:var, 0}, {:atom_type}}, @table)

      assert chars ==
               "(" <>
                 "11111;" <>
                 ";" <>
                 ";" <>
                 "(" <>
                 "1;" <>
                 ";" <>
                 ";" <>
                 ")" <>
                 "(" <>
                 "111111111111111111;" <> ";" <> ";" <> ")" <> ")"
    end
  end

  describe "interned names" do
    test "an atom literal carries the name INDEX" do
      # tag 19 (atom_lit), name "a" at index 1, number 0, no children
      assert {:ok, chars} = ProofWire.encode_term({:atom_lit, :a}, @table)
      assert chars == "(" <> String.duplicate("1", 19) <> ";" <> "1;" <> ";" <> ")"
    end

    test "a name absent from the table cannot be written" do
      assert {:error, {:unknown_name, "missing"}} =
               ProofWire.encode_term({:global, :missing}, @table)
    end

    test "the empty name must be in the table" do
      assert {:error, {:unknown_name, ""}} = ProofWire.encode_term({:var, 0}, ["a"])
    end

    test "an atom and its string form are the same wire identity" do
      assert {:ok, chars} = ProofWire.encode_term({:global, "a"}, @table)
      assert {:ok, same} = ProofWire.encode_term({:global, :a}, @table)
      assert chars == same
    end
  end

  describe "binder grades" do
    test "grades render as 0..3 and are not interchangeable" do
      {:ok, erased} = ProofWire.encode_term({:lam, :erased, {:atom_type}, {:var, 0}}, @table)
      {:ok, unrestricted} = ProofWire.encode_term({:lam, :unrestricted, {:atom_type}, {:var, 0}}, @table)
      refute erased == unrestricted
    end
  end

  describe "reflection tags" do
    test "distinct nodes reflect to distinct tags" do
      {:ok, nat} = ProofWire.code({:nat_lit, 0})
      {:ok, ctor} = ProofWire.code({:ctor, :c, []})
      {:ok, positive} = ProofWire.code({:int_lit, 0})
      {:ok, negative} = ProofWire.code({:int_lit, -1})
      {:ok, absurd} = ProofWire.code({:absurd})

      tags = [nat, ctor, positive, negative, absurd]
      distinct = tags |> Enum.map(&elem(&1, 1)) |> Enum.uniq()
      assert length(distinct) == length(tags)
    end

    test "a negative integer literal uses the negative-successor tag" do
      assert {:ok, {:node, 12, "", 0, []}} = ProofWire.code({:int_lit, -1})
      assert {:ok, {:node, 12, "", 4, []}} = ProofWire.code({:int_lit, -5})
    end

    test "a case carries its branches as a marker-100 child list" do
      branch = {:c, 1, {:var, 0}}

      {:ok, {:node, 8, "", 0, [_scrutinee, _motive, {:node, 100, "", 0, [branch_code]}]}} =
        ProofWire.code({:case, {:var, 0}, {:atom_type}, [branch]})

      assert {:node, 0, "c", 1, [_body]} = branch_code
    end

    test "a malformed term is rejected rather than silently encoded" do
      assert {:error, {:malformed_term, {:pi, {:atom_type}}}} =
               ProofWire.encode_term({:pi, {:atom_type}}, @table)
    end
  end

  describe "fail-closed representation boundaries" do
    test "out-of-range universes and invalid binder grades return errors" do
      for term <- [
            {:type, 3},
            {:type, -1},
            {:type, 1.0},
            {:pi, :unknown, {:atom_type}, {:atom_type}},
            {:lam, :unknown, {:atom_type}, {:var, 0}},
            {:let, :unknown, {:atom_type}, {:atom_lit, :a}, {:var, 0}}
          ] do
        assert {:error, {:malformed_term, ^term}} = ProofWire.encode_term(term, @table)
      end
    end

    test "Float payloads are unsupported rather than silently erased" do
      assert {:error, {:unsupported_term, {:float_lit, 0.5}}} =
               ProofWire.encode_term({:float_lit, 0.5}, @table)

      assert {:error, {:malformed_term, {:float_lit}}} = ProofWire.encode_term({:float_lit}, @table)
    end

    test "invalid symbolic identities do not become name-table indices" do
      for term <- [{:global, 42}, {:atom_lit, []}, {:hole, %{}}, {:ctor, 42, []}, {:data, 42, [], []}] do
        assert {:error, {:malformed_term, ^term}} = ProofWire.encode_term(term, @table)
      end

      assert {:error, {:malformed_term, _}} =
               ProofWire.encode_term({:case, {:var, 0}, {:atom_type}, [{42, 1, {:var, 0}}]}, @table)
    end

    test "malformed and invalid UTF-8 name tables are rejected in full" do
      for table <- [42, ["a", 42], [:a | :improper], ["a", <<255>>]] do
        assert {:error, {:malformed_table, ^table}} = ProofWire.encode_term({:global, :a}, table)
        assert :error = ProofWire.index_of(:a, table)
      end

      assert {:error, {:malformed_term, {:global, <<255>>}}} =
               ProofWire.encode_term({:global, <<255>>}, @table)
    end

    test "improper child lists and raw reflected codes return structured errors" do
      assert {:error, {:malformed_term, _}} =
               ProofWire.code({:ctor, :a, [{:atom_type} | :improper]})

      for code <- [
            {:node, -1, "", 0, []},
            {:node, 1, "", -1, []},
            {:node, 1, 42, 0, []},
            {:node, 1, "", 0, [invalid: :child]}
          ] do
        assert {:error, {:malformed_code, _}} = ProofWire.intern(code, @table)
      end
    end
  end

  describe "the shared cross-language vector" do
    # `Proof.WireExamples.cross-table` is `"" ∷ "a" ∷ []` and
    # `cross-node` is `[atom 19, atom 1, atom 0]` for `tm-atom_lit "a"`;
    # the Agda module pins the same characters
    # `cross-characters`. This is the hand-checked artifact shared by the
    # producer and the formal codec.
    test "an atom literal matches the formal side's pinned characters" do
      table = ["", "a"]
      assert {:ok, chars} = ProofWire.encode_term({:atom_lit, :a}, table)

      assert chars == "(" <> String.duplicate("1", 19) <> ";" <> "1;" <> ";" <> ")"
    end
  end
end

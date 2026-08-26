defmodule Cure.Core.SerializeSymbolBoundTest do
  # K12 / spec §D: the untrusted decode boundary must NOT intern arbitrary strings
  # as atoms — unbounded `String.to_atom` on external C2 input is an atom-table-
  # exhaustion DoS (the atom table never shrinks). A name that was never interned
  # ⇒ decode fails closed, creating no new atom. Names that already exist (any
  # real program's globals/ctors) still decode. NB: the "unseen" names below must
  # appear NOWHERE as atom literals in the codebase, or the test is vacuous.
  use ExUnit.Case, async: true
  alias Cure.Core.Serialize

  test "decode fails closed on an unknown global symbol (no unbounded atom interning)" do
    assert {:error, _} = Serialize.decode("(global cure_k12_unseen_symbol_qz)")
  end

  test "decode fails closed on an unknown constructor symbol" do
    assert {:error, _} = Serialize.decode("(ctor CureK12UnseenCtorQz)")
  end

  test "decode still roundtrips a global whose atom already exists" do
    term = {:global, :cure_k12_seen_symbol}
    assert {:ok, ^term} = Serialize.decode(Serialize.encode(term))
  end

  test "decode stays total (returns error, never raises) on an unknown symbol" do
    assert {:error, _} = Serialize.decode("(data CureK12UnseenFamQz () ())")
  end
end

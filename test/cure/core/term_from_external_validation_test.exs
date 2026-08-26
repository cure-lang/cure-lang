defmodule Cure.Core.TermFromExternalValidationTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Serialize, Term}

  # `Serialize.decode/1` and `Term.from_external/1` are the two external-decode
  # entry points for the same Core node grammar, and both are trust boundaries:
  # whatever they are handed came off disk. Each re-checks the tuple it built
  # against `Term.term?/1` so a malformed field cannot become a term an
  # independent checker is later asked to trust.
  #
  # A negative de Bruijn index is the case that distinguishes the check from the
  # atom-interning one `term_test.exs` covers: `{:var, -1}` is built from
  # perfectly well-typed input and is only caught by the shape gate.
  test "a negative de Bruijn index is rejected by both external-decode entry points" do
    malformed_index = -1
    external = %{"node" => "var", "index" => malformed_index}

    refute Term.term?({:var, malformed_index}),
           "the premise of this test: {:var, -1} is not a well-formed term"

    # `Serialize.decode/1` reports it, because its contract is a result tuple.
    assert {:error, {:ill_formed_term, {:var, -1}}} ==
             Serialize.decode("(var #{malformed_index})")

    # `from_external/1` returns a term or nothing at all, so it raises rather
    # than handing back the ungated `{:var, -1}`.
    assert_raise ArgumentError, ~r/ill-formed external Core term/, fn ->
      Term.from_external(external)
    end
  end
end

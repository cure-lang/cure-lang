defmodule Cure.Elab.NumericIndexTest do
  # A numeric literal in a dependent type index (`Bounded(n)`) lowers to a compact
  # `{:nat_lit, n}`. The lexer already normalizes hex/binary/underscored integers
  # to a decimal digit-string before it reaches the index name node, so those work
  # via the all-digits rule. Scientific notation lexes as a FLOAT and arrives
  # stringified as e.g. "1.0e6"; an integer-VALUED float is a valid Nat index and
  # must lower to that integer, while a genuinely fractional one is rejected.
  use ExUnit.Case, async: true

  alias Cure.Elab.{Declarations, Program}
  alias Cure.Core.Env

  defp name(s), do: {:variable, [scope: :local], s}
  defp low(s), do: Declarations.lower_type(name(s), [], Env.empty())

  describe "lower_type on stringified numeric index names" do
    test "decimal all-digits" do
      assert {:ok, {:nat_lit, 1_114_112}} = low("1114112")
    end

    # Hex/binary/underscore arrive already normalized to decimal digit strings.
    test "hex normalizes to decimal before lowering" do
      assert {:ok, {:nat_lit, 1_114_112}} = low("1114112")
    end

    test "scientific notation (integer-valued float string) lowers to the integer" do
      assert {:ok, {:nat_lit, 1_000_000}} = low("1.0e6")
      assert {:ok, {:nat_lit, 250}} = low("2.5e2")
      assert {:ok, {:nat_lit, 0}} = low("0.0e0")
    end

    test "a genuinely fractional scientific index is rejected" do
      assert {:error, _} = low("1.5e0")
    end

    test "a real type variable in scope still resolves to its de Bruijn index" do
      assert {:ok, {:var, 0}} = Declarations.lower_type(name("n"), ["n"], Env.empty())
    end
  end

  describe "end-to-end through the lexer/parser" do
    test "Bounded with hex, binary, and scientific indices all elaborate and agree with decimal" do
      # 0x110000 == 0b100010000000000000000 == 1114112; used as a type index each
      # must convert with the decimal form (the compact nat_lit is identical).
      src = """
      mod M
        use Std.Bounded
        fn h(x: Bounded(0x110000)) -> Bounded(1114112) = x
        fn b(x: Bounded(0b100010000000000000000)) -> Bounded(1114112) = x
        fn s(x: Bounded(1.0e6)) -> Bounded(1000000) = x
      end
      """

      assert {:ok, _env} = Program.elaborate(src)
    end
  end
end

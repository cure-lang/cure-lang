defmodule Cure.Elab.BoundedLiteralTest do
  # A `Bounded(n)` value is written as an integer literal checked against the type
  # (`let c : Bounded(1114112) = 97`), lowered to ONE compact node with a
  # `0 <= k < n` bound check — Lean's `Fin n` (a compact `Nat` + a `< n` witness),
  # NOT a `Next(Next(...First))` tower. This is the value half of modelling
  # `Char = Bounded(0x110000)`: an emoji is one integer at every stage.
  use ExUnit.Case, async: true

  alias Cure.Elab.Program
  alias Cure.Core.Env

  defp body_of(env, name), do: Env.get_def(env, name).body

  describe "elaboration: integer literal checked against Bounded(n)" do
    test "an in-range integer literal lowers to a compact bounded_lit (not a tower)" do
      src = """
      mod M
        use Std.Bounded
        typealias Char = Bounded(1114112)
        fn a() -> Char = 97
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert {:bounded_lit, 97} = body_of(env, :a)
    end

    test "the full-plane emoji codepoint stays ONE compact node" do
      src = """
      mod M
        use Std.Bounded
        typealias Char = Bounded(1114112)
        fn emoji() -> Char = 128512
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert {:bounded_lit, 128_512} = body_of(env, :emoji)
    end

    test "a 1e7 bound + a near-max value stay compact (no 10M-node tower)" do
      # The whole point of the compact representation: a ten-million bound and a
      # value near it are each ONE node. In the old `Next(...First)` tower this
      # program would be ~20 million Core nodes and never finish; here it is
      # instant. `1e7` also exercises scientific-notation index lowering.
      src = """
      mod M
        use Std.Bounded
        fn big() -> Bounded(1e7) = 9999999
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert {:bounded_lit, 9_999_999} = body_of(env, :big)
    end

    test "an out-of-range literal is rejected at the bound" do
      src = """
      mod M
        use Std.Bounded
        fn bad() -> Bounded(10) = 20
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end
  end
end

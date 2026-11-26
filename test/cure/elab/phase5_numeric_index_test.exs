defmodule Cure.Elab.Phase5NumericIndexTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.Program

  test "numeric equality indices retain their checked Int, Nat and Bounded carriers" do
    source = """
    mod NumericIndexCarriers
      use Std.Bounded
      use Std.Equivalent
      fn keep(
        {int_proof: Equivalent(Int, 18, 18)},
        {nat_proof: Equivalent(Nat, 18, 18)},
        {bounded_proof: Equivalent(Bounded(2), 1, 1)},
        value: Int
      ) -> Int = value
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def_type(env, :"NumericIndexCarriers#keep")
    assert :ok = Kernel.check_def(env, :"NumericIndexCarriers#keep")

    %{type: {:pi, :erased, int, {:pi, :erased, nat, {:pi, :erased, bounded, _}}}} =
      Env.get_def(env, :"NumericIndexCarriers#keep")

    assert {:data, _, [_], [{:int_lit, 18}, {:int_lit, 18}]} = int
    assert {:data, _, [_], [{:nat_lit, 18}, {:nat_lit, 18}]} = nat
    assert {:data, _, [_], [{:bounded_lit, 1}, {:bounded_lit, 1}]} = bounded
  end

  test "an explicit Nat constructor is not coerced to the Int equality carrier" do
    source = """
    mod WrongNumericIndexCarrier
      use Std.Equivalent
      fn keep({proof: Equivalent(Int, Z(), Z())}, value: Int) -> Int = value
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end

  test "numeric literals at opaque or empty Bounded indices still reject" do
    for bound <- ["n", "Z()"] do
      source = """
      mod OpaqueNumericIndexCarrier
        use Std.Bounded
        use Std.Equivalent
        fn keep(n: Nat, {proof: Equivalent(Bounded(#{bound}), 0, 0)}, value: Int) -> Int = value
      end
      """

      assert {:error, _reason} = Program.elaborate(source)
    end
  end
end

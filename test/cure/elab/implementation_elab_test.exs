defmodule Cure.Elab.ImplementationElabTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Coherence}
  alias Cure.Core.Env

  defp env!(src) do
    {:ok, e} = Program.elaborate(src)
    e
  end

  test "an anonymous implementation registers a dictionary for (iface, head)" do
    e =
      env!("""
      mod M
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool
        implementation Eqs for Int
          fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      end
      """)

    assert {:ok, _dict_ref} = Coherence.lookup_anon(Env.coherence(e), :Eqs, :"Std.Int#Int")
  end

  test "a duplicate anonymous instance is an overlap error" do
    assert {:error, {:overlapping_instance, %{interface: :Eqs, head: :"Std.Int#Int"}}} =
             Program.elaborate("""
             mod M
               interface Eqs(a)
                 fn eqs(x: a, y: a) -> Bool
               implementation Eqs for Int
                 fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
               implementation Eqs for Int
                 fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
             end
             """)
  end

  test "an implementation omitting a method with a default is filled from the default" do
    e =
      env!("""
      mod M
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool
          fn nes(x: a, y: a) -> Bool = true
        implementation Eqs for Int
          fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      end
      """)

    # `nes` is omitted by the implementation but has an interface default, so
    # registration must still succeed. Deeper behavioural verification of the
    # filled-in default's value happens once method-call resolution exists
    # (Task 4) and via the stdlib's real `Equatable.ne` default (Task 8).
    assert {:ok, _} = Coherence.lookup_anon(Env.coherence(e), :Eqs, :"Std.Int#Int")
  end
end

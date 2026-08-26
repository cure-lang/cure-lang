defmodule Cure.Elab.InterfaceElabTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.Env

  test "a kind-Type interface registers a record type former and descriptor" do
    src = """
    mod M
      interface Showable(a)
        fn show(x: a) -> Bool
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    desc = Env.get_interface(env, :Showable)
    assert desc.head_kind == :type
    assert :show in Map.keys(desc.methods)
  end

  test "Functor's head kind is inferred as Type -> Type (applied head)" do
    src = """
    mod M
      interface Functor(f)
        fn fmap(container: f(a), g: a -> b) -> f(b)
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    desc = Env.get_interface(env, :Functor)
    assert desc.head_kind == {:arrow, :type, :type}
  end

  test "an inconsistently-kinded head is rejected" do
    src = """
    mod M
      interface Bad(a)
        fn m1(x: a) -> Bool
        fn m2(y: a(a)) -> Bool
    end
    """

    # `m2` must be indented to the same level as `m1` — nested inside the
    # interface block — or it parses as an unrelated top-level def with a
    # free/unbound `a`, and `Bad` ends up with only the (consistent) `m1`,
    # never exercising the inconsistent-head-kind check at all.
    assert {:error, error} = Program.elaborate(src)
    assert {:inconsistent_head_kind, :Bad} = Program.semantic_error(error)
  end
end

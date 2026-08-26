defmodule Cure.Compiler.PartialApplicationCodegenTest do
  @moduledoc """
  E4: partial application of an explicit-arg function must codegen to an eta-expanded closure,
  not a call at the supplied (wrong) arity. Previously `lower_app_spine`'s `Enum.split` emitted
  `f/n` for a call supplying `n < arity` args (e.g. `add/1`), which does not exist. These run
  the emitted BEAM to prove the closure applies correctly.
  """
  use ExUnit.Case, async: false

  test "a one-argument-short partial application lowers to a working closure" do
    src = """
    mod PaOne
      fn add(a: Nat, b: Nat) -> Nat = a
      fn partial() -> (Nat) -> Nat = add(Z)
      fn use_it() -> Nat = partial()(S(Z))
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    # add(Z, S(Z)) = a = Z = 0
    assert apply(mod, :use_it, []) == 0
  end

  test "a two-argument-short partial application curries through nested closures" do
    src = """
    mod PaTwo
      fn tri(a: Nat, b: Nat, c: Nat) -> Nat = b
      fn p1() -> (Nat) -> (Nat) -> Nat = tri(Z)
      fn run() -> Nat = p1()(S(Z))(Z)
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    # tri(Z, S(Z), Z) = b = S(Z) = 1
    assert apply(mod, :run, []) == 1
  end

  test "a partial application passed to a higher-order function works" do
    src = """
    mod PaHof
      fn add(a: Nat, b: Nat) -> Nat = a
      fn apply1(f: (Nat) -> Nat, x: Nat) -> Nat = f(x)
      fn go() -> Nat = apply1(add(S(Z)), Z)
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    # apply1(add(S(Z)), Z) = add(S(Z), Z) = a = S(Z) = 1
    assert apply(mod, :go, []) == 1
  end
end

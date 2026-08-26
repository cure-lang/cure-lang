defmodule Cure.Compiler.DependentSurfaceCodegenTest do
  @moduledoc """
  End-to-end checks for dependent surface features that no longer need an
  `indexed type` declaration to enter the trusted Core compiler path.
  """
  use ExUnit.Case, async: false

  test "typed erased parameters route through Core and erase from runtime arity" do
    src = """
    mod DepImplicitOnly
      type Nat = Z | S(Nat)
      fn id_nat({n: Nat}, x: Nat) -> Nat = x
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert mod == :"Cure.DepImplicitOnly"
    assert function_exported?(mod, :id_nat, 1)
    refute function_exported?(mod, :id_nat, 2)
    assert apply(mod, :id_nat, [:Z]) == :Z
    assert apply(mod, :id_nat, [{:S, :Z}]) == {:S, :Z}
  end

  test "Sigma-only Cure source routes through Core and emits pairs/projections" do
    src = """
    mod DepSigmaOnly
      type Dec = Dcoupled | Causal
      fn pack(d: Dec) -> Sigma(x: Dec, Dec) = %[d, d]
      fn recover(p: Sigma(x: Dec, Dec)) -> Dec = p.2
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert mod == :"Cure.DepSigmaOnly"
    assert apply(mod, :pack, [:Causal]) == {:Causal, :Causal}
    assert apply(mod, :recover, [{:Dcoupled, :Causal}]) == :Causal
  end
end

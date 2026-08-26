defmodule Cure.Compiler.InterfaceDispatchCodegenTest do
  @moduledoc """
  End-to-end check that an `interface` + `implementation` plus a top-level
  derived helper (`strictly_before` dispatching `cmp`) compiles through the sole
  (dependent) pipeline to a loadable BEAM module. A dropped interface would leave
  `cmp` undefined and the module would fail to load.
  """
  use ExUnit.Case, async: false

  @src """
  mod IfaceDispatch
    interface Ordf(t)
      fn cmp(a: t, b: t) -> Bool

    implementation Ordf for Int
      fn cmp(a: Int, b: Int) -> Bool = a < b

    fn strictly_before(a: t, b: t) -> Bool where Ordf(t) = cmp(a, b)
  end
  """

  test "a top-level helper dispatching an interface method compiles to loadable BEAM" do
    assert {:ok, mod} = Cure.Compiler.compile_and_load(@src, emit_events: false)
    assert is_atom(mod)
    # `strictly_before` carries `where Ordf(t)`, so the dependent pipeline emits
    # it with an explicit interface-dictionary parameter — arity 3, not 2.
    assert function_exported?(mod, :strictly_before, 3)
  end
end

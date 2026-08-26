defmodule Cure.Elab.OpaqueTypeTest do
  @moduledoc """
  #1 (opaque inert-carrier former, batch 2026-07-10). `opaque type Name(params)`
  declares a constructor-less family MARKED opaque: the kernel treats it as an
  inhabited but non-eliminable type (Agda `postulate T : Set`). Its purpose is to
  carry BEAM ops from a macro/@extern through the TCB to codegen without the
  kernel ever inspecting them — so the surface guarantees are (1) the type
  elaborates and is marked, (2) a value of it can be passed through uninspected,
  and (3) it can NEVER be eliminated (that soundness pin is in
  `test/antigen/opaque_former_antibody_test.exs`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program
  alias Cure.Core.Inductive

  test "`opaque type Effect(a)` declares a marked, constructor-less family" do
    {:ok, env} = Program.elaborate("mod M\n  opaque type Effect(a)\nend\n")
    assert Inductive.get_family(env, :Effect)
    assert Inductive.opaque?(env, :Effect)
    assert Inductive.ctors_of(env, :Effect) == []
  end

  test "a nullary `opaque type Widget` works" do
    {:ok, env} = Program.elaborate("mod M\n  opaque type Widget\nend\n")
    assert Inductive.opaque?(env, :Widget)
  end

  test "an opaque value carries through uninspected (non-eliminable, still usable)" do
    assert {:ok, _} =
             Program.elaborate("mod M\n  opaque type Effect(a)\n  fn id(e: Effect(a)) -> Effect(a) = e\nend\n")
  end

  test "a genuine empty inductive is NOT marked opaque (the marker is the distinction)" do
    {:ok, env} = Program.elaborate("mod M\n  type Void =\n    |\nend\n")
    assert Inductive.get_family(env, :Void)
    refute Inductive.opaque?(env, :Void)
  end
end

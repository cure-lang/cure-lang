defmodule Cure.Stdlib.PrimitiveModulesTest do
  @moduledoc """
  The machine base types have visible, inspectable Std homes (spec 2026-07-10-
  primitive-type-declarations): Std.Float and Std.Binary each declare their
  `@builtin(:tag) primitive Name` and elaborate cleanly. Std.Int is no longer a
  primitive floor — it declares the inductive `type Int = FromNat(Nat) |
  NegativeSuccessor(Nat)` family (native at runtime), so `Env.primitive` returns
  nil for it, exactly as it does for Nat.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.Env

  test "Std.Int declares the inductive Int family and elaborates cleanly" do
    {:ok, env} = Program.elaborate(File.read!("lib/std/int.cure"))
    # Int left the primitive floor: it is now a family, not a machine base type,
    # so it has no primitive binding (same as Nat).
    assert Env.primitive(env, "Int") == nil
  end

  test "Std.Float declares Float and elaborates cleanly" do
    {:ok, env} = Program.elaborate(File.read!("lib/std/float.cure"))
    assert Env.primitive(env, "Float") == {:float_type}
  end

  test "Std.Binary still elaborates with the primitive Binary declaration" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/binary.cure"))
  end
end

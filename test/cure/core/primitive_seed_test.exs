defmodule Cure.Core.PrimitiveSeedTest do
  @moduledoc """
  The primitive-type floor (spec 2026-07-10-primitive-type-declarations): every
  seeded env0 resolves the machine base names to their Core nodes, so bare
  `x: Float` works with no import. `Int` is now the inductive `Std.Int#Int`
  family (like `Nat`/`Bool`), resolved via the family floor — not a primitive.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Env}

  defp seeded, do: Builtins.seed(Env.empty())

  test "the seed floor binds the machine base types" do
    env = seeded()
    assert Env.primitive(env, "Float") == {:float_type}
    assert Env.primitive(env, "Binary") == {:binary_type}
  end

  test "a family name (Nat, Int) has no primitive binding" do
    assert Env.primitive(seeded(), "Nat") == nil
    assert Env.primitive(seeded(), "Int") == nil
  end
end

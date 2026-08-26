defmodule Antigen.BuiltinIntDriftTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  # builtins-drift finding: `lib/cure/core/builtins.ex:352`'s `int_family`/
  # `int_ctors` (private, hand-authored) are a byte-for-byte mirror of the
  # `@builtin(:int)` surface declaration in `Std.Int` (lib/std/int.cure). Each
  # ctor's single field is a *canonical* `Nat` (Std.Nat#Nat), so this source
  # pulls Nat in with `use Std.Nat`, exactly as the real Std.Int module does.
  # Bool/List/Sigma already have this antibody; Nat/Int/Equivalent did not.
  @int_src """
  @group(:core)
  mod Std.Int
    use Std.Nat

    @builtin(:int)
    type Int = FromNat(Nat) | NegativeSuccessor(Nat)
  """

  test "the seeded :int family exists with ctors FromNat/1 and NegativeSuccessor/1" do
    seeded = Builtins.seed(Env.empty())
    assert Inductive.builtin(seeded, :int) == :"Std.Int#Int"

    ctors =
      seeded
      |> Inductive.ctors_of(:Int)
      |> Enum.map(fn c -> {c.name, length(c.args)} end)
      |> Enum.sort()

    assert ctors == [{:"Std.Int#FromNat", 1}, {:"Std.Int#NegativeSuccessor", 1}]
  end

  test "prelude-compiled Std.Int family is structurally identical to Builtins.seed's" do
    {:ok, env} = Cure.Elab.Program.elaborate(@int_src)
    seeded = Builtins.seed(Env.empty())

    assert Inductive.get_family(env, :Int) == Inductive.get_family(seeded, :Int)

    from_prelude = env |> Inductive.ctors_of(:Int) |> Enum.sort_by(& &1.name)
    from_seed = seeded |> Inductive.ctors_of(:Int) |> Enum.sort_by(& &1.name)
    assert from_prelude == from_seed
  end

  test "Inductive.builtin(env, :int) resolves after seeding" do
    assert Inductive.builtin(Builtins.seed(Env.empty()), :int) == :"Std.Int#Int"
  end
end

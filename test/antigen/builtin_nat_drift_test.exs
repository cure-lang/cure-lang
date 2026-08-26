defmodule Antigen.BuiltinNatDriftTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  # builtins-drift finding: `lib/cure/core/builtins.ex`'s `nat_family`/`nat_ctors`
  # (private, hand-authored) are a byte-for-byte mirror of the `@builtin(:nat)`
  # surface declaration in `Std.Nat` (lib/std/nat.cure). Bool/List/Sigma already
  # have this antibody (builtin_bool_drift_test.exs, builtin_list_drift_test.exs,
  # builtin_sigma_drift_test.exs); Nat did not. This pins the two copies equal
  # TODAY so any future edit to either side that silently diverges from the
  # other fails loudly, mirroring the existing family of drift tests.
  @nat_src """
  @group(:core)
  mod Std.Nat
    @builtin(:nat)
    type Nat = Z | S(Nat)
  """

  test "the seeded :nat family exists with ctors Z/0 and S/1" do
    seeded = Builtins.seed(Env.empty())
    assert Inductive.builtin(seeded, :nat) == :"Std.Nat#Nat"

    ctors =
      seeded
      |> Inductive.ctors_of(:Nat)
      |> Enum.map(fn c -> {c.name, length(c.args)} end)
      |> Enum.sort()

    assert ctors == [{:"Std.Nat#S", 1}, {:"Std.Nat#Z", 0}]
  end

  test "prelude-compiled Std.Nat family is structurally identical to Builtins.seed's" do
    {:ok, env} = Cure.Elab.Program.elaborate(@nat_src)
    seeded = Builtins.seed(Env.empty())

    assert Inductive.get_family(env, :Nat) == Inductive.get_family(seeded, :Nat)

    from_prelude = env |> Inductive.ctors_of(:Nat) |> Enum.sort_by(& &1.name)
    from_seed = seeded |> Inductive.ctors_of(:Nat) |> Enum.sort_by(& &1.name)
    assert from_prelude == from_seed
  end

  test "Inductive.builtin(env, :nat) resolves after seeding" do
    assert Inductive.builtin(Builtins.seed(Env.empty()), :nat) == :"Std.Nat#Nat"
  end
end

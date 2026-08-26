defmodule Antigen.BuiltinListDriftTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  # The @builtin(:list) surface declaration in Std.List is the source of truth;
  # Builtins.seed/2 carries a byte-for-byte programmatic mirror so [..]/[h|t] work
  # in every module without `use`. This antibody fails if the two ever drift.
  # First parametrized + self-referential family through this comparison.
  @list_src """
  @group(:collections)
  mod Std.List
    @builtin(:list)
    type List(a) = Nil | Cons(a, List(a))
  """

  test "the seeded :list family exists with ctors Nil/0 and Cons/2" do
    seeded = Builtins.seed(Env.empty())
    assert Inductive.builtin(seeded, :list) == :"Std.List#List"

    ctors =
      seeded
      |> Inductive.ctors_of(:List)
      |> Enum.map(fn c -> {c.name, length(c.args)} end)
      |> Enum.sort()

    assert ctors == [{:"Std.List#Cons", 2}, {:"Std.List#Nil", 0}]
  end

  test "prelude-compiled Std.List family is structurally identical to Builtins.seed's" do
    {:ok, env} = Cure.Elab.Program.elaborate(@list_src)
    seeded = Builtins.seed(Env.empty())

    assert Inductive.get_family(env, :List) == Inductive.get_family(seeded, :List)

    from_prelude = env |> Inductive.ctors_of(:List) |> Enum.sort_by(& &1.name)
    from_seed = seeded |> Inductive.ctors_of(:List) |> Enum.sort_by(& &1.name)
    assert from_prelude == from_seed
  end

  test "Inductive.builtin(env, :list) resolves after seeding" do
    assert Inductive.builtin(Builtins.seed(Env.empty()), :list) == :"Std.List#List"
  end
end

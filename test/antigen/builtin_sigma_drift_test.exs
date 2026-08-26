defmodule Antigen.BuiltinSigmaDriftTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  # The @builtin(:sigma) surface declaration in Std.Sigma is the source of truth;
  # Builtins.seed/2 carries a byte-for-byte programmatic mirror so %[..]/.1/.2 work
  # in every module without `use`. This antibody fails if the two ever drift.
  # Mechanism mirrors builtin_prelude_seed_test.exs: plain Elixir `==` on
  # Inductive.get_family/2 maps and Enum.sort_by(&.name) ctor lists (Core terms are
  # bare tuples/maps — no metadata to strip). This is the FIRST family with params
  # and a function-typed field to run through this comparison.
  @sigma_src """
  @group(:core)
  mod Std.Sigma
    @builtin(:sigma)
    type Sigma(a: Type, b: (a) -> Type) indices ()
      mk_pair : (x: a) -> b(x) -> Sigma(a, b)
  """

  test "the seeded :sigma family exists with ctor mk_pair/2" do
    seeded = Builtins.seed(Env.empty())
    assert Inductive.builtin(seeded, :sigma) == :"Std.Sigma#Sigma"

    ctors =
      seeded
      |> Inductive.ctors_of(:Sigma)
      |> Enum.map(fn c -> {c.name, length(c.args)} end)

    assert ctors == [{:"Std.Sigma#mk_pair", 2}]
  end

  test "prelude-compiled Std.Sigma family is structurally identical to Builtins.seed's" do
    {:ok, env} = Cure.Elab.Program.elaborate(@sigma_src)
    seeded = Builtins.seed(Env.empty())

    assert Inductive.get_family(env, :Sigma) == Inductive.get_family(seeded, :Sigma)

    from_prelude = env |> Inductive.ctors_of(:Sigma) |> Enum.sort_by(& &1.name)
    from_seed = seeded |> Inductive.ctors_of(:Sigma) |> Enum.sort_by(& &1.name)
    assert from_prelude == from_seed
  end

  test "Inductive.builtin(env, :sigma) resolves after seeding" do
    assert Inductive.builtin(Builtins.seed(Env.empty()), :sigma) == :"Std.Sigma#Sigma"
  end
end

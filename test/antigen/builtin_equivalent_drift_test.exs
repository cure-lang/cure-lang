defmodule Antigen.BuiltinEquivalentDriftTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  # builtins-drift finding: THREE copies of the Equivalent (identity type)
  # inductive schema exist: (1) `lib/cure/core/builtins.ex:379`'s
  # `eq_family`/`eq_ctors` (private, hand-authored), (2) the `@builtin(:eq)`
  # surface declaration in `Std.Equivalent` (lib/std/equivalent.cure), and
  # (3) `lib/antigen/generators/rewrite.ex:86-91`'s private `eq_family/0`
  # (a "byte-mirror" per its own comment, built unqualified because its
  # challenge env starts from `Env.empty()` with no builtins seeded). Bool/
  # List/Sigma already have the (1)-vs-(2) antibody; Equivalent did not, and
  # (3) had no antibody at all. This file pins all three equal TODAY.

  @equivalent_src """
  @group(:core)
  mod Std.Equivalent
    @builtin(:eq)
    type Equivalent(a: Type) indices (x: a, y: a)
      reflexive : Equivalent(a, w, w)
  """

  test "the seeded :eq family exists with ctor reflexive/1" do
    seeded = Builtins.seed(Env.empty())
    assert Inductive.builtin(seeded, :eq) == :"Std.Equivalent#Equivalent"

    ctors =
      seeded
      |> Inductive.ctors_of(:Equivalent)
      |> Enum.map(fn c -> {c.name, length(c.args)} end)

    assert ctors == [{:"Std.Equivalent#reflexive", 1}]
  end

  test "prelude-compiled Std.Equivalent family is structurally identical to Builtins.seed's" do
    {:ok, env} = Cure.Elab.Program.elaborate(@equivalent_src)
    seeded = Builtins.seed(Env.empty())

    assert Inductive.get_family(env, :Equivalent) == Inductive.get_family(seeded, :Equivalent)

    from_prelude = env |> Inductive.ctors_of(:Equivalent) |> Enum.sort_by(& &1.name)
    from_seed = seeded |> Inductive.ctors_of(:Equivalent) |> Enum.sort_by(& &1.name)
    assert from_prelude == from_seed
  end

  test "Inductive.builtin(env, :eq) resolves after seeding" do
    assert Inductive.builtin(Builtins.seed(Env.empty()), :eq) == :"Std.Equivalent#Equivalent"
  end

  # -- the THIRD copy: lib/antigen/generators/rewrite.ex's private eq_family/0 --
  #
  # `Antigen.Generators.Rewrite.eq_family/0` (lines 86-91) is `defp`, so it
  # cannot be called from outside; this reproduces its literal body verbatim
  # (comment included) as the honest way to pin an un-exported private copy.
  # It is intentionally built with BARE (unqualified) names — its own comment
  # explains why: "the challenge env is rebuilt from Env.empty, which has no
  # builtins". The structural comparison below therefore strips the
  # `Std.Equivalent#` owner qualification from the seeded copy's names before
  # comparing, rather than asserting raw equality of the maps.

  # Equivalent itself — byte-mirror of core/builtins.ex's eq_family/eq_ctors
  # (the challenge env is rebuilt from Env.empty, which has no builtins).
  defp antigen_eq_family,
    do:
      {Inductive.family(:Equivalent, [a: {:type, 0}], [x: {:var, 0}, y: {:var, 1}], 0),
       [Inductive.ctor(:reflexive, [w: {:var, 0}], [{:var, 0}, {:var, 0}], [:erased], [{:var, 1}])]}

  defp strip_owner(name) when is_atom(name), do: String.to_atom(Cure.Elab.Name.base(name))

  test "antigen's rewrite.ex Equivalent copy matches Builtins.seed's (mod owner qualification)" do
    seeded = Builtins.seed(Env.empty())
    seeded_family = Inductive.get_family(seeded, :Equivalent)
    seeded_ctors = Inductive.ctors_of(seeded, :Equivalent)

    seeded_ctors_stripped =
      Enum.map(seeded_ctors, fn c -> %{c | name: strip_owner(c.name)} end)

    {antigen_family, antigen_ctors} = antigen_eq_family()

    # `:ctor_order` is not part of a hand-built family: `Inductive.declare/3`
    # stamps it on at registration, because `env.ctors` is a map and arrival
    # order is unrecoverable afterwards. Antigen's copy is the pre-registration
    # pair, so the seeded family carries the key and the copy cannot. Compare the
    # authored shape structurally, and check the stamped order against the very
    # ctors it is supposed to be recording — which is the drift that would matter.
    seeded_family_stripped =
      %{seeded_family | name: strip_owner(seeded_family.name)}
      |> Map.delete(:ctor_order)

    assert Enum.map(seeded_family.ctor_order, &strip_owner/1) ==
             Enum.map(seeded_ctors_stripped, & &1.name)

    assert antigen_family == seeded_family_stripped
    assert antigen_ctors == seeded_ctors_stripped
  end
end

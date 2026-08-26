defmodule Cure.Elab.HoleIdentityTest do
  @moduledoc """
  Every source `?` must lower to a UNIQUE, deterministic hole id (first-class
  holes, Slice 1). This is the soundness pivot: once holes are stuck neutrals
  that flow through conversion, two holes sharing an id are definitionally equal,
  so `refl : ?a = ?b` would type-check. Distinct ids per occurrence prevent that.
  Determinism (positional/name-derived, no gensym counter) keeps Antigen and the
  differential oracle replay-stable.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @src """
  mod Holes
    fn a() -> Type = ?
    fn b() -> Type = ?
    fn c() -> Type = ?goal
  end
  """

  defp hole_ids(env) do
    env.defs
    |> Enum.filter(fn {name, _definition} -> Cure.Elab.Name.owner(name) == env.module_owner end)
    |> Enum.map(&elem(&1, 1))
    |> Enum.map(& &1.body)
    |> Enum.filter(&match?({:hole, _}, &1))
    |> Enum.map(fn {:hole, id} -> id end)
  end

  test "each source ? lowers to a unique, non-empty hole id" do
    {:ok, env} = Program.elaborate(@src)
    ids = hole_ids(env)

    assert length(ids) == 3

    assert Enum.all?(ids, &(is_binary(&1) and &1 != "")),
           "every hole id must be a non-empty string: #{inspect(ids)}"

    assert length(Enum.uniq(ids)) == 3,
           "hole ids must be distinct per source occurrence: #{inspect(ids)}"
  end

  test "a named hole ?goal carries its name in the id" do
    {:ok, env} = Program.elaborate(@src)
    ids = hole_ids(env)
    assert Enum.any?(ids, &String.contains?(&1, "goal")), "?goal must keep its name: #{inspect(ids)}"
  end

  test "elaboration is deterministic — identical source yields identical hole ids" do
    {:ok, env1} = Program.elaborate(@src)
    {:ok, env2} = Program.elaborate(@src)
    assert Enum.sort(hole_ids(env1)) == Enum.sort(hole_ids(env2))
  end

  @same_named_src """
  mod HolesSameName
    fn a() -> Type = ?goal
    fn b() -> Type = ?goal
  end
  """

  test "the SAME named hole in TWO DIFFERENT defs gets DISTINCT ids (cross-def collision guard)" do
    # The design doc (2026-07-18-first-class-holes-design.md, "the soundness
    # pivot") specifies the named scheme as `<module>.<def>#name` precisely so
    # that "the same surface name in two defs is two holes". If `hole_id/2`
    # qualifies only by module (not by the enclosing def), `?goal` in `a` and
    # `?goal` in `b` mint the IDENTICAL id string. Once holes are neutrals
    # flowing through `Conv`, identical ids are DEFINITIONALLY EQUAL
    # (`conv_neutral?({:nhole,id},{:nhole,id}) -> true`) — so two semantically
    # unrelated holes from different definitions would collapse to the same
    # axiom, defeating the very distinctness property first-class holes exist
    # to guarantee.
    {:ok, env} = Program.elaborate(@same_named_src)
    ids = hole_ids(env)

    assert length(ids) == 2

    assert length(Enum.uniq(ids)) == 2,
           "CROSS-DEF HOLE COLLISION: the same named hole `?goal` in two different " <>
             "defs minted the SAME id #{inspect(ids)} — Conv would judge them " <>
             "definitionally equal despite being unrelated holes."
  end
end

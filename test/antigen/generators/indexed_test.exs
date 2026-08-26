defmodule Antigen.Generators.IndexedTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Indexed
  alias Cure.Core.Inductive

  test "4.1 branch_family :ill_typed genuinely contains a foreign-family branch" do
    c = Indexed.branch_family(:ill_typed)
    env = Indexed.env_of(c)
    {:case, _scrut, _motive, branches} = c.payload.def_body
    branch_ctors = Enum.map(branches, fn {cn, _ar, _b} -> cn end)

    # MkFoo is present as a branch, and it really belongs to Foo, not Dec.
    assert :MkFoo in branch_ctors
    assert Inductive.ctor_family(env, :MkFoo) == :Foo
    assert Inductive.ctor_family(env, :Causal) == :Dec
    # ...and every Dec ctor is still covered (so coverage passes; the additive form).
    assert :Dcoupled in branch_ctors and :Causal in branch_ctors
  end

  test "4.1 branch_family :well_typed draws all branches from Dec" do
    c = Indexed.branch_family(:well_typed)
    env = Indexed.env_of(c)
    {:case, _s, _m, branches} = c.payload.def_body
    assert Enum.all?(branches, fn {cn, _ar, _b} -> Inductive.ctor_family(env, cn) == :Dec end)
  end

  test "4.2 coverage :ill_typed genuinely omits a declared ctor" do
    c = Indexed.coverage(:ill_typed)
    env = Indexed.env_of(c)
    declared = env |> Inductive.ctors_of(:Tri) |> Enum.map(& &1.name) |> MapSet.new()
    {:lam, _, _, {:case, {:var, 0}, _m, branches}} = c.payload.def_body
    covered = branches |> Enum.map(fn {cn, _, _} -> cn end) |> MapSet.new()
    refute MapSet.subset?(declared, covered)
  end

  test "4.2 coverage :well_typed specializes a known constructor" do
    c = Indexed.coverage(:well_typed)
    env = Indexed.env_of(c)
    assert env |> Inductive.ctors_of(:Tri) |> length() == 3
    {:case, {:ctor, :A, []}, _m, branches} = c.payload.def_body
    covered = branches |> Enum.map(fn {cn, _, _} -> cn end) |> MapSet.new()
    assert covered == MapSet.new([:A])
  end

  test "4.3 refinement family's wrap ctor has a NON-variable (ground) result index, and h needs it" do
    c = Indexed.refinement(:well_typed)
    env = Indexed.env_of(c)
    [ridx] = Inductive.get_ctor(env, :wrap).result_indices
    # it's {:ctor, :Causal, []}, so refinement is DROPPED
    refute match?({:var, _}, ridx)
    assert ridx == {:ctor, :Causal, []}

    # def_type: Π(n:Dec). Π(h:Ix n). Π(ix:Ix n). Ix n — h's declared domain is
    # `Ix n` (the SAME shape the wrap branch requires, `Ix _`), differing only in
    # which index term fills the hole; only the dropped n:=Causal equation could
    # ever bridge `Ix n` (h's declared type) to `Ix Causal` (the branch's goal).
    {:pi, _g1, _dec, {:pi, _g2, h_dom, {:pi, _g3, _ix_dom, _cod}}} = c.payload.def_type
    assert h_dom == {:data, :Ix, [], [{:var, 0}]}
  end

  test "4.3 ill-typed refinement body is a deliberately wrong-typed term" do
    c = Indexed.refinement(:ill_typed)
    {:case, _s, _m, [{:wrap, 1, body}]} = c.payload.def_body
    assert body == {:type, 0}
  end

  test "4.4 ill-typed motive has an extra lambda layer (over-applied)" do
    good = Indexed.motive_wf(:well_typed)
    bad = Indexed.motive_wf(:ill_typed)
    {:case, _s, {:lam, _g, _, good_inner}, _} = good.payload.def_body
    {:case, _s2, {:lam, _g, _, bad_inner}, _} = bad.payload.def_body
    # good_inner is a plain type; bad_inner is itself another lambda (the extra layer).
    refute match?({:lam, _g, _, _}, good_inner)
    assert match?({:lam, _g, _, _}, bad_inner)
  end
end

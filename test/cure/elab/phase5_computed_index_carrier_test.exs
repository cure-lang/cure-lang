defmodule Cure.Elab.Phase5ComputedIndexCarrierTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Kernel, Term, Validator}
  alias Cure.Elab.{Program, Relevance}

  @base_source """
  mod ComputedIndexCarrier
    type Nat = Z | S(Nat)
    type Bounded indices (n: Nat)
      First : {m: Nat} -> Bounded(S(m))
      Next : {m: Nat} -> Bounded(m) -> Bounded(S(m))
    type Box indices (n: Nat)
      MkBox : Nat -> Box(n)
    type Thread indices (n: Nat)
      ThreadAccepted : Thread(n)
      ThreadActive : Bounded(n) -> Thread(n)
    type Comp = MkComp(Nat)

    @reducible
    fn state_count(comp: Comp) -> Nat = match comp
      MkComp(n) -> n

    fn box_a(comp: Comp) -> Box(state_count(comp)) = MkBox(Z())
    fn box_b(comp: Comp) -> Box(state_count(comp)) = MkBox(Z())

    @reducible
    fn dest(n: Nat, box: Box(n), src: Thread(n)) -> Nat = match src
      ThreadAccepted() -> Z()
      ThreadActive(_) -> match box
        MkBox(k) -> k

    fn active_equiv(comp: Comp, state: Bounded(state_count(comp))) -> Equivalent(Nat, dest(state_count(comp), box_a(comp), ThreadActive(state)), dest(state_count(comp), box_b(comp), ThreadActive(state))) = reflexive(Z())

    fn thread_equiv(comp: Comp, src: Thread(state_count(comp))) -> Equivalent(Nat, dest(state_count(comp), box_a(comp), src), dest(state_count(comp), box_b(comp), src)) = match src
      ThreadAccepted() -> reflexive(dest(state_count(comp), box_a(comp), ThreadAccepted()))
      ThreadActive(state) -> active_equiv(comp, state)
  end
  """

  test "computed-index match with dependent carrier subterms closes under original Kernel, Validator, and Relevance" do
    assert {:ok, env} = Program.elaborate(@base_source)
    assert :ok = Kernel.check_def(env, :"ComputedIndexCarrier#thread_equiv")

    %{type: type, body: body} = Env.get_def(env, :"ComputedIndexCarrier#thread_equiv")
    assert Term.closed?(type)
    assert Term.closed?(body)
    assert {:ok, _} = Validator.validate(body, Validator.release_config(), env)
    assert :ok = Relevance.check(env, :"ComputedIndexCarrier#thread_equiv", [], body)
  end

  test "computed-index carrier retry rejects a wrong branch" do
    wrong_branch =
      String.replace(
        @base_source,
        "ThreadAccepted() -> reflexive(dest(state_count(comp), box_a(comp), ThreadAccepted()))",
        "ThreadAccepted() -> reflexive(S(Z()))"
      )

    refute wrong_branch == @base_source
    assert {:error, _} = Program.elaborate(wrong_branch)
  end

  test "computed-index carrier retry rejects an unrelated goal" do
    wrong_goal =
      String.replace(
        @base_source,
        "dest(state_count(comp), box_b(comp), src)",
        "S(dest(state_count(comp), box_b(comp), src))"
      )

    refute wrong_goal == @base_source
    assert {:error, _} = Program.elaborate(wrong_goal)
  end
end

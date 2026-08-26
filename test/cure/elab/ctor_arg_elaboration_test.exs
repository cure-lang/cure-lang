defmodule Cure.Elab.CtorArgElaborationTest do
  @moduledoc """
  Regression coverage for a dependent-elaborator bug: a NON-NULLARY constructor
  application passed as a function-call argument (e.g. `id(S(n))`, `plus(Z, S(n))`)
  failed with `{:error, :ctor_arity}`, because a global-headed call elaborated its
  arguments through the untyped path, which resolved the constructor head to its
  NULLARY shape `{:ctor, :S, []}` and then applied it to an argument.

  Programs go through the real pipeline via Cure.Elab.Program.elaborate/1.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @preamble """
  type Nat = Z | S(Nat)
  fn id(x: Nat) -> Nat = x
  fn plus(m: Nat, n: Nat) -> Nat = match m
    Z() -> n
    S(k) -> S(plus(k, n))
  """

  defp with_body(body) do
    @preamble <>
      """
      fn probe(n: Nat) -> Nat = #{body}
      """
  end

  # FAIL cases (pre-fix: {:error, :ctor_arity}).
  test "id(S(n)) — non-nullary ctor arg to a unary global" do
    assert {:ok, _env} = Program.elaborate(with_body("id(S(n))"))
  end

  test "plus(Z, S(n)) — non-nullary ctor in second argument position" do
    assert {:ok, _env} = Program.elaborate(with_body("plus(Z, S(n))"))
  end

  test "plus(S(n), Z) — non-nullary ctor in first argument position" do
    assert {:ok, _env} = Program.elaborate(with_body("plus(S(n), Z)"))
  end

  test "plus(n, S(Z)) — non-nullary ctor wrapping a nullary ctor arg" do
    assert {:ok, _env} = Program.elaborate(with_body("plus(n, S(Z))"))
  end

  # OK guard: a nullary ctor arg already worked and must keep working.
  test "plus(n, Z) — nullary ctor arg (guard, must stay green)" do
    assert {:ok, _env} = Program.elaborate(with_body("plus(n, Z)"))
  end

  test "same-named family constructor lowers canonically inside an index" do
    source = """
    type Nat = Z | S(Nat)
    type List(a: Type) = Nil | Cons(a, List(a))
    type Frame = Frame(List(Nat))
    type Holder indices (frame: Frame)
      held : Holder(Frame(Nil()))
    fn make_holder() -> Holder(Frame(Nil())) = held()
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end

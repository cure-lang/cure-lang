defmodule Cure.Elab.HaveTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Validator}
  alias Cure.Elab.{Erase, Program}

  test "a have fact is checked, bound once as Core let, and usable afterward" do
    source = "mod HaveEvidence\n  fn answer() -> Int =\n    have fact: Int = 42\n    fact\nend\n"

    assert {:ok, env} = Program.elaborate(source)
    body = env |> Env.get_def(:answer) |> Map.fetch!(:body)

    assert match?({:let, _, _, {:int_lit, 42}, {:var, 0}}, body)
    assert Enum.count(Validator.nodes(body), &match?({:int_lit, 42}, &1)) == 1
  end

  test "inferred facts and shadowing elaborate" do
    source = "mod HaveShadow\n  fn answer() -> Int =\n    have fact = 1\n    have fact = 2\n    fact\nend\n"
    assert {:ok, _env} = Program.elaborate(source)
  end

  test "dependent annotations retain let transparency" do
    source = """
    mod HaveDependent
      use Std.Equivalent
      type Nat = Z | S(Nat)
      fn proof() -> Equivalent(Nat, Z, Z) =
        have value: Nat = Z
        reflexive(value)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "have has exactly the same Core relevance and erasure as let" do
    have_source = "mod HaveForm\n  fn answer() -> Int =\n    have fact: Int = 42\n    fact\nend\n"
    let_source = "mod LetForm\n  fn answer() -> Int =\n    let fact: Int = 42\n    fact\nend\n"

    assert {:ok, have_env} = Program.elaborate(have_source)
    assert {:ok, let_env} = Program.elaborate(let_source)
    have_core = have_env |> Env.get_def(:answer) |> Map.fetch!(:body)
    let_core = let_env |> Env.get_def(:answer) |> Map.fetch!(:body)

    assert have_core == let_core
    assert Erase.erase(have_env, have_core) == Erase.erase(let_env, let_core)
  end
end

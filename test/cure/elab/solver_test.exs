defmodule Cure.Elab.SolverTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Kernel}
  alias Cure.Diagnostic.{Adapter, ProofChainMismatchProblem}
  alias Cure.Elab.{Program, Solver}

  defp elaborate(body, imports \\ "use Std.Proof.Math") do
    Program.elaborate("mod SolverFixture\n  #{imports}\n  #{body}\nend\n")
  end

  test "decide closes inline and block equality justifications" do
    for justification <- ["by decide", "\n      by decide"] do
      assert {:ok, _} =
               elaborate(
                 """
                 fn chain() -> Equivalent(Bool, True(), True()) = proof chain
                     True() == True()
                     because #{justification}
                 """
                 |> String.replace("\n", "\n  ")
               )
    end
  end

  test "solver evidence is checked in nested non-equality expression positions" do
    assert {:ok, env} =
             elaborate(
               "fn branch(n: Nat, h: IsPositive(n), flag: Bool) -> IsPositive(n) = if flag then by search else by positivity"
             )

    assert :ok = Kernel.check_def(env, :branch)
  end

  test "positivity does not use arbitrary tagged lemmas even recursively" do
    source = """
    mod RestrictedPositivity
      use Std.Proof.Math
      type Witness indices (n: Nat)
        MkWitness : IsPositive(n) -> Witness(n)
      @lemma
      fn from_witness({n: Nat}, w: Witness(n)) -> IsPositive(n) = match w
        MkWitness(h) -> h
      fn restricted(n: Nat, m: Nat, w: Witness(n)) -> IsPositive(plus(n, m)) = by positivity
    end
    """

    assert {:error,
            {:source_context, {:proof_chain_mismatch, %{cause: {:solver_failed, :positivity, :no_evidence}}}, _}} =
             Program.elaborate(source)
  end

  defp assert_refused(source, mode) do
    assert {:error, {:source_context, {:proof_chain_mismatch, problem}, _}} = elaborate(source)
    assert %ProofChainMismatchProblem{kind: :solver_failed, cause: {:solver_failed, ^mode, _}} = problem
    assert %{code: "E110"} = Adapter.from_error({:proof_chain_mismatch, problem}, [])
    problem
  end

  test "search closes a non-equality fn body from a local hypothesis" do
    assert {:ok, _} =
             elaborate("fn local(n: Nat, h: IsPositive(n)) -> IsPositive(n) = by search")
  end

  test "search applies tagged lemmas" do
    assert {:ok, _} = elaborate("fn successor(n: Nat) -> IsPositive(S(n)) = by search")
  end

  test "search refuses missing and ambiguous evidence" do
    assert_refused("fn absent(n: Nat) -> IsPositive(n) = by search", :search)

    problem =
      assert_refused(
        "fn ambiguous(n: Nat, h: IsPositive(n), k: IsPositive(n)) -> IsPositive(n) = by search",
        :search
      )

    assert {:solver_failed, :search, {:ambiguous_proof_search, _, [_, _]}} = problem.cause
  end

  test "positivity handles successors, addition and multiplication" do
    for {name, target, binders} <- [
          {"successor", "S(n)", ""},
          {"addition", "plus(n, m)", ", m: Nat, h: IsPositive(n)"},
          {"product", "multiply(n, m)", ", m: Nat, h: IsPositive(n), k: IsPositive(m)"}
        ] do
      assert {:ok, _} =
               elaborate("fn #{name}(n: Nat#{binders}) -> IsPositive(#{target}) = by positivity")
    end
  end

  test "positivity refuses zero, unknown signs and unrelated local propositions" do
    assert_refused("fn zero() -> IsPositive(Z()) = by positivity", :positivity)
    assert_refused("fn unknown(n: Nat) -> IsPositive(n) = by positivity", :positivity)

    assert_refused(
      "fn unrelated(n: Nat, h: Equivalent(Nat, n, n)) -> Equivalent(Nat, n, n) = by positivity",
      :positivity
    )
  end

  test "search does not silently use the positivity addition strategy" do
    assert_refused(
      "fn addition(n: Nat, m: Nat, h: IsPositive(n)) -> IsPositive(plus(n, m)) = by search",
      :search
    )
  end

  test "decide infers the certified Bool equality decider" do
    for value <- ["True()", "False()"] do
      assert {:ok, env} =
               elaborate("fn decided() -> Equivalent(Bool, #{value}, #{value}) = by decide")

      assert :ok = Kernel.check_def(env, :decided)
    end
  end

  test "decide accepts an explicit Decision for non-equality propositions" do
    assert {:ok, env} =
             elaborate("fn positive() -> IsPositive(S(Z())) = by decide using decide_is_positive(S(Z()))")

    assert :ok = Kernel.check_def(env, :positive)

    assert {:ok, env} =
             elaborate(
               "fn local(n: Nat, h: IsPositive(n)) -> IsPositive(n) = by decide using Yes(h)",
               "use Std.Proof.Math\n  use Std.Decision"
             )

    assert :ok = Kernel.check_def(env, :local)
  end

  test "decide refuses No, a stuck decision, a Bool, and evidence for another goal" do
    problem = assert_refused("fn no() -> Equivalent(Bool, True(), False()) = by decide", :decide)
    assert {:solver_failed, :decide, :decision_no} = problem.cause

    assert_refused(
      "fn stuck(n: Nat) -> IsPositive(n) = by decide using decide_is_positive(n)",
      :decide
    )

    assert_refused("fn boolean() -> IsPositive(S(Z())) = by decide using True()", :decide)
    assert_refused("fn mismatch() -> IsPositive(Z()) = by decide using decide_is_positive(S(Z()))", :decide)
    assert_refused("fn uninferred(n: Nat) -> IsPositive(n) = by decide", :decide)

    assert_refused(
      "fn stuck(d: Decision(IsPositive(S(Z())))) -> IsPositive(S(Z())) = by decide using d",
      :decide
    )
  end

  test "inline and block because solvers see local have facts" do
    for {binders, justification} <- [
          {", h: Equivalent(Int, x, x)", "by search"},
          {"", "\n      have fact: Equivalent(Int, x, x) = reflexive(x)\n      by search"}
        ] do
      assert {:ok, _} =
               elaborate(
                 """
                 fn chain(x: Int#{binders}) -> Equivalent(Int, x, x) = proof chain
                     x == x
                     because #{justification}
                 """
                 |> String.replace("\n", "\n  ")
               )
    end
  end

  test "decide does not unfold an uncertified decision implementation" do
    assert {:ok, env} = elaborate("fn identity(n: Nat) -> Nat = n")

    key = Env.resolve_key(env, env.defs, :decide_is_positive)
    env = %{env | certified: MapSet.delete(env.certified, key)}
    ctx = Context.empty(env)
    expected = {:data, :"Std.Proof.Math#IsPositive", [], [{:nat_lit, 1}]}
    zero = {:function_call, [name: "Z"], []}
    one = {:function_call, [name: "S"], [zero]}
    command = {:solver_command, [solver: :decide], [{:function_call, [name: "decide_is_positive"], [one]}]}

    assert {:error, {:proof_chain_mismatch, %{cause: {:solver_failed, :decide, :decision_stuck}}}} =
             Solver.solve(command, expected, [], ctx, env)
  end
end

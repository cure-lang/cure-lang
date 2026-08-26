defmodule Cure.Elab.ProofInductionLoweringProbeTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Env, Kernel, Validator}
  alias Cure.Elab.Program

  @source """
  mod InductionLoweringProbe
    type Nat = Z | S(Nat)

    fn plus(left: Nat, right: Nat) -> Nat = match left
      Z() -> right
      S(previous) -> S(plus(previous, right))

    fn parameter_induction(value: Nat) -> Equivalent(Nat, plus(value, Z), value) = match value
      Z() -> reflexive(Z)
      S(previous) -> rewrite parameter_induction(previous) in reflexive(S(previous))

    fn expression_induction(offset: Nat, value: Nat) -> Equivalent(Nat, plus(value, offset), plus(value, offset)) =
      expression_induction_aux(offset, value)

    local fn expression_induction_aux(offset: Nat, subject: Nat) -> Equivalent(Nat, plus(subject, offset), plus(subject, offset)) = match subject
      Z() -> reflexive(offset)
      S(previous) -> rewrite expression_induction_aux(offset, previous) in reflexive(S(plus(previous, offset)))
  end
  """

  test "enclosing-parameter induction is an ordinary recursive definition" do
    assert {:ok, env} = Program.elaborate(@source)
    assert Env.certified?(env, :parameter_induction)
    assert :ok = Kernel.check_def(env, :parameter_induction)

    body = Env.get_def(env, :parameter_induction).body
    assert Enum.any?(Validator.nodes(body), &match?({:global, :"InductionLoweringProbe#parameter_induction"}, &1))
  end

  test "arbitrary-subject induction is a private closure-lifted recursive definition" do
    assert {:ok, env} = Program.elaborate(@source)
    helper = Env.get_def(env, :expression_induction_aux)

    assert helper.name == :"InductionLoweringProbe#expression_induction_aux"
    assert Env.certified?(env, :expression_induction_aux)
    assert :ok = Kernel.check_def(env, :expression_induction_aux)

    nodes = Validator.nodes(helper.body)
    assert Enum.any?(nodes, &match?({:global, :"InductionLoweringProbe#expression_induction_aux"}, &1))

    refute Enum.any?(nodes, fn
             {tag, _, _} when tag in [:induction, :proof_induction, :fix] -> true
             _ -> false
           end)
  end

  test "structured parameter induction lowers to the probed recursive representation" do
    source = """
    mod StructuredInduction
      type Nat = Z | S(Nat)
      fn plus(left: Nat, right: Nat) -> Nat = match left
        Z() -> right
        S(previous) -> S(plus(previous, right))

      fn plus_zero_right(value: Nat) -> Equivalent(Nat, plus(value, Z), value) = induction value
        case Z =>
          reflexive(Z)

        case S(previous, induction_hypothesis) =>
          rewrite induction_hypothesis in reflexive(S(previous))
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert Env.certified?(env, :plus_zero_right)
    assert :ok = Kernel.check_def(env, :plus_zero_right)

    nodes = env |> Env.get_def(:plus_zero_right) |> Map.fetch!(:body) |> Validator.nodes()
    refute Enum.any?(nodes, &match?({:induction, _, _}, &1))
  end

  test "indexed evidence induction can suppress an unused generated hypothesis" do
    source = """
    mod IndexedEvidenceInduction
      type Nat = Z | S(Nat)
      type ListNat = Nil | Cons(Nat, ListNat)
      type Evidence indices (values: ListNat)
        Empty : Evidence(Nil())
        More : {tail: ListNat} -> {head: Nat} -> Evidence(tail) -> Evidence(Cons(head, tail))

      fn rebuild({values: ListNat}, proof: Evidence(values)) -> Evidence(values) = induction proof
        case Empty => Empty()
        case More({tail = tail}, {head = head}, rest, _) => More(rest)
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert Env.certified?(env, :rebuild)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :rebuild))
  end

  test "an arbitrary constructor expression is closure-lifted to a private total helper" do
    source = """
    mod LiftedExpressionInduction
      type Nat = Z | S(Nat)

      fn prove(value: Nat) -> Equivalent(Nat, S(value), S(value)) = induction S(value)
        case Z =>
          reflexive(Z)

        case S(previous, induction_hypothesis) =>
          reflexive(S(previous))
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    helper_name = :"LiftedExpressionInduction#__induction_prove_1"
    assert %{body: helper_body} = Env.get_def(env, helper_name)
    assert Env.certified?(env, helper_name)
    assert :ok = Kernel.check_def(env, helper_name)

    assert Enum.any?(Validator.nodes(helper_body), &match?({:global, ^helper_name}, &1))
    refute Enum.any?(Validator.nodes(helper_body), &match?({:induction, _, _}, &1))
  end

  test "an annotated local subject is closure-lifted with its enclosing captures" do
    source = """
    mod LiftedLocalInduction
      type Nat = Z | S(Nat)

      fn prove(value: Nat) -> Equivalent(Nat, S(value), S(value)) =
        let selected: Nat = S(value)
        induction selected
          case Z => reflexive(S(value))
          case S(previous, induction_hypothesis) => reflexive(S(value))
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    helper_name = :"LiftedLocalInduction#__induction_prove_1"
    assert Env.certified?(env, helper_name)
    assert :ok = Kernel.check_def(env, helper_name)
  end

  test "indexed induction reuses ordinary impossible-case coverage" do
    source = """
    mod IndexedInduction
      type Nat = Z | S(Nat)
      type SNat indices (n: Nat)
        szero : SNat(Z)
        ssuc : SNat(n) -> SNat(S(n))

      fn zero_only(witness: SNat(Z)) -> Equivalent(Nat, Z, Z) = induction witness
        case szero => reflexive(Z)
        case ssuc(index, previous, induction_hypothesis) => impossible
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert Env.certified?(env, :zero_only)
    assert :ok = Kernel.check_def(env, :zero_only)
  end

  test "multi-recursive constructors receive hypotheses in field order" do
    source = """
    mod TreeInduction
      type Nat = Z | S(Nat)
      type Tree = Leaf(Nat) | Node(Tree, Tree)

      fn tree_refl(tree: Tree) -> Equivalent(Tree, tree, tree) = induction tree
        case Leaf(value) => reflexive(Leaf(value))
        case Node(left, right, left_induction_hypothesis, right_induction_hypothesis) =>
          reflexive(Node(left, right))
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert Env.certified?(env, :tree_refl)
    assert :ok = Kernel.check_def(env, :tree_refl)
  end

  test "canonical Int induction follows its ordinary constructors" do
    source = """
    mod IntInduction
      fn int_refl(value: Int) -> Equivalent(Int, value, value) = induction value
        case FromNat(natural) => reflexive(FromNat(natural))
        case NegativeSuccessor(natural) => reflexive(NegativeSuccessor(natural))
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert Env.certified?(env, :int_refl)
    assert :ok = Kernel.check_def(env, :int_refl)
  end

  test "nested induction over another enclosing parameter remains ordinary recursion" do
    source = """
    mod NestedInduction
      type Nat = Z | S(Nat)

      fn nested(left: Nat, right: Nat) -> Equivalent(Nat, Z, Z) = induction left
        case Z =>
          induction right
            case Z => reflexive(Z)
            case S(previous_right, right_induction_hypothesis) => reflexive(Z)

        case S(previous_left, left_induction_hypothesis) => reflexive(Z)
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert Env.certified?(env, :nested)
    assert :ok = Kernel.check_def(env, :nested)
  end

  test "ordinary totality rejects a non-decreasing call hidden inside induction" do
    source = """
    mod NonTotalInduction
      type Nat = Z | S(Nat)

      fn bad(value: Nat) -> Nat = induction value
        case Z => bad(Z)
        case S(previous, induction_hypothesis) => induction_hypothesis

      type UsesBad indices (value: Nat)
        witness : UsesBad(bad(Z))
    end
    """

    assert {:error, {:totality_required, :"NonTotalInduction#bad"}} =
             source |> Program.elaborate() |> Program.semantic_result()
  end

  test "compiled induction erases to direct proof behavior with no tactic representation" do
    source = """
    mod EmittedInduction
      type Nat = Z | S(Nat)
      fn proof(value: Nat) -> Equivalent(Nat, value, value) = induction value
        case Z => reflexive(Z)
        case S(previous, induction_hypothesis) => reflexive(S(previous))
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :proof, [:Z]) == :reflexive
    assert apply(module, :proof, [{:S, :Z}]) == :reflexive
  end
end

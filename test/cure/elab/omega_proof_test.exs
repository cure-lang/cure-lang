defmodule Cure.Elab.Omega.ProofTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Eval, Kernel}
  alias Cure.Elab.Omega.Proof
  alias Cure.Elab.Program

  @int {:data, :"Std.Int#Int", [], []}
  @le :"Std.Proof.IntOrder#IsLessThanOrEqual"

  setup_all do
    assert {:ok, env} =
             Program.elaborate("""
             mod OmegaProofTestScope
               use Std.Proof.IntOrder
             end
             """)

    {:ok, env: env}
  end

  test "qualified linear unary operations and integer constants remain valid lemma indices",
       %{env: env} do
    {ctx, names} = context(env, [:x], [])
    x = var(names, :x)

    for term <- [
          {:global, :"Std.Proof.IntOrder#int_zero"},
          call(:"Std.Int#negate", [x]),
          call(:"Std.Proof.IntOrder#succ_int", [x]),
          call(:"Std.Proof.IntOrder#pred_int", [x])
        ] do
      assert_proves(order(term, term), ctx, env)
    end
  end

  defp order(left, right), do: {:data, @le, [], [left, right]}
  defp var(names, name), do: {:var, Enum.find_index(names, &(&1 == name))}
  defp call(name, args), do: Enum.reduce(args, {:global, name}, &{:app, &2, &1})
  defp add(a, b), do: call(:"Std.Proof.IntOrder#add_int", [a, b])
  defp scale(n, a), do: call(:"Std.Proof.IntOrder#scale_nat_int", [{:nat_lit, n}, a])

  defp bind({ctx, names}, name, type) do
    {Context.extend(ctx, Eval.eval(type, Context.env(ctx))), [name | names]}
  end

  defp context(env, integers, inequalities) do
    initial = Enum.reduce(integers, {Context.empty(env), []}, &bind(&2, &1, @int))

    Enum.reduce(inequalities, initial, fn {name, left, right}, {_ctx, names} = acc ->
      bind(acc, name, order(var(names, left), var(names, right)))
    end)
  end

  defp assert_proves(goal, ctx, env) do
    assert {:ok, evidence} = Proof.solve(goal, ctx, env)
    assert :ok = Kernel.check(ctx, evidence, Eval.eval(goal, Context.env(ctx)))
    evidence
  end

  defp globals({:global, name}), do: [name]
  defp globals(term) when is_tuple(term), do: term |> Tuple.to_list() |> Enum.flat_map(&globals/1)
  defp globals(terms) when is_list(terms), do: Enum.flat_map(terms, &globals/1)
  defp globals(_), do: []

  test "uses the actual local proof and preserves indices across unrelated binders", %{env: env} do
    {ctx, names} = context(env, [:a, :b], [{:ab, :a, :b}])
    {ctx, names} = bind({ctx, names}, :unrelated, {:data, :"Std.Nat#Nat", [], []})
    {ctx, names} = bind({ctx, names}, :extra_int, @int)
    goal = order(var(names, :a), var(names, :b))
    assert {:var, 2} = assert_proves(goal, ctx, env)
  end

  test "reconstructs open integer reflexivity with the qualified lemma", %{env: env} do
    {ctx, names} = context(env, [:x], [])
    evidence = assert_proves(order(var(names, :x), var(names, :x)), ctx, env)
    assert [:"Std.Proof.IntOrder#is_less_than_or_equal_is_reflexive"] = globals(evidence)
  end

  test "reconstructs a genuinely transitive open goal", %{env: env} do
    {ctx, names} = context(env, [:a, :b, :c], [{:ab, :a, :b}, {:bc, :b, :c}])
    evidence = assert_proves(order(var(names, :a), var(names, :c)), ctx, env)
    assert [:"Std.Proof.IntOrder#is_less_than_or_equal_is_transitive"] = globals(evidence)
  end

  test "reconstructs multiple transitive hops despite unrelated local indices", %{env: env} do
    {ctx, names} =
      context(env, [:a, :b, :c, :d], [{:ab, :a, :b}, {:bc, :b, :c}, {:cd, :c, :d}])

    {ctx, names} = bind({ctx, names}, :unrelated, {:data, :"Std.Bool#Bool", [], []})
    evidence = assert_proves(order(var(names, :a), var(names, :d)), ctx, env)
    assert [_, _] = globals(evidence)
  end

  test "adds the same arbitrary integer using a checked monotonicity proof", %{env: env} do
    {ctx, names} = context(env, [:a, :b, :c], [{:ab, :a, :b}])
    [a, b, c] = Enum.map([:a, :b, :c], &var(names, &1))
    evidence = assert_proves(order(add(c, a), add(c, b)), ctx, env)

    assert [:"Std.Proof.IntOrder#adding_the_same_number_preserves_less_than_or_equal"] =
             globals(evidence)
  end

  test "adds two independent open inequalities", %{env: env} do
    {ctx, names} = context(env, [:a, :b, :c, :d], [{:ab, :a, :b}, {:cd, :c, :d}])
    [a, b, c, d] = Enum.map([:a, :b, :c, :d], &var(names, &1))
    evidence = assert_proves(order(add(a, c), add(b, d)), ctx, env)
    assert [:"Std.Proof.IntOrder#adding_preserves_less_than_or_equal"] = globals(evidence)
  end

  test "scales an inequality with a compact nonnegative natural literal", %{env: env} do
    {ctx, names} = context(env, [:a, :b], [{:ab, :a, :b}])
    [a, b] = Enum.map([:a, :b], &var(names, &1))
    evidence = assert_proves(order(scale(7, a), scale(7, b)), ctx, env)
    assert [:"Std.Proof.IntOrder#scale_nat_int_is_monotone"] = globals(evidence)
    assert {:app, {:app, {:app, {:app, _, {:nat_lit, 7}}, ^a}, ^b}, {:var, 0}} = evidence
  end

  test "composes transitivity, scaling and addition in one open goal", %{env: env} do
    {ctx, names} =
      context(env, [:a, :b, :c, :d], [{:ab, :a, :b}, {:bc, :b, :c}])

    [a, c, d] = Enum.map([:a, :c, :d], &var(names, &1))
    evidence = assert_proves(order(add(d, scale(2, a)), add(d, scale(2, c))), ctx, env)

    assert [
             :"Std.Proof.IntOrder#adding_the_same_number_preserves_less_than_or_equal",
             :"Std.Proof.IntOrder#scale_nat_int",
             :"Std.Proof.IntOrder#scale_nat_int",
             :"Std.Proof.IntOrder#scale_nat_int_is_monotone",
             :"Std.Proof.IntOrder#is_less_than_or_equal_is_transitive"
           ] = globals(evidence)
  end

  test "accepts an explicit Nat constructor scalar but emits compact Core", %{env: env} do
    {ctx, names} = context(env, [:a, :b], [{:ab, :a, :b}])
    [a, b] = Enum.map([:a, :b], &var(names, &1))
    two = {:ctor, :"Std.Nat#S", [{:ctor, :"Std.Nat#S", [{:ctor, :"Std.Nat#Z", []}]}]}
    left = call(:"Std.Proof.IntOrder#scale_nat_int", [two, a])
    right = call(:"Std.Proof.IntOrder#scale_nat_int", [two, b])
    evidence = assert_proves(order(left, right), ctx, env)
    assert {:app, {:app, {:app, {:app, _, {:nat_lit, 2}}, ^a}, ^b}, _} = evidence
  end

  test "refuses a false closed goal and an unconstrained open goal", %{env: env} do
    assert :unknown = Proof.solve(order({:int_lit, 1}, {:int_lit, 0}), Context.empty(env), env)
    {ctx, names} = context(env, [:a, :b], [])
    assert :unknown = Proof.solve(order(var(names, :a), var(names, :b)), ctx, env)
  end

  test "unrelated hypotheses and missing transitive premises cannot prove a goal", %{env: env} do
    {ctx, names} = context(env, [:a, :b, :c, :d], [{:ab, :a, :b}, {:cd, :c, :d}])
    assert :unknown = Proof.solve(order(var(names, :a), var(names, :d)), ctx, env)
    assert :unknown = Proof.solve(order(var(names, :b), var(names, :a)), ctx, env)
  end

  test "sum reconstruction requires both premises", %{env: env} do
    {ctx, names} = context(env, [:a, :b, :c, :d], [{:ab, :a, :b}])
    [a, b, c, d] = Enum.map([:a, :b, :c, :d], &var(names, &1))
    assert :unknown = Proof.solve(order(add(a, c), add(b, d)), ctx, env)
  end

  test "refuses strict, equality, nonlinear and unsupported algebraic goals", %{env: env} do
    {ctx, names} = context(env, [:a, :b], [{:ab, :a, :b}])
    [a, b] = Enum.map([:a, :b], &var(names, &1))
    assert :unknown = Proof.solve({:data, :"Std.Proof.IntOrder#IsLessThan", [], [a, b]}, ctx, env)
    assert :unknown = Proof.solve({:data, :"Std.Equivalent#Equivalent", [@int], [a, a]}, ctx, env)
    product = call(:"Std.Proof.IntOrder#multiply_int", [a, b])
    assert :unknown = Proof.solve(order(product, product), ctx, env)
    assert :unknown = Proof.solve(order(add(a, b), add(b, a)), ctx, env)
  end

  test "does not recognize user operations by basename or accept nonliteral scaling", %{env: env} do
    {ctx, names} = context(env, [:a, :b], [{:ab, :a, :b}])
    {ctx, names} = bind({ctx, names}, :n, {:data, :"Std.Nat#Nat", [], []})
    [a, b, n] = Enum.map([:a, :b, :n], &var(names, &1))
    fake = call(:"User#add_int", [a, b])
    assert :unknown = Proof.solve(order(fake, fake), ctx, env)
    left = call(:"Std.Proof.IntOrder#scale_nat_int", [n, a])
    right = call(:"Std.Proof.IntOrder#scale_nat_int", [n, b])
    assert :unknown = Proof.solve(order(left, right), ctx, env)
    assert :unknown = Proof.solve(order(scale(1_025, a), scale(1_025, b)), ctx, env)
  end

  test "cycles in local inequalities terminate without inventing an exit", %{env: env} do
    {ctx, names} = context(env, [:a, :b, :c], [{:ab, :a, :b}, {:ba, :b, :a}])
    assert :unknown = Proof.solve(order(var(names, :a), var(names, :c)), ctx, env)
  end

  test "a transitive path beyond the search depth refuses rather than bypassing the kernel",
       %{env: env} do
    variables = Enum.to_list(0..14)
    inequalities = Enum.map(0..13, &{{:edge, &1}, &1, &1 + 1})
    {ctx, names} = context(env, variables, inequalities)
    assert :unknown = Proof.solve(order(var(names, 0), var(names, 14)), ctx, env)
  end

  test "nonlinear local facts are not smuggled into an otherwise supported goal", %{env: env} do
    {ctx, names} = context(env, [:a, :b, :c], [])
    [a, b, c] = Enum.map([:a, :b, :c], &var(names, &1))
    product = call(:"Std.Proof.IntOrder#multiply_int", [a, b])
    {ctx, names} = bind({ctx, names}, :nonlinear, order(product, c))
    assert :unknown = Proof.solve(order(var(names, :a), var(names, :c)), ctx, env)
  end

  test "missing arithmetic lemmas give unknown instead of a generic lemma fallback", %{env: env} do
    key = :"Std.Proof.IntOrder#is_less_than_or_equal_is_transitive"
    env = %{env | defs: Map.delete(env.defs, key)}
    {ctx, names} = context(env, [:a, :b, :c], [{:ab, :a, :b}, {:bc, :b, :c}])
    assert :unknown = Proof.solve(order(var(names, :a), var(names, :c)), ctx, env)
  end

  test "the reflection wrappers themselves elaborate and kernel-check at exact indexed types" do
    source = File.read!("lib/std/proof_linear_arithmetic_reflection.cure")
    assert {:ok, env} = Program.elaborate(source)

    for name <- [:checked_holds, :goal_evaluates_true, :close_less_than_or_equal, :close_less_than] do
      key = String.to_existing_atom("Std.Proof.LinearArithmetic.Reflection#" <> Atom.to_string(name))
      assert Env.get_def(env, key)
      assert :ok = Kernel.check_def(env, key)
    end
  end

  test "the reflection API cannot turn arbitrary True evidence into a false order proof" do
    assert {:error, _} =
             Program.elaborate("""
             mod OmegaReflectionRefusal
               use Std.Proof.IntOrder
               use Std.Proof.LinearArithmetic.Reflection
               fn false_goal() -> IsLessThanOrEqual(FromNat(S(Z())), FromNat(Z())) =
                 close_less_than_or_equal(Confirmed())
             end
             """)
  end

  test "the indexed checker wrapper refuses a Bool instead of proof of its exact verdict" do
    source = """
    mod OmegaCheckerEvidenceRefusal
      use Std.Proof.IntMath
      use Std.Proof.LinearArithmetic
      use Std.Proof.LinearArithmetic.Reflection
      fn preserve(h: Hypotheses, g: LinearAtom, w: FarkasWitness,
        evidence: IsTrue(check_lia_candidate(h, g, w))
      ) -> IsTrue(check_lia_candidate(h, g, w)) =
        checked_holds(h, g, w, evidence)
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"OmegaCheckerEvidenceRefusal#preserve")

    invalid =
      String.replace(source, "checked_holds(h, g, w, evidence)", "checked_holds(h, g, w, check_lia_candidate(h, g, w))")

    assert {:error, _} = Program.elaborate(invalid)
  end

  test "the semantic wrapper refuses trivial truth for an open unrelated atom" do
    source = """
    mod OmegaSemanticEvidenceRefusal
      use Std.Proof.IntMath
      use Std.Proof.LinearArithmetic
      use Std.Proof.LinearArithmetic.Reflection
      fn preserve(g: LinearAtom, v: Valuation,
        evidence: IsTrue(evaluate_atom(g, v))
      ) -> IsTrue(evaluate_atom(g, v)) =
        goal_evaluates_true(g, v, evidence)
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"OmegaSemanticEvidenceRefusal#preserve")
    invalid = String.replace(source, "goal_evaluates_true(g, v, evidence)", "goal_evaluates_true(g, v, Confirmed())")
    assert {:error, _} = Program.elaborate(invalid)
  end
end

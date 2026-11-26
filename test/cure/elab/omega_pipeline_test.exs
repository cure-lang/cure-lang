defmodule Cure.Elab.OmegaPipelineTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Eval, Kernel}
  alias Cure.Elab.{Omega, Program}
  alias Cure.Elab.Omega.{Certificate, Linear}

  setup_all do
    assert {:ok, env} =
             Program.elaborate("""
             mod OmegaPipelineFixture
               use Std.Proof.LinearArithmetic
               use Std.Proof.IntOrder
               fn seed(a: Int, b: Int, h: IsLessThanOrEqual(a, b)) -> IsLessThanOrEqual(a, b) = h
             end
             """)

    %{type: type} = Env.get_def(env, :seed)
    {context, target} = open_telescope(type, Context.empty(env))
    %{env: env, context: context, target: target}
  end

  defp open_telescope({:pi, grade, domain, body}, context),
    do: open_telescope(body, Context.extend(context, Eval.eval(domain, Context.env(context)), grade))

  defp open_telescope(target, context), do: {context, target}

  test "an affine positive constant is contradictory, not a negative one" do
    assert {:prf, [1]} = Omega.solve([Omega.atom_le({1, %{}})])
    assert :unknown = Omega.solve([Omega.atom_le({-1, %{}})])
    assert {:prf, [1]} = Omega.solve([Omega.atom_lt({0, %{}})])
  end

  test "negation is the integer complement for both relations" do
    for bound <- -2..2, coefficient <- [-2, -1, 1, 2], relation <- [:le, :lt], x <- -3..3 do
      atom = {{bound, %{0 => coefficient}}, relation}
      refute holds?(atom, %{0 => x}) == holds?(Omega.negate(atom), %{0 => x})
    end
  end

  test "witness provenance survives multiple variable-elimination rounds" do
    atoms = [
      {{0, %{0 => 1, 1 => -1}}, :le},
      {{0, %{1 => 1, 2 => -1}}, :le},
      {{-1, %{0 => -1, 2 => 1}}, :le}
    ]

    assert {:prf, [1, 1, 1] = witness} = Omega.solve(atoms)
    assert Omega.valid_witness?(atoms, witness)
    refute Omega.valid_witness?(atoms, [1, 0, 1])
    refute Omega.valid_witness?(atoms, [1, 1])
    refute Omega.valid_witness?(atoms, [-1, 1, 1])

    assert {:prf, [0, 1, 1, 1] = expanded} = Omega.solve([{{0, %{9 => 0}}, :le} | atoms])
    assert Omega.valid_witness?([{{0, %{9 => 0}}, :le} | atoms], expanded)
  end

  test "every small produced witness independently cancels coefficients to a negative bound" do
    for a <- -1..1, b <- -1..1, c <- -1..1 do
      atoms = [{{a, %{0 => 1, 1 => -1}}, :le}, {{b, %{1 => 1}}, :le}, {{c, %{0 => -1}}, :le}]

      case Omega.solve(atoms) do
        {:prf, witness} ->
          assert Omega.valid_witness?(atoms, witness)
          for x <- -2..2, y <- -2..2, do: refute(Enum.all?(atoms, &holds?(&1, %{0 => x, 1 => y})))

        :unknown ->
          :ok
      end
    end
  end

  test "the search guard refuses a large cross product before expanding it" do
    positive = for n <- 1..65, do: {{n, %{0 => 1}}, :le}
    negative = for n <- 1..65, do: {{n, %{0 => -1}}, :le}
    assert :unknown = Omega.solve(positive ++ negative)
  end

  test "reified hypotheses retain authored names and append the negated goal", %{
    context: context,
    env: env,
    target: target
  } do
    hypotheses = Linear.reify_hypotheses(context, ["h", "b", "a"])
    assert [{"h", ^target}, {"b", _}, {"a", _}] = hypotheses
    assert {:ok, [positive, negative] = atoms} = Linear.atoms(hypotheses, target, context, env)
    assert positive == {{0, %{2 => 1, 1 => -1}}, :le}
    assert negative == {{-1, %{2 => -1, 1 => 1}}, :le}
    assert {:prf, [1, 1] = witness} = Omega.solve(atoms)
    assert Omega.valid_witness?(atoms, witness)
  end

  test "literal natural scaling is inside the canonical integer fragment", %{context: context, env: env} do
    scale = fn value -> {:app, {:app, {:global, :"Std.Proof.IntOrder#scale_nat_int"}, {:nat_lit, 3}}, value} end
    goal = {:data, :"Std.Proof.IntOrder#IsLessThanOrEqual", [], [scale.({:var, 2}), scale.({:var, 1})]}
    assert {:ok, {{0, %{2 => 3, 1 => -3}}, :le}} = Linear.goal_atom(goal, context, env)
  end

  test "equality needs two independent obligations and canonical integer carrier", %{context: context, env: env} do
    equality = {:data, :"Std.Equivalent#Equivalent", [{:data, :"Std.Int#Int", [], []}], [{:var, 2}, {:var, 1}]}
    assert {:ok, [{left, _}, {right, _}]} = Linear.obligations([{"h", equality}], equality, context, env)
    assert {:prf, left_witness} = Omega.solve(left)
    assert {:prf, right_witness} = Omega.solve(right)
    assert Omega.valid_witness?(left, left_witness)
    assert Omega.valid_witness?(right, right_witness)
    assert :outside_fragment = Linear.atoms([], equality, context, env)
  end

  test "unrelated user families or arithmetic names do not masquerade as the integer fragment", %{
    context: context,
    env: env
  } do
    spoofed_family = {:data, :"Spoof#IsLessThanOrEqual", [], [{:var, 2}, {:var, 1}]}
    assert :outside_fragment = Linear.goal_atom(spoofed_family, context, env)
    spoofed_add = {:app, {:app, {:global, :"Spoof#add_int"}, {:var, 2}}, {:int_lit, 1}}
    goal = {:data, :"Std.Proof.IntOrder#IsLessThanOrEqual", [], [spoofed_add, {:var, 1}]}
    assert :outside_fragment = Linear.goal_atom(goal, context, env)
  end

  test "the native candidate checker certifies the scalar data but rejects forged multipliers", %{env: env} do
    goal = {{0, %{5 => 1, 9 => -1}}, :le}
    hypotheses = [goal]
    assert Env.certified?(env, :"Std.Proof.LinearArithmetic#check_lia_candidate")
    assert :ok = Kernel.check_def(env, :"Std.Proof.LinearArithmetic#check_lia_candidate")
    assert {:ctor, :"Std.Bool#True", []} = candidate(hypotheses, goal, [1, 1], env)
    assert {:ctor, :"Std.Bool#False", []} = candidate(hypotheses, goal, [0, 0], env)
    assert {:ctor, :"Std.Bool#False", []} = candidate(hypotheses, goal, [1], env)
  end

  test "sparse coordinates share one dense basis and do not alias different variables", %{env: env} do
    hypothesis = {{0, %{5 => 1}}, :le}
    goal = {{0, %{9 => 1}}, :le}
    assert [5, 9] = Certificate.basis([hypothesis, goal])
    assert {:ctor, :"Std.Bool#False", []} = candidate([hypothesis], goal, [1, 1], env)

    assert {:ctor, :"Std.List#Cons", [{:var, 5}, {:ctor, :"Std.List#Cons", [{:var, 9}, {:ctor, :"Std.List#Nil", []}]}]} =
             Certificate.valuation([hypothesis, goal])
  end

  defp candidate(hypotheses, goal, witness, env) do
    assert {:ok, term} = Certificate.term(hypotheses, goal, witness)
    context = Context.empty(env)
    assert :ok = Kernel.check(context, term, Kernel.bool_type_value(env))
    Kernel.normalize(context, term)
  end

  defp holds?({{bound, coefficients}, relation}, valuation) do
    value =
      Enum.reduce(coefficients, 0, fn {index, coefficient}, sum -> sum + coefficient * Map.fetch!(valuation, index) end)

    if relation == :le, do: value <= bound, else: value < bound
  end
end

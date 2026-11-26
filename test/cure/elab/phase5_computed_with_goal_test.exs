defmodule Cure.Elab.Phase5ComputedWithGoalTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Eval, Kernel, Normalise, Term, Validator}
  alias Cure.Elab.{Declarations, Elaborator, Emit, Program, Relevance}

  @guard {Elaborator, :computed_with_goal_retry}
  @prefix """
  mod FilterGoalProbe
    @reducible
    fn empty() -> List(Nat) = Nil()
    type Member(head: Nat) indices (items: List(Nat))
      Here : {tail: List(Nat)} -> Member(head, Cons(head, tail))
      There : {other: Nat} -> {tail: List(Nat)} -> (prior: Member(head, tail)) -> Member(head, Cons(other, tail))
    fn here(head: Nat, tail: List(Nat)) -> Member(head, Cons(head, tail)) = Here()
    fn impossible_member({result: Type}, head: Nat, evidence: Member(head, empty())) -> result = match evidence
      Here() -> impossible
      There(_) -> impossible
    fn copy_values(items: List(Nat)) -> List(Nat) = match items
      Nil() -> empty()
      Cons(head, tail) -> Cons(head, tail)
    @reducible
    fn sift(test: (Nat -> Bool), items: List(Nat)) -> List(Nat) = match items
      Nil() -> empty()
      Cons(head, tail) -> match test(head)
        True() -> Cons(head, tail)
        False() -> empty()
  """
  @direct """
    fn direct(test: (Nat -> Bool), head: Nat, evidence: Member(head, sift(test, Cons(head, empty())))) -> Member(head, sift(test, copy_values(Cons(head, empty())))) = evidence
  """
  @split """
    fn split(test: (Nat -> Bool), head: Nat, evidence: Member(head, sift(test, Cons(head, empty())))) -> Member(head, sift(test, copy_values(Cons(head, empty())))) = with test(head)
      True() -> here(head, empty())
      False() -> impossible_member(head, evidence)
  """
  @targets [
    {Elaborator, :retry_computed_with_goal, 2},
    {Elaborator, :computed_with_prepare_goal, 3},
    {Elaborator, :computed_with_whnf, 3},
    {Elaborator, :computed_with_focus, 6}
  ]

  setup_all do
    # The baseline producer must reach the source assertion, not fail in setup.
    assert {:ok, env} = Program.elaborate(@prefix <> @direct <> extensions() <> "end\n")
    {:ok, fixture: fixture(env)}
  end

  @tag :computed_with_callback_fuel
  test "exhaustion after prepared-goal callback entry propagates separately from frontier exhaustion", %{fixture: f} do
    {{:ok, _}, remaining} = budgeted(fn -> invoke(f) end)
    used = 100_000 - remaining
    key = Normalise.fuel_key()

    budget =
      Enum.find((used - 1)..1//-1, fn budget ->
        {result, events} =
          trace(
            fn -> Normalise.with_fuel(budget, fn -> invoke(f) end) end,
            [{Elaborator, :elaborate_with_original, 8}, {Normalise, :spend_fuel, 1}]
          )

        result == :fuel_exhausted and match?([_, _], calls(events, :elaborate_with_original)) and
          spend_throw_in?(events, :elaborate_with_original, 8)
      end)

    assert is_integer(budget)

    for previous <- [:absent, nil, false] do
      with_process(@guard, previous, fn ->
        {result, events} =
          trace(
            fn -> Normalise.with_fuel(budget, fn -> invoke(f) end) end,
            [{Elaborator, :elaborate_with_original, 8}, {Normalise, :spend_fuel, 1}]
          )

        assert result == :fuel_exhausted
        assert spend_throw_in?(events, :elaborate_with_original, 8)
        assert Process.get(@guard, :absent) == previous
        assert [_, _] = calls(events, :elaborate_with_original)

        assert Enum.any?(events, fn
                 {:trace, _, :exception_from, {Elaborator, :elaborate_with_original, 8}, {:throw, {^key, :exhausted}}} ->
                   true

                 _ ->
                   false
               end)

        assert Enum.any?(events, fn
                 {:trace, _, :return_from, {Elaborator, :computed_with_prepare_goal, 3}, {:ok, _}} -> true
                 _ -> false
               end)
      end)
    end
  end

  @tag :computed_with_source
  test "the unchanged twenty-four-line split and direct control close at their original headers" do
    source = @prefix <> @direct <> @split <> "end\n"
    assert length(String.split(source, "\n", trim: true)) == 24
    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, q(:direct))
    assert :ok = Kernel.check_def(env, q(:split))
    assert Env.get_def(env, q(:direct)).type == Env.get_def(env, q(:split)).type
  end

  test "the original checked failure retries the complete producer once with unchanged source arguments", %{fixture: f} do
    assert {:error, :branch_type} = original(f)

    {{:ok, term}, events} =
      trace(fn -> invoke(f) end, [{Elaborator, :elaborate_with_original, 8}, {Elaborator, :elaborate_with, 8}])

    assert :ok = Kernel.check(f.ctx, term, expected(f))
    assert {:ok, []} = Validator.validate(term, Validator.release_config(), f.env)
    assert :ok = Relevance.check(f.env, q(:split), Enum.reverse(f.ctx.grades), term)
    assert :ok = Kernel.check_def(close(f, term), q(:split))
    assert [[_, _, prepared_ctx]] = calls(events, :computed_with_prepare_goal)
    assert prepared_ctx == f.ctx

    assert [[_, _, _, first_goal, _, _, _, _], [_, _, _, prepared_goal, _, _, _, _]] =
             calls(events, :elaborate_with_original)

    assert first_goal == f.goal
    assert prepared_goal != f.goal
    {:data, family, params, [_]} = f.goal
    assert {:data, ^family, ^params, [_]} = prepared_goal

    for [scrutinee, arms, proof, _goal, names, ctx, env, original_params] <- calls(events, :elaborate_with_original) do
      assert {scrutinee, arms, proof, names, ctx, env, original_params} ==
               {f.scrutinee, f.arms, f.proof, f.names, f.ctx, f.env, f.original_params}
    end

    assert [] = Enum.drop(calls(events, :computed_with_prepare_goal), 1)
  end

  test "regular certified wrappers need no reducible publication and have only a growing blocking-head allowlist", %{
    fixture: f
  } do
    assert Env.certified?(f.env, q(:copy_values))
    refute Map.get(Env.get_def(f.env, q(:copy_values)), :reducible, false)
    {{:ok, _}, events} = trace(fn -> invoke(f) end, [{Normalise, :whnf, 3}])
    assert [[_, _, first], [_, _, second]] = calls(events, :computed_with_whnf)
    assert first == MapSet.new([q(:sift)])
    assert second == MapSet.new([q(:sift), q(:copy_values)])

    for {:trace, _, :call, {Normalise, :whnf, [_, _, options]}} <- during(events, :computed_with_prepare_goal, 3) do
      assert Keyword.fetch!(options, :delta) == :certified
      assert Keyword.fetch!(options, :stuck_cases) == :expose
      assert %MapSet{} = Keyword.fetch!(options, :delta_allow)
      refute MapSet.member?(Keyword.fetch!(options, :delta_allow), q(:empty))
    end
  end

  @tag :computed_with_focus
  test "a separately typed scrutinee focus exposes the next blocker without splicing the focus into its whole case", %{
    fixture: f
  } do
    focused = %{f | goal: replace(f.goal, q(:copy_values), q(:wrap_1))}
    assert {:error, _} = original(focused)
    {{:ok, term}, events} = trace(fn -> invoke(focused) end)
    assert :ok = Kernel.check(f.ctx, term, expected(focused))
    assert [_ | _] = calls(events, :computed_with_focus)

    assert Enum.any?(events, fn
             {:trace, _, :return_from, {Elaborator, :computed_with_focus, 6}, {:ok, _, 1, _, _}} -> true
             _ -> false
           end)

    assert [[_, original, _] | _] = calls(events, :computed_with_whnf)
    {:data, _, _, [^original]} = focused.goal
    assert Enum.count(calls(events, :computed_with_whnf), fn [_, input, _] -> input == original end) == 1
  end

  @tag :computed_with_identity
  test "already working goals retain exact Core and exact existing delta budget", %{fixture: f} do
    working = %{f | goal: remove_wrapper(f.goal, q(:copy_values))}
    {old, old_budget} = budgeted(fn -> original(working) end)
    {{current, current_budget}, events} = trace(fn -> budgeted(fn -> invoke(working) end) end)
    assert {:ok, _} = old
    assert current == old
    assert current_budget == old_budget
    assert [] = calls(events, :computed_with_prepare_goal)
    assert [] = calls(events, :computed_with_whnf)
  end

  test "unrelated failures return the exact original error without frontier normalization", %{fixture: f} do
    broken = %{f | arms: [arm("True", invoke_ast("unknown_branch_function", [])), arm("False", invoke_ast("Z", []))]}
    old = original(broken)
    assert {:error, _} = old
    {result, events} = trace(fn -> invoke(broken) end)
    assert result == old
    assert [] = calls(events, :computed_with_whnf)
  end

  test "proof clauses and variable majors remain outside the retry class", %{fixture: f} do
    proof = %{f | proof: "equation"}
    {result, events} = trace(fn -> invoke(proof) end)
    assert result == original(proof)
    assert [] = calls(events, :computed_with_prepare_goal)

    extended = Context.extend(f.ctx, Eval.eval(bool(), []))

    variable = %{
      f
      | ctx: extended,
        names: ["flag" | f.names],
        scrutinee: variable("flag"),
        goal: Term.shift(f.goal, 1, 0)
    }

    {result, events} = trace(fn -> invoke(variable) end)
    assert result == original(variable)
    assert [] = calls(events, :computed_with_prepare_goal)
  end

  @tag :computed_with_preflight
  test "oversized raw goals refuse before any new retry goal typing or source-major elaboration", %{fixture: f} do
    large = Enum.reduce(1..4_100, zero(), fn _, term -> {:ctor, :"Std.Nat#S", [term]} end)
    {:data, family, _params, indices} = f.goal
    oversized = %{f | goal: {:data, family, [large], indices}}
    old = original(oversized)

    {result, events} =
      trace(fn -> invoke(oversized) end, [{Kernel, :infer, 2}, {Elaborator, :elaborate_expr_typed, 4}])

    assert result == old
    assert [] = calls(during(events, :retry_computed_with_goal, 2), :computed_with_prepare_goal)
    assert [] = module_calls(during(events, :retry_computed_with_goal, 2), Kernel, :infer)
    assert [] = calls(during(events, :retry_computed_with_goal, 2), :elaborate_expr_typed)
  end

  @tag :computed_with_authority
  test "Context.signature supplies authority and missing certificates do not become publication", %{fixture: f} do
    unrelated_env = %{f.env | certified: MapSet.delete(f.env.certified, q(:copy_values))}
    assert {:ok, _} = invoke(%{f | env: unrelated_env})
    no_certificate = %{f.env | certified: MapSet.delete(f.env.certified, q(:copy_values))}
    refused = %{f | env: no_certificate, ctx: %{f.ctx | signature: no_certificate}}
    old = original(refused)
    {result, events} = trace(fn -> invoke(refused) end)
    assert result == old

    refute Enum.any?(calls(events, :computed_with_whnf), fn [_, _, allowed] ->
             MapSet.member?(allowed, q(:copy_values))
           end)
  end

  test "an open or bodyless blocker is never enrolled", %{fixture: f} do
    for body <- [{:var, 0}, nil, {:extern, {:unknown, :unknown, 1}}] do
      altered = put_definition(f, :copy_values, :body, body)

      # Forged certified nil/extern bodies already crash the old normalizer.
      # Such declarations normally lack certificates; do not claim that their
      # certificate refusal reaches the later closed-body eligibility guard.
      altered =
        if body == {:var, 0} do
          altered
        else
          env = %{altered.env | certified: MapSet.delete(altered.env.certified, q(:copy_values))}
          %{altered | env: env, ctx: %{altered.ctx | signature: env}}
        end

      old = original(altered)
      {result, events} = trace(fn -> invoke(altered) end)
      assert result == old

      refute Enum.any?(calls(events, :computed_with_whnf), fn [_, _, allowed] ->
               MapSet.member?(allowed, q(:copy_values))
             end)
    end
  end

  @tag :computed_with_heads
  test "eight discovered heads are allowed but a ninth head refuses the entire retry", %{fixture: f} do
    boundary = %{f | goal: replace(f.goal, q(:copy_values), q(:wrap_6))}
    {{:ok, term}, accepted} = trace(fn -> invoke(boundary) end)
    assert :ok = Kernel.check(f.ctx, term, expected(boundary))
    assert 8 == length(Enum.uniq(Enum.map(calls(accepted, :computed_with_whnf), &List.last/1)))
    beyond = %{f | goal: replace(f.goal, q(:copy_values), q(:wrap_7))}
    old = original(beyond)
    {result, events} = trace(fn -> invoke(beyond) end)
    assert result == old
    assert 8 == MapSet.size(List.last(List.last(calls(events, :computed_with_whnf))))
  end

  @tag :computed_with_guard
  test "selection skips unrelated indices, preserves parameters, and refuses nine indices before new typing", %{
    fixture: f
  } do
    {:data, _, [head], [operand]} = f.goal
    goal = {:data, q(:Goal), [head], [zero(), operand]}
    frame = %{f | goal: goal, arms: Enum.map(f.arms, &wrap_goal_arm/1)}
    assert {:ok, _} = Kernel.infer(f.ctx, goal)
    assert {:error, _} = original(frame)
    {{:ok, term}, events} = trace(fn -> invoke(frame) end, [{Elaborator, :elaborate_with_original, 8}])
    assert :ok = Kernel.check(f.ctx, term, expected(frame))
    assert [_, [_, _, _, {:data, _, [^head], [first, _]}, _, _, _, _]] = calls(events, :elaborate_with_original)
    assert first == zero()

    beyond = %{f | goal: {:data, q(:NineGoal), [head], List.duplicate(zero(), 8) ++ [operand]}}
    old = original(beyond)
    {result, events} = trace(fn -> invoke(beyond) end, [{Kernel, :infer, 2}, {Elaborator, :elaborate_expr_typed, 4}])
    assert result == old
    assert [] = module_calls(during(events, :retry_computed_with_goal, 2), Kernel, :infer)
    assert [] = calls(during(events, :retry_computed_with_goal, 2), :elaborate_expr_typed)
  end

  @tag :computed_with_body_bound
  test "a large closed blocker body refuses before its normalization even though the raw goal is well formed", %{
    fixture: f
  } do
    definition = Env.get_def(f.env, q(:copy_values))
    large = Enum.reduce(1..1_100, zero(), fn _, term -> {:ctor, :"Std.Nat#S", [term]} end)
    {:lam, grade, domain, body} = definition.body
    padded = {:lam, grade, domain, {:let, :unrestricted, nat(), large, Term.shift(body, 1, 0)}}
    altered = put_definition(f, :copy_values, :body, padded)
    assert {:ok, _} = Kernel.infer(altered.ctx, altered.goal)
    assert :ok = Kernel.check(Context.empty(altered.env), padded, Eval.eval(definition.type, []))
    old = original(altered)
    {result, events} = trace(fn -> invoke(altered) end)
    assert result == old

    refute Enum.any?(calls(events, :computed_with_whnf), fn [_, _, allowed] ->
             MapSet.member?(allowed, q(:copy_values))
           end)
  end

  @tag :computed_with_work
  test "structural work is shared across bounded outputs and refuses the entire attempt at32768", %{fixture: f} do
    list =
      Enum.reduce(1..490, {:ctor, :"Std.List#Nil", []}, fn _, rest -> {:ctor, :"Std.List#Cons", [zero(), rest]} end)

    definition = Env.get_def(f.env, q(:sift))
    padded = replace_nil_branch(definition.body, list)
    altered = put_definition(f, :sift, :body, padded)
    frame = %{altered | goal: replace(altered.goal, q(:copy_values), q(:wrap_6))}
    assert :ok = Kernel.check(Context.empty(frame.env), padded, Eval.eval(definition.type, []))
    assert {:ok, _} = Kernel.infer(frame.ctx, frame.goal)
    old = original(frame)
    {result, events} = trace(fn -> invoke(frame) end, [{Elaborator, :computed_with_frontier, 2}])
    assert result == old
    states = for [_, state] <- calls(events, :computed_with_frontier), do: state
    assert [_ | _] = states
    assert Enum.all?(states, &(&1.work <= 32_768))
    assert List.last(states).work > 24_000
    assert List.last(states).pass < 8

    refute Enum.any?(events, fn
             {:trace, _, :return_from, {Elaborator, :computed_with_prepare_goal, 3}, {:ok, _}} -> true
             _ -> false
           end)
  end

  @tag :computed_with_guard
  test "the one-shot guard restores absent nil and false on successful and refused retries", %{fixture: f} do
    for previous <- [:absent, nil, false] do
      with_process(@guard, previous, fn ->
        assert {:ok, _} = invoke(f)
        assert Process.get(@guard, :absent) == previous
        refusing = %{f | goal: replace(f.goal, q(:copy_values), q(:wrap_7))}
        {result, events} = trace(fn -> invoke(refusing) end)
        assert {:error, _} = result
        assert [[_, _, _]] = calls(events, :computed_with_prepare_goal)
        assert [_ | _] = calls(events, :computed_with_whnf)
        assert Process.get(@guard, :absent) == previous
      end)
    end
  end

  @tag :computed_with_fuel
  test "finite fuel is shared and exhaustion after frontier entry propagates while restoring the guard", %{fixture: f} do
    key = Normalise.fuel_key()
    assert Process.get(key, :absent) == :absent
    {{:ok, _}, full_remaining} = budgeted(fn -> invoke(f) end)
    {{:error, _}, old_remaining} = budgeted(fn -> original(f) end)
    used = 100_000 - full_remaining
    old_used = 100_000 - old_remaining
    assert used > old_used

    budgets = Enum.uniq([used - 1 | Enum.to_list((old_used + 1)..used//8)])

    found =
      Enum.find(budgets, fn budget ->
        with_process(@guard, nil, fn ->
          {result, events} =
            trace(fn -> Normalise.with_fuel(budget, fn -> invoke(f) end) end, [{Normalise, :spend_fuel, 1}])

          assert Process.get(@guard, :absent) == nil
          assert Process.get(key, :absent) == :absent

          result == :fuel_exhausted and
            spend_throw_in?(events, :computed_with_whnf, 3)
        end)
      end)

    assert is_integer(found)

    with_process(key, 0, fn ->
      assert catch_throw(invoke(f)) == {key, :exhausted}
      assert Process.get(key) == 0
    end)
  end

  test "absent fuel installs one bounded local budget and leaves the caller absent", %{fixture: f} do
    {{:ok, _}, events} = trace(fn -> invoke(f) end, [{Normalise, :with_fuel, 2}])
    assert Process.get(Normalise.fuel_key(), :absent) == :absent
    local = module_calls(during(events, :computed_with_prepare_goal, 3), Normalise, :with_fuel)
    assert [_] = Enum.filter(local, fn [fuel, _] -> fuel == 128 end)
    {_, events} = trace(fn -> budgeted(fn -> invoke(f) end) end, [{Normalise, :with_fuel, 2}])

    refute Enum.any?(
             module_calls(during(events, :computed_with_prepare_goal, 3), Normalise, :with_fuel),
             fn [fuel, _] -> is_integer(fuel) end
           )
  end

  test "a complete repaired term cannot prove an unrelated well-formed goal", %{fixture: f} do
    assert {:ok, term} = invoke(f)
    {:data, family, params, [operand]} = f.goal
    {:ok, type} = Kernel.infer(f.ctx, operand)
    ctx = Context.extend(f.ctx, type)
    wrong = {:data, family, Enum.map(params, &Term.shift(&1, 1, 0)), [{:var, 0}]}
    assert {:ok, _} = Kernel.infer(ctx, wrong)
    assert {:error, _} = Kernel.check(ctx, Term.shift(term, 1, 0), Eval.eval(wrong, Context.env(ctx)))
    assert {:error, _} = invoke(%{f | ctx: ctx, names: ["items" | f.names], goal: wrong})
  end

  @tag :computed_with_protection
  test "a protected global is not enrolled at a different typed argument spine", %{fixture: f} do
    ctx = Context.empty(f.env) |> Context.extend(Eval.eval(bool(), [])) |> Context.extend(Eval.eval(bool(), []))

    frame = %{
      f
      | ctx: ctx,
        names: ["other", "first"],
        original_params: [],
        scrutinee: invoke_ast("flip", [variable("first")]),
        goal: {:data, q(:IsTrue), [], [{:app, {:global, q(:flip)}, {:var, 0}}]},
        arms: [arm("True", invoke_ast("yep", [])), arm("False", invoke_ast("yep", []))]
    }

    assert {:ok, _} = Kernel.infer(ctx, frame.goal)
    assert {:error, {:branch_type, _, {:conversion_failure, _, _}}} = old = original(frame)
    {result, events} = trace(fn -> invoke(frame) end)
    assert result == old
    assert [[_, _, _]] = calls(events, :computed_with_prepare_goal)
    assert [] = calls(events, :computed_with_whnf)
  end

  @tag :computed_with_scope
  test "constructors binders and case branches never supply a blocking-head discovery path", %{fixture: f} do
    {:data, family, params, [operand]} = f.goal
    list_type = {:data, :"Std.List#List", [{:level_value, Cure.Core.UniverseLevel.zero()}, nat()], []}

    hidden = [
      {:let, :unrestricted, list_type, operand, {:var, 0}},
      {:app, {:lam, :unrestricted, nat(), Term.shift(operand, 1, 0)}, zero()},
      {:ctor, :"Std.List#Cons", [zero(), operand]},
      {:case, {:ctor, :"Std.Bool#False", []}, {:lam, :unrestricted, bool(), list_type},
       [{:"Std.Bool#False", 0, operand}, {:"Std.Bool#True", 0, operand}]}
    ]

    for value <- hidden do
      frame = %{f | goal: {:data, family, params, [value]}}
      assert {:ok, _} = Kernel.infer(f.ctx, frame.goal)
      old = original(frame)
      {result, events} = trace(fn -> invoke(frame) end)
      assert result == old
      assert [] = calls(events, :computed_with_whnf)
    end
  end

  @tag :computed_with_quantities
  test "otherwise well-typed repaired candidates still reject erased use and linear or affine misuse", %{fixture: f} do
    for {grade, values} <- [
          {:erased, [variable("secret"), variable("secret")]},
          {:linear, [variable("secret"), variable("secret")]},
          {:affine, [variable("secret"), variable("secret")]},
          {:linear, [invoke_ast("Z", []), invoke_ast("Z", [])]}
        ] do
      frame = payload_frame(f, grade, values)
      assert {:error, _} = original(frame)
      {{:ok, term}, events} = trace(fn -> invoke(frame) end)
      assert [[_, _, _]] = calls(events, :computed_with_prepare_goal)
      assert :ok = Kernel.check(frame.ctx, term, expected(frame))
      assert {:error, _} = Relevance.check(frame.env, q(:quantitative_split), Enum.reverse(frame.ctx.grades), term)
    end
  end

  @tag :computed_with_hole
  test "a value hole survives an otherwise valid repaired candidate and the ordinary release and Emit gates reject it",
       %{fixture: f} do
    frame = payload_frame(f, :unrestricted, [{:hole, [], "unfinished"}, invoke_ast("Z", [])])
    assert {:error, _} = original(frame)
    {{:ok, term}, events} = trace(fn -> invoke(frame) end)
    assert [[_, _, _]] = calls(events, :computed_with_prepare_goal)
    assert :ok = Kernel.check(frame.ctx, term, expected(frame))
    assert {:error, _} = Validator.validate(term, Validator.release_config(), frame.env)
    domains = f.domains ++ [{:unrestricted, nat()}]
    type = Enum.reduce(Enum.reverse(domains), frame.goal, fn {grade, domain}, rest -> {:pi, grade, domain, rest} end)
    body = Enum.reduce(Enum.reverse(domains), term, fn {grade, domain}, rest -> {:lam, grade, domain, rest} end)
    env = Env.add_def(frame.env, q(:hole_split), type, body, Enum.map(domains, &elem(&1, 0)))
    assert :ok = Kernel.check_def(env, q(:hole_split))
    assert {:error, {:unfilled_hole, _}} = Emit.compile_forms(env, :ComputedWithHoleNegative, [:hole_split])
  end

  @tag :tmp_dir
  test "the repaired source runs through normal Compiler relevance and Emit with erased proof ABI", %{tmp_dir: dir} do
    source =
      @prefix <>
        @direct <>
        @split <>
        """
          fn accept(value: Nat) -> Bool = True()
          fn supply(head: Nat) -> Member(head, sift(accept, Cons(head, empty()))) = Here()
          fn consume(head: Nat, @erased evidence: Member(head, sift(accept, copy_values(Cons(head, empty()))))) -> Nat = S(S(Z()))
          fn run() -> Nat = consume(Z(), split(accept, Z(), supply(Z())))
        end
        """

    path = Path.join(dir, "computed_with_goal.cure")
    File.write!(path, source)
    assert {:ok, env} = Cure.Compiler.check_source(source, file: path, source_roots: [dir])
    assert :ok = Kernel.check_def(env, q(:split))
    module = :"Cure.FilterGoalProbe"

    functions = [
      :empty,
      :here,
      :impossible_member,
      :copy_values,
      :sift,
      :direct,
      :split,
      :accept,
      :supply,
      :consume,
      :run
    ]

    try do
      assert {:ok, forms} = Emit.compile_forms(env, module, functions)
      assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: functions)
      assert apply(module, :run, []) == 2
      exports = for {:attribute, _, :export, entries} <- forms, entry <- entries, do: entry
      assert {:consume, 1} in exports
      refute {:consume, 2} in exports
      assert {:run, 0} in exports
    after
      :code.purge(module)
      :code.delete(module)
    end
  end

  defp q(name), do: String.to_atom("FilterGoalProbe##{name}")
  defp nat, do: {:data, :"Std.Nat#Nat", [], []}
  defp bool, do: {:data, :"Std.Bool#Bool", [], []}
  defp zero, do: {:ctor, :"Std.Nat#Z", []}
  defp variable(name), do: {:variable, [], name}
  defp invoke_ast(name, args), do: {:function_call, [name: name], args}
  defp arm(name, body), do: {:match_arm, [pattern: invoke_ast(name, [])], [body]}
  defp expected(f), do: Eval.eval(f.goal, Context.env(f.ctx))

  defp fixture(env) do
    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(@prefix <> @split <> "end\n", emit_events: false)
    {:ok, ast} = Cure.Compiler.BufferParse.parse(@prefix <> @split <> "end\n", tokens, emit_events: false)
    [declaration] = find_split(ast)
    {:function_def, meta, [{:with_abs, _, [scrutinee | arms]}]} = declaration
    {:ok, env} = Declarations.register_signature(declaration, env)
    definition = Env.get_def(env, q(:split))
    names = for {:param, _, name} <- Keyword.fetch!(meta, :params), do: name

    {ctx, names, goal, domains} =
      Enum.reduce(names, {Context.empty(env), [], definition.type, []}, fn name,
                                                                           {ctx, names, {:pi, grade, domain, body},
                                                                            domains} ->
        {Context.extend(ctx, Eval.eval(domain, Context.env(ctx)), grade), [name | names], body,
         domains ++ [{grade, domain}]}
      end)

    %{
      env: env,
      ctx: ctx,
      names: names,
      goal: goal,
      domains: domains,
      type: definition.type,
      scrutinee: scrutinee,
      arms: arms,
      proof: nil,
      original_params: Keyword.fetch!(meta, :params)
    }
  end

  defp find_split({:function_def, meta, _} = node) do
    if Keyword.get(meta, :name) == "split", do: [node], else: []
  end

  defp find_split(term) when is_tuple(term), do: term |> Tuple.to_list() |> Enum.flat_map(&find_split/1)
  defp find_split(term) when is_list(term), do: Enum.flat_map(term, &find_split/1)
  defp find_split(_), do: []

  defp invoke(f),
    do: Elaborator.elaborate_with(f.scrutinee, f.arms, f.proof, f.goal, f.names, f.ctx, f.env, f.original_params)

  defp original(f), do: with_process(@guard, true, fn -> invoke(f) end)

  defp close(f, term) do
    body = Enum.reduce(Enum.reverse(f.domains), term, fn {grade, domain}, rest -> {:lam, grade, domain, rest} end)
    definition = Env.get_def(f.env, q(:split))
    Env.add_def(f.env, q(:split), f.type, body, definition.quantities, definition.plicities)
  end

  defp replace({:global, name}, name, replacement), do: {:global, replacement}

  defp replace(term, name, replacement) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.map(&replace(&1, name, replacement)) |> List.to_tuple()

  defp replace(term, name, replacement) when is_list(term), do: Enum.map(term, &replace(&1, name, replacement))
  defp replace(term, _, _), do: term

  defp remove_wrapper({:app, {:global, name}, argument}, name), do: argument

  defp remove_wrapper(term, name) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.map(&remove_wrapper(&1, name)) |> List.to_tuple()

  defp remove_wrapper(term, name) when is_list(term), do: Enum.map(term, &remove_wrapper(&1, name))
  defp remove_wrapper(term, _), do: term

  defp payload_frame(f, grade, values) do
    ctx = Context.extend(f.ctx, Eval.eval(nat(), []), grade)
    {:data, _, params, indices} = Term.shift(f.goal, 1, 0)
    evidence = invoke_ast("here", [variable("head"), invoke_ast("empty", [])])
    [_true, false_arm] = f.arms

    %{
      f
      | ctx: ctx,
        names: ["secret" | f.names],
        goal: {:data, q(:Payload), params, indices},
        arms: [arm("True", invoke_ast("PayloadHere", values ++ [evidence])), false_arm]
    }
  end

  defp wrap_goal_arm({:match_arm, meta, [body]}),
    do: {:match_arm, meta, [invoke_ast("GoalHere", [invoke_ast("Z", []), body])]}

  defp replace_nil_branch({:case, scrutinee, motive, branches}, list) do
    {:case, scrutinee, motive,
     Enum.map(branches, fn
       {:"Std.List#Nil", 0, _} -> {:"Std.List#Nil", 0, list}
       {name, arity, body} -> {name, arity, replace_nil_branch(body, list)}
     end)}
  end

  defp replace_nil_branch(term, list) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.map(&replace_nil_branch(&1, list)) |> List.to_tuple()

  defp replace_nil_branch(term, list) when is_list(term), do: Enum.map(term, &replace_nil_branch(&1, list))
  defp replace_nil_branch(term, _), do: term

  defp put_definition(f, name, field, value) do
    env = %{f.env | defs: Map.update!(f.env.defs, q(name), &Map.put(&1, field, value))}
    %{f | env: env, ctx: %{f.ctx | signature: env}}
  end

  defp budgeted(operation),
    do: Normalise.with_fuel(100_000, fn -> {operation.(), Process.get(Normalise.fuel_key())} end)

  defp with_process(key, value, operation) do
    previous = Process.get(key, :absent)
    if value == :absent, do: Process.delete(key), else: Process.put(key, value)

    try do
      operation.()
    after
      if previous == :absent, do: Process.delete(key), else: Process.put(key, previous)
    end
  end

  defp spend_throw_in?(events, function, arity) do
    key = Normalise.fuel_key()

    {_, _, found} =
      Enum.reduce(events, {false, false, false}, fn
        {:trace, _, :call, {Elaborator, ^function, _}}, {_, _, found} ->
          {true, false, found}

        {:trace, _, :exception_from, {Normalise, :spend_fuel, 1}, {:throw, {^key, :exhausted}}}, {true, _, found} ->
          {true, true, found}

        {:trace, _, :exception_from, {Elaborator, ^function, ^arity}, {:throw, {^key, :exhausted}}},
        {true, spent, found} ->
          {false, false, found or spent}

        {:trace, _, :return_from, {Elaborator, ^function, ^arity}, _}, {_, _, found} ->
          {false, false, found}

        _, state ->
          state
      end)

    found
  end

  defp calls(events, name), do: module_calls(events, Elaborator, name)

  defp module_calls(events, module, name),
    do: for({:trace, _, :call, {^module, ^name, arguments}} <- events, do: arguments)

  defp during(events, name, arity) do
    case Enum.find_index(events, &match?({:trace, _, :call, {Elaborator, ^name, _}}, &1)) do
      nil ->
        []

      index ->
        events
        |> Enum.drop(index + 1)
        |> Enum.take_while(fn
          {:trace, _, kind, {Elaborator, ^name, ^arity}, _} when kind in [:return_from, :exception_from] -> false
          _ -> true
        end)
    end
  end

  defp trace(operation, extra \\ []) do
    Code.ensure_loaded!(Elaborator)
    tracer = spawn(fn -> collect([]) end)

    previous =
      Enum.map(@targets ++ extra, fn target ->
        saved = {:erlang.trace_info(target, :traced), :erlang.trace_info(target, :match_spec)}
        :erlang.trace_pattern(target, [{:_, [], [{:exception_trace}]}], [:local])
        {target, saved}
      end)

    try do
      :erlang.trace(self(), true, [:call, {:tracer, tracer}])
      result = operation.()
      :erlang.trace(self(), false, [:call])
      reference = :erlang.trace_delivered(self())

      receive do
        {:trace_delivered, _, ^reference} -> :ok
      after
        5_000 -> flunk("computed-with trace delivery did not complete")
      end

      send(tracer, {:collect, self()})

      receive do
        {:collected, events} -> {result, events}
      after
        5_000 -> flunk("computed-with tracer did not reply")
      end
    after
      :erlang.trace(self(), false, [:call])

      Enum.each(previous, fn
        {target, {{:traced, false}, _}} -> :erlang.trace_pattern(target, false, [:local])
        {target, {{:traced, mode}, {:match_spec, spec}}} -> :erlang.trace_pattern(target, spec, [mode])
      end)

      monitor = Process.monitor(tracer)
      send(tracer, :stop)

      receive do
        {:DOWN, ^monitor, :process, ^tracer, _} -> :ok
      after
        1_000 ->
          Process.exit(tracer, :kill)
          receive do: ({:DOWN, ^monitor, :process, ^tracer, _} -> :ok)
      end
    end
  end

  defp collect(events) do
    receive do
      {:collect, owner} ->
        send(owner, {:collected, Enum.reverse(events)})
        collect([])

      :stop ->
        :ok

      event ->
        collect([event | events])
    end
  end

  defp extensions do
    wrappers =
      for index <- 1..7 do
        prior = if index == 1, do: "copy_values", else: "wrap_#{index - 1}"
        "  fn wrap_#{index}(items: List(Nat)) -> List(Nat) = #{prior}(items)\n"
      end

    IO.iodata_to_binary([
      wrappers,
      """
        type IsTrue indices (flag: Bool)
          Yep : IsTrue(True())
        fn yep() -> IsTrue(True()) = Yep()
        fn flip(flag: Bool) -> Bool = match flag
          True() -> False()
          False() -> True()
        type Payload(head: Nat) indices (items: List(Nat))
          PayloadHere : {items: List(Nat)} -> (left: Nat) -> (right: Nat) -> (evidence: Member(head, items)) -> Payload(head, items)
        type Goal(head: Nat) indices (number: Nat, items: List(Nat))
          GoalHere : {items: List(Nat)} -> (number: Nat) -> (evidence: Member(head, items)) -> Goal(head, number, items)
        type NineGoal(head: Nat) indices (a: Nat, b: Nat, c: Nat, d: Nat, e: Nat, f: Nat, g: Nat, h: Nat, items: List(Nat))
          NineHere : {a: Nat} -> {b: Nat} -> {c: Nat} -> {d: Nat} -> {e: Nat} -> {f: Nat} -> {g: Nat} -> {h: Nat} -> {items: List(Nat)} -> (evidence: Member(head, items)) -> NineGoal(head, a, b, c, d, e, f, g, h, items)
      """
    ])
  end
end

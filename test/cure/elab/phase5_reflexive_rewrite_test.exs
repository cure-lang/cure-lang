defmodule Cure.Elab.Phase5ReflexiveRewriteTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Eval, Kernel, Normalise, Quote, Term, Validator}
  alias Cure.Elab.{Elaborator, Emit, Program, Relevance, Rewrite}

  @prefix """
  mod ReflexiveLegacy
    @reducible
    fn nil_nats() -> List(Nat) = Nil()
    @reducible
    fn nil_bools() -> List(Bool) = Nil()
  """
  @preserve """
    fn preserve(proof: Equivalent(List(Nat), nil_nats(), nil_nats())) -> Equivalent(List(Bool), nil_bools(), nil_bools()) =
      rewrite proof in
        reflexive(nil_bools())
  """
  @trace_targets [
    {Elaborator, :retry_reflexive_legacy_transport, 4},
    {Rewrite, :constant_motive, 2}
  ]

  setup_all do
    # All setup declarations work on the original producer. The intended
    # baseline failure belongs to the preserve assertion, not fixture setup.
    assert {:ok, env} =
             Program.elaborate(
               @prefix <>
                 """
                   typealias BoolGoal = Equivalent(List(Bool), nil_bools(), nil_bools())
                   @reducible
                   fn nil_nat_lists() -> List(List(Nat)) = Nil()
                   @reducible
                   fn one_nat_list() -> List(List(Nat)) = Cons(nil_nats(), Nil())
                   @reducible
                   fn nil_bool_lists() -> List(List(Bool)) = Nil()
                   @reducible
                   fn one_bool_list() -> List(List(Bool)) = Cons(nil_bools(), Nil())
                   type Mark indices (items: List(Bool))
                     Marked : Mark(nil_bools())
                 end
                 """
             )

    proof_type = Rewrite.mk_eq(list(nat()), global(:nil_nats), global(:nil_nats))
    ctx = Context.extend(Context.empty(env), Eval.eval(proof_type, []))
    goal = Rewrite.mk_eq(list(bool()), global(:nil_bools), global(:nil_bools))
    body = invoke("reflexive", [invoke("nil_bools", [])])
    expr = {:rewrite_expr, [], [variable("proof"), body]}
    {:ok, fixture: %{env: env, ctx: ctx, goal: goal, names: ["proof"], body: body, expr: expr}}
  end

  @tag :reflexive_transport_source
  test "typed mixed-carrier Nil rewrite becomes a complete independently checked definition" do
    assert {:ok, env} = Program.elaborate(@prefix <> @preserve <> "end\n")
    assert :ok = Kernel.check_def(env, q(:preserve))

    assert {:ok, ordinary} =
             Program.elaborate(@prefix <> String.replace(@preserve, "rewrite proof in\n", "") <> "end\n")

    assert :ok = Kernel.check_def(ordinary, q(:preserve))
  end

  @tag :reflexive_transport_retained
  test "only final bad_motive retries and exact original proof and checked body survive", %{fixture: f} do
    old = legacy(f)
    assert old.check == {:error, :bad_motive}
    assert old.a == old.b
    assert old.body_goal == old.normalized_goal
    {{:ok, candidate}, events} = trace_operation(fn -> checked(f) end)

    assert [[{:error, :bad_motive}, data, raw_goal, _ctx]] =
             calls(events, Elaborator, :retry_reflexive_legacy_transport)

    assert {old.proof, old.proof_type, old.ty, old.a, old.b, old.normalized_goal, old.body_goal, old.body} == data
    assert raw_goal == f.goal
    motive = constant_motive(old.ty, f.goal)
    expected = {:app, Rewrite.transport_case(old.proof, old.ty, motive, old.a), old.body}
    assert candidate == expected
    assert {:app, {:case, proof, _, _}, body} = candidate
    assert proof == old.proof
    assert body == old.body
    assert :ok = Kernel.check(f.ctx, candidate, Eval.eval(f.goal, Context.env(f.ctx)))
    assert {:ok, _} = Validator.validate(candidate, Validator.release_config(), f.env)
    assert :ok = Relevance.check(f.env, q(:local), Enum.reverse(f.ctx.grades), candidate)
    assert [[ty, ^raw_goal]] = calls(events, Rewrite, :constant_motive)
    assert ty == old.ty
  end

  @tag :reflexive_transport_raw_motive
  test "the constant motive retains the raw goal and delegates carrier grade policy", %{fixture: f} do
    raw = {:global, q(:BoolGoal)}
    old = legacy(%{f | goal: raw})
    assert {:ok, candidate} = checked(%{f | goal: raw})
    motive = constant_motive(old.ty, raw)
    assert {:lam, :unrestricted, _, shifted} = motive
    assert shifted == Term.shift(raw, 1, 0)
    assert candidate == {:app, Rewrite.transport_case(old.proof, old.ty, motive, old.a), old.body}
    assert :ok = Kernel.check(f.ctx, candidate, Eval.eval(raw, Context.env(f.ctx)))
    level_motive = constant_motive({:level_type}, f.goal)
    assert {:lam, :erased, {:level_type}, _} = level_motive
    assert {:ok, _} = Kernel.infer(f.ctx, level_motive)
  end

  @tag :reflexive_transport_working
  test "a working legacy transport returns its exact old Core without the retry", %{fixture: f} do
    numbers = Context.extend(Context.empty(f.env), Eval.eval(nat(), []))
    equality = Rewrite.mk_eq(nat(), {:var, 0}, {:var, 0})
    ctx = Context.extend(numbers, Eval.eval(equality, Context.env(numbers)))
    goal = Rewrite.mk_eq(nat(), {:var, 1}, {:var, 1})
    body = invoke("reflexive", [variable("number")])
    expr = {:rewrite_expr, [], [variable("proof"), body]}
    working = %{f | ctx: ctx, goal: goal, body: body, expr: expr, names: ["proof", "number"]}
    old = legacy(working)
    assert old.check == :ok
    {{:ok, term}, events} = trace_operation(fn -> checked(working) end)
    assert term == old.term
    assert [] = calls(events, Elaborator, :retry_reflexive_legacy_transport)
    assert [] = calls(events, Rewrite, :constant_motive)
  end

  @tag :reflexive_transport_nonreflexive
  test "a non-reflexive hypothesis with a changed body goal preserves the exact old failure", %{fixture: f} do
    carrier = list(list(nat()))
    proof_type = Rewrite.mk_eq(carrier, global(:nil_nat_lists), global(:one_nat_list))
    ctx = Context.extend(Context.empty(f.env), Eval.eval(proof_type, []))
    goal = Rewrite.mk_eq(list(list(bool())), global(:nil_bool_lists), global(:nil_bool_lists))
    body = invoke("reflexive", [invoke("one_bool_list", [])])
    expr = {:rewrite_expr, [], [variable("proof"), body]}
    frame = %{f | ctx: ctx, goal: goal, body: body, expr: expr}
    old = legacy(frame)
    refute old.a == old.b
    refute old.body_goal == old.normalized_goal
    assert old.check == {:error, :bad_motive}
    {result, events} = trace_operation(fn -> checked(frame) end, [{Kernel, :check, 3}])
    assert result == old.check
    assert [_] = calls(events, Elaborator, :retry_reflexive_legacy_transport)
    assert [] = calls(events, Rewrite, :constant_motive)
    assert [] = calls(during_retry(events), Kernel, :check)
    # The equality is a context hypothesis; this tests the elaborator's guard,
    # not a false claim that the kernel rejects inconsistent assumptions.
  end

  @tag :reflexive_transport_other_error
  test "proof-shape and body-elaboration errors pass through without a retry", %{fixture: f} do
    invalid_proof = {:rewrite_expr, [], [invoke("Z", []), f.body]}
    {proof_error, proof_events} = trace_operation(fn -> checked(f, invalid_proof) end)
    assert {:error, {:source_context, :rewrite_proof_not_equality, _}} = proof_error
    assert [] = calls(proof_events, Elaborator, :retry_reflexive_legacy_transport)
    missing = variable("missing_rewrite_body")
    body_goal = legacy(f).body_goal
    expected_error = Elaborator.elaborate_expr_checked(missing, body_goal, f.names, f.ctx, f.env)
    assert {:error, _} = expected_error
    expression = {:rewrite_expr, [], [variable("proof"), missing]}
    {body_error, body_events} = trace_operation(fn -> checked(f, expression) end)
    assert body_error == expected_error
    assert [] = calls(body_events, Elaborator, :retry_reflexive_legacy_transport)
  end

  @tag :reflexive_transport_raw_goal
  test "the raw goal is sorted instead of trusting its beta-normalized replacement", %{fixture: f} do
    malformed = {:app, {:lam, :unrestricted, nat(), Term.shift(f.goal, 1, 0)}, {:ctor, :"Std.Bool#True", []}}
    frame = %{f | goal: malformed}
    assert {:error, _} = Kernel.infer(f.ctx, malformed)
    old = legacy(frame)
    assert old.check == {:error, :bad_motive}
    {result, events} = trace_operation(fn -> checked(frame) end)
    assert result == old.check
    assert [_] = calls(events, Elaborator, :retry_reflexive_legacy_transport)
    assert [] = calls(events, Rewrite, :constant_motive)
  end

  test "wrong proofs bodies and different well-formed raw goals remain rejected", %{fixture: f} do
    old = legacy(f)
    motive = constant_motive(old.ty, f.goal)
    assert {:ok, candidate} = checked(f)
    wrong_body = {:app, Rewrite.transport_case(old.proof, old.ty, motive, old.a), {:nat_lit, 0}}
    assert {:error, _} = Kernel.check(f.ctx, wrong_body, Eval.eval(f.goal, Context.env(f.ctx)))
    wrong_proof = {:app, Rewrite.transport_case({:nat_lit, 0}, old.ty, motive, old.a), old.body}
    assert {:error, _} = Kernel.check(f.ctx, wrong_proof, Eval.eval(f.goal, Context.env(f.ctx)))
    other = Context.extend(f.ctx, Eval.eval(list(bool()), Context.env(f.ctx)))
    goal = Rewrite.mk_eq(list(bool()), global(:nil_bools), {:var, 0})
    assert {:ok, {:vtype, _}} = Kernel.infer(other, goal)
    assert {:error, _} = Kernel.check(other, Term.shift(candidate, 1, 0), Eval.eval(goal, Context.env(other)))
  end

  test "development holes remain release failures and proof holes do not infer", %{fixture: f} do
    old = legacy(f)
    motive = constant_motive(old.ty, f.goal)
    body_hole = {:app, Rewrite.transport_case(old.proof, old.ty, motive, old.a), {:hole, "body-negative"}}
    assert {:error, _} = Validator.validate(body_hole, Validator.release_config(), f.env)
    assert {:error, _} = Kernel.infer(f.ctx, {:hole, "proof-negative"})
    expression = {:rewrite_expr, [], [{:hole, [], "proof-negative"}, f.body]}
    {result, events} = trace_operation(fn -> checked(f, expression) end)
    assert {:error, _} = result
    assert [] = calls(events, Elaborator, :retry_reflexive_legacy_transport)
    # Body-hole rejection above is a RELEASE judgment, not an invented
    # development-kernel prohibition on proof holes in checking position.
  end

  test "the ordinary relevance gate still rejects an erased runtime result", %{fixture: f} do
    goal = {:data, q(:Mark), [], [global(:nil_bools)]}
    values = Context.extend(Context.empty(f.env), Eval.eval(goal, []), :erased)
    proof_type = Rewrite.mk_eq(list(nat()), global(:nil_nats), global(:nil_nats))
    ctx = Context.extend(values, Eval.eval(proof_type, Context.env(values)))
    body = variable("value")
    expression = {:rewrite_expr, [], [variable("proof"), body]}
    frame = %{f | ctx: ctx, goal: goal, body: body, expr: expression, names: ["proof", "value"]}
    assert {:ok, candidate} = checked(frame)
    assert :ok = Kernel.check(ctx, candidate, Eval.eval(goal, Context.env(ctx)))
    assert {:error, _} = Relevance.check(f.env, q(:erased_result), Enum.reverse(ctx.grades), candidate)
  end

  test "directed occurrence ambiguity and transport retain their existing policy", %{fixture: f} do
    old = legacy(f)

    assert {:error, {:ambiguous_occurrence, [_first, _second]}} =
             Rewrite.directed_plan(old.proof, old.ty, old.a, old.b, old.normalized_goal, :backwards)

    assert {:ok, build, _, _} =
             Rewrite.directed_plan(old.proof, old.ty, old.a, old.b, old.normalized_goal, :backwards, 1)

    assert {:error, :bad_motive} = Kernel.check(f.ctx, build.(old.body), Eval.eval(f.goal, Context.env(f.ctx)))
  end

  @tag :reflexive_transport_fuel
  test "shared delta fuel is consumed and exhaustion propagates from inside the retry", %{fixture: f} do
    frame = %{f | goal: {:global, q(:BoolGoal)}}
    fuel_key = Normalise.fuel_key()
    assert Process.get(fuel_key, :absent) == :absent

    assert {:ok, remaining} =
             Normalise.with_fuel(1_024, fn ->
               assert {:ok, _} = checked(frame)
               {:ok, Process.get(fuel_key)}
             end)

    assert remaining > 0 and remaining < 1_024
    assert Process.get(fuel_key, :absent) == :absent

    exhausted =
      for budget <- 1..64, reduce: [] do
        found ->
          {result, events} = trace_operation(fn -> Normalise.with_fuel(budget, fn -> checked(frame) end) end)
          assert Process.get(fuel_key, :absent) == :absent

          propagated? =
            Enum.any?(events, fn
              {:trace, _, :exception_from, {Elaborator, :retry_reflexive_legacy_transport, 4},
               {:throw, {^fuel_key, :exhausted}}} ->
                true

              _ ->
                false
            end)

          if result == :fuel_exhausted and propagated?, do: [budget | found], else: found
      end

    refute exhausted == []
    # This measures the existing delta/iota service and retry ENTRY/exception,
    # not a hard beta-work bound or successful transport completion.
  end

  @tag :tmp_dir
  test "repaired source compiles through normal relevance erasure and Emit", %{tmp_dir: dir} do
    source =
      @prefix <>
        @preserve <>
        """
          fn run() -> Nat = match preserve(reflexive(nil_nats()))
            reflexive() -> S(S(Z()))
        end
        """

    file = Path.join(dir, "reflexive_legacy.cure")
    File.write!(file, source)
    assert {:ok, env} = Cure.Compiler.check_source(source, file: file, source_roots: [dir])
    assert :ok = Kernel.check_def(env, q(:preserve))
    assert :ok = Kernel.check_def(env, q(:run))
    module = :"Cure.ReflexiveLegacy"
    functions = [:nil_nats, :nil_bools, :preserve, :run]

    try do
      assert {:ok, forms} = Emit.compile_forms(env, module, functions)
      assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: functions)
      assert apply(module, :run, []) == 2
      exports = for {:attribute, _, :export, entries} <- forms, entry <- entries, do: entry
      assert {:run, 0} in exports
    after
      :code.purge(module)
      :code.delete(module)
    end
  end

  defp q(name), do: String.to_atom("ReflexiveLegacy##{name}")
  defp global(name), do: {:global, q(name)}
  defp nat, do: {:data, :"Std.Nat#Nat", [], []}
  defp bool, do: {:data, :"Std.Bool#Bool", [], []}
  defp list(type), do: {:data, :"Std.List#List", [{:level_value, Cure.Core.UniverseLevel.zero()}, type], []}
  defp variable(name), do: {:variable, [], name}
  defp invoke(name, args), do: {:function_call, [name: name], args}

  # The genuine baseline lacks this new builder. Dynamic lookup keeps excluded
  # test bodies warning-free there, while every positive call checks its export.
  defp constant_motive(ty, goal) do
    assert function_exported?(Rewrite, :constant_motive, 2)
    apply(Rewrite, :constant_motive, [ty, goal])
  end

  defp checked(f, expression \\ nil),
    do: Elaborator.elaborate_expr_checked(expression || f.expr, f.goal, f.names, f.ctx, f.env)

  defp legacy(f) do
    {:rewrite_expr, _, [proof_ast, body_ast]} = f.expr
    assert {:ok, proof, proof_type} = Elaborator.elaborate_expr_typed(proof_ast, f.names, f.ctx, f.env)
    assert {:ok, ty_value, a_value, b_value} = Rewrite.eq_parts(proof_type, f.env)
    depth = f.ctx.length
    ty = Kernel.normalize(f.ctx, Quote.reify(ty_value, depth))
    a = Kernel.normalize(f.ctx, Quote.reify(a_value, depth))
    b = Kernel.normalize(f.ctx, Quote.reify(b_value, depth))
    normalized_goal = Kernel.normalize(f.ctx, f.goal)
    assert {:ok, build, body_goal} = Rewrite.legacy_plan(proof, ty, a, b, normalized_goal)
    assert {:ok, body} = Elaborator.elaborate_expr_checked(body_ast, body_goal, f.names, f.ctx, f.env)
    term = build.(body)

    %{
      proof: proof,
      proof_type: proof_type,
      ty: ty,
      a: a,
      b: b,
      normalized_goal: normalized_goal,
      body_goal: body_goal,
      body: body,
      term: term,
      check: Kernel.check(f.ctx, term, Eval.eval(f.goal, Context.env(f.ctx)))
    }
  end

  defp calls(events, module, name) do
    for {:trace, _, :call, {^module, ^name, arguments}} <- events, do: arguments
  end

  defp during_retry(events) do
    start =
      Enum.find_index(events, fn
        {:trace, _, :call, {Elaborator, :retry_reflexive_legacy_transport, _}} -> true
        _ -> false
      end)

    assert is_integer(start)

    events
    |> Enum.drop(start + 1)
    |> Enum.take_while(fn
      {:trace, _, kind, {Elaborator, :retry_reflexive_legacy_transport, 4}, _}
      when kind in [:return_from, :exception_from] ->
        false

      _ ->
        true
    end)
  end

  defp trace_operation(operation, extra \\ []) do
    Code.ensure_loaded!(Elaborator)
    Code.ensure_loaded!(Rewrite)
    tracer = spawn(fn -> collect_trace([]) end)

    previous =
      Enum.map(@trace_targets ++ extra, fn target ->
        state = {:erlang.trace_info(target, :traced), :erlang.trace_info(target, :match_spec)}
        :erlang.trace_pattern(target, [{:_, [], [{:exception_trace}]}], [:local])
        {target, state}
      end)

    try do
      :erlang.trace(self(), true, [:call, {:tracer, tracer}])
      result = operation.()
      :erlang.trace(self(), false, [:call])
      delivered = :erlang.trace_delivered(self())

      receive do
        {:trace_delivered, _, ^delivered} -> :ok
      after
        5_000 -> flunk("reflexive transport trace delivery did not complete")
      end

      send(tracer, {:collect, self()})

      receive do
        {:collected, events} -> {result, events}
      after
        5_000 -> flunk("reflexive transport trace collector did not reply")
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

  defp collect_trace(events) do
    receive do
      {:collect, owner} ->
        send(owner, {:collected, Enum.reverse(events)})
        collect_trace([])

      :stop ->
        :ok

      event ->
        collect_trace([event | events])
    end
  end
end

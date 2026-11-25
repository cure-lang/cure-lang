defmodule Cure.Elab.Phase5GoalValueOperandTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Eval, Kernel, Normalise, Term}
  alias Cure.Elab.{Elaborator, Emit, Program}

  @prefix """
  mod GoalValueOperand
    type Switch = On | Off
    type View indices (flag: Switch, tag: Nat, value: Nat)
      Here : {n: Nat} -> View(On(), S(n), n)
    @reducible
    fn view_value(flag: Switch, tag: Nat, value: Nat, view: View(flag, tag, value)) -> Nat = match view
      Here() -> value
    typealias Pack(n: Nat) = Sigma(value: Nat, View(On(), S(n), value))
    @reducible
    fn packed_value(n: Nat, packed: Pack(n)) -> Nat = match packed
      mk_pair(value, view) -> view_value(On(), S(n), value, view)
  """
  @proof """
    fn exact(n: Nat, packed: Pack(n)) -> Equivalent(Nat, packed_value(n, packed), n) = match packed
      mk_pair(value, view) -> match view
        Here() -> reflexive(n)
  """
  @retry_key {Elaborator, :goal_value_operand_retry}
  @trace_functions [
    retry_goal_value_operand_match: 2,
    prepare_goal_value_operand: 4,
    normalize_goal_value_operand: 3
  ]

  setup_all do
    # No repaired theorem is needed to construct the fixture. In particular,
    # disabling the retry must fail the regression assertion, not setup_all.
    assert {:ok, env} = Program.elaborate(@prefix <> extension_source() <> "end\n")
    {domains, _} = peel_pis(Env.get_def(env, q(:packed_value)).type, [])

    ctx =
      Enum.reduce(domains, Context.empty(env), fn {grade, domain}, context ->
        type = domain |> Eval.eval(Context.env(context)) |> Normalise.whnf_value(env)
        Context.extend(context, type, grade)
      end)

    goal = equivalent(nat(), call(q(:packed_value), [{:var, 1}, {:var, 0}]), {:var, 1})
    inner = {:match_arm, [pattern: constructor("Here", [])], [invoke("reflexive", [variable("n")])]}
    body = {:pattern_match, [], [variable("view"), inner]}
    arms = [{:match_arm, [pattern: constructor("mk_pair", [variable("value"), variable("view")])], [body]}]
    {:ok, fixture: %{env: env, ctx: ctx, goal: goal, arms: arms, domains: domains}}
  end

  @tag :goal_value_source
  test "a genuine folded projection failure becomes a complete checked source definition" do
    source = @prefix <> @proof <> "end\n"
    assert length(String.split(source, "\n", trim: true)) == 15
    assert {:error, error} = without_retry(fn -> Program.elaborate(source) end)
    assert Program.semantic_error(error) == :bad_motive
    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, q(:exact))
    wrong = String.replace(source, "reflexive(n)", "reflexive(S(n))")
    assert {:error, _} = Program.elaborate(wrong)
  end

  test "the whole raw goal and original predecessor argument remain authoritative", %{fixture: f} do
    assert {:ok, {:vtype, _}} = Kernel.infer(f.ctx, f.goal)
    assert {:ok, term} = public_match(f)
    assert :ok = Kernel.check(f.ctx, term, Eval.eval(f.goal, Context.env(f.ctx)))
    {env, whole} = close_definition(f, term, f.goal)
    assert :ok = Kernel.check_def(env, q(:checked))
    {:data, family, params, [left, right]} = f.goal
    wrong_goal = {:data, family, params, [left, {:ctor, :"Std.Nat#S", [right]}]}
    assert {:ok, {:vtype, _}} = Kernel.infer(f.ctx, wrong_goal)
    assert {:error, _} = Kernel.check(f.ctx, term, Eval.eval(wrong_goal, Context.env(f.ctx)))
    wrong_argument = {:app, {:app, whole, {:ctor, :"Std.Nat#S", [{:var, 1}]}}, {:var, 0}}
    assert {:error, _} = Kernel.check(f.ctx, wrong_argument, Eval.eval(f.goal, Context.env(f.ctx)))
    {result, events} = trace_operation(fn -> public_match(f, wrong_goal) end)
    assert {:error, _} = result
    assert [_] = calls(events, :normalize_goal_value_operand)
    assert_exact_fallback(events, wrong_goal, f.ctx.length)
  end

  @tag :goal_value_working
  test "already working folded projections keep their exact original Core", %{fixture: f} do
    {:data, family, params, [left, _]} = f.goal
    goal = {:data, family, params, [left, left]}
    proof = invoke("reflexive", [invoke("packed_value", [variable("n"), variable("packed")])])
    [{:match_arm, metadata, [_]}] = f.arms
    arms = [{:match_arm, metadata, [proof]}]
    assert {:ok, original} = without_retry(fn -> public_match(f, goal, arms) end)
    {{:ok, current}, events} = trace_operation(fn -> public_match(f, goal, arms) end)
    assert current == original
    assert :ok = Kernel.check(f.ctx, current, Eval.eval(goal, Context.env(f.ctx)))
    assert [] = calls(events, :prepare_goal_value_operand)
    assert [] = calls(events, :normalize_goal_value_operand)
    assert_exact_fallback(events, goal, f.ctx.length)
  end

  test "absent nil false and active guards restore exactly and nested retries stay suppressed", %{fixture: f} do
    for previous <- [:absent, nil, false] do
      with_guard(previous, fn ->
        {{:ok, term}, events} = trace_operation(fn -> public_match(f) end)
        assert :ok = Kernel.check(f.ctx, term, Eval.eval(f.goal, Context.env(f.ctx)))
        assert [_] = calls(events, :normalize_goal_value_operand)
        assert Process.get(@retry_key, :absent) == previous
      end)
    end

    with_guard(true, fn ->
      {result, events} = trace_operation(fn -> public_match(f) end)
      assert {:error, _} = result
      assert [] = calls(events, :prepare_goal_value_operand)
      assert [] = calls(events, :normalize_goal_value_operand)
      assert_exact_fallback(events, f.goal, f.ctx.length)
      assert Process.get(@retry_key)
    end)
  end

  test "raw malformed annotations cannot be beta-normalized into admission", %{fixture: f} do
    {:data, family, params, [left, right]} = f.goal

    malformed =
      {:data, family, params,
       [{:app, {:lam, :unrestricted, nat(), Term.shift(left, 1, 0)}, {:ctor, q(:On), []}}, right]}

    assert {:error, _} = Kernel.infer(f.ctx, malformed)
    {_result, events} = trace_operation(fn -> public_match(f, malformed) end)
    assert [] = calls(events, :prepare_goal_value_operand)
    assert [] = calls(events, :normalize_goal_value_operand)
    assert_exact_fallback(events, malformed, f.ctx.length)
    assert {:ok, valid_term} = public_match(f)
    {bad_env, _} = close_definition(f, valid_term, malformed)
    assert {:error, _} = Kernel.check_def(bad_env, q(:checked))
  end

  test "typed authored lambda Pi let and case operands refuse before new normalization", %{fixture: f} do
    {:data, family, params, [left, right]} = f.goal

    operands = [
      {:app, {:lam, :unrestricted, nat(), Term.shift(left, 1, 0)}, zero()},
      call(q(:keep_type), [{:pi, :unrestricted, nat(), nat()}, left]),
      {:let, :unrestricted, nat(), left, {:var, 0}},
      {:case, {:var, 1}, {:lam, :unrestricted, nat(), nat()},
       [{:"Std.Nat#Z", 0, left}, {:"Std.Nat#S", 1, Term.shift(left, 1, 0)}]}
    ]

    for operand <- operands do
      goal = {:data, family, params, [operand, right]}
      assert_refused_before_nf(f, goal)
    end
  end

  test "opaque uncertified and open bodies do not license projection normalization", %{fixture: f} do
    root = q(:packed_value)

    variants = [
      Env.put_reducible(f.env, root, false),
      %{f.env | certified: MapSet.delete(f.env.certified, root)},
      %{f.env | defs: Map.update!(f.env.defs, root, &Map.put(&1, :body, {:var, 0}))}
    ]

    # The open-body mutation is solely a refusal assay, never a positive proof
    # or an invented certificate used for admission.
    for env <- variants do
      frame = %{f | env: env, ctx: %{f.ctx | signature: env}}
      assert_refused_before_nf(frame, f.goal)
    end
  end

  @tag :goal_value_cycles
  test "canonical mixed aliases and recursion in erased fields or annotations stay folded", %{fixture: f} do
    n = {:var, 1}
    packed = {:var, 0}
    ghost = {:data, q(:Ghost), [], []}
    end_value = {:ctor, q(:GhostZero), []}
    a = call(:ghost_a_pack, [n, packed, n])
    b = call(q(:ghost_b_pack), [n, packed, n])
    pair = {:data, q(:GhostPair), [], []}
    self = call(:ghost_pack, [n, packed, n])

    for name <- [:ghost_pack, :ghost_a_pack, :ghost_b_pack, :annotation_pack] do
      assert Env.certified?(f.env, q(name))
      assert Term.closed?(Env.get_def(f.env, q(name)).body)
      assert :ok = Kernel.check_def(f.env, q(name))
    end

    goals = [
      equivalent(ghost, self, end_value),
      equivalent(pair, {:ctor, q(:GP), [a, b]}, {:ctor, q(:GP), [end_value, end_value]}),
      equivalent(nat(), call(:annotation_pack, [n, packed, n]), n)
    ]

    for goal <- goals do
      {_result, events} = assert_refused_before_nf(f, goal, acyclic_goal_value_globals: 2)

      assert Enum.any?(events, fn
               {:trace, _, :return_from, {Elaborator, :acyclic_goal_value_globals, 2}, {:ok, allowed}} ->
                 MapSet.size(allowed) == 0

               _ ->
                 false
             end)
    end

    assert_refused_before_nf(f, equivalent(ghost, {:ctor, q(:GhostStep), [self]}, end_value))
  end

  test "safe aliases share canonical eligibility without erasing their spelling correspondence", %{fixture: f} do
    bare = call(:packed_value, [{:var, 1}, {:var, 0}])
    goal = equivalent(nat(), bare, {:var, 1})
    assert Env.resolve_key(f.env, f.env.defs, :packed_value) == q(:packed_value)
    {{:ok, term}, events} = trace_operation(fn -> public_match(f, goal) end)
    assert :ok = Kernel.check(f.ctx, term, Eval.eval(goal, Context.env(f.ctx)))
    [[_ctx, ^bare, allowed]] = calls(events, :normalize_goal_value_operand)
    assert MapSet.member?(allowed, :packed_value)
    assert MapSet.member?(allowed, q(:packed_value))
    assert MapSet.member?(allowed, q(:view_value))
  end

  @tag :goal_value_prefix
  test "licensed full constructor prefixes preserve types and other goal fields", %{fixture: f} do
    {:data, _, _, [left, right]} = f.goal
    alias_type = {:global, q(:nat_carrier)}
    option = {:data, :"Std.Option#Option", [alias_type], []}
    some = fn value -> {:ctor, :"Std.Option#Some", [alias_type, value]} end
    goal = equivalent(option, some.(left), some.(right))
    arms = wrap_reflexive(f.arms, "Some")
    {{:ok, term}, events} = trace_operation(fn -> public_match(f, goal, arms) end)
    assert :ok = Kernel.check(f.ctx, term, Eval.eval(goal, Context.env(f.ctx)))
    [[_ctx, _operand, allowed]] = calls(events, :normalize_goal_value_operand)
    refute MapSet.member?(allowed, q(:nat_carrier))

    assert {:ok, {:data, family, params, [{:ctor, :"Std.Option#Some", [^alias_type, _]}, last]}} =
             returned_value(events, :prepare_goal_value_operand, 4)

    assert {:data, ^family, ^params, [_first, ^last]} = goal

    dependent_type = call(q(:carrier), [{:var, 1}, {:var, 0}])
    list = {:data, :"Std.List#List", [dependent_type], []}
    nil_value = {:ctor, :"Std.List#Nil", [dependent_type]}
    assert_refused_before_nf(f, equivalent(list, nil_value, nil_value))

    fields_only = {:ctor, :"Std.Option#Some", [left]}
    short_goal = equivalent(option, fields_only, {:ctor, :"Std.Option#Some", [right]})
    assert {:ok, {:vtype, _}} = Kernel.infer(f.ctx, short_goal)
    assert {:error, _} = Kernel.infer(f.ctx, fields_only)
    assert_refused_before_nf(f, short_goal)

    # These malformed applications are rejected by the raw Kernel first, not
    # claimed as reachability coverage of the new constructor collector.
    for bad <- [{:ctor, :"Std.Option#Some", []}, {:ctor, :"Std.Option#Some", [alias_type, left, right]}] do
      bad_goal = equivalent(option, bad, some.(right))
      assert {:error, _} = Kernel.infer(f.ctx, bad_goal)
      {_result, rejected} = trace_operation(fn -> public_match(f, bad_goal, arms) end)
      assert [] = calls(rejected, :normalize_goal_value_operand)
    end
  end

  test "root argument root node and operand node bounds retain the exact candidate", %{fixture: f} do
    {:data, _, _, [left, right]} = f.goal
    root9 = {:data, q(:Rel9), [], [left | List.duplicate(right, 8)]}
    large_right = Enum.reduce(1..2_050, right, fn _, term -> {:ctor, :"Std.Nat#S", [term]} end)
    large_left = Enum.reduce(1..260, left, fn _, term -> call(q(:id_0), [term]) end)

    for goal <- [root9, equivalent(nat(), left, large_right), equivalent(nat(), large_left, right)] do
      assert_refused_before_nf(f, goal)
    end
  end

  @tag :goal_value_graph
  test "definition unique-work edge and body bounds refuse through the public pipeline", %{fixture: f} do
    {:data, _, _, [left, right]} = f.goal
    definitions = Enum.reduce(0..16, left, fn i, term -> call(q("id_#{i}"), [term]) end)
    work = Enum.reduce(0..32, left, fn i, term -> call(q("opaque_#{i}"), [term]) end)
    annotation_edges = Enum.reduce(0..8, left, fn i, term -> call(q("annotation_dense_#{i}"), [term]) end)

    for operand <- [
          definitions,
          work,
          call(q(:dense_0), [left]),
          call(q(:huge), [left]),
          call(q(:total_0), [left]),
          annotation_edges
        ] do
      assert_refused_before_nf(f, equivalent(nat(), operand, right))
    end
  end

  @tag :goal_value_order
  test "sixteen eligible definitions plus an opaque tail are independent of work order", %{fixture: f} do
    {:data, _, _, [left, right]} = f.goal
    ids = Enum.map(0..13, &q("id_#{&1}"))
    orders = [ids, Enum.reverse(ids), Enum.drop(ids, 7) ++ Enum.take(ids, 7)]

    results =
      for order <- orders do
        operand = Enum.reduce(order, left, fn name, term -> call(name, [term]) end)
        operand = call(q(:zz_tail), [operand])
        goal = equivalent(nat(), operand, right)
        {{:ok, term}, events} = trace_operation(fn -> public_match(f, goal) end)
        assert :ok = Kernel.check(f.ctx, term, Eval.eval(goal, Context.env(f.ctx)))
        [[_ctx, _operand, allowed]] = calls(events, :normalize_goal_value_operand)
        assert MapSet.size(allowed) == 16
        refute MapSet.member?(allowed, q(:zz_tail))
        {term, allowed}
      end

    [first | _] = results
    assert [^first, ^first, ^first] = results
  end

  @tag :goal_value_growth
  test "output growth is checked after NF without replacing a failed original candidate", %{fixture: f} do
    goal = equivalent(nat(), call(q(:grow), [{:var, 1}, {:var, 0}]), {:var, 1})
    {result, events} = trace_operation(fn -> public_match(f, goal) end)
    assert {:error, _} = result
    assert [_] = calls(events, :normalize_goal_value_operand)
    assert {:refused, false} = returned_value(events, :prepare_goal_value_operand, 4)
    assert_exact_fallback(events, goal, f.ctx.length)
    # This is post-NF admission, not a pre-allocation memory or hard CPU bound.
  end

  @tag :goal_value_fuel
  test "local512 and incoming delta budgets restore without resetting shared work", %{fixture: f} do
    fuel_key = Normalise.fuel_key()
    goal = equivalent(nat(), call(q(:heavy), [{:var, 1}, {:var, 0}]), {:var, 1})
    assert Process.get(fuel_key, :absent) == :absent
    {result, events} = trace_operation(fn -> public_match(f, goal) end)
    assert {:error, _} = result
    assert [_] = calls(events, :normalize_goal_value_operand)
    assert_exact_fallback(events, goal, f.ctx.length)
    assert Process.get(fuel_key, :absent) == :absent

    original_cost =
      Normalise.with_fuel(100_000, fn ->
        assert {:error, _} = without_retry(fn -> public_match(f, goal) end)
        100_000 - Process.get(fuel_key)
      end)

    for extra <- [16, 128, 512] do
      {exhausted, traced} =
        trace_operation(fn ->
          Normalise.with_fuel(original_cost + extra, fn -> public_match(f, goal) end)
        end)

      assert exhausted == :fuel_exhausted
      assert [_] = calls(traced, :normalize_goal_value_operand)
      assert Process.get(fuel_key, :absent) == :absent
    end

    assert {:ok, remaining} =
             Normalise.with_fuel(16_384, fn ->
               assert {:ok, _term} = public_match(f)
               {:ok, Process.get(fuel_key)}
             end)

    assert remaining > 0 and remaining < 16_384
    assert Process.get(fuel_key, :absent) == :absent
  end

  test "computed indexed sibling and non-data scopes never enter the new preparer", %{fixture: f} do
    nat_arms =
      for name <- ["Z", "S"] do
        fields = if name == "S", do: [variable("previous")], else: []
        {:match_arm, [pattern: constructor(name, fields)], [invoke("Z", [])]}
      end

    computed = invoke("keep", [variable("n"), variable("n")])
    non_data = {:pi, :unrestricted, nat(), nat()}

    for {major, goal, arms} <- [
          {computed, f.goal, nat_arms},
          {variable("n"), f.goal, nat_arms},
          {variable("packed"), non_data, f.arms}
        ] do
      {_result, events} = trace_operation(fn -> public_match(f, goal, arms, major) end)
      assert [] = calls(events, :prepare_goal_value_operand)
      assert [] = calls(events, :normalize_goal_value_operand)
      assert_exact_fallback(events, goal, f.ctx.length)
    end

    values = Context.extend(f.ctx, Eval.eval(nat(), Context.env(f.ctx)))
    view = {:data, q(:View), [], [{:ctor, q(:On), []}, {:ctor, :"Std.Nat#S", [{:var, 2}]}, {:var, 0}]}
    indexed = Context.extend(values, Eval.eval(view, Context.env(values)))
    indexed_goal = Term.shift(f.goal, 2, 0)
    arms = [{:match_arm, [pattern: constructor("Here", [])], [invoke("reflexive", [variable("n")])]}]
    assert {:ok, {:vtype, _}} = Kernel.infer(indexed, indexed_goal)

    {_result, events} =
      trace_operation(fn ->
        Elaborator.elaborate_match(
          variable("view"),
          arms,
          indexed_goal,
          ["view", "value", "packed", "n"],
          indexed,
          f.env
        )
      end)

    assert [] = calls(events, :prepare_goal_value_operand)
    assert [] = calls(events, :normalize_goal_value_operand)
    assert_exact_fallback(events, indexed_goal, indexed.length)
  end

  @tag :tmp_dir
  test "a repaired source runs through normal Compiler Relevance and Emit", %{tmp_dir: dir} do
    source =
      @prefix <>
        @proof <>
        """
          fn supplied(n: Nat) -> Pack(n) = %[n, Here()]
          fn consume(n: Nat, packed: Pack(n)) -> Nat = match exact(n, packed)
            reflexive() -> packed_value(n, packed)
          fn runtime_value() -> Nat = consume(S(S(S(Z()))), supplied(S(S(S(Z())))))
        end
        """

    file = Path.join(dir, "goal_value_operand.cure")
    File.write!(file, source)
    assert {:ok, env} = Cure.Compiler.check_source(source, file: file, source_roots: [dir])
    for name <- [:exact, :supplied, :consume, :runtime_value], do: assert(:ok = Kernel.check_def(env, q(name)))
    module = :"Cure.GoalValueOperand"
    functions = [:view_value, :packed_value, :exact, :supplied, :consume, :runtime_value]

    try do
      assert {:ok, forms} = Emit.compile_forms(env, module, functions)
      assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: functions)
      assert apply(module, :runtime_value, []) == 3
      assert {7, {:Here, 7}} = packed = apply(module, :supplied, [7])
      assert apply(module, :consume, [7, packed]) == 7
      exports = for {:attribute, _, :export, entries} <- forms, entry <- entries, do: entry
      assert {:consume, 2} in exports
      assert {:runtime_value, 0} in exports
    after
      :code.purge(module)
      :code.delete(module)
    end
  end

  defp q(name), do: String.to_atom("GoalValueOperand##{name}")
  defp nat, do: {:data, :"Std.Nat#Nat", [], []}
  defp zero, do: {:ctor, :"Std.Nat#Z", []}
  defp variable(name), do: {:variable, [], name}
  defp constructor(name, args), do: {:function_call, [name: name], args}
  defp invoke(name, args), do: constructor(name, args)
  defp call(name, args), do: Enum.reduce(args, {:global, name}, &{:app, &2, &1})
  defp equivalent(type, left, right), do: {:data, :"Std.Equivalent#Equivalent", [type], [left, right]}

  defp public_match(f, goal \\ nil, arms \\ nil, major \\ nil) do
    Elaborator.elaborate_match(
      major || variable("packed"),
      arms || f.arms,
      goal || f.goal,
      ["packed", "n"],
      f.ctx,
      f.env
    )
  end

  defp close_definition(f, term, goal) do
    type = Enum.reduce(Enum.reverse(f.domains), goal, fn {g, d}, body -> {:pi, g, d, body} end)
    body = Enum.reduce(Enum.reverse(f.domains), term, fn {g, d}, body -> {:lam, g, d, body} end)
    {Env.add_def(f.env, q(:checked), type, body), body}
  end

  defp peel_pis({:pi, grade, domain, body}, acc), do: peel_pis(body, acc ++ [{grade, domain}])
  defp peel_pis(body, acc), do: {acc, body}
  defp without_retry(operation), do: with_guard(true, operation)

  defp with_guard(value, operation) do
    previous = Process.get(@retry_key, :absent)
    if value == :absent, do: Process.delete(@retry_key), else: Process.put(@retry_key, value)

    try do
      operation.()
    after
      if previous == :absent, do: Process.delete(@retry_key), else: Process.put(@retry_key, previous)
    end
  end

  defp wrap_reflexive({:function_call, metadata, [argument]}, name) do
    if Keyword.get(metadata, :name) == "reflexive",
      do: {:function_call, metadata, [invoke(name, [argument])]},
      else: {:function_call, metadata, [wrap_reflexive(argument, name)]}
  end

  defp wrap_reflexive(term, name) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.map(&wrap_reflexive(&1, name)) |> List.to_tuple()

  defp wrap_reflexive(terms, name) when is_list(terms), do: Enum.map(terms, &wrap_reflexive(&1, name))
  defp wrap_reflexive(term, _name), do: term

  defp assert_refused_before_nf(f, goal, extra \\ []) do
    assert {:ok, {:vtype, _}} = Kernel.infer(f.ctx, goal)
    {result, events} = trace_operation(fn -> public_match(f, goal) end, extra)
    refute calls(events, :prepare_goal_value_operand) == []
    assert [] = calls(events, :normalize_goal_value_operand)
    assert_exact_fallback(events, goal, f.ctx.length)
    {result, events}
  end

  defp calls(events, name) do
    for {:trace, _, :call, {Elaborator, ^name, arguments}} <- events, do: arguments
  end

  defp returned_value(events, name, arity) do
    Enum.find_value(Enum.reverse(events), fn
      {:trace, _, :return_from, {Elaborator, ^name, ^arity}, result} -> result
      _ -> nil
    end)
  end

  defp assert_exact_fallback(events, goal, depth) do
    {_pending, pairs} =
      Enum.reduce(events, {[], []}, fn event, {pending, pairs} ->
        case event do
          {:trace, _, :call, {Elaborator, :retry_goal_value_operand_match, [candidate, cfg]}} ->
            {[{candidate, cfg} | pending], pairs}

          {:trace, _, :return_from, {Elaborator, :retry_goal_value_operand_match, 2}, result} ->
            [{candidate, cfg} | rest] = pending
            {rest, [{candidate, cfg, result} | pairs]}

          {:trace, _, :exception_from, {Elaborator, :retry_goal_value_operand_match, 2}, _} ->
            {tl(pending), pairs}

          _ ->
            {pending, pairs}
        end
      end)

    matching = Enum.filter(pairs, fn {_, cfg, _} -> cfg.ctx.length == depth and cfg.original_goal == goal end)
    refute matching == []
    assert Enum.all?(matching, fn {candidate, _, result} -> candidate == result end)
  end

  defp trace_operation(operation, extra \\ []) do
    Code.ensure_loaded!(Elaborator)
    tracer = spawn(fn -> collect_trace([]) end)

    previous =
      for {name, arity} <- @trace_functions ++ extra do
        target = {Elaborator, name, arity}
        state = {:erlang.trace_info(target, :traced), :erlang.trace_info(target, :match_spec)}
        :erlang.trace_pattern(target, [{:_, [], [{:exception_trace}]}], [:local])
        {target, state}
      end

    try do
      :erlang.trace(self(), true, [:call, {:tracer, tracer}])
      result = operation.()
      :erlang.trace(self(), false, [:call])
      delivered = :erlang.trace_delivered(self())

      receive do
        {:trace_delivered, _, ^delivered} -> :ok
      after
        5_000 -> flunk("value-operand trace delivery did not complete")
      end

      send(tracer, {:collect, self()})

      receive do
        {:collected, events} -> {result, events}
      after
        5_000 -> flunk("value-operand trace collector did not reply")
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

  defp extension_source do
    ids = for i <- 0..16, do: "  @reducible\n  fn id_#{i}(x: Nat) -> Nat = x\n"
    opaque = for i <- 0..32, do: "  fn opaque_#{i}(x: Nat) -> Nat = x\n"

    dense =
      for i <- 0..8 do
        body = Enum.reduce(8..(i + 1)//-1, "x", fn j, acc -> "dense_#{j}(#{acc})" end)
        "  @reducible\n  fn dense_#{i}(x: Nat) -> Nat = #{body}\n"
      end

    annotation_dense =
      for i <- 0..8 do
        proofs =
          for j <- (i + 1)..8//1 do
            value = "annotation_dense_#{j}(x)"
            "    let proof_#{j}: Equivalent(Nat, #{value}, #{value}) = reflexive(#{value})\n"
          end

        ["  @reducible\n  fn annotation_dense_#{i}(x: Nat) -> Nat =\n", proofs, "    x\n"]
      end

    huge = "  @reducible\n  fn huge(x: Nat) -> Nat = #{nested("S", "x", 4_100)}\n"

    total =
      for i <- 0..4 do
        next = if i == 4, do: "x", else: "total_#{i + 1}(x)"
        "  @reducible\n  fn total_#{i}(x: Nat) -> Nat = keep(#{next}, #{nested("S", "Z()", 3_300)})\n"
      end

    growth =
      Enum.reduce(0..17, "  @reducible\n  fn grow(n: Nat, packed: Pack(n)) -> Nat = match n\n", fn i, acc ->
        indent = String.duplicate("  ", i + 2)
        suffix = if i == 17, do: "packed_value(n, packed)", else: "match k#{i}"
        acc <> "#{indent}Z() -> packed_value(n, packed)\n#{indent}S(k#{i}) -> #{suffix}\n"
      end)

    IO.iodata_to_binary([
      ids,
      opaque,
      dense,
      annotation_dense,
      huge,
      total,
      growth,
      """
        @reducible
        fn keep(x: Nat, unused: Nat) -> Nat = x
        @reducible
        fn keep_type(t: Type, x: Nat) -> Nat = x
        fn zz_tail(x: Nat) -> Nat = x
        @reducible
        fn carrier(n: Nat, packed: Pack(n)) -> Type = Nat
        @reducible
        fn nat_carrier() -> Type = Nat
        type Rel9 indices (a: Nat, b: Nat, c: Nat, d: Nat, e: Nat, f: Nat, g: Nat, h: Nat, i: Nat)
          R9 : Rel9(a, b, c, d, e, f, g, h, i)
        type Ghost indices ()
          GhostZero : Ghost
          GhostStep : (@erased previous: Ghost) -> Ghost
        type GhostPair = GP(Ghost, Ghost)
        @reducible
        fn ghost_pack(n: Nat, packed: Pack(n), count: Nat) -> Ghost = match count
          Z() -> GhostZero()
          S(k) -> GhostStep(ghost_pack(n, packed, k))
        @reducible
        fn ghost_a_pack(n: Nat, packed: Pack(n), count: Nat) -> Ghost = match count
          Z() -> GhostZero()
          S(k) -> GhostStep(ghost_b_pack(n, packed, k))
        @reducible
        fn ghost_b_pack(n: Nat, packed: Pack(n), count: Nat) -> Ghost = match count
          Z() -> GhostZero()
          S(k) -> GhostStep(ghost_a_pack(n, packed, k))
        @reducible
        fn annotation_pack(n: Nat, packed: Pack(n), count: Nat) -> Nat = match count
          Z() -> n
          S(k) ->
            let proof: Equivalent(Nat, annotation_pack(n, packed, k), annotation_pack(n, packed, k)) = reflexive(annotation_pack(n, packed, k))
            n
        @reducible
        fn heavy(n: Nat, packed: Pack(n)) -> Nat = #{nested("id_0", "packed_value(n, packed)", 600)}
      """
    ])
  end

  defp nested(function, value, count),
    do: String.duplicate(function <> "(", count) <> value <> String.duplicate(")", count)
end

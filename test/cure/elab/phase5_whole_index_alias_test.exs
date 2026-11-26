defmodule Cure.Elab.Phase5WholeIndexAliasTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel, Normalise, Term, Validator}
  alias Cure.Elab.{Elaborator, Emit, Program, Relevance}

  @prefix """
  mod WholeIndexAlias
    type Tag = Fixed(Nat) | Other
    @reducible
    fn fixed_tag() -> Tag = Fixed(Z())
    type Witness indices (tag: Tag, flag: Bool)
      Here : {flag: Bool} -> Witness(Fixed(Z()), flag)
    @reducible
    fn project(tag: Tag, flag: Bool, witness: Witness(tag, flag)) -> Nat = match witness
      Here() -> Z()
  """
  @direct """
    fn direct(flag: Bool, witness: Witness(fixed_tag(), flag)) -> Equivalent(Nat, project(fixed_tag(), flag, witness), Z()) = match witness
      Here() -> reflexive(Z())
  """
  @nested """
    fn nested(flag: Bool, witness: Witness(fixed_tag(), flag)) -> Equivalent(Nat, project(fixed_tag(), flag, witness), Z()) = match flag
      True() -> match witness
        Here() -> reflexive(Z())
      False() -> match witness
        Here() -> reflexive(Z())
  """
  @targets [
    {Elaborator, :retry_checked_whole_index_alias, 4},
    {Elaborator, :whole_index_prefix, 3},
    {Elaborator, :whole_index_alias_nf, 5}
  ]

  setup_all do
    # Deliberately omit the nested theorem from setup, so the old-producer
    # sensitivity fails its source assertion rather than fixture construction.
    assert {:ok, env} = Program.elaborate(@prefix <> extensions() <> "end\n")
    {:ok, fixture: fixture(env)}
  end

  @tag :whole_index_source
  test "the genuine seventeen-line nested source closes under the original Kernel" do
    assert {:ok, control} = Program.elaborate(@prefix <> @direct <> "end\n")
    assert :ok = Kernel.check_def(control, q(:direct))
    source = @prefix <> @direct <> @nested <> "end\n"
    assert length(String.split(source, "\n", trim: true)) == 17
    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, q(:direct))
    assert :ok = Kernel.check_def(env, q(:nested))
  end

  @tag :whole_index_case
  test "only the rejected checked wrapper changes the motive, preserving every branch and binder", %{fixture: f} do
    assert {:ok, old} = public_match(f)
    assert {:error, :bad_motive} = Kernel.check_with_branch_details(f.ctx, old, expected(f))

    {{:ok, repaired}, events} =
      trace(fn -> checked(f) end, [
        {Elaborator, :elaborate_match, 6},
        {Elaborator, :elaborate_branch_body, 5},
        {Elaborator, :elaborate_expr_checked, 5}
      ])

    assert [[{:error, :bad_motive}, ^old, raw, _]] = calls(events, Elaborator, :retry_checked_whole_index_alias)
    assert raw == f.goal
    assert {:case, old_major, old_motive, old_branches} = old
    assert {:case, ^old_major, new_motive, ^old_branches} = repaired
    {old_domains, old_body} = peel(old_motive, [])
    {new_domains, new_body} = peel(new_motive, [])
    assert old_domains == new_domains
    assert {:data, family, params, _} = old_body
    assert {:data, ^family, ^params, _} = new_body
    assert {:ok, _} = Kernel.infer(f.ctx, new_motive)
    assert :ok = Kernel.check(f.ctx, repaired, expected(f))
    assert {:ok, _} = Validator.validate(repaired, Validator.release_config(), f.env)
    assert :ok = Relevance.check(f.env, q(:checked_case), Enum.reverse(f.ctx.grades), repaired)
    {env, _} = close(f, repaired)
    assert :ok = Kernel.check_def(env, q(:checked_case))

    for function <- [:elaborate_match, :elaborate_branch_body, :elaborate_expr_checked] do
      assert [] = calls(during(events), Elaborator, function)
    end
  end

  @tag :whole_index_working
  test "working checked matches keep exact Core and the exact old delta-service budget", %{fixture: f} do
    flags = Context.extend(Context.empty(f.env), Eval.eval(bool(), []))
    domain = witness(global(:fixed_tag), {:var, 0})
    ctx = Context.extend(flags, Eval.eval(domain, Context.env(flags)))
    goal = equality(project(global(:fixed_tag), {:var, 1}, {:var, 0}), zero())
    direct = %{f | ctx: ctx, goal: goal, names: ["witness", "flag"]}
    {old, old_remaining} = budgeted(fn -> old_checked(direct) end)
    {{current, new_remaining}, events} = trace(fn -> budgeted(fn -> checked(direct) end) end)
    assert {:ok, term} = current
    assert current == old
    assert old_remaining == new_remaining
    assert :ok = Kernel.check(ctx, term, expected(direct))
    assert [] = calls(events, Elaborator, :retry_checked_whole_index_alias)
    assert [] = calls(events, Elaborator, :whole_index_alias_nf)
  end

  test "other errors remain exactly the old checked result", %{fixture: f} do
    arms = [arm("Here", [], invoke("Other", []))]
    frame = %{f | arms: arms}
    assert {:error, _} = old = old_checked(frame)
    {result, events} = trace(fn -> checked(frame) end)
    assert result == old
    assert [] = calls(events, Elaborator, :retry_checked_whole_index_alias)
    assert [] = calls(events, Elaborator, :whole_index_alias_nf)
  end

  @tag :whole_index_cache
  test "canonical aliases normalize once with only their raw and canonical roots allowed", %{fixture: f} do
    left = project({:global, :fixed_tag}, false_term(), {:var, 0})
    right = project(global(:fixed_tag), false_term(), {:var, 0})
    frame = %{f | goal: equality(left, right)}
    assert Env.resolve_key(f.env, f.env.defs, :fixed_tag) == q(:fixed_tag)
    {{:ok, term}, events} = trace(fn -> checked(frame) end, [{Normalise, :nf, 3}])
    assert :ok = Kernel.check(f.ctx, term, expected(frame))

    nf =
      for {:trace, _, :call, {Normalise, :nf, [_, {:global, name}, options]}} <- during(events),
          name == q(:fixed_tag),
          do: options

    assert [options] = nf
    assert Keyword.fetch!(options, :delta) == :reducible
    assert Keyword.fetch!(options, :delta_allow) == MapSet.new([q(:fixed_tag), :fixed_tag])
    assert Keyword.fetch!(options, :fuel) == 512
    assert Process.get(Normalise.fuel_key(), :absent) == :absent
  end

  test "parameters stay byte-identical while later dependent data indices use prepared values", %{fixture: f} do
    alias_type = global(:SmallNat)
    frame = %{f | goal: equality(project(global(:fixed_tag), false_term(), {:var, 0}), zero(), alias_type)}
    assert {:ok, old} = public_match(frame)
    {{:ok, term}, _} = trace(fn -> checked(frame) end)
    {:case, _, old_motive, old_branches} = old
    {:case, _, new_motive, ^old_branches} = term
    {_, {:data, _, old_params, _}} = peel(old_motive, [])
    {_, {:data, _, new_params, _}} = peel(new_motive, [])
    assert old_params == [{:level_value, Cure.Core.UniverseLevel.zero()}, alias_type]
    assert new_params == old_params
    tag = call(q(:id_tag), [global(:fixed_tag)])
    dependent_goal = {:data, q(:DependentGoal), [], [tag, false_term(), {:var, 0}]}
    dependent = %{f | goal: dependent_goal, arms: [arm("Here", [], invoke("Dependent", []))]}
    assert {:ok, {:vtype, _}} = Kernel.infer(f.ctx, dependent_goal)
    assert {:ok, result} = checked(dependent)
    assert :ok = Kernel.check(f.ctx, result, expected(dependent))
  end

  @tag :whole_index_scope
  test "constructors lambda let and case contents do not enroll alias occurrences", %{fixture: f} do
    alias_term = global(:fixed_tag)
    tag_let = {:let, :unrestricted, tag(), alias_term, {:var, 0}}
    tag_lambda = {:app, {:lam, :unrestricted, nat(), Term.shift(alias_term, 1, 0)}, zero()}

    tag_case =
      {:case, false_term(), {:lam, :unrestricted, bool(), tag()},
       [{:"Std.Bool#True", 0, alias_term}, {:"Std.Bool#False", 0, alias_term}]}

    for value <- [tag_let, tag_lambda, tag_case] do
      frame = %{f | goal: equality(project(value, false_term(), {:var, 0}), zero())}
      assert_rejected(frame, false)
    end

    wrapped = {:ctor, q(:Box), [project(alias_term, false_term(), {:var, 0})]}
    goal = equality(wrapped, {:ctor, q(:Box), [zero()]}, {:data, q(:Boxed), [], []})
    frame = %{f | goal: goal, arms: [arm("Here", [], invoke("reflexive", [invoke("Box", [invoke("Z", [])])]))]}
    assert_rejected(frame, false)
    direct_index = {:data, q(:DirectGoal), [], [alias_term, project(alias_term, false_term(), {:var, 0})]}
    frame = %{f | goal: direct_index, arms: [arm("Here", [], invoke("Direct", []))]}
    assert {:error, :bad_motive} = old_checked(frame)
    assert {:ok, {:case, _, motive, _} = term} = checked(frame)
    {_, {:data, _, _, [^alias_term, _]}} = peel(motive, [])
    assert :ok = Kernel.check(f.ctx, term, expected(frame))
  end

  @tag :whole_index_type_slots
  test "erased and type-valued application slots never grant discovery", %{fixture: f} do
    erased_goal = equality(call(q(:erased_project), [global(:fixed_tag), false_term(), {:var, 0}]), zero())

    {_result, erased_events} =
      assert_rejected(%{f | goal: erased_goal}, false, [{Elaborator, :whole_index_alias_info, 3}])

    assert [] = calls(erased_events, Elaborator, :whole_index_alias_info)

    ctx =
      Context.extend(
        Context.empty(f.env),
        Eval.eval({:data, q(:TypeWitness), [], [nat(), false_term()]}, [])
      )

    type_goal = equality(call(q(:type_project), [global(:SmallNat), false_term(), {:var, 0}]), zero())
    type_frame = %{f | ctx: ctx, goal: type_goal, arms: [arm("TypeHere", [], invoke("reflexive", [invoke("Z", [])]))]}
    {_result, type_events} = assert_rejected(type_frame, false, [{Elaborator, :whole_index_alias_info, 3}])
    assert [] = calls(type_events, Elaborator, :whole_index_alias_info)

    # Surface type parameters may already have quantity zero. This separately
    # well-sorted Pi has a PRESENT Type-valued argument, so the value-slot
    # classification is tested independently of the erased-slot barrier.
    function_type =
      {:pi, :unrestricted, {:type, Cure.Core.Sort.finite_closed(0)},
       {:pi, :unrestricted, bool(), {:pi, :unrestricted, {:data, q(:TypeWitness), [], [{:var, 1}, {:var, 0}]}, tag()}}}

    assert {:ok, {:vtype, _}} = Kernel.infer(Context.empty(f.env), function_type)
    functions = Context.extend(Context.empty(f.env), Eval.eval(function_type, []))
    present_ctx = Context.extend(functions, Eval.eval({:data, q(:TypeWitness), [], [nat(), false_term()]}, []))
    application = call_term({:var, 1}, [global(:SmallNat), false_term(), {:var, 0}])
    present_goal = equality(application, application, tag())
    branch_value = invoke("function", [variable("SmallNat"), invoke("False", []), invoke("TypeHere", [])])

    present_frame = %{
      f
      | ctx: present_ctx,
        goal: present_goal,
        names: ["witness", "function"],
        arms: [arm("TypeHere", [], invoke("reflexive", [branch_value]))]
    }

    {_result, present_events} =
      assert_rejected(present_frame, false, [{Elaborator, :whole_index_alias_info, 3}])

    assert [] = calls(present_events, Elaborator, :whole_index_alias_info)
  end

  @tag :whole_index_eligibility
  test "unpublished computed and binder-bodied aliases remain outside the initial class", %{fixture: f} do
    for name <- [:opaque_tag, :app_tag, :let_tag] do
      goal = equality(project(global(name), false_term(), {:var, 0}), zero())
      assert_rejected(%{f | goal: goal}, false)
    end

    root = q(:fixed_tag)
    uncertified = %{f.env | certified: MapSet.delete(f.env.certified, root)}
    frame = %{f | env: uncertified, ctx: %{f.ctx | signature: uncertified}}
    assert {:error, _} = Kernel.infer(frame.ctx, frame.goal)
    {_result, events} = trace(fn -> checked(frame) end)
    assert [] = calls(events, Elaborator, :whole_index_alias_nf)
    assert [] = calls(events, Elaborator, :whole_index_prefix)
    # Here certification is needed by the raw goal's conversion already:
    # do not claim that this reaches the later alias-body eligibility guard.
  end

  test "Context.signature alone supplies alias metadata, not the elaborator environment", %{fixture: f} do
    altered = %{f.env | defs: Map.update!(f.env.defs, q(:fixed_tag), &Map.put(&1, :reducible, false))}
    assert {:ok, term} = checked(%{f | env: altered})
    assert :ok = Kernel.check(f.ctx, term, expected(f))
  end

  @tag :whole_index_nil
  test "identical Nil syntax at different carriers never licenses an index substitution", %{fixture: f} do
    nil_term = {:ctor, :"Std.List#Nil", []}
    domain = {:data, q(:ListWitness), [], [nil_term, false_term()]}
    ctx = Context.extend(Context.empty(f.env), Eval.eval(domain, []))

    value =
      call(q(:ignore_list), [
        global(:nil_bools),
        call(q(:list_project), [nil_term, false_term(), {:var, 0}])
      ])

    frame = %{
      f
      | ctx: ctx,
        goal: equality(value, zero()),
        arms: [arm("ListHere", [], invoke("reflexive", [invoke("Z", [])]))]
    }

    assert {:error, _} =
             Kernel.check(
               ctx,
               global(:nil_bools),
               Eval.eval({:data, :"Std.List#List", [{:level_value, Cure.Core.UniverseLevel.zero()}, nat()], []}, [])
             )

    assert_rejected(frame, false)
  end

  test "uncertified and open metadata cannot enroll an otherwise ignored value argument", %{fixture: f} do
    name = q(:alias_0)
    value = call(q(:take_tag), [project(global(:fixed_tag), false_term(), {:var, 0}), global(:alias_0)])

    for env <- [
          %{f.env | certified: MapSet.delete(f.env.certified, name)},
          %{f.env | defs: Map.update!(f.env.defs, name, &Map.put(&1, :body, {:ctor, q(:Fixed), [{:var, 0}]}))}
        ] do
      frame = %{f | env: env, ctx: %{f.ctx | signature: env}, goal: equality(value, zero())}
      assert {:ok, {:vtype, _}} = Kernel.infer(frame.ctx, frame.goal)
      {_result, events} = trace(fn -> checked(frame) end)
      refute Enum.any?(calls(events, Elaborator, :whole_index_alias_nf), fn [canonical | _] -> canonical == name end)
    end

    # The open-body mutation only assays refusal to unfold it. No positive
    # proof or certificate is manufactured from that mutated body.
  end

  @tag :whole_index_metadata
  test "malformed Pi grades and constructor bodies refuse without a new exception or partial result", %{fixture: f} do
    project = Map.fetch!(f.env.defs, q(:project))
    {:pi, _, domain, result} = project.type
    env = %{f.env | defs: Map.put(f.env.defs, q(:project), %{project | type: {:pi, :invalid, domain, result}})}
    frame = %{f | env: env, ctx: %{f.ctx | signature: env}}
    assert_rejected(frame, false)

    env = %{f.env | defs: Map.update!(f.env.defs, q(:alias_0), &Map.put(&1, :body, {:ctor, q(:Fixed), []}))}
    value = call(q(:take_tag), [project(global(:fixed_tag), false_term(), {:var, 0}), global(:alias_0)])
    frame = %{f | env: env, ctx: %{f.ctx | signature: env}, goal: equality(value, zero())}
    {_result, events} = assert_rejected(frame, true)
    assert [_partial_preparation] = calls(events, Elaborator, :whole_index_alias_nf)

    ctor = Map.fetch!(f.env.ctors, q(:Other))

    env = %{
      f.env
      | ctors: Map.put(f.env.ctors, q(:Other), %{ctor | quantities: [:erased]}),
        defs: Map.update!(f.env.defs, q(:alias_0), &Map.put(&1, :body, other()))
    }

    frame = %{f | env: env, ctx: %{f.ctx | signature: env}, goal: equality(value, zero())}
    assert :ok = Kernel.check(frame.ctx, other(), Eval.eval(tag(), []))
    {_result, events} = assert_rejected(frame, true)
    assert [_only_the_valid_alias] = calls(events, Elaborator, :whole_index_alias_nf)
  end

  @tag :whole_index_entry
  test "nine-index and computed-major cases remain outside the checked plain-variable class", %{fixture: f} do
    flags = Enum.reduce(1..8, Context.empty(f.env), fn _, ctx -> Context.extend(ctx, Eval.eval(bool(), [])) end)
    arguments = for i <- 7..0//-1, do: {:var, i}
    domain = {:data, q(:ManyWitness), [], [fixed() | arguments]}
    ctx = Context.extend(flags, Eval.eval(domain, Context.env(flags)))
    values = for i <- 8..1//-1, do: {:var, i}
    value = call(q(:many_project), [global(:fixed_tag) | values] ++ [{:var, 0}])

    frame = %{
      f
      | ctx: ctx,
        goal: equality(value, zero()),
        names: ["witness" | Enum.map(0..7, &"flag_#{&1}")],
        arms: [arm("ManyHere", [], invoke("reflexive", [invoke("Z", [])]))]
    }

    assert_rejected(frame, false)

    major = invoke("id_witness", [invoke("Fixed", [invoke("Z", [])]), invoke("False", []), variable("witness")])
    term = call(q(:id_witness), [fixed(), false_term(), {:var, 0}])
    goal = equality(project(global(:fixed_tag), false_term(), term), zero())
    assert {:ok, {:vtype, _}} = Kernel.infer(f.ctx, goal)

    {result, events} =
      trace(fn ->
        Elaborator.elaborate_expr_checked({:pattern_match, [], [major | f.arms]}, goal, f.names, f.ctx, f.env)
      end)

    assert {:error, :bad_motive} = result
    assert [] = calls(events, Elaborator, :whole_index_alias_nf)
  end

  @tag :whole_index_prefix
  test "a malformed authoritative raw domain is rejected before fresh-context evaluation or NF", %{fixture: f} do
    family = Map.fetch!(f.env.families, q(:Witness))
    [{name, _old} | tail] = family.indices
    malformed = {:app, {:lam, :unrestricted, nat(), tag()}, false_term()}
    env = %{f.env | families: Map.put(f.env.families, q(:Witness), %{family | indices: [{name, malformed} | tail]})}
    frame = %{f | env: env, ctx: %{f.ctx | signature: env}}
    assert {:error, _} = Kernel.infer(frame.ctx, malformed)
    {_result, events} = assert_rejected(frame, false)
    assert [_first_raw_domain] = calls(events, Elaborator, :whole_index_prefix)
  end

  @tag :whole_index_ambiguity
  test "multiple typed matching indices refuse the whole attempt", %{fixture: f} do
    domain = {:data, q(:PairWitness), [], [fixed(), fixed()]}
    ctx = Context.extend(Context.empty(f.env), Eval.eval(domain, []))
    value = call(q(:pair_project), [global(:fixed_tag), global(:fixed_tag), {:var, 0}])

    frame = %{
      f
      | ctx: ctx,
        goal: equality(value, zero()),
        arms: [arm("PairHere", [], invoke("reflexive", [invoke("Z", [])]))]
    }

    {_result, events} = assert_rejected(frame, true)
    assert [_first_ambiguous_alias] = calls(events, Elaborator, :whole_index_alias_nf)
  end

  @tag :whole_index_bounds
  test "global and eligible bounds reject transactionally rather than returning a prepared prefix", %{fixture: f} do
    value = project(global(:fixed_tag), false_term(), {:var, 0})
    opaque = for i <- 0..32, do: global("opaque_#{i}")
    eligible = for i <- 0..15, do: global("alias_#{i}")

    for arguments <- [opaque, eligible ++ List.duplicate(other(), 17)] do
      goal = equality(call(q(:take_many), [value | arguments]), zero())
      assert_rejected(%{f | goal: goal}, true)
    end

    repeated = List.duplicate(global(:opaque_0), 33)
    goal = equality(call(q(:take_many), [value | repeated]), zero())
    assert {:ok, term} = checked(%{f | goal: goal})
    assert :ok = Kernel.check(f.ctx, term, Eval.eval(goal, Context.env(f.ctx)))

    boundary =
      for(i <- 0..14, do: global("alias_#{i}")) ++
        [global(:opaque_32)] ++ List.duplicate(other(), 17)

    goal = equality(call(q(:take_many), [value | boundary]), zero())
    assert {:ok, result} = checked(%{f | goal: goal})
    assert :ok = Kernel.check(f.ctx, result, Eval.eval(goal, Context.env(f.ctx)))
  end

  @tag :whole_index_bodies
  test "closed constructor body and target node limits are independent", %{fixture: f} do
    value = project(global(:fixed_tag), false_term(), {:var, 0})
    oversized = equality(call(q(:take_tag), [value, global(:deep_63)]), zero())
    assert_rejected(%{f | goal: oversized}, true)
    boundary = equality(call(q(:take_tag), [value, global(:deep_62)]), zero())
    assert {:ok, boundary_term} = checked(%{f | goal: boundary})
    assert :ok = Kernel.check(f.ctx, boundary_term, Eval.eval(boundary, Context.env(f.ctx)))
    domain = {:data, q(:AnyWitness), [], [deep(63), false_term()]}
    ctx = Context.extend(Context.empty(f.env), Eval.eval(domain, []))
    goal = equality(call(q(:any_project), [global(:deep_63), false_term(), {:var, 0}]), zero())

    frame = %{
      f
      | ctx: ctx,
        goal: goal,
        arms: [arm("AnyHere", [variable("number")], invoke("reflexive", [invoke("Z", [])]))]
    }

    {_result, events} = assert_rejected(frame, false, [{Elaborator, :whole_index_alias_info, 3}])
    assert [] = calls(events, Elaborator, :whole_index_alias_info)
  end

  @tag :whole_index_body_size
  test "large data bodies refuse before normalization", %{fixture: f} do
    large = Enum.reduce(1..4_100, zero(), fn _, term -> {:ctor, :"Std.Nat#S", [term]} end)
    value = call(q(:keep_nat), [large, project(global(:fixed_tag), false_term(), {:var, 0})])
    assert_rejected(%{f | goal: equality(value, zero())}, false)
  end

  @tag :whole_index_raw_goal
  test "raw malformed goals are not repaired by normalizing their annotations", %{fixture: f} do
    bad_value =
      {:app, {:lam, :unrestricted, nat(), Term.shift(project(global(:fixed_tag), false_term(), {:var, 0}), 1, 0)},
       false_term()}

    frame = %{f | goal: equality(bad_value, zero())}
    assert {:error, _} = Kernel.infer(f.ctx, frame.goal)
    {_result, events} = trace(fn -> checked(frame) end)
    assert [] = calls(events, Elaborator, :whole_index_alias_nf)
    assert [] = calls(events, Elaborator, :whole_index_prefix)
  end

  @tag :whole_index_target_license
  test "target licenses reject malformed metadata before NF while partial spines fail raw typing", %{fixture: f} do
    ctor = Map.fetch!(f.env.ctors, q(:Fixed))
    env = %{f.env | ctors: Map.put(f.env.ctors, q(:Fixed), %{ctor | quantities: [:invalid]})}
    frame = %{f | env: env, ctx: %{f.ctx | signature: env}}
    assert :ok = Kernel.check(frame.ctx, fixed(), Eval.eval(tag(), []))
    {_result, events} = assert_rejected(frame, false, [{Elaborator, :whole_index_alias_info, 3}])
    assert [] = calls(events, Elaborator, :whole_index_alias_info)

    target = {:ctor, q(:IndexedCtor), [zero()]}
    target_type = {:data, q(:Indexed), [], [{:ctor, :"Std.Nat#S", [zero()]}]}
    assert {:error, :ctor_arity} = Kernel.check(Context.empty(f.env), target, Eval.eval(target_type, []))
    assert Inductive.ctor_application_quantities(f.env, q(:IndexedCtor), 1) == nil
    # The actual Kernel refuses this omitted-field spelling first. It is not
    # claimed as reachability of the new target guard above.
  end

  test "wrong well-formed goals and branches cannot bypass the final original-goal check", %{fixture: f} do
    assert {:ok, term} = checked(f)
    wrong = %{f | goal: equality(project(global(:fixed_tag), false_term(), {:var, 0}), {:ctor, :"Std.Nat#S", [zero()]})}
    assert {:ok, {:vtype, _}} = Kernel.infer(f.ctx, wrong.goal)
    assert {:error, _} = Kernel.check(f.ctx, term, expected(wrong))
    assert {:error, _} = checked(wrong)
    bad = %{f | arms: [arm("Here", [], invoke("reflexive", [invoke("S", [invoke("Z", [])])]))]}
    assert {:error, _} = checked(bad)
  end

  @tag :whole_index_fuel
  test "root-only NF inherits finite fuel including exhaustion and restores absent local state", %{fixture: f} do
    key = Normalise.fuel_key()
    assert Process.get(key, :absent) == :absent
    {{:ok, _}, events} = trace(fn -> checked(f) end, [{Normalise, :nf, 3}])
    assert Process.get(key, :absent) == :absent

    assert Enum.any?(during(events), fn
             {:trace, _, :call, {Normalise, :nf, [_, {:global, name}, options]}} ->
               name == q(:fixed_tag) and Keyword.get(options, :fuel) == 512

             _ ->
               false
           end)

    assert {:ok, remaining} =
             Normalise.with_fuel(1_024, fn ->
               assert {:ok, _} = checked(f)
               {:ok, Process.get(key)}
             end)

    assert remaining > 0 and remaining < 1_024

    exhausted =
      for budget <- 1..96, reduce: [] do
        found ->
          {result, traced} = trace(fn -> Normalise.with_fuel(budget, fn -> checked(f) end) end)

          propagated =
            Enum.any?(traced, fn
              {:trace, _, :exception_from, {Elaborator, :whole_index_alias_nf, 5}, {:throw, {^key, :exhausted}}} -> true
              _ -> false
            end)

          assert Process.get(key, :absent) == :absent
          if result == :fuel_exhausted and propagated, do: [budget | found], else: found
      end

    refute exhausted == []
    # Fixed(Z) needs one root delta step. This proves incoming exhaustion at
    # the NF service, not a beta/CPU bound or completed normalization.
  end

  @tag :tmp_dir
  test "the repaired nested source executes through normal Compiler relevance and Emit", %{tmp_dir: dir} do
    source =
      @prefix <>
        @direct <>
        @nested <>
        """
          fn supply(flag: Bool) -> Witness(fixed_tag(), flag) = Here()
          fn run() -> Nat = match nested(False(), supply(False()))
            reflexive() -> S(S(Z()))
        end
        """

    path = Path.join(dir, "whole_index_alias.cure")
    File.write!(path, source)
    assert {:ok, env} = Cure.Compiler.check_source(source, file: path, source_roots: [dir])
    assert :ok = Kernel.check_def(env, q(:nested))
    module = :"Cure.WholeIndexAlias"
    functions = [:fixed_tag, :project, :direct, :nested, :supply, :run]

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

  defp q(name), do: String.to_atom("WholeIndexAlias##{name}")
  defp global(name), do: {:global, q(name)}
  defp nat, do: {:data, :"Std.Nat#Nat", [], []}
  defp bool, do: {:data, :"Std.Bool#Bool", [], []}
  defp tag, do: {:data, q(:Tag), [], []}
  defp zero, do: {:ctor, :"Std.Nat#Z", []}
  defp false_term, do: {:ctor, :"Std.Bool#False", []}
  defp fixed, do: {:ctor, q(:Fixed), [zero()]}
  defp other, do: {:ctor, q(:Other), []}
  defp deep(count), do: {:ctor, q(:Fixed), [Enum.reduce(1..count, zero(), fn _, t -> {:ctor, :"Std.Nat#S", [t]} end)]}
  defp witness(value, flag), do: {:data, q(:Witness), [], [value, flag]}
  defp call(name, args), do: Enum.reduce(args, {:global, name}, &{:app, &2, &1})
  defp call_term(function, args), do: Enum.reduce(args, function, &{:app, &2, &1})
  defp project(value, flag, proof), do: call(q(:project), [value, flag, proof])

  defp equality(left, right, type \\ nat()),
    do: {:data, :"Std.Equivalent#Equivalent", [{:level_value, Cure.Core.UniverseLevel.zero()}, type], [left, right]}

  defp variable(name), do: {:variable, [], name}
  defp invoke(name, args), do: {:function_call, [name: name], args}
  defp arm(name, args, body), do: {:match_arm, [pattern: invoke(name, args)], [body]}

  defp fixture(env) do
    domain = witness(fixed(), false_term())
    ctx = Context.extend(Context.empty(env), Eval.eval(domain, []))

    %{
      env: env,
      ctx: ctx,
      domain: domain,
      names: ["witness"],
      goal: equality(project(global(:fixed_tag), false_term(), {:var, 0}), zero()),
      arms: [arm("Here", [], invoke("reflexive", [invoke("Z", [])]))]
    }
  end

  defp public_match(f),
    do: Elaborator.elaborate_match(variable("witness"), f.arms, f.goal, f.names, f.ctx, f.env)

  defp checked(f),
    do:
      Elaborator.elaborate_expr_checked(
        {:pattern_match, [], [variable("witness") | f.arms]},
        f.goal,
        f.names,
        f.ctx,
        f.env
      )

  defp expected(f), do: Eval.eval(f.goal, Context.env(f.ctx))

  defp old_checked(f) do
    case public_match(f) do
      {:ok, term} ->
        case Kernel.check_with_branch_details(f.ctx, term, expected(f)) do
          :ok -> {:ok, term}
          error -> error
        end

      error ->
        error
    end
  end

  defp close(f, term) do
    type = {:pi, :unrestricted, f.domain, f.goal}
    body = {:lam, :unrestricted, f.domain, term}
    {Env.add_def(f.env, q(:checked_case), type, body), body}
  end

  defp peel({:lam, grade, domain, body}, acc), do: peel(body, acc ++ [{grade, domain}])
  defp peel(body, acc), do: {acc, body}

  defp budgeted(operation) do
    Normalise.with_fuel(100_000, fn -> {operation.(), Process.get(Normalise.fuel_key())} end)
  end

  defp assert_rejected(f, nf?, extra \\ []) do
    assert {:ok, {:vtype, _}} = Kernel.infer(f.ctx, f.goal)
    assert {:error, :bad_motive} = old_checked(f)
    {result, events} = trace(fn -> checked(f) end, extra)
    assert result == {:error, :bad_motive}
    assert [_] = calls(events, Elaborator, :retry_checked_whole_index_alias)
    normalizations = calls(events, Elaborator, :whole_index_alias_nf)
    if nf?, do: refute(normalizations == []), else: assert(normalizations == [])
    {result, events}
  end

  defp calls(events, module, name),
    do: for({:trace, _, :call, {^module, ^name, args}} <- events, do: args)

  defp during(events) do
    index =
      Enum.find_index(events, fn
        {:trace, _, :call, {Elaborator, :retry_checked_whole_index_alias, _}} -> true
        _ -> false
      end)

    assert is_integer(index)

    events
    |> Enum.drop(index + 1)
    |> Enum.take_while(fn
      {:trace, _, kind, {Elaborator, :retry_checked_whole_index_alias, 4}, _}
      when kind in [:return_from, :exception_from] ->
        false

      _ ->
        true
    end)
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
      ref = :erlang.trace_delivered(self())

      receive do
        {:trace_delivered, _, ^ref} -> :ok
      after
        5_000 -> flunk("whole-index alias trace delivery did not complete")
      end

      send(tracer, {:collect, self()})

      receive do
        {:collected, events} -> {result, events}
      after
        5_000 -> flunk("whole-index alias collector did not reply")
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
    aliases = for i <- 0..15, do: "  @reducible\n  fn alias_#{i}() -> Tag = Fixed(Z())\n"
    opaque = for i <- 0..32, do: "  fn opaque_#{i}() -> Tag = Fixed(Z())\n"
    params = Enum.map_join(0..32, ", ", &"tag_#{&1}: Tag")
    flags = Enum.map_join(0..7, ", ", &"flag_#{&1}: Bool")
    flag_names = Enum.map_join(0..7, ", ", &"flag_#{&1}")
    hidden_flags = Enum.map_join(0..7, " -> ", &"{flag_#{&1}: Bool}")

    IO.iodata_to_binary([
      aliases,
      opaque,
      """
        typealias SmallNat = Nat
        type Boxed = Box(Nat)
        @reducible
        fn id_tag(value: Tag) -> Tag = value
        fn take_tag(value: Nat, ignored: Tag) -> Nat = value
        fn take_many(value: Nat, #{params}) -> Nat = value
        fn keep_nat(ignored: Nat, value: Nat) -> Nat = value
        fn id_witness(tag: Tag, flag: Bool, value: Witness(tag, flag)) -> Witness(tag, flag) = value
        fn opaque_tag() -> Tag = Fixed(Z())
        @reducible
        fn app_tag() -> Tag = id_tag(fixed_tag())
        @reducible
        fn let_tag() -> Tag =
          let value = fixed_tag()
          value
        @reducible
        fn deep_62() -> Tag = #{nested_nat(62)}
        @reducible
        fn deep_63() -> Tag = #{nested_nat(63)}
        type PairWitness indices (left: Tag, right: Tag)
          PairHere : PairWitness(Fixed(Z()), Fixed(Z()))
        fn pair_project(left: Tag, right: Tag, proof: PairWitness(left, right)) -> Nat = match proof
          PairHere() -> Z()
        type DependentGoal indices (tag: Tag, flag: Bool, proof: Witness(tag, flag))
          Dependent : {tag: Tag} -> {flag: Bool} -> {proof: Witness(tag, flag)} -> DependentGoal(tag, flag, proof)
        type DirectGoal indices (tag: Tag, value: Nat)
          Direct : {tag: Tag} -> DirectGoal(tag, Z())
        fn erased_project(@erased tag: Tag, flag: Bool, proof: Witness(tag, flag)) -> Nat = match proof
          Here() -> Z()
        type TypeWitness indices (carrier: Type, flag: Bool)
          TypeHere : {flag: Bool} -> TypeWitness(Nat, flag)
        fn type_project(carrier: Type, flag: Bool, proof: TypeWitness(carrier, flag)) -> Nat = match proof
          TypeHere() -> Z()
        type AnyWitness indices (tag: Tag, flag: Bool)
          AnyHere : {flag: Bool} -> (number: Nat) -> AnyWitness(Fixed(number), flag)
        fn any_project(tag: Tag, flag: Bool, proof: AnyWitness(tag, flag)) -> Nat = match proof
          AnyHere(number) -> Z()
        type Indexed indices (n: Nat)
          IndexedCtor : (value: Nat) -> Indexed(n)
        @reducible
        fn indexed_one() -> Indexed(S(Z())) = IndexedCtor(Z())
        type IndexedWitness indices (value: Indexed(S(Z())), flag: Bool)
          IndexedHere : {flag: Bool} -> IndexedWitness(IndexedCtor(Z()), flag)
        fn indexed_project(value: Indexed(S(Z())), flag: Bool, proof: IndexedWitness(value, flag)) -> Nat = match proof
          IndexedHere() -> Z()
        @reducible
        fn nil_bools() -> List(Bool) = Nil()
        type ListWitness indices (items: List(Nat), flag: Bool)
          ListHere : {flag: Bool} -> ListWitness(Nil(), flag)
        fn list_project(items: List(Nat), flag: Bool, value: ListWitness(items, flag)) -> Nat = match value
          ListHere() -> Z()
        fn ignore_list(ignored: List(Bool), value: Nat) -> Nat = value
        type ManyWitness indices (tag: Tag, #{flags})
          ManyHere : #{hidden_flags} -> ManyWitness(Fixed(Z()), #{flag_names})
        fn many_project(tag: Tag, #{flags}, value: ManyWitness(tag, #{flag_names})) -> Nat = match value
          ManyHere() -> Z()
      """
    ])
  end

  defp nested_nat(count),
    do: "Fixed(" <> String.duplicate("S(", count) <> "Z()" <> String.duplicate(")", count) <> ")"
end

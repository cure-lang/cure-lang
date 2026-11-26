defmodule Cure.Elab.Phase5FixedIndexMotiveTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel, Normalise, Sort, Term, UniverseLevel}
  alias Cure.Elab.{Elaborator, Program, Relevance}

  @tag_source """
  mod Std.Bounded
    type Tag = Zero | One
    type Payload indices (tag: Tag)
      PZero : Payload(Zero())
      POne : Payload(One())
    type AtZero indices (value: Payload(Zero()))
      ViewZero : AtZero(PZero())
    fn exact(value: Payload(Zero())) -> AtZero(value) = match value
      PZero() -> ViewZero()
  end
  """

  @tag :variable_constant_motive
  test "a variable major can retain its original phantom uniform result parameter" do
    source = """
    mod PhantomFixedMajor
      type Tag = Zero | One
      type Payload indices (tag: Tag)
        PZero : Payload(Zero())
        POne : Payload(One())
      type Output(value: Payload(Zero())) indices ()
        MkOutput : Nat -> Output(value)
      fn inspect(value: Payload(Zero())) -> Output(value) = match value
        PZero() -> MkOutput(Z())
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"PhantomFixedMajor#inspect")

    assert %{body: {:lam, _, payload, {:case, scrutinee, motive, branches} = term}} =
             Env.get_def(env, :"PhantomFixedMajor#inspect")

    assert {:lam, grade, tag, {:lam, major_grade, major_type, {:data, output, [{:var, 2}], []}}} = motive
    ctx = Context.extend(Context.empty(env), Eval.eval(payload, []))
    goal = {:data, output, [{:var, 0}], []}
    assert :ok = Kernel.check(ctx, term, Eval.eval(goal, Context.env(ctx)))

    naive = {:lam, grade, tag, {:lam, major_grade, major_type, {:data, output, [{:var, 0}], []}}}

    assert {:error, :bad_motive} =
             Kernel.check(ctx, {:case, scrutinee, naive, branches}, Eval.eval(goal, Context.env(ctx)))

    other_ctx = Context.extend(ctx, Eval.eval(payload, Context.env(ctx)))
    other_goal = {:data, output, [{:var, 0}], []}
    assert {:ok, {:vtype, _}} = Kernel.infer(other_ctx, other_goal)

    assert {:error, _} =
             Kernel.check(other_ctx, Term.shift(term, 1, 0), Eval.eval(other_goal, Context.env(other_ctx)))
  end

  @tag :tmp_dir
  @tag :fixed_convoy_composition
  test "fixed-index wrappers compose with projected reconstructed-carrier convoys", %{tmp_dir: dir} do
    source = projected_carrier_source(dir)
    assert {:ok, env} = Program.elaborate(source, source_roots: [dir])
    assert :ok = Kernel.check_def(env, :"TinyPackedCarrier#inspect")
    assert %{body: body} = Env.get_def(env, :"TinyPackedCarrier#inspect")
    assert Term.closed?(body)

    refute Enum.any?(Cure.Core.Validator.nodes(body), fn
             {:var, index} -> index < 0
             _ -> false
           end)
  end

  @tag :tmp_dir
  test "projected reconstructed carriers reject a wrong branch and an unrelated well-typed goal", %{tmp_dir: dir} do
    source = projected_carrier_source(dir)
    assert {:ok, env} = Program.elaborate(source, source_roots: [dir])
    assert :ok = Kernel.check_def(env, :"TinyPackedCarrier#inspect")

    wrong_branch = String.replace(source, "WasMore(rest, edge, tail)", "WasDone(edge)")
    assert {:error, _} = Program.elaborate(wrong_branch, source_roots: [dir])

    wrong_goal =
      source
      |> String.replace(
        "packed: Pack(n, machine, input)) -> ExactAcceptanceStartView(n, machine, input, packed)",
        "packed: Pack(n, machine, input), other: Pack(n, machine, input)) -> ExactAcceptanceStartView(n, machine, input, other)"
      )

    refute wrong_goal == source
    assert {:error, _} = Program.elaborate(wrong_goal, source_roots: [dir])

    %{type: type, body: body} = Env.get_def(env, :"TinyPackedCarrier#inspect")
    {ctx, result, term} = definition_frame(type, body, Context.empty(env))
    assert {:data, view, [n, machine], [input, _package]} = result
    package_type = {:data, :"TinyPackedCarrier#Pack", [n, machine], [input]}
    other_ctx = Context.extend(ctx, Eval.eval(package_type, Context.env(ctx)))
    {:data, ^view, parameters, [shifted_input, _]} = Term.shift(result, 1, 0)
    other_goal = {:data, view, parameters, [shifted_input, {:var, 0}]}
    assert {:ok, {:vtype, _}} = Kernel.infer(other_ctx, other_goal)

    assert {:error, _} =
             Kernel.check(other_ctx, Term.shift(term, 1, 0), Eval.eval(other_goal, Context.env(other_ctx)))
  end

  @tag :tmp_dir
  test "distinct same-size machines do not make their carried edges interchangeable", %{tmp_dir: dir} do
    source =
      dir
      |> projected_carrier_source()
      |> String.replace(
        "packed: Pack(n, machine, input)) ->",
        "packed: Pack(n, machine, input), other: Machine(n), wrong: Edge(n, starts_of(n, other), input)) ->"
      )
      |> String.replace("WasLive(value, edge)", "WasLive(value, wrong)")
      |> String.replace("WasDone(edge)", "WasDone(wrong)")
      |> String.replace("WasMore(rest, edge, tail)", "WasMore(rest, wrong, tail)")

    assert {:error, _} = Program.elaborate(source, source_roots: [dir])
  end

  defp definition_frame({:pi, grade, domain, codomain}, {:lam, _, _, body}, ctx) do
    definition_frame(codomain, body, Context.extend(ctx, Eval.eval(domain, Context.env(ctx)), grade))
  end

  defp definition_frame(result, body, ctx), do: {ctx, result, body}

  defp projected_carrier_source(dir) do
    File.write!(Path.join(dir, "tiny_carrier_state.cure"), """
    mod TinyCarrierState
      type State indices (n: Nat)
        On : State(n)
        Off : State(n)
      type Machine indices (n: Nat)
        MkMachine : (starts: List(State(n))) -> Machine(n)
      @reducible
      fn starts_of(n: Nat, machine: Machine(n)) -> List(State(n)) = match machine
        MkMachine(starts) -> starts
      type Thread indices (n: Nat)
        OnThread : Thread(n)
        OffThread : Thread(n)
      @reducible
      fn thread_of(n: Nat, state: State(n)) -> Thread(n) = match state
        On() -> OnThread()
        Off() -> OffThread()
    end
    """)

    """
    mod TinyPackedCarrier
      use TinyCarrierState
      type Path(n: Nat, machine: Machine(n)) indices (input: Nat, state: Thread(n))
        Done : Path(n, machine, Z(), OffThread())
        More : (rest: Nat) -> Path(n, machine, rest, OffThread()) -> Path(n, machine, S(rest), OffThread())
        Live : (input: Nat) -> Path(n, machine, input, OnThread())
      type Edge(n: Nat, starts: List(State(n))) indices (input: Nat)
        HereEdge : Edge(n, starts, Z())
        NextEdge : (rest: Nat) -> Edge(n, starts, S(rest))
      type Pack(n: Nat, machine: Machine(n)) indices (input: Nat)
        MkPack : (state: State(n)) -> Edge(n, starts_of(n, machine), input) -> Path(n, machine, input, thread_of(n, state)) -> Pack(n, machine, input)
      type ExactAcceptanceStartView(n: Nat, machine: Machine(n)) indices (input: Nat, packed: Pack(n, machine, input))
        WasDone : (edge: Edge(n, starts_of(n, machine), Z())) -> ExactAcceptanceStartView(n, machine, Z(), MkPack(Off(), edge, Done()))
        WasMore : (rest: Nat) -> (edge: Edge(n, starts_of(n, machine), S(rest))) -> (path: Path(n, machine, rest, OffThread())) -> ExactAcceptanceStartView(n, machine, S(rest), MkPack(Off(), edge, More(rest, path)))
        WasLive : (input: Nat) -> (edge: Edge(n, starts_of(n, machine), input)) -> ExactAcceptanceStartView(n, machine, input, MkPack(On(), edge, Live(input)))
      fn inspect(n: Nat, machine: Machine(n), input: Nat, packed: Pack(n, machine, input)) -> ExactAcceptanceStartView(n, machine, input, packed) = match machine
        MkMachine(starts) -> match packed
          MkPack(On(), edge, path) -> match path
            Live(value) -> WasLive(value, edge)
          MkPack(Off(), edge, path) -> match path
            Done() -> WasDone(edge)
            More(rest, tail) -> WasMore(rest, edge, tail)
    end
    """
  end

  test "proof wrappers emit exactly one inferable constructor parameter prefix" do
    assert {:ok, env} = Program.elaborate(computed_with_source(" proof observed"))
    %{body: body} = Env.get_def(env, :"Std.Bounded#prove")

    constructors =
      for {:ctor, name, arguments} <- Cure.Core.Validator.nodes(body),
          name in [:"Std.Bounded#OZero", :"Std.Bounded#OOne"],
          do: arguments

    assert [left, right] = constructors
    assert [_, _] = left
    assert [_, _] = right
    nat = {:data, :"Std.Bounded#Nat", [], []}
    zero = {:ctor, :"Std.Bounded#Z", []}
    ctx = Context.extend(Context.empty(env), Eval.eval(nat, []))
    ctx = Context.extend(ctx, Eval.eval({:data, :"Std.Bounded#Evidence", [], [zero]}, Context.env(ctx)))
    parameter = {:app, {:global, :"Std.Bounded#unrelated"}, {:var, 1}}
    completed = {:ctor, :"Std.Bounded#OZero", [parameter, {:var, 0}]}
    assert {:ok, _} = Kernel.infer(ctx, completed)
    assert {:error, _} = Kernel.infer(ctx, {:ctor, :"Std.Bounded#OZero", [parameter, parameter, {:var, 0}]})
    assert :ok = Kernel.check_def(env, :"Std.Bounded#prove")
  end

  test "proof wrappers preserve existing zero-parameter constructor bodies" do
    source =
      computed_with_source(" proof observed")
      |> String.replace("type Output(other: Nat) indices", "type Output indices")
      |> String.replace("Output(other, Z())", "Output(Z())")
      |> String.replace("Output(other, S(Z()))", "Output(S(Z()))")
      |> String.replace("Output(unrelated(value), choose(value))", "Output(choose(value))")

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"Std.Bounded#prove")
  end

  test "the goal's open sort is shifted past fresh motive binders" do
    assert {:ok, env} = Program.elaborate(@tag_source)
    payload = {:data, :"Std.Bounded#Payload", [], [{:ctor, :"Std.Bounded#Zero", []}]}

    env =
      Inductive.declare(
        env,
        Inductive.family(
          :LevelView,
          [level: {:level_type}],
          [value: payload],
          Sort.finite(UniverseLevel.atom({:var, 1}))
        ),
        [Inductive.ctor(:LevelZero, [], [{:ctor, :"Std.Bounded#PZero", []}])]
      )

    ctx =
      Context.empty(env)
      |> Context.extend({:vlevel_type}, :erased)
      |> Context.extend(Eval.eval(payload, []))

    witness = {:data, :LevelView, [{:var, 1}], [{:ctor, :"Std.Bounded#PZero", []}]}
    ctx = Context.extend(ctx, Eval.eval(witness, Context.env(ctx)))
    goal = {:data, :LevelView, [{:var, 2}], [{:var, 1}]}
    assert {:ok, {:vtype, {:finite, %{atoms: [_]}}}} = Kernel.infer(ctx, goal)
    pattern = {:function_call, [name: "Std.Bounded#PZero"], []}
    body = {:variable, [], "witness"}
    arms = [{:match_arm, [pattern: pattern], [body]}]

    assert {:ok, term} =
             Elaborator.elaborate_match(
               {:variable, [], "value"},
               arms,
               goal,
               ["witness", "value", "level"],
               ctx,
               env
             )

    assert :ok = Kernel.check(ctx, term, Eval.eval(goal, Context.env(ctx)))
  end

  test "the attempt guard restores absent, nil and false process state" do
    key = {Elaborator, :fixed_index_motive}

    for previous <- [:absent, nil, false] do
      if previous == :absent, do: Process.delete(key), else: Process.put(key, previous)
      assert {:ok, _env} = Program.elaborate(@tag_source)
      assert Process.get(key, :absent) == previous
    end

    Process.delete(key)
  end

  test "dependency closure carries hidden unrestricted followers by index" do
    source = shadow_source()
    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"Std.Bounded#probe")
    assert {:ok, _env} = Program.elaborate(String.replace(source, "    let evidence = evidence\n", ""))
  end

  test "dependency closure preserves hidden erased followers" do
    [declarations, _probe] = String.split(shadow_source("@erased "), "  fn probe", parts: 2)
    assert {:ok, env} = Program.elaborate(declarations <> "end\n")
    nat = {:data, :"Std.Bounded#Nat", [], []}
    ctx = Context.extend(Context.empty(env), Eval.eval(nat, []))
    machine = {:data, :"Std.Bounded#Machine", [], [{:var, 0}]}
    ctx = Context.extend(ctx, Eval.eval(machine, Context.env(ctx)))
    state = {:data, :"Std.Bounded#State", [], [{:var, 1}]}
    ctx = Context.extend(ctx, Eval.eval(state, Context.env(ctx)))
    evidence = {:data, :"Std.Bounded#Dep", [{:var, 2}, {:var, 1}], [{:var, 0}]}
    evidence_value = Eval.eval(evidence, Context.env(ctx))
    ctx = ctx |> Context.extend(evidence_value, :erased) |> Context.extend(evidence_value, :erased)
    pattern = {:function_call, [name: "Std.Bounded#MkState"], []}
    arguments = Enum.map(["n", "machine", "evidence"], &{:variable, [], &1})
    body = {:function_call, [name: "consume"], arguments}

    for hidden_name <- ["evidence", nil] do
      names = ["evidence", hidden_name, "state", "machine", "n"]

      assert {:ok, term} =
               Elaborator.elaborate_match(
                 {:variable, [], "state"},
                 [{:match_arm, [pattern: pattern], [body]}],
                 nat,
                 names,
                 ctx,
                 env
               )

      assert :ok = Kernel.check(ctx, term, Eval.eval(nat, Context.env(ctx)))

      assert :ok =
               Relevance.check(
                 env,
                 :erased_shadow,
                 [:unrestricted, :unrestricted, :unrestricted, :erased, :erased],
                 term
               )
    end
  end

  test "hidden restricted followers remain unsupported rather than duplicating their source" do
    for grade <- ["@linear ", "@affine "] do
      source =
        shadow_source(grade)
        |> String.replace("MkDep : Dep(n, machine, state)", "MkDep : Nat -> Dep(n, machine, state)")
        |> String.replace("-> Nat = Z()", "-> Nat = match evidence\n    MkDep(value) -> value", global: false)
        |> String.replace("let evidence", "let #{grade}evidence")

      assert {:error, _reason} = Program.elaborate(source)
      assert {:ok, _env} = Program.elaborate(String.replace(source, "    let #{grade}evidence = evidence\n", ""))
    end
  end

  test "a synthetic hidden name never redirects a visible shadow to an old correct proof" do
    source = """
    mod Std.Bounded
      type Nat = Z | S(Nat)
      type Machine indices (n: Nat)
        MkMachine : Machine(n)
      type State indices (n: Nat)
        MkState : State(n)
        OtherState : State(n)
      type Dep(n: Nat, machine: Machine(n)) indices (state: State(n))
        MkDep : Dep(n, machine, state)
      fn consume(n: Nat, machine: Machine(n), evidence: Dep(n, machine, MkState())) -> Nat = Z()
      fn probe(n: Nat, machine: Machine(n), state: State(n), evidence: Dep(n, machine, MkState()), wrong: Dep(n, machine, OtherState())) -> Nat =
        let evidence = wrong
        match state
          MkState() -> consume(n, machine, evidence)
          OtherState() -> Z()
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end

  defp shadow_source(grade \\ "") do
    """
    mod Std.Bounded
      type Nat = Z | S(Nat)
      type Machine indices (n: Nat)
        MkMachine : Machine(n)
      type State indices (n: Nat)
        MkState : State(n)
      type Dep(n: Nat, machine: Machine(n)) indices (state: State(n))
        MkDep : Dep(n, machine, state)
      fn consume(n: Nat, machine: Machine(n), #{grade}evidence: Dep(n, machine, MkState())) -> Nat = Z()
      fn probe(n: Nat, machine: Machine(n), state: State(n), #{grade}evidence: Dep(n, machine, state)) -> Nat =
        let evidence = evidence
        match state
          MkState() -> consume(n, machine, evidence)
    end
    """
  end

  test "bare polymorphic nullary indices do not abstract across different carriers" do
    for {body, expected} <- [{"AtNil()", :accept}, {"Z()", :reject}] do
      source = """
      mod Std.Bounded
        type Nat = Z | S(Nat)
        type Mixed indices (flags: List(Bool), numbers: List(Nat))
          MixedNil : Mixed(Nil(), Nil())
        type AtNatList indices (numbers: List(Nat))
          AtNil : AtNatList(Nil())
        fn probe(value: Mixed(Nil(), Nil())) -> AtNatList(Nil()) = match value
          MixedNil() -> #{body}
      end
      """

      case expected do
        :accept ->
          assert {:ok, env} = Program.elaborate(source)
          assert :ok = Kernel.check_def(env, :"Std.Bounded#probe")

        :reject ->
          assert {:error, _reason} = Program.elaborate(source)
      end
    end
  end

  test "a fixed nullary index retains a major-dependent original goal" do
    assert {:ok, env} = Program.elaborate(@tag_source)
    assert :ok = Kernel.check_def(env, :"Std.Bounded#exact")
  end

  test "an indexed index carries its dependent ambient carrier" do
    source = """
    mod Std.Bounded
      type Nat = Z | S(Nat)
      type Carrier indices (n: Nat)
        MkCarrier : Carrier(n)
      type State indices (n: Nat)
        Accepted : State(n)
        Other : State(n)
      type Path(n: Nat, carrier: Carrier(n)) indices (state: State(n))
        Stop : Path(n, carrier, Accepted())
        Continue : Path(n, carrier, Other())
      type View(n: Nat, carrier: Carrier(n)) indices (path: Path(n, carrier, Accepted()))
        Done : View(n, carrier, Stop())
      fn exact(n: Nat, carrier: Carrier(n), path: Path(n, carrier, Accepted())) -> View(n, carrier, path) = match path
        Stop() -> Done()
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"Std.Bounded#exact")
  end

  test "a wrong proof branch is still rejected" do
    source = String.replace(@tag_source, "PZero() -> ViewZero()", "PZero() -> PZero()")
    assert {:error, _reason} = Program.elaborate(source)
  end

  test "the original goal is not replaced by the fallback's filler" do
    assert {:ok, env} = Program.elaborate(@tag_source)
    %{body: body} = Env.get_def(env, :"Std.Bounded#exact")
    payload = {:data, :"Std.Bounded#Payload", [], [{:ctor, :"Std.Bounded#Zero", []}]}
    wrong_type = {:pi, :unrestricted, payload, {:data, :"Std.Bounded#Tag", [], []}}

    assert {:error, _reason} =
             Kernel.check(Context.empty(env), body, Eval.eval(wrong_type, []))
  end

  test "the original generic fixed-domain motive remains invalid" do
    assert {:ok, env} = Program.elaborate(@tag_source)
    tag = {:data, :"Std.Bounded#Tag", [], []}
    payload = fn index -> {:data, :"Std.Bounded#Payload", [], [index]} end
    view = fn value -> {:data, :"Std.Bounded#AtZero", [], [value]} end
    ctx = Context.extend(Context.empty(env), Eval.eval(payload.({:ctor, :"Std.Bounded#Zero", []}), []))

    motive =
      {:lam, :unrestricted, tag, {:lam, :unrestricted, payload.({:var, 0}), view.({:var, 0})}}

    term = {:case, {:var, 0}, motive, [{:"Std.Bounded#PZero", 0, {:ctor, :"Std.Bounded#ViewZero", []}}]}
    assert {:error, :bad_motive} = Kernel.check(ctx, term, Eval.eval(view.({:var, 0}), Context.env(ctx)))
  end

  test "computed with refines a folded result goal in both convoy and proof forms" do
    for proof <- ["", " proof observed"] do
      assert {:ok, env} = Program.elaborate(computed_with_source(proof))
      assert :ok = Kernel.check_def(env, :"Std.Bounded#prove")
      {ctx, _scrutinee, _arms, _goal} = computed_with_context(env)
      opaque_call = {:app, {:global, :"Std.Bounded#unrelated"}, {:var, 1}}
      assert ^opaque_call = Normalise.nf(ctx, opaque_call)
    end
  end

  test "computed with rejects a wrong proof and a different well-typed result goal" do
    source = computed_with_source()
    assert {:ok, env} = Program.elaborate(source)

    assert {:error, _} =
             Program.elaborate(String.replace(source, "True() -> OZero(evidence)", "True() -> OOne(evidence)"))

    assert {:error, _} =
             Program.elaborate(String.replace(source, "True() -> OZero(evidence)", "True() -> EZero()"))

    {ctx, scrutinee, arms, _goal} = computed_with_context(env)

    wrong_goal =
      {:data, :"Std.Bounded#Output", [{:app, {:global, :"Std.Bounded#unrelated"}, {:var, 1}}],
       [{:ctor, :"Std.Bounded#S", [{:ctor, :"Std.Bounded#Z", []}]}]}

    assert {:ok, {:vtype, _}} = Kernel.infer(ctx, wrong_goal)
    assert {:error, _} = Elaborator.elaborate_with(scrutinee, arms, nil, wrong_goal, ["evidence", "value"], ctx, env)
  end

  test "with checks original goal annotations instead of only their evaluated value" do
    assert {:ok, env} = Program.elaborate(computed_with_source())
    {ctx, scrutinee, arms, goal} = computed_with_context(env)

    malformed_goal =
      {:app, {:lam, :unrestricted, {:data, :"Std.Bounded#Nat", [], []}, Cure.Core.Term.shift(goal, 1, 0)},
       {:ctor, :"Std.Bool#True", []}}

    assert {:error, _} = Kernel.infer(ctx, malformed_goal)

    assert {:error, _} =
             Elaborator.elaborate_with(scrutinee, arms, nil, malformed_goal, ["evidence", "value"], ctx, env)
  end

  test "an unpublished folded helper is not exposed to synthesize a with motive" do
    source = String.replace(computed_with_source(), "  @reducible\n  fn choose", "  fn choose")
    assert {:error, _} = Program.elaborate(source)
  end

  test "publication without a delta certificate does not authorize goal exposure" do
    assert {:ok, env} = Program.elaborate(computed_with_source())
    choose = :"Std.Bounded#choose"
    assert Env.certified?(env, choose)
    assert %{reducible: true} = Env.get_def(env, choose)
    env = %{env | certified: MapSet.delete(env.certified, choose)}
    refute Env.certified?(env, choose)
    {ctx, scrutinee, arms, goal} = computed_with_context(env)
    assert ^goal = Normalise.nf(ctx, goal)
    assert {:error, _} = Elaborator.elaborate_with(scrutinee, arms, nil, goal, ["evidence", "value"], ctx, env)
  end

  test "variable with keeps its existing goal abstraction" do
    source =
      computed_with_source()
      |> String.replace("= with is_zero(value)", "= with value")
      |> String.replace("True() -> OZero(evidence)", "Z() -> OZero(evidence)")
      |> String.replace("False() -> OOne(evidence)", "S(rest) -> OOne(evidence)")

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"Std.Bounded#prove")
  end

  defp computed_with_source(proof \\ "") do
    """
    mod Std.Bounded
      type Nat = Z | S(Nat)
      @reducible
      fn is_zero(value: Nat) -> Bool = match value
        Z() -> True()
        S(rest) -> False()
      @reducible
      fn choose(value: Nat) -> Nat = match is_zero(value)
        True() -> Z()
        False() -> S(Z())
      fn unrelated(value: Nat) -> Nat = match value
        Z() -> S(Z())
        S(rest) -> Z()
      type Evidence indices (index: Nat)
        EZero : Evidence(Z())
        EOne : Evidence(S(Z()))
      type Output(other: Nat) indices (index: Nat)
        OZero : Evidence(Z()) -> Output(other, Z())
        OOne : Evidence(S(Z())) -> Output(other, S(Z()))
      fn prove(value: Nat, evidence: Evidence(choose(value))) -> Output(unrelated(value), choose(value)) = with is_zero(value)#{proof}
        True() -> OZero(evidence)
        False() -> OOne(evidence)
    end
    """
  end

  defp computed_with_context(env) do
    nat = {:data, :"Std.Bounded#Nat", [], []}
    ctx = Context.extend(Context.empty(env), Eval.eval(nat, []))
    evidence = {:data, :"Std.Bounded#Evidence", [], [{:app, {:global, :"Std.Bounded#choose"}, {:var, 0}}]}
    ctx = Context.extend(ctx, Eval.eval(evidence, Context.env(ctx)))

    goal =
      {:data, :"Std.Bounded#Output", [{:app, {:global, :"Std.Bounded#unrelated"}, {:var, 1}}],
       [{:app, {:global, :"Std.Bounded#choose"}, {:var, 1}}]}

    scrutinee = {:function_call, [name: "is_zero"], [{:variable, [], "value"}]}

    arms =
      for {pattern, body} <- [{"True", "OZero"}, {"False", "OOne"}] do
        {:match_arm, [pattern: {:function_call, [name: pattern], []}],
         [{:function_call, [name: body], [{:variable, [], "evidence"}]}]}
      end

    {ctx, scrutinee, arms, goal}
  end

  test "hidden prerequisites depending only on a structured field remain unsupported" do
    source = """
    mod StructuredHiddenPrerequisite
      type Field = FZero | FNext(Field)
      type Index = C(Field) | Stop
      type Payload indices (index: Index)
        PC : (field: Field) -> Payload(C(field))
        PS : Payload(Stop())
      type G indices (field: Field)
        MkG : G(field)
      type H(field: Field) indices (index: Index, h: G(field))
        MkH : (h: G(field)) -> H(field, C(field), h)
      type View indices (field: Field, value: Payload(C(field)))
        VC : (field: Field) -> View(field, PC(field))
      fn exact(field: Field, value: Payload(C(field)), h: G(field), selected: H(field, C(field), h)) -> View(field, value) =
        let h: G(field) = MkG()
        match value
          PC(found) -> VC(found)
    end
    """

    assert {:error, error} = Program.elaborate(source)
    assert Program.semantic_error(error) == :bad_motive
    visible = String.replace(source, "    let h: G(field) = MkG()\n", "")
    assert {:ok, env} = Program.elaborate(visible)
    assert :ok = Kernel.check_def(env, :"StructuredHiddenPrerequisite#exact")
  end

  test "a fixed constructor field is abstracted as a caller variable" do
    assert {:ok, env} = Program.elaborate(variable_field_source())
    assert :ok = Kernel.check_def(env, :"Std.Bounded#exact")
  end

  test "multiple present fields must be pairwise distinct caller variables" do
    source = """
    mod Std.Bounded
      type Field = FZero | FNext(Field)
      type Index = Pair(Field, Field) | Stop
      type Payload indices (index: Index)
        PC : (left: Field) -> (right: Field) -> Payload(Pair(left, right))
        PS : Payload(Stop())
      type View indices (left: Field, right: Field, value: Payload(Pair(left, right)))
        VC : (left: Field) -> (right: Field) -> View(left, right, PC(left, right))
      fn exact(left: Field, right: Field, value: Payload(Pair(left, right))) -> View(left, right, value) = match value
        PC(found_left, found_right) -> VC(found_left, found_right)
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"Std.Bounded#exact")
  end

  test "a repeated caller variable is not treated as two independent constructor fields" do
    source = """
    mod Std.Bounded
      type Field = FZero | FNext(Field)
      type Index = Pair(Field, Field) | Stop
      type Payload indices (index: Index)
        PC : (left: Field) -> (right: Field) -> Payload(Pair(left, right))
        PS : Payload(Stop())
      type View indices (field: Field, value: Payload(Pair(field, field)))
        VC : (field: Field) -> View(field, PC(field, field))
      fn exact(field: Field, value: Payload(Pair(field, field))) -> View(field, value) = match value
        PC(left, right) -> VC(left)
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end

  test "nested terms in present constructor fields remain unsupported" do
    source = """
    mod Std.Bounded
      type Field = FZero | FNext(Field)
      type Index = C(Field) | Stop
      type Payload indices (index: Index)
        PC : (field: Field) -> Payload(C(field))
        PS : Payload(Stop())
      type View indices (field: Field, value: Payload(C(FNext(field))))
        VC : (field: Field) -> View(field, PC(FNext(field)))
      fn exact(field: Field, value: Payload(C(FNext(field)))) -> View(field, value) = match value
        PC(found) -> VC(field)
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end

  test "variable-field synthesis retains the original goal and rejects wrong branches" do
    source = variable_field_source()
    assert {:ok, env} = Program.elaborate(source)
    assert {:error, _} = Program.elaborate(String.replace(source, "PC(found) -> VC(found)", "PC(found) -> PC(found)"))
    %{body: {:lam, _, _, {:lam, _, _, term}}} = Env.get_def(env, :"Std.Bounded#exact")
    field = {:data, :"Std.Bounded#Field", [], []}
    payload = fn value -> {:data, :"Std.Bounded#Payload", [], [{:ctor, :"Std.Bounded#C", [value]}]} end
    view = fn value, proof -> {:data, :"Std.Bounded#View", [], [value, proof]} end
    ctx = Context.extend(Context.empty(env), Eval.eval(field, []))
    ctx = Context.extend(ctx, Eval.eval(payload.({:var, 0}), Context.env(ctx)))
    assert :ok = Kernel.check(ctx, term, Eval.eval(view.({:var, 1}, {:var, 0}), Context.env(ctx)))
    other = Context.extend(ctx, Eval.eval(field, []))
    other = Context.extend(other, Eval.eval(payload.({:var, 0}), Context.env(other)))
    wrong_goal = view.({:var, 1}, {:var, 0})
    assert {:ok, {:vtype, _}} = Kernel.infer(other, wrong_goal)

    assert {:error, _} =
             Kernel.check(other, Cure.Core.Term.shift(term, 2, 0), Eval.eval(wrong_goal, Context.env(other)))
  end

  test "variable-field support does not admit the old untyped generic motive" do
    assert {:ok, env} = Program.elaborate(variable_field_source())
    field = {:data, :"Std.Bounded#Field", [], []}
    index = {:data, :"Std.Bounded#Index", [], []}
    payload = fn value -> {:data, :"Std.Bounded#Payload", [], [value]} end
    view = fn value, proof -> {:data, :"Std.Bounded#View", [], [value, proof]} end
    ctx = Context.extend(Context.empty(env), Eval.eval(field, []))
    ctx = Context.extend(ctx, Eval.eval(payload.({:ctor, :"Std.Bounded#C", [{:var, 0}]}), Context.env(ctx)))
    motive = {:lam, :unrestricted, index, {:lam, :unrestricted, payload.({:var, 0}), view.({:var, 3}, {:var, 0})}}
    term = {:case, {:var, 0}, motive, [{:"Std.Bounded#PC", 1, {:ctor, :"Std.Bounded#VC", [{:var, 0}]}}]}

    assert {:error, :bad_motive} =
             Kernel.check(ctx, term, Eval.eval(view.({:var, 1}, {:var, 0}), Context.env(ctx)))
  end

  defp variable_field_source do
    """
    mod Std.Bounded
      type Field = FZero | FNext(Field)
      type Index = C(Field) | Stop
      type Payload indices (index: Index)
        PC : (field: Field) -> Payload(C(field))
        PS : Payload(Stop())
      type View indices (field: Field, value: Payload(C(field)))
        VC : (field: Field) -> View(field, PC(field))
      fn exact(field: Field, value: Payload(C(field))) -> View(field, value) = match value
        PC(found) -> VC(found)
    end
    """
  end

  test "constant constructor fields remain unsupported" do
    source = """
    mod Std.Bounded
      type Tag = Zero | Next(Tag)
      type Payload indices (tag: Tag)
        PNext : Payload(Next(Zero()))
      type AtNext indices (value: Payload(Next(Zero())))
        ViewNext : AtNext(PNext())
      fn exact(value: Payload(Next(Zero()))) -> AtNext(value) = match value
        PNext() -> ViewNext()
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end

  test "multiple fixed constructor indices retain the original rejection" do
    source = """
    mod Std.Bounded
      type Tag = Zero | One
      type Payload indices (left: Tag, right: Tag)
        PZero : Payload(Zero(), Zero())
      type AtZero indices (value: Payload(Zero(), Zero()))
        ViewZero : AtZero(PZero())
      fn exact(value: Payload(Zero(), Zero())) -> AtZero(value) = match value
        PZero() -> ViewZero()
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end

  test "a wrong-domain lambda annotation is not normalized away before motive checking" do
    assert {:ok, env} = Program.elaborate(@tag_source)
    tag = {:data, :"Std.Bounded#Tag", [], []}
    payload = {:data, :"Std.Bounded#Payload", [], [{:ctor, :"Std.Bounded#Zero", []}]}
    ctx = Context.extend(Context.empty(env), Eval.eval(payload, []))
    motive = {:lam, :unrestricted, tag, {:lam, :unrestricted, tag, {:type, Sort.finite_closed(0)}}}
    term = {:case, {:var, 0}, motive, [{:"Std.Bounded#PZero", 0, tag}]}

    assert {:error, :bad_motive} = Kernel.infer(ctx, term)
  end
end

defmodule Cure.Elab.DependentBranchReducibleConversionTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "a refined dependent argument converts through a reducible wrapper chain" do
    source = """
    mod BranchConversion
      type Unit = MkUnit

      type Nat = Z | S(Nat)

      @reducible
      fn plus(left: Nat, right: Nat) -> Nat = match left
        Z() -> right
        S(previous) -> S(plus(previous, right))

      type Bound indices (n: Nat)
        First : Bound(S(m))
        Next : Bound(m) -> Bound(S(m))

      @reducible
      fn widen({n: Nat}, {extra: Nat}, value: Bound(n)) -> Bound(plus(n, extra)) = match value
        First() -> First()
        Next(previous) -> Next(widen(previous))

      @reducible
      fn inject_inner({left: Nat}, {right: Nat}, value: Bound(left)) -> Bound(plus(left, right)) = widen(value)

      @reducible
      fn inject(left: Nat, right: Nat, value: Bound(left)) -> Bound(plus(left, right)) = inject_inner(value)

      type State indices (n: Nat)
        Active : Bound(n) -> Unit -> State(n)

      type Thread indices (n: Nat)
        ThreadActive : Bound(n) -> Thread(n)

      type Path(n: Nat) indices (thread: Thread(n))
        PathHere : Path(n, thread)

      type Edge(left: Nat) indices (source: Bound(left), routine: Unit)
        EdgeHere : Edge(left, source, routine)

      type Origin(left: Nat, right: Nat) indices (destination: State(plus(left, right)))
        ActiveOrigin : (source: Bound(left)) -> (routine: Unit) -> (edge: Edge(left, source, routine)) -> Origin(left, right, Active(inject(left, right, source), routine))

      @reducible
      fn state_thread(n: Nat, state: State(n)) -> Thread(n) = match state
        Active(value, _) -> ThreadActive(value)

      fn consume(left: Nat, right: Nat, source: Bound(left), path: Path(plus(left, right), ThreadActive(inject(left, right, source)))) -> Unit = MkUnit()

      fn classify(left: Nat, right: Nat, destination: State(plus(left, right)), origin: Origin(left, right, destination), path: Path(plus(left, right), state_thread(plus(left, right), destination))) -> Unit = match origin
        ActiveOrigin(source, _, _) -> consume(left, right, source, path)
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "matching an indexed family transports its fixed parameter into the result index" do
    source = """
    mod FixedParameterRefinement
      use Std.List

      type Unit = MkUnit
      type Marker = Left | Right

      type Execution indices (routine: List(Marker))
        ExecutionHere : Execution(routine)

      @reducible
      fn append(left: List(Marker), right: List(Marker)) -> List(Marker) = match left
        Nil() -> right
        Cons(head, tail) -> Cons(head, append(tail, right))

      @reducible
      fn mark(routine: List(Marker), marker: Marker) -> List(Marker) = append(routine, Cons(marker, Nil()))

      type Origin(marker: Marker) indices (states: List(Marker), destination: List(Marker))
        OriginHere : (routine: List(Marker)) -> (edge: Execution(states)) -> Origin(marker, states, mark(routine, marker))

      fn consume(routine: List(Marker), execution: Execution(mark(routine, Left()))) -> Unit = MkUnit()

      fn classify(states: List(Marker), destination: List(Marker), origin: Origin(Left(), states, destination), execution: Execution(destination)) -> Unit = match origin
        OriginHere(routine, _) -> consume(routine, execution)
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a Regex machine-state origin transports its injected state into a dependent path" do
    source = """
    mod RegexStateRefinement
      use Std.Regex
      use Std.Bounded
      use Std.List

      type Unit = MkUnit

      type Path(n: Nat) indices (thread: ThreadState(n))
        PathHere : Path(n, thread)

      type Origin(left: Nat, right: Nat, marker: EvidenceInstruction) indices (states: List(MachineState(left)), destination: MachineState(plus(left, right)))
        ActiveOrigin : (source: Bounded(left)) -> (routine: List(EvidenceInstruction)) -> (edge: ListMember(MachineState(left), Active(source, routine, Nil()), states)) -> Origin(left, right, marker, states, Active(inject_alternate_left(left, right, source), routine, Nil()))

      fn consume(left: Nat, right: Nat, source: Bounded(left), path: Path(plus(left, right), ThreadActive(inject_alternate_left(left, right, source)))) -> Unit = MkUnit()

      fn classify(left: Nat, right: Nat, a1: Unit, a2: Unit, a3: Unit, a4: Unit, a5: Unit, a6: Unit, a7: Unit, a8: Unit, a9: Unit, a10: Unit, a11: Unit, a12: Unit, states: List(MachineState(left)), destination: MachineState(plus(left, right)), origin: Origin(left, right, EmitLeft(), states, destination), path: Path(plus(left, right), machine_state_thread(plus(left, right), destination))) -> Unit = match origin
        ActiveOrigin(source, _, _) -> consume(left, right, source, path)
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "matching an indexed origin refines later execution and accepting-path siblings" do
    source = """
    mod RegexSiblingRefinement
      use Std.Regex
      use Std.Regex.Proof

      fn classify(left_count: Nat, left_machine: PatternMachine(left_count), right_count: Nat, right_machine: PatternMachine(right_count), prefer_right: Bool, position: InitialPosition, input: List(Char), after_input: List(Char), input_evidence: List(Evidence), input_captures: List(CaptureFrame), destination: MachineState(plus(left_count, right_count)), initial_evidence: List(Evidence), initial_captures: List(CaptureFrame), path_routine: List(ExtendedInstruction), final_evidence: List(Evidence), origin: FilteredLeftMarkedStateOrigin(left_count, right_count, EmitLeft(), initial_machine_destinations(left_count, left_machine, position, input, after_input), destination), initial_execution: RoutineExecution(machine_state_routine(plus(left_count, right_count), destination), input_evidence, input_captures, initial_evidence, initial_captures), path: AcceptingFrom(plus(left_count, right_count), alternate_pattern_machine(left_count, left_machine, right_count, right_machine, prefer_right), input, after_input, machine_state_thread(plus(left_count, right_count), destination), initial_evidence, initial_captures, final_evidence, path_routine)) -> AlternateLeftCapturedAcceptance(left_count, left_machine, position, input, after_input, input_evidence, input_captures, final_evidence, accepting_final_captures(plus(left_count, right_count), alternate_pattern_machine(left_count, left_machine, right_count, right_machine, prefer_right), input, after_input, machine_state_thread(plus(left_count, right_count), destination), initial_evidence, initial_captures, final_evidence, path_routine, path)) = match origin
        FilteredLeftActiveOrigin(source, regular, child_edge) -> alternate_left_active_acceptance_captures(left_count, left_machine, right_count, right_machine, prefer_right, position, input, after_input, input_evidence, input_captures, source, regular, initial_evidence, initial_captures, path_routine, child_edge, initial_execution, path)
        FilteredLeftAcceptedOrigin(regular, child_edge) -> match accepted_path_view(plus(left_count, right_count), alternate_pattern_machine(left_count, left_machine, right_count, right_machine, prefer_right), input, after_input, initial_evidence, initial_captures, final_evidence, path_routine, path)
          AcceptedPathNow() -> rewrite accepted_path_final_captures(plus(left_count, right_count), alternate_pattern_machine(left_count, left_machine, right_count, right_machine, prefer_right), input, after_input, initial_evidence, initial_captures, final_evidence, path_routine, path) in
            alternate_left_accepted_acceptance_captures(left_count, left_machine, position, after_input, input_evidence, input_captures, regular, initial_captures, child_edge, initial_execution)
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "matching a Sigma refines a dependent local hypothesis to the reconstructed pair" do
    source = """
    mod SigmaSiblingRefinement
      use Std.Sigma

      type Unit = MkUnit
      type Nat = Z | S(Nat)

      type Witness indices (pair: Sigma(left: Nat, Nat))
        WitnessHere : Witness(pair)

      fn consume(left: Nat, right: Nat, witness: Witness(mk_pair(left, right))) -> Unit = MkUnit()

      fn classify(pair: Sigma(left: Nat, Nat), witness: Witness(pair)) -> Unit = match pair
        mk_pair(left, right) -> consume(left, right, witness)
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a computed indexed scrutinee refines siblings through variables inside a structured index" do
    source = """
    mod ComputedStructuredIndexRefinement
      use Std.List

      type Unit = MkUnit
      type State = Active(List(Unit), List(Unit))

      type Origin indices (state: State)
        ActiveOrigin : (routine: List(Unit)) -> Origin(Active(routine, Nil()))

      type Execution indices (routine: List(Unit), constraints: List(Unit))
        Executed : Execution(routine, constraints)

      fn inspect_origin(state: State, origin: Origin(state)) -> Origin(state) = origin

      fn consume(routine: List(Unit), execution: Execution(routine, Nil())) -> Unit = MkUnit()

      fn classify(routine: List(Unit), origin: Origin(Active(routine, Nil())), execution: Execution(routine, Nil())) -> Unit = match inspect_origin(Active(routine, Nil()), origin)
        ActiveOrigin(child_routine) -> consume(child_routine, execution)
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a computed indexed branch transports its result motive with dependent siblings" do
    source = """
    mod ComputedStructuredResultRefinement
      use Std.List

      type Unit = MkUnit
      type State = Active(List(Unit), List(Unit))

      type Origin indices (state: State)
        ActiveOrigin : (routine: List(Unit)) -> Origin(Active(routine, Nil()))

      type Execution indices (routine: List(Unit), constraints: List(Unit))
        Executed : Execution(routine, constraints)

      type Projection indices (routine: List(Unit), execution: Execution(routine, Nil()))
        Projected : (same_execution: Execution(routine, Nil())) -> Projection(routine, same_execution)

      fn inspect_origin(state: State, origin: Origin(state)) -> Origin(state) = origin

      fn classify(routine: List(Unit), origin: Origin(Active(routine, Nil())), execution: Execution(routine, Nil())) -> Projection(routine, execution) = match inspect_origin(Active(routine, Nil()), origin)
        ActiveOrigin(child_routine) -> Projected(execution)
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a lone carried Sigma sibling remains atomic instead of being eta-expanded as a compiler pack" do
    source = """
    mod Std.Bool
      type Flag = Off | On
      type Box indices (flag: Flag)
        Boxed : Box(flag)

      type Origin indices (flag: Flag)
        IsOn : Origin(On())

      type Projection(flag: Flag) indices (payload: Sigma(value: Nat, Box(flag)))
        Projected : Projection(flag, payload)

      fn classify(flag: Flag, origin: Origin(flag), payload: Sigma(value: Nat, Box(flag))) -> Projection(flag, payload) = match origin
        IsOn() -> Projected()
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "checking a Sigma argument preserves an already well-typed local atomically" do
    source = """
    mod SigmaCheckedArgumentIdentity
      use Std.Sigma

      type Unit = MkUnit
      type Nat = Z | S(Nat)
      type Equivalent(a: Type) indices (left: a, right: a)
        Reflexive : (value: a) -> Equivalent(a, value, value)

      typealias Pack = Sigma(first: Nat, Sigma(second: Nat, Equivalent(Nat, first, first)))

      type Holder indices (pack: Pack)
        Held : Holder(pack)

      fn consume(pack: Pack, transform: (Nat) -> Nat, holder: Holder(pack)) -> Unit = MkUnit()

      fn preserve(pack: Pack, holder: Holder(pack)) -> Unit = consume(pack, fn(value) -> value, holder)
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a reducible helper declared after its caller is available during dependent conversion" do
    source = """
    mod ForwardReducibleConversion
      use Std.List

      type Witness indices (values: List(Nat))
        EmptyWitness : Witness(Nil())

      fn witness() -> Witness(empty_values()) = EmptyWitness()

      @reducible
      fn empty_values() -> List(Nat) = Nil()
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a nested indexed view refines a reducible projection of the matched value" do
    source = """
    mod NestedReducibleProjectionRefinement
      type Unit = MkUnit
      type Pair = PairValue(Nat, Nat, Nat)

      type Equivalent(a: Type) indices (left: a, right: a)
        Reflexive : (value: a) -> Equivalent(a, value, value)

      @reducible
      fn projected(pair: Pair) -> Nat = match pair
        PairValue(_, right, _) -> right

      type View(indices_from: Nat) indices (combined: Nat)
        Viewed : (child_value: Nat) -> (exact: Equivalent(Nat, child_value, combined)) -> View(indices_from, combined)

      fn inspect(left: Nat, right: Nat) -> View(left, right) = Viewed(right, Reflexive(right))

      fn consume(left: Nat, right: Nat, exact: Equivalent(Nat, left, right)) -> Unit = MkUnit()

      fn classify(pair: Pair) -> Unit = match pair
        PairValue(left, right, _) -> match inspect(left, right)
          Viewed(child_value, exact) -> consume(child_value, projected(pair), exact)
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end

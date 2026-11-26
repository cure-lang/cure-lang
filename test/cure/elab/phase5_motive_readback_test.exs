defmodule Cure.Elab.Phase5MotiveReadbackTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Eval, Inductive, Kernel, Normalise, Quote}
  alias Cure.Elab.Program

  test "motive parameters preserve an indexed carrier's parameter/index split" do
    source = """
    mod Std.Bounded
      type Nat = Z | S(Nat)
      type Box indices (n: Nat)
        Mk : Box(n)
      type Same(a: Type) indices (left: a, right: a)
        SameRefl : (value: a) -> Same(a, value, value)
      fn probe(n: Nat, x: Box(n), y: Box(n), equality: Same(Box(n), x, y)) -> Nat = match equality
        SameRefl(value) -> Z()
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"Std.Bounded#probe")
  end

  test "an indexed value convoy also carries an index-dependent ambient carrier" do
    source = """
    mod Std.Bounded
      type Nat = Z | S(Nat)
      type Machine indices (n: Nat)
        MkMachine : Machine(n)
      type State indices (n: Nat)
        MkState : State(n)
      type Dep(n: Nat, machine: Machine(n)) indices (state: State(n))
        MkDep : Dep(n, machine, state)
      fn consume(n: Nat, machine: Machine(n), evidence: Dep(n, machine, MkState())) -> Nat = Z()
      fn probe(n: Nat, machine: Machine(n), state: State(n), evidence: Dep(n, machine, state)) -> Nat = match state
        MkState() -> consume(n, machine, evidence)
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"Std.Bounded#probe")
  end

  test "nested indexed matches keep folded goals until their indices are abstracted" do
    source = """
    mod MotiveConvoyProbe
      use Std.Bounded
      use Std.Equivalent

      type Rows indices (remaining: Nat)
        NoRows : Rows(Z())
        MoreRows : Nat -> Rows(rest) -> Rows(S(rest))

      @reducible
      fn build(n: Nat, inject: (Bounded(n)) -> Nat) -> Rows(n) = match n
        Z() -> NoRows()
        S(rest) -> MoreRows(inject(First()), build(rest, fn(state) -> inject(Next(state))))

      @reducible
      fn read({n: Nat}, rows: Rows(n), state: Bounded(n)) -> Nat = match rows
        NoRows() -> match state
        MoreRows(head, tail) -> match state
          First() -> head
          Next(index) -> read(tail, index)

      fn probe(n: Nat, inject: (Bounded(n)) -> Nat, state: Bounded(n)) -> Equivalent(Nat, read(build(n, inject), state), inject(state)) = match n
        Z() -> match state
        S(rest) -> match state
          First() -> reflexive(inject(First()))
          Next(index) -> probe(rest, fn(state) -> inject(Next(state)), index)
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"MotiveConvoyProbe#probe")
  end

  test "inferred pickup branches retain indexed carriers, including inside containers" do
    for carrier <- ["Box(n)", "List(Box(n))"] do
      source = """
      mod Std.Bounded
        type Nat = Z | S(Nat)
        type Box indices (n: Nat)
          Mk : Box(n)
        fn probe(n: Nat, x: #{carrier}, condition: Bool, tag: Nat) -> #{carrier} = match tag
          Z() -> pickup
            condition -> x
            else -> x
          S(rest) -> x
      end
      """

      assert {:ok, env} = Program.elaborate(source)
      assert :ok = Kernel.check_def(env, :"Std.Bounded#probe")
    end
  end

  test "a computed-index match preserves its original carrier without inventing an equality" do
    for {proof, expected} <- [{"key(n, box)", :accept}, {"S(key(n, box))", :reject}] do
      source = """
      mod Std.Bounded
        type Nat = Z | S(Nat)
        type Box indices (n: Nat)
          MkBox : Nat -> Box(n)
        type Same(a: Type) indices (left: a, right: a)
          SameRefl : (value: a) -> Same(a, value, value)
        @reducible
        fn key(n: Nat, box: Box(n)) -> Nat = match box
          MkBox(value) -> value
        type Execution indices (routine: Nat, n: Nat, final: Nat)
          Done : Execution(routine, n, final)
        type Package indices (routine: Nat, n: Nat)
          Packed : (final: Nat) -> Execution(routine, n, final) -> Package(routine, n)
        fn make(n: Nat, box: Box(n)) -> Package(key(n, box), n) = Packed(Z(), Done())
        type Witness(n: Nat, box: Box(n)) indices (final: Nat)
          Witnessed : (routine: Nat) -> Execution(routine, n, final) -> Same(Nat, routine, key(n, box)) -> Witness(n, box, final)
        type SomeWitness(n: Nat, box: Box(n)) indices (present: Bool)
          SomeWitnessed : (final: Nat) -> Witness(n, box, final) -> SomeWitness(n, box, True())
        fn probe(n: Nat, box: Box(n)) -> SomeWitness(n, box, True()) = match make(n, box)
          Packed(final, execution) -> SomeWitnessed(final, Witnessed(key(n, box), execution, SameRefl(#{proof})))
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

  describe "strict kernel typing of symbolic Bounded readback" do
    setup do
      assert {:ok, env} =
               Program.elaborate("""
               mod BoundedReadbackProbe
                 use Std.Bounded
                 fn identity(n: Nat) -> Nat = n
               end
               """)

      nat = Inductive.builtin(env, :nat)
      bounded = Inductive.builtin(env, :bounded)
      ctors = Inductive.ctors_of(env, bounded)
      first = Enum.find(ctors, &(Cure.Elab.Name.base(&1.name) == "First")).name
      next = Enum.find(ctors, &(Cure.Elab.Name.base(&1.name) == "Next")).name
      succ = Enum.find(Inductive.ctors_of(env, nat), &(Cure.Elab.Name.base(&1.name) == "S")).name
      ctx = Context.extend(Context.empty(env), {:vdata, nat, []})

      %{ctx: ctx, bounded: bounded, first: first, next: next, succ: succ}
    end

    test "First and Next still check at their original symbolic bounds after readback", info do
      %{ctx: ctx, bounded: bounded, first: first, next: next, succ: succ} = info
      bound = {:vneutral, {:nvar, 0}}
      first_term = {:ctor, first, [{:var, 0}]}
      next_term = {:ctor, next, [{:ctor, succ, [{:var, 0}]}, first_term]}

      for {term, size} <- [
            {first_term, {:vctor, succ, [bound]}},
            {next_term, {:vctor, succ, [{:vctor, succ, [bound]}]}}
          ] do
        expected = {:vdata, bounded, [size]}
        assert :ok = Kernel.check(ctx, term, expected)
        quoted = Quote.reify(Eval.eval(term, Context.env(ctx)), Context.length(ctx), Context.signature(ctx))
        assert :ok = Kernel.check(ctx, quoted, expected)
        assert :ok = Kernel.check(ctx, Normalise.nf(ctx, term), expected)
      end
    end

    test "a bound-free literal is not admitted at an opaque or empty bound", info do
      %{ctx: ctx, bounded: bounded} = info
      assert {:error, _} = Kernel.check(ctx, {:bounded_lit, 0}, {:vdata, bounded, [{:vneutral, {:nvar, 0}}]})
      assert {:error, _} = Kernel.check(ctx, {:bounded_lit, 0}, {:vdata, bounded, [{:vnat, 0}]})
    end

    test "an inferred lambda type remains a well-formed indexed Pi after readback", info do
      %{ctx: ctx, bounded: bounded} = info
      identity = {:lam, :unrestricted, {:data, bounded, [], [{:var, 0}]}, {:var, 0}}

      assert {:ok, inferred} = Kernel.infer(ctx, identity)
      quoted = Quote.reify(inferred, Context.length(ctx), Context.signature(ctx))
      assert {:ok, {:vtype, _sort}} = Kernel.infer(ctx, quoted)
    end
  end
end

defmodule Cure.Elab.CtorIndexFromGoalTest do
  @moduledoc """
  A constructor arm body whose field type depends on an index that NO present
  argument determines — the index is available only from the branch's refined goal.

  `MkP : Eq(f(x), OT) -> P(x)` at the refined goal `P(OA)`: the field
  `reflexive(OT()) : Eq(OT, OT)` hides `f(OA)` behind an ι-reduction, so the field
  cannot fix the index `x`. Before the fix, `elaborate_branch_body`'s constructor
  arm inferred first and only retried checking mode on `:unsolved_metavariables` /
  `:unsupported_expression`; inference here failed with `:index_mismatch`
  (`f(?0) ≠ OT`, the index left a metavariable) and surfaced that error directly,
  never letting the goal seed the constructor's index. The fix retries checking
  mode on ANY inference error (surfacing the original if the retry also fails), so
  `elaborate_ctor_app_bidirectional` pins `x := OA` from `P(OA)` before checking the
  field. This is the enabling machinery for the intrinsic (GADT-indexed) well-scoped
  BST: `owoto`'s trichotomy constructors (`TLt`/`TEq`/`TGt`) are proof-carrying and
  their key index comes only from the refined branch goal.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @preamble """
    use Std.Equivalent
    type OKey = OA | OB | OC
    type OBit = OF | OT
    fn f(x: OKey) -> OBit = match x
      OA() -> OT()
      OB() -> OT()
      OC() -> OT()
    type P indices (x: OKey)
      MkP : Equivalent(OBit, f(x), OT()) -> P(x)
  """

  test "constructor arm index is seeded from the refined branch goal" do
    src = """
    mod CtorGoalOK
    #{@preamble}
      fn build(x: OKey) -> P(x) = match x
        OA() -> MkP(reflexive(OT()))
        OB() -> MkP(reflexive(OT()))
        OC() -> MkP(reflexive(OT()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "an indexed constructor inherits its family index through higher-order fields" do
    src = """
    mod IndexedConstructorGoal
      use Std.Bounded

      type State indices (n: Nat)
        Stop : State(n)

      type Machine indices (n: Nat)
        MkMachine : List(State(n)) -> ((Bounded(n)) -> List(State(n))) -> Machine(n)

      fn no_next({n: Nat}, _state: Bounded(n)) -> List(State(n)) = []

      fn build() -> Machine(Z()) =
        let starts: List(State(Z())) = [Stop()]
        MkMachine(starts, no_next)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "constructor result numerals are checked against a Bounded index telescope" do
    # Constructor result indices are bidirectional positions. Lowering `1` as a
    # Nat before consulting `state : Bounded(2)` loses the compact bounded value
    # and rejects the declaration during interface registration.
    src = """
    mod BoundedConstructorIndex
      use Std.Bounded

      type Slot indices (state: Bounded(plus(1, 1)))
        Second : Slot(1)

      fn second() -> Slot(1) = Second()
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "numeric indices in parameter signatures lower before a local kernel context exists" do
    src = """
    mod NumericParameterIndex
      type Slot indices (index: Nat)
        At : Slot(1)

      fn preserve(value: Slot(1)) -> Slot(1) = value
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "nested constructors in a result index inherit every enclosing field expectation" do
    src = """
    mod NestedConstructorResultIndex
      type Frame = Frame(List(Nat), List(Nat))

      type FrameStack indices (frames: List(Frame))
        EmptyFrame : FrameStack(Cons(Frame(Nil(), Nil()), Nil()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "the trichotomy pattern (owoto returning proof-carrying GADT ctors) elaborates" do
    src = """
    mod OwotoTrichotomy
      use Std.Equivalent
      type OKey = OA | OB | OC
      type OBit = OF | OT
      fn slt(x: OKey, y: OKey) -> OBit = match x
        OA() -> match y
          OA() -> OF()
          OB() -> OT()
          OC() -> OT()
        OB() -> match y
          OA() -> OF()
          OB() -> OF()
          OC() -> OT()
        OC() -> match y
          OA() -> OF()
          OB() -> OF()
          OC() -> OF()
      type Tri indices (x: OKey, k: OKey)
        TLt : Equivalent(OBit, slt(x, k), OT()) -> Tri(x, k)
        TEq : Equivalent(OKey, x, k) -> Tri(x, k)
        TGt : Equivalent(OBit, slt(k, x), OT()) -> Tri(x, k)
      fn owoto(x: OKey, k: OKey) -> Tri(x, k) = match x
        OA() -> match k
          OA() -> TEq(reflexive(OA()))
          OB() -> TLt(reflexive(OT()))
          OC() -> TLt(reflexive(OT()))
        OB() -> match k
          OA() -> TGt(reflexive(OT()))
          OB() -> TEq(reflexive(OB()))
          OC() -> TLt(reflexive(OT()))
        OC() -> match k
          OA() -> TGt(reflexive(OT()))
          OB() -> TGt(reflexive(OT()))
          OC() -> TEq(reflexive(OC()))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "antibody: a genuinely ill-typed constructor arm still rejects" do
    # `MkP` at `P(OA)` demands `Eq(f(OA), OT) = Eq(OT, OT)`; supplying `reflexive(OF())`
    # (: `Eq(OF, OF)`) must NOT be laundered into an accept by the goal-seeding retry.
    src = """
    mod CtorGoalAntibody
    #{@preamble}
      fn build(x: OKey) -> P(x) = match x
        OA() -> MkP(reflexive(OF()))
        OB() -> MkP(reflexive(OT()))
        OC() -> MkP(reflexive(OT()))
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end

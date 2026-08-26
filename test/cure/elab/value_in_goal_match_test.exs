defmodule Cure.Elab.ValueInGoalMatchTest do
  @moduledoc """
  A dependent `match` whose GOAL mentions the scrutinee VALUE (not just its
  index) — e.g. `Equivalent(NV(n), v, v)`. In each branch the dependent match refines the
  scrutinee to that branch's constructor, so the goal refines to `Equivalent(NV(Z), vz,
  vz)` / `Equivalent(NV(S m), vs s, vs s)`, which `reflexive(ctor)` inhabits. Idris accepts all
  of these (`idris2 --check`, zero errors).

  RED before the fix: the plain-`match` branch computed its checking-mode
  `branch_expected` via an ad-hoc `branch_index_subst` that only inverts when the
  CONSTRUCTOR result index is a variable. For `v : NV(n)` matched by `vz : NV(Z)`
  the pair is `{Z, n}` (Z is not a var), so the scrutinee's index var `n` was
  never inverted to `Z`; the goal stayed `Equivalent(NV(n), vz, vz)` and the body
  `reflexive(vz()) : Equivalent(NV(Z), …)` failed conversion `NV(Z) ≢ NV(n)`. The kernel's own
  `branch_unify` verdict already carries `n := Z` (the `j >= arity` inverse
  clause), and the with-rematch path already uses it; this fix routes the plain
  path through the same verdict.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @preamble """
    type Nat = Z | S(Nat)
    type SNat indices (n: Nat)
      szero : SNat(Z)
      ssuc : SNat(n) -> SNat(S(n))
    type NV indices (n: Nat)
      vz : NV(Z)
      vs : SNat(n) -> NV(S(n))
    fn toS(m: Nat) -> SNat(m) = match m
      Z() -> szero()
      S(j) -> ssuc(toS(j))
    fn view(n: Nat) -> NV(n) = match n
      Z() -> vz()
      S(m) -> vs(toS(m))
  """
  defp mod(b), do: "mod P\n" <> @preamble <> b <> "end\n"

  test "goal Equivalent(NV(n), v, v), var scrutinee, reflexive(ctor) bodies" do
    src =
      mod("""
        fn f({n: Nat}, v: NV(n)) -> Equivalent(NV(n), v, v) =
          match v
            vz() -> reflexive(vz())
            vs(s) -> reflexive(vs(s))
      """)

    assert {:ok, _} = Program.elaborate(src)
  end

  test "goal Equivalent(NV(n), v, v), reflexive(v) bodies (value-occurrence in both positions)" do
    src =
      mod("""
        fn f({n: Nat}, v: NV(n)) -> Equivalent(NV(n), v, v) =
          match v
            vz() -> reflexive(v)
            vs(s) -> reflexive(v)
      """)

    assert {:ok, _} = Program.elaborate(src)
  end

  test "scrutinee refinement reconstructs inferred constructor fields" do
    src = """
    mod InferredFieldReconstruction
      type Nat = Z | S(Nat)
      type List(a: Type) = Nil | Cons(a, List(a))
      type Path indices (input: List(Nat), final: Nat)
        Finished : Path(Nil(), final)
        Stepped : (head: Nat) -> (tail: List(Nat)) -> Path(tail, final) -> Path(Cons(head, tail), final)

      fn ignore({input: List(Nat)}, {final: Nat}, _path: Path(input, final)) -> Nat = Z()

      fn retain(input: List(Nat), final: Nat, path: Path(input, final)) -> Nat = match input
        Nil() -> match path
          Finished() -> ignore(path)
        Cons(_, _) -> match path
          Stepped(head, tail, suffix) -> ignore(path)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "constructor index refinement ignores variables bound inside a normalized index" do
    src = """
    mod BinderAwareIndexRefinement
      type Nat = Z | S(Nat)
      type List(a: Type) = Nil | Cons(a, List(a))

      @reducible
      fn copied(xs: List(Nat)) -> List(Nat) = match xs
        Nil() -> Nil()
        Cons(head, tail) -> Cons(head, copied(tail))

      type Indexed indices (value: List(Nat))
        IndexedBy : (projected: List(Nat)) -> Indexed(projected)

      fn projected_is_copied(xs: List(Nat), witness: Indexed(copied(xs))) -> Equivalent(List(Nat), copied(xs), copied(xs)) = match witness
        IndexedBy(projected) -> reflexive(projected)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "an explicit erased parameter is consumed before a dependent present argument" do
    src =
      mod("""
        fn retain(@erased marker: Nat, value: Nat) -> Nat = value
        fn f(marker: Nat, value: Nat) -> Nat = retain(marker, value)
      """)

    assert {:ok, _} = Program.elaborate(src)
  end

  test "goal Equivalent(NV(n), view(n), view(n)), computed scrutinee" do
    src =
      mod("""
        fn f(n: Nat) -> Equivalent(NV(n), view(n), view(n)) =
          match view(n)
            vz() -> reflexive(vz())
            vs(s) -> reflexive(vs(s))
      """)

    assert {:ok, _} = Program.elaborate(src)
  end

  test "computed scrutinee refines a goal through published reducible definitions" do
    src =
      mod("""
        type Bool = False | True
        type BoolView indices (value: Bool)
          false_view : BoolView(False())
          true_view : BoolView(True())
        fn parity(n: Nat) -> Bool = match n
          Z() -> False()
          S(_) -> True()
        @reducible
        fn wrapped_once(value: Bool) -> Bool = value
        @reducible
        fn wrapped_twice(value: Bool) -> Bool = wrapped_once(value)
        fn parity_view(n: Nat) -> BoolView(wrapped_twice(parity(n))) =
          match parity(n)
            False() -> false_view()
            True() -> true_view()
      """)

    assert {:ok, _} = Program.elaborate(src)
  end

  test "case evaluation reserves erased constructor-index binder slots" do
    src =
      mod("""
        type IBox indices (n: Nat)
          IBoxed : Nat -> IBox(n)
        @reducible
        fn boxed_zero() -> IBox(Z()) = IBoxed(Z())
        @reducible
        fn unbox({n: Nat}, boxed: IBox(n)) -> Nat = match boxed
          IBoxed(value) -> value
      """)

    assert {:ok, env} = Program.elaborate(src)

    zero = {:ctor, :"P#Z", []}

    term =
      {:app, {:app, {:global, :"P#unbox"}, zero}, {:global, :"P#boxed_zero"}}

    assert {:ctor, :"P#Z", []} =
             Cure.Core.Normalise.nf(Cure.Core.Context.empty(env), term,
               delta: :certified,
               stuck_cases: :expose
             )
  end

  test "index refinement does not replace a runtime value with an erased branch witness" do
    src =
      mod("""
        type Bool = False | True
        type BoolView indices (value: Bool)
          true_view : BoolView(True())
        fn runtime_identity(value: Bool) -> Bool = value
        fn retain_runtime_value(value: Bool, view: BoolView(value)) -> Bool = with view
          true_view() -> runtime_identity(value)
      """)

    assert {:ok, _} = Program.elaborate(src)
  end

  test "soundness control: an ill-typed body at the refined goal is rejected" do
    # In the vz branch the goal refines to `Equivalent(NV(Z), vz, vz)`. Returning
    # `reflexive(vs(...))` (: Equivalent(NV(S _), vs _, vs _)) must be rejected — the value
    # refinement must not over-accept a mismatched constructor.
    src =
      mod("""
        fn f({n: Nat}, v: NV(n)) -> Equivalent(NV(n), v, v) =
          match v
            vz() -> reflexive(vs(szero()))
            vs(s) -> reflexive(vs(s))
      """)

    assert {:error, _} = Program.elaborate(src)
  end

  test "control: index-only goal still elaborates (no regression on the plain path)" do
    src =
      mod("""
        fn f({n: Nat}, v: NV(n)) -> NV(n) =
          match v
            vz() -> vz()
            vs(s) -> vs(s)
      """)

    assert {:ok, _} = Program.elaborate(src)
  end

  test "nested match refines a scrutinee value retained in the dependent result" do
    src =
      """
      mod NestedPathRefinement
        type Input = Empty | One
        type Path indices (input: Input)
          PEmpty : Path(Empty())
          POne : Path(One())
        type Out = OEmpty | OOne
        @reducible
        fn final({input: Input}, path: Path(input)) -> Out = match path
          PEmpty() -> OEmpty()
          POne() -> OOne()
        type Witness indices (out: Out)
          WEmpty : Witness(OEmpty())
          WOne : Witness(OOne())
        fn prove(input: Input, path: Path(input)) -> Witness(final(path)) = match input
          Empty() -> match path
            PEmpty() -> WEmpty()
          One() -> match path
            POne() -> WOne()
      """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "nested constructor decomposition retains the outer scrutinee refinement" do
    src = """
    mod NestedOuterScrutineeRefinement
      type Nat = Z | S(Nat)
      type Box = MkBox(Nat)
      type Pair = MkPair(Nat, Box)

      @reducible
      fn boxed_value(box: Box) -> Nat = match box
        MkBox(value) -> value

      @reducible
      fn pair_box(pair: Pair) -> Box = match pair
        MkPair(_, box) -> box

      fn projected_is_itself(pair: Pair) -> Equivalent(Nat, boxed_value(pair_box(pair)), boxed_value(pair_box(pair))) = match pair
        MkPair(_, box) -> match box
          MkBox(value) -> reflexive(value)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end

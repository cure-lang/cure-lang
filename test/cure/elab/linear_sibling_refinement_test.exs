defmodule Cure.Elab.LinearSiblingRefinementTest do
  @moduledoc """
  A `with r` handler may match on `r` while a LINEAR sibling whose type depends on
  `r` (`cap : ReplyCap(r)`) is in scope, refine that sibling per branch, and consume
  it exactly once — the ergonomic OTP handler shape

      with r
        GetCount() -> reply(cap, R0)
        …

  Previously this over-rejected: `with`'s Eq-transport encodes the sibling as
  `transport_case(prf) applied to cap` (a collapsible case = identity on `cap`)
  which the relevance checker ω-scaled pre-erasure. The sibling refinement now uses
  MOTIVE-GENERALIZATION — `(case r of λcap'. body) cap`, a real λ binder per branch —
  and the relevance CONVOY rule counts the linear `cap` once. Linearity is still
  enforced: dropping or duplicating `cap` in a branch is rejected.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  defp verdict(defs) do
    src = """
    mod LinSib
      type Reply0 = R0
      type Reply1 = R1a | R1b
      type Req = GetCount | SetName(Reply0) | Ping
      fn ReplyOf(r: Req) -> Type = match r
        GetCount()  -> Reply0
        SetName(_)  -> Reply1
        Ping()      -> Reply1
      type ReplyCap(r: Req) indices ()
        MkCap : ReplyCap(r)
      type Replied = Done
      type Pair = MkPair(Replied, Replied)
      fn reply({r: Req}, @linear cap : ReplyCap(r), v: ReplyOf(r)) -> Replied =
        match cap
          MkCap() -> Done
    #{defs}
    end
    """

    case Program.elaborate(src) do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "branching handler consuming the linear capability once per path is accepted" do
    defs = """
      fn handle(r: Req, @linear cap : ReplyCap(r)) -> Replied = with r
        GetCount()  -> reply(cap, R0)
        SetName(_)  -> reply(cap, R1a)
        Ping()      -> reply(cap, R1b)
    """

    assert verdict(defs) == :accept
  end

  test "a branch that DROPS the linear capability is rejected" do
    defs = """
      fn handle(r: Req, @linear cap : ReplyCap(r)) -> Replied = with r
        GetCount()  -> Done
        SetName(_)  -> reply(cap, R1a)
        Ping()      -> reply(cap, R1b)
    """

    assert verdict(defs) == :reject
  end

  test "a branch that DUPLICATES the linear capability is rejected" do
    defs = """
      fn handle(r: Req, @linear cap : ReplyCap(r)) -> Pair = with r
        GetCount()  -> MkPair(reply(cap, R0), reply(cap, R0))
        SetName(_)  -> MkPair(reply(cap, R1a), Done)
        Ping()      -> MkPair(reply(cap, R1b), Done)
    """

    assert verdict(defs) == :reject
  end

  describe "motive-generalization refines MULTIPLE linear siblings" do
    defp verdict2(handle) do
      src = """
      mod TwoSib
        type Reply0 = R0
        type Req = A | B
        fn ReplyOf(r: Req) -> Type = match r
          A() -> Reply0
          B() -> Reply0
        type Cap1(r: Req) indices ()
          MkC1 : Cap1(r)
        type Cap2(r: Req) indices ()
          MkC2 : Cap2(r)
        type Replied = Done
        fn use_both({r: Req}, @linear c1 : Cap1(r), @linear c2 : Cap2(r), v: ReplyOf(r)) -> Replied =
          match c1
            MkC1() -> match c2
              MkC2() -> Done
        fn use1({r: Req}, @linear c1 : Cap1(r), v: ReplyOf(r)) -> Replied = match c1
          MkC1() -> Done
      #{handle}
      end
      """

      case Program.elaborate(src) do
        {:ok, _} -> :accept
        {:error, _} -> :reject
      end
    end

    test "two linear siblings each consumed once per path is accepted" do
      handle = """
        fn handle(r: Req, @linear c1 : Cap1(r), @linear c2 : Cap2(r)) -> Replied = with r
          A() -> use_both(c1, c2, R0)
          B() -> use_both(c1, c2, R0)
      """

      assert verdict2(handle) == :accept
    end

    test "dropping the second sibling in a branch is rejected" do
      handle = """
        fn handle(r: Req, @linear c1 : Cap1(r), @linear c2 : Cap2(r)) -> Replied = with r
          A() -> use1(c1, R0)
          B() -> use_both(c1, c2, R0)
      """

      assert verdict2(handle) == :reject
    end

    test "duplicating a sibling in a branch is rejected" do
      handle = """
        fn handle(r: Req, @linear c1 : Cap1(r), @linear c2 : Cap2(r)) -> Replied = with r
          A() -> let x = use1(c1, R0) in use_both(c1, c2, R0)
          B() -> use_both(c1, c2, R0)
      """

      assert verdict2(handle) == :reject
    end
  end

  describe "plain `match` (not `with`) refines the linear sibling too (item C)" do
    # `match r` — no `with` — routes to the same motive-generalization machinery when
    # its standard path fails and a scrutinee-dependent sibling is in scope, so the
    # ergonomic OTP handler needs no `with`. Linearity is still enforced.
    test "plain-match handler consuming cap once per path is accepted" do
      defs = """
        fn handle(r: Req, @linear cap : ReplyCap(r)) -> Replied = match r
          GetCount()  -> reply(cap, R0)
          SetName(_)  -> reply(cap, R1a)
          Ping()      -> reply(cap, R1b)
      """

      assert verdict(defs) == :accept
    end

    test "plain-match: a branch that DROPS the capability is rejected" do
      defs = """
        fn handle(r: Req, @linear cap : ReplyCap(r)) -> Replied = match r
          GetCount()  -> Done
          SetName(_)  -> reply(cap, R1a)
          Ping()      -> reply(cap, R1b)
      """

      assert verdict(defs) == :reject
    end

    test "plain-match: a branch that DUPLICATES the capability is rejected" do
      defs = """
        fn handle(r: Req, @linear cap : ReplyCap(r)) -> Pair = match r
          GetCount()  -> MkPair(reply(cap, R0), reply(cap, R0))
          SetName(_)  -> MkPair(reply(cap, R1a), Done)
          Ping()      -> MkPair(reply(cap, R1b), Done)
      """

      assert verdict(defs) == :reject
    end

    test "plain-match: a branch that RETURNS a scrutinee-dependent sibling directly" do
      # `GetCount() -> w` reads the sibling `w : ReplyOf(r)` at its refined type
      # `Reply0`. The standard path builds a term the KERNEL rejects, outside
      # `elaborate_match`; the gated kernel-check retry (item-C edge) catches it.
      defs = """
        fn use_it(r: Req, w: ReplyOf(r)) -> Reply0 = match r
          GetCount()  -> w
          SetName(_)  -> R0
          Ping()      -> R0
      """

      assert verdict(defs) == :accept
    end
  end

  describe "sibling refinement handles INDEX-bearing families (reify gap handled by resplit)" do
    # The motive-gen path abstracts a sibling's type into the case motive as a Π
    # domain. `collect_with_siblings` applies `resplit_data`, so an INDEX-bearing
    # sibling family — the `Π(SNat(w))` shape the eq-transport design avoided for fear
    # of `Quote.reify`'s param/index collapse — refines correctly. These pin that the
    # gap is not reachable via sibling refinement.
    defp idx_verdict(src) do
      case Program.elaborate(src) do
        {:ok, _} -> :accept
        {:error, _} -> :reject
      end
    end

    test "sibling of an index-bearing family (F indexed by the scrutinee) refines" do
      src = """
      mod IdxSib
        type Tag = TA | TB
        type Res = MkRes
        type F(a: Type) indices (t: Tag)
          MkFA : F(a, TA)
          MkFB : F(a, TB)
        fn useF({a: Type}, {t: Tag}, x: F(a, t)) -> Res = match x
          MkFA() -> MkRes
          MkFB() -> MkRes
        fn handle(r: Tag, w: F(Res, r)) -> Res = with r
          TA() -> useF(w)
          TB() -> useF(w)
      end
      """

      assert idx_verdict(src) == :accept
    end

    test "sibling with a COMPUTED index `G(flip(r))` refines" do
      src = """
      mod ComputedIdx
        type Tag = TA | TB
        type Res = MkRes
        fn flip(t: Tag) -> Tag = match t
          TA() -> TB()
          TB() -> TA()
        type G indices (t: Tag)
          MkGA : G(TA)
          MkGB : G(TB)
        fn useG({t: Tag}, y: G(t)) -> Res = match y
          MkGA() -> MkRes
          MkGB() -> MkRes
        fn handle(r: Tag, w: G(flip(r))) -> Res = with r
          TA() -> useG(w)
          TB() -> useG(w)
      end
      """

      assert idx_verdict(src) == :accept
    end

    test "sibling indexed by a projection of a dependent computation refines" do
      src = """
      mod DependentComputedCore
        type Shape = LeftShape | RightShape | PairShape(Shape, Shape)
        type Pattern indices (shape: Shape)
          LeftPattern : (Nat -> Bool) -> Pattern(LeftShape)
          RightPattern : Pattern(RightShape)
          PairPattern : Pattern(left_shape) -> Pattern(right_shape) -> Pattern(PairShape(left_shape, right_shape))
        type Compilation indices (shape: Shape)
          LeftCompilation : (Nat -> Bool) -> Compilation(LeftShape)
          RightCompilation : Compilation(RightShape)
          PairCompilation : Compilation(left_shape) -> Compilation(right_shape) -> Compilation(PairShape(left_shape, right_shape))
        fn compile({shape: Shape}, pattern: Pattern(shape)) -> Compilation(shape) = match pattern
          LeftPattern(test) -> LeftCompilation(test)
          RightPattern() -> RightCompilation()
          PairPattern(left, right) -> PairCompilation(compile(left), compile(right))
        fn state_count({shape: Shape}, compilation: Compilation(shape)) -> Nat = match compilation
          LeftCompilation(_) -> S(Z())
          RightCompilation() -> Z()
          PairCompilation(_, _) -> Z()
        type Machine indices (state_count: Nat)
          LeftMachine : Machine(S(Z()))
          RightMachine : Machine(Z())
        fn machine({shape: Shape}, compilation: Compilation(shape)) -> Machine(state_count(compilation)) = match compilation
          LeftCompilation(_) -> LeftMachine()
          RightCompilation() -> RightMachine()
          PairCompilation(_, _) -> RightMachine()
        type Path(n: Nat, machine: Machine(n)) indices ()
          MkPath : Path(n, machine)
        type CompilationProof indices (shape: Shape, pattern: Pattern(shape), compilation: Compilation(shape))
          ProvesLeft : (test: (Nat -> Bool)) -> CompilationProof(LeftShape, LeftPattern(test), LeftCompilation(test))
          ProvesRight : CompilationProof(RightShape, RightPattern(), RightCompilation())
          ProvesPair : (left: Pattern(left_shape)) -> (right: Pattern(right_shape)) -> (left_proof: CompilationProof(left_shape, left, compile(left))) -> (right_proof: CompilationProof(right_shape, right, compile(right))) -> CompilationProof(PairShape(left_shape, right_shape), PairPattern(left, right), PairCompilation(compile(left), compile(right)))
      end

      mod DependentComputedIdx
        use DependentComputedCore
        type Denotation indices (shape: Shape, pattern: Pattern(shape))
          DenotesLeft : (test: (Nat -> Bool)) -> Denotation(LeftShape, LeftPattern(test))
          DenotesRight : Denotation(RightShape, RightPattern())
          DenotesPair : (left: Pattern(left_shape)) -> (right: Pattern(right_shape)) -> Denotation(PairShape(left_shape, right_shape), PairPattern(left, right))
        fn consume_left(test: (Nat -> Bool), path: Path(S(Z()), LeftMachine())) -> Denotation(LeftShape, LeftPattern(test)) = match path
          MkPath() -> DenotesLeft(test)
        fn consume_right(path: Path(Z(), RightMachine())) -> Denotation(RightShape, RightPattern()) = match path
          MkPath() -> DenotesRight()
        fn consume_pair({left_shape: Shape}, {right_shape: Shape}, left: Pattern(left_shape), right: Pattern(right_shape), path: Path(Z(), RightMachine())) -> Denotation(PairShape(left_shape, right_shape), PairPattern(left, right)) = match path
          MkPath() -> DenotesPair(left, right)
        fn sound({shape: Shape}, pattern: Pattern(shape), compilation: Compilation(shape), proof: CompilationProof(shape, pattern, compilation), path: Path(state_count(compilation), machine(compilation))) -> Denotation(shape, pattern) = match proof
          ProvesLeft(test) -> consume_left(test, path)
          ProvesRight() -> consume_right(path)
          ProvesPair(left, right, _, _) -> consume_pair(left, right, path)
      end
      """

      assert {:ok, _env} = Program.elaborate(src)
    end
  end
end

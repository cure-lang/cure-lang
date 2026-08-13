defmodule Cure.Elab.SiblingContextRefinementTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.Env

  test "E1: indexed evidence refines a sibling value for nested coverage" do
    source = """
    mod E1
      type Tag = TA | TB
      type Behaviour = BNil | BSend(Tag, Behaviour) | BRecv(Tag, Behaviour)
      type SendsIn indices (b: Behaviour, t: Tag)
        SendHere  : SendsIn(BSend(t, k), t)
        SendSendK : SendsIn(k, t) -> SendsIn(BSend(y, k), t)
      fn witness_head(b: Behaviour, {t: Tag}, s: SendsIn(b, t)) -> Tag = match s
        SendHere()    -> match b
          BSend(y, k) -> y
          BNil()      -> impossible
          BRecv(y, k) -> impossible
        SendSendK(s2) -> match b
          BSend(y, k) -> y
          BNil()      -> impossible
          BRecv(y, k) -> impossible
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "E1/E2: an implication witness refines both sibling bits" do
    source = """
    mod ImpRefine
      type B = F | T
      type Imp indices (a: B, b: B)
        ImpFF : Imp(F, F)
        ImpFT : Imp(F, T)
        ImpTT : Imp(T, T)
      fn f(xa: B, ya: B, i: Imp(xa, ya)) -> B = match i
        ImpFF() -> xa
        ImpFT() -> ya
        ImpTT() -> xa
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a sibling refined by an outer match remains well-scoped in a nested indexed match" do
    source = """
    mod NestedSiblingConvoy
      type Bit = Off | On
      type Item = A | B
      type Bag = Empty | One
      fn bag(bit: Bit) -> Bag = match bit
        Off() -> Empty()
        On() -> One()
      type Member indices (item: Item, bag: Bag)
        HereA : Member(A(), One())
      type Payload indices (item: Item)
        PayloadA : Payload(A())
        PayloadB : Payload(B())
      fn impossible_member({item: Item}, member: Member(item, Empty())) -> Payload(item) = match member
      fn consume(bit: Bit, item: Item, member: Member(item, bag(bit)), payload: Payload(item), _d1: Unit, _d2: Unit, _d3: Unit, _d4: Unit, _d5: Unit) -> Payload(item) = match bit
        Off() -> impossible_member(member)
        On() -> match member
          HereA() -> payload
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "dependent index variables are not duplicated as carried siblings" do
    source = """
    mod DependentIndexSibling
      type Shape = Text | Number
      type Compilation indices (shape: Shape)
        TextCompilation : Compilation(Text())
        NumberCompilation : Compilation(Number())
      type Proof indices (shape: Shape, compilation: Compilation(shape))
        TextProof : Proof(Text(), TextCompilation())
        NumberProof : Proof(Number(), NumberCompilation())
      type Acceptance indices (shape: Shape, compilation: Compilation(shape))
        TextAccepted : Acceptance(Text(), TextCompilation())
        NumberAccepted : Acceptance(Number(), NumberCompilation())
      fn preserve({shape: Shape}, {compilation: Compilation(shape)}, proof: Proof(shape, compilation), acceptance: Acceptance(shape, compilation)) -> Acceptance(shape, compilation) = match proof
        TextProof() -> acceptance
        NumberProof() -> acceptance
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "an erased family index stays erased while constructing an indexed certificate" do
    source = """
    mod IndexedCertificateErasure
      type Shape = Leaf | Pair(Shape, Shape)

      type Pattern indices (shape: Shape)
        LeafPattern : Pattern(Leaf())
        PairPattern : Pattern(left) -> Pattern(right) -> Pattern(Pair(left, right))

      type Compilation indices (shape: Shape)
        LeafCompilation : Compilation(Leaf())
        PairCompilation : Compilation(left) -> Compilation(right) -> Compilation(Pair(left, right))

      fn compile({shape: Shape}, pattern: Pattern(shape)) -> Compilation(shape) = match pattern
        LeafPattern() -> LeafCompilation()
        PairPattern(left, right) -> PairCompilation(compile(left), compile(right))

      type Proof indices (shape: Shape, compilation: Compilation(shape))
        LeafProof : Proof(Leaf(), LeafCompilation())
        PairProof : {@erased left_shape: Shape} -> {@erased right_shape: Shape} -> (left: Compilation(left_shape)) -> (right: Compilation(right_shape)) -> (left_proof: Proof(left_shape, left)) -> (right_proof: Proof(right_shape, right)) -> Proof(Pair(left_shape, right_shape), PairCompilation(left, right))

      type Certified indices (shape: Shape, compilation: Compilation(shape))
        MkCertified : (compilation: Compilation(shape)) -> (proof: Proof(shape, compilation)) -> Certified(shape, compilation)

      fn certify({shape: Shape}, pattern: Pattern(shape)) -> Certified(shape, compile(pattern)) = match pattern
        LeafPattern() -> MkCertified(LeafCompilation(), LeafProof())
        PairPattern(left, right) -> match certify(left)
          MkCertified(left_compilation, left_proof) -> match certify(right)
            MkCertified(right_compilation, right_proof) -> MkCertified(PairCompilation(left_compilation, right_compilation), PairProof(left_compilation, right_compilation, left_proof, right_proof))
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "constructor fields can apply a function whose hidden index is fixed by an earlier field" do
    source = """
    mod ConstructorHiddenIndexApplication
      type Shape = One
      type Compilation indices (shape: Shape)
        OneCompilation : Compilation(One())
      fn compilation_size({shape: Shape}, compilation: Compilation(shape)) -> Nat = 0
      type Witness indices (n: Nat)
        Witnessed : Witness(n)
      type Packed indices (shape: Shape)
        Pack : {packed_shape: Shape} -> (compilation: Compilation(packed_shape)) -> (@erased witness: Witness(compilation_size(compilation))) -> Packed(packed_shape)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "nested pattern lowering preserves contextual impossible branches" do
    source = """
    mod NestedContextualImpossible
      type Marker = Stop | Value
      type Markers = Empty | More(Marker, Markers)
      type Encodes indices (markers: Markers)
        EncodesValue : Encodes(More(Value(), rest))

      fn consume(markers: Markers, @erased proof: Encodes(markers)) -> Unit = match markers
        Empty() -> impossible
        More(Stop(), _) -> impossible
        More(Value(), _) -> match proof
          EncodesValue() -> ()
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "nested constructor refinement keeps an erased dependent sibling erased" do
    source = """
    mod NestedErasedSibling
      type Tag = A | B
      type Marker = MA | MB | MX
      type Markers = Empty | More(Marker, Markers)
      type Encodes indices (tag: Tag, markers: Markers)
        EncodesA : Encodes(A(), More(MA(), tail))
        EncodesB : Encodes(B(), More(MB(), tail))

      fn consume({tag: Tag}, markers: Markers, @erased proof: Encodes(tag, markers)) -> Unit = match markers
        Empty() -> impossible
        More(MA(), _) -> match proof
          EncodesA() -> ()
        More(MB(), _) -> match proof
          EncodesB() -> ()
        More(MX(), _) -> impossible
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "nested indexed certificates preserve hidden telescope positions" do
    source = """
    mod NestedIndexedCertificateTelescope
      type Shape = Character | Text

      type Pattern indices (shape: Shape)
        Predicate : Pattern(Character())
        Group : (inner: Pattern(inner_shape)) -> Pattern(Text())

      type Compilation indices (shape: Shape)
        PredicateCompilation : Compilation(Character())
        GroupCompilation : (inner: Compilation(inner_shape)) -> Compilation(Text())

      fn compile({shape: Shape}, pattern: Pattern(shape)) -> Compilation(shape) = match pattern
        Predicate() -> PredicateCompilation()
        Group(inner) -> GroupCompilation(compile(inner))

      type Path indices (shape: Shape, compilation: Compilation(shape))
        PredicatePath : Path(Character(), PredicateCompilation())

      type Captures indices (shape: Shape, compilation: Compilation(shape), path: Path(shape, compilation))
        CapturesExact : {shape: Shape} -> {compilation: Compilation(shape)} -> {path: Path(shape, compilation)} -> Captures(shape, compilation, path)

      type Marker = Mark

      type Certificate indices (shape: Shape, pattern: Pattern(shape), first: Marker, second: Marker, third: Marker, fourth: Marker, fifth: Marker, path: Path(shape, compile(pattern)))
        Certified : {shape: Shape} -> {pattern: Pattern(shape)} -> {first: Marker} -> {second: Marker} -> {third: Marker} -> {fourth: Marker} -> {fifth: Marker} -> {path: Path(shape, compile(pattern))} -> (captures: Captures(shape, compile(pattern), path)) -> Certificate(shape, pattern, first, second, third, fourth, fifth, path)

      type Completion(shape: Shape, pattern: Pattern(shape), first: Marker, second: Marker, third: Marker, fourth: Marker, fifth: Marker) indices ()
        Completed : (path: Path(shape, compile(pattern))) -> (certificate: Certificate(shape, pattern, first, second, third, fourth, fifth, path)) -> Completion(shape, pattern, first, second, third, fourth, fifth)

      fn retain_computed_local_annotation(
        shape: Shape,
        pattern: Pattern(shape),
        path: Path(shape, compile(pattern))
      ) -> Path(shape, compile(pattern)) =
        let same: Path(shape, compile(pattern)) = path
        same

      type Machine indices (n: Nat)
        MkMachine : {n: Nat} -> (starts: List(Nat)) -> (next: (Nat -> Nat -> List(Nat))) -> Machine(n)

      fn state_count({shape: Shape}, compilation: Compilation(shape)) -> Nat = match compilation
        PredicateCompilation() -> S(Z())
        GroupCompilation(_) -> S(S(Z()))

      fn machine({shape: Shape}, compilation: Compilation(shape)) -> Machine(state_count(compilation)) = match compilation
        PredicateCompilation() -> MkMachine(Nil(), fn(_) -> fn(_) -> Nil())
        GroupCompilation(_) -> MkMachine(Nil(), fn(_) -> fn(_) -> Nil())

      fn group_machine(n: Nat, starts: List(Nat), next: (Nat -> Nat -> List(Nat))) -> Machine(n) =
        MkMachine(starts, next)

      type Embedding indices (n: Nat, grouped: Machine(n))
        Embedded : {n: Nat} -> {grouped: Machine(n)} -> Embedding(n, grouped)

      type Acceptance(n: Nat, accepted_machine: Machine(n)) indices ()
        Accepted : Acceptance(n, accepted_machine)

      type MachineCaptures(n: Nat, accepted_machine: Machine(n), acceptance: Acceptance(n, accepted_machine)) indices ()
        Captured : MachineCaptures(n, accepted_machine, acceptance)

      fn lift(n: Nat, starts: List(Nat), next: (Nat -> Nat -> List(Nat)), acceptance: Acceptance(n, MkMachine(starts, next)), captures: MachineCaptures(n, MkMachine(starts, next), acceptance)) -> Embedding(n, group_machine(n, starts, next)) =
        Embedded()

      fn retain_nested_computed_annotation(
        shape: Shape,
        pattern: Pattern(shape),
        path: Path(shape, compile(pattern)),
        acceptance: Acceptance(state_count(compile(pattern)), machine(compile(pattern))),
        captures: MachineCaptures(state_count(compile(pattern)), machine(compile(pattern)), acceptance)
      ) -> Unit =
        let compilation: Compilation(shape) = compile(pattern)
        let concrete_machine = machine(compilation)
        match concrete_machine
          MkMachine(starts, next) ->
            let lifted: Embedding(state_count(compilation), group_machine(state_count(compilation), starts, next)) = lift(state_count(compilation), starts, next, acceptance, captures)
            ()

      fn consume(
        shape: Shape,
        pattern: Pattern(shape),
        first: Marker,
        second: Marker,
        third: Marker,
        fourth: Marker,
        fifth: Marker,
        completion: Completion(shape, pattern, first, second, third, fourth, fifth)
      ) -> Unit = match completion
        Completed(_, Certified(_)) -> ()

    """

    assert {:ok, tokens} = Lexer.tokenize(source)
    assert {:ok, ast} = Parser.parse(tokens)
    assert {:ok, prepared} = Program.canonical_register_interface(ast, Env.empty())
    assert {:ok, _env} = Program.canonical_check_bodies(prepared)
  end
end

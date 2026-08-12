defmodule Cure.Elab.SiblingContextRefinementTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

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
end

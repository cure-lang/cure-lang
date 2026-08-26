defmodule Cure.Elab.BeamEncodeTest do
  use ExUnit.Case, async: true

  test "an ADT can derive its native BEAM representation" do
    source = """
    mod Cure.BeamDerived
      use Std.Beam

      type Message = Ping | Data(Int) deriving BeamEncode

      fn encode(message: Message) -> BeamTerm = to_beam(message)
      fn ping() -> BeamTerm = encode(Ping())
      fn data(value: Int) -> BeamTerm = encode(Data(value))
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :ping, []) == :Ping
    assert apply(module, :data, [7]) == {:Data, 7}
  end

  test "a hand-written BeamEncode implementation overrides the derived representation" do
    source = """
    mod Cure.BeamOverride
      use Std.Beam

      type Message = Ping | Data(Int)

      implementation BeamEncode for Message
        fn to_beam(message: Message) -> BeamTerm = forget(:wire_message)

      fn encode(message: Message) -> BeamTerm = to_beam(message)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :encode, [:Ping]) == :wire_message
    assert apply(module, :encode, [{:Data, 7}]) == :wire_message
  end

  test "BeamDecode is not fabricated for foreign input" do
    source = """
    mod Cure.NoBeamDecoder
      use Std.Beam
      use Std.Result

      type Message = Ping

      fn decode(term: BeamTerm) -> Result(Message, BeamDecodeError) = from_beam(term)
    """

    assert {:error, error} = Cure.Elab.Program.elaborate(source)
    assert {:no_instance, :BeamDecode, _type} = Cure.Elab.Program.semantic_error(error)
  end

  test "a derived BeamDecode validates constructor tags, arities, and primitive fields" do
    source = """
    mod Cure.BeamDecoded
      use Std.Beam
      use Std.Result

      type Message = Ping | Data(Int) | Pair(Int, Bool) deriving BeamDecode

      fn decode(term: BeamTerm) -> Result(Message, BeamDecodeError) = from_beam(term)
      fn tag(term: BeamTerm) -> Option(Atom) = adt_tag(term)
      fn arity(term: BeamTerm) -> Option(Int) = adt_arity(term)
      fn is_ping(term: BeamTerm) -> Bool = match adt_tag(term)
        Some(value) -> value == :Ping
        None() -> false
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :tag, [:Ping]) == {:some, :Ping}
    assert apply(module, :arity, [:Ping]) == {:some, 0}
    assert apply(module, :is_ping, [:Ping]) == true
    assert apply(module, :decode, [:Ping]) == {:ok, :Ping}
    assert apply(module, :decode, [{:Data, 7}]) == {:ok, {:Data, 7}}
    assert apply(module, :decode, [{:Pair, 7, true}]) == {:ok, {:Pair, 7, true}}
    assert apply(module, :decode, [:Unknown]) == {:error, :InvalidBeamTerm}
    assert apply(module, :decode, [{:Data}]) == {:error, :InvalidBeamTerm}
    assert apply(module, :decode, [{:Data, 7, 8}]) == {:error, :InvalidBeamTerm}
    assert apply(module, :decode, [{:Data, :not_an_integer}]) == {:error, :InvalidBeamTerm}
    assert apply(module, :decode, [{:Pair, 7, :not_a_bool}]) == {:error, :InvalidBeamTerm}
  end

  test "derived BeamDecode recursively validates nested ADT fields" do
    source = """
    mod Cure.NestedBeamDecoded
      use Std.Beam
      use Std.Result

      type Inner = Number(Int) deriving BeamDecode
      type Outer = Empty | Wrap(Inner) deriving BeamDecode

      fn decode(term: BeamTerm) -> Result(Outer, BeamDecodeError) = from_beam(term)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :decode, [{:Wrap, {:Number, 9}}]) == {:ok, {:Wrap, {:Number, 9}}}
    assert apply(module, :decode, [{:Wrap, {:Number, :bad}}]) == {:error, :InvalidBeamTerm}
    assert apply(module, :decode, [{:Wrap, {:Unknown, 9}}]) == {:error, :InvalidBeamTerm}
  end

  test "derived BeamDecode validates recursive ADTs without a runtime schema interpreter" do
    source = """
    mod Cure.RecursiveBeamDecoded
      use Std.Beam
      use Std.Result

      type Tree = Leaf(Int) | Branch(Tree, Tree) deriving BeamDecode

      fn decode(term: BeamTerm) -> Result(Tree, BeamDecodeError) = from_beam(term)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    tree = {:Branch, {:Leaf, 1}, {:Branch, {:Leaf, 2}, {:Leaf, 3}}}
    assert apply(module, :decode, [tree]) == {:ok, tree}

    assert apply(module, :decode, [{:Branch, {:Leaf, 1}, {:Leaf, :bad}}]) ==
             {:error, :InvalidBeamTerm}
  end
end

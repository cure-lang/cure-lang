defmodule Cure.Compiler.NestedConstructorSiblingRefinementTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "a nested constructor refines a later sibling's dependent index" do
    source = """
    mod NestedConstructorSiblingRefinement
      type NonEmpty indices (items: List(Nat))
        Present : (head: Nat) -> (tail: List(Nat)) -> NonEmpty(Cons(head, tail))

      type Payload indices (items: List(Nat))
        PayloadFor : (head: Nat) -> (tail: List(Nat)) -> Payload(Cons(head, tail))

      type Packed indices ()
        Pack : (items: List(Nat)) -> (nonempty: NonEmpty(items)) -> (payload: Payload(items)) -> Packed()

      fn payload_head(head: Nat, tail: List(Nat), payload: Payload(Cons(head, tail))) -> Nat = head

      fn unpack(value: Packed()) -> Nat = match value
        Pack(_, Present(head, tail), payload) -> payload_head(head, tail, payload)
    end
    """

    assert {:ok, _env} = Program.elaborate(source, file: "nested_constructor_sibling_refinement.cure")
  end
end

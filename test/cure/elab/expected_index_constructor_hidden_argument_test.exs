defmodule Cure.Elab.ExpectedIndexConstructorHiddenArgumentTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.Program

  test "a result-index constructor learns a hidden index from an explicit field" do
    source = """
    mod HiddenResultIndex
      type Shape = LeafShape | WrappedShape

      type Pattern indices (shape: Shape)
        LeafPattern : Pattern(LeafShape())
        WrappedPattern : (inner: Pattern(inner_shape)) -> Pattern(WrappedShape())

      type Denotation indices (shape: Shape, pattern: Pattern(shape))
        LeafDenotation : Denotation(LeafShape(), LeafPattern())
        WrappedDenotation : (inner: Pattern(inner_shape)) -> (@erased proof: Denotation(inner_shape, inner)) -> Denotation(WrappedShape(), WrappedPattern(inner))

      fn wrap(
        {inner_shape: Shape},
        inner: Pattern(inner_shape),
        @erased proof: Denotation(inner_shape, inner)
      ) -> Denotation(WrappedShape(), WrappedPattern(inner)) = WrappedDenotation(inner, proof)
    """

    assert {:ok, env} = Program.elaborate(source)
    assert Env.total?(env, :wrap)
  end

  test "field-type fallback preserves an index fixed by an earlier explicit field" do
    source = """
    mod PreservedExplicitIndex
      type Singleton indices (input: List(Nat), item: Nat)
        IsSingleton : (input: List(Nat)) -> (item: Nat) -> (@erased exact: Equivalent(List(Nat), input, Cons(item, Nil()))) -> Singleton(input, item)

      type Witness indices (input: List(Nat))
        Exact : (input: List(Nat)) -> (item: Nat) -> (@erased singleton: Singleton(input, item)) -> Witness(input)

      fn preserve(input: List(Nat), item: Nat, @erased exact: Equivalent(List(Nat), input, Cons(item, Nil()))) -> Witness(input) =
        Exact(input, item, IsSingleton(input, item, exact))
    """

    assert {:ok, env} = Program.elaborate(source)
    assert Env.total?(env, :preserve)
  end
end

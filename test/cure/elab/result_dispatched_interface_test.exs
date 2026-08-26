defmodule Cure.Elab.ResultDispatchedInterfaceTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "a result-dispatched method projects from a rigid constrained dictionary" do
    source = """
    mod ResultDispatchedConstraint
      type Box(t) = Boxed(t)

      interface Decode(t)
        fn decode(value: Int) -> Box(t)

      implementation Decode for Bool
        fn decode(_value: Int) -> Box(Bool) = Boxed(true)

      fn generic(value: Int) -> Box(t) requires Decode(t) =
        assert_type decode(value) : Box(t)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a constrained function can select its dictionary from the expected result" do
    source = """
    mod ResultOnlyConstrainedCall
      type Box(t) = Boxed(t)

      interface Decode(t)
        fn decode(value: Int) -> Box(t)

      implementation Decode for Bool
        fn decode(_value: Int) -> Box(Bool) = Boxed(true)

      fn decode_as(value: Int) -> Box(t) requires Decode(t) =
        assert_type decode(value) : Box(t)

      fn concrete() -> Box(Bool) =
        assert_type decode_as(1) : Box(Bool)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end

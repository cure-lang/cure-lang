defmodule Cure.Elab.SuperinterfaceTest do
  @moduledoc "Phase 2: `interface C(t) requires D(t)` obliges a D instance and scopes D's methods in C's defaults."
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "implementing the sub-interface without the super-interface is rejected" do
    src = """
    mod M
      interface Small(t)
        fn small(a: t) -> Bool
      interface Big(t) requires Small(t)
        fn big(a: t) -> Bool

      type Color = Red | Green | Blue
      implementation Big for Color
        fn big(a: Color) -> Bool = True()
    end
    """

    # `head_key` (Tasks 1.1/1.2) keys the coherence head on the module-qualified
    # type name, so `Color` in `mod M` keys as `:"M#Color"`. Both anon instances
    # key identically, which is why the success path (test below) resolves.
    assert {:error,
            {:missing_superinterface,
             %{
               interface: :Big,
               superinterface: :Small,
               head: :"M#Color",
               for: "Color",
               span: %Cure.Diagnostic.Span{}
             }}} =
             Program.elaborate(src)
  end

  test "providing both instances succeeds" do
    src = """
    mod M
      interface Small(t)
        fn small(a: t) -> Bool
      interface Big(t) requires Small(t)
        fn big(a: t) -> Bool

      type Color = Red | Green | Blue
      implementation Small for Color
        fn small(a: Color) -> Bool = True()
      implementation Big for Color
        fn big(a: Color) -> Bool = True()
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "the super-interface may be implemented AFTER the sub-interface (order-independent)" do
    # `Big for Color` is written textually BEFORE `Small for Color`. The
    # obligation is drained against the FINAL coherence table after the whole
    # registration fold, so the adverse order still elaborates — matching Idris.
    src = """
    mod M
      interface Small(t)
        fn small(a: t) -> Bool
      interface Big(t) requires Small(t)
        fn big(a: t) -> Bool

      type Color = Red | Green | Blue
      implementation Big for Color
        fn big(a: Color) -> Bool = True()
      implementation Small for Color
        fn small(a: Color) -> Bool = True()
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end

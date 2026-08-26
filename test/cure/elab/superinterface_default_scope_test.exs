# test/cure/elab/superinterface_default_scope_test.exs
defmodule Cure.Elab.SuperinterfaceDefaultScopeTest do
  @moduledoc "Phase 2: a sub-interface default body may call a super-interface method."
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "Big's default calls Small's method" do
    src = """
    mod M
      use Std.Bool
      interface Small(t)
        fn small(a: t) -> Bool
      interface Big(t) requires Small(t)
        fn big(a: t) -> Bool
        fn bigger(a: t) -> Bool = small(a)   # default references the superinterface method

      type Color = Red | Green | Blue
      implementation Small for Color
        fn small(a: Color) -> Bool = True()
      implementation Big for Color
        fn big(a: Color) -> Bool = True()
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end

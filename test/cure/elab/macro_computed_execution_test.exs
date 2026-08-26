defmodule Cure.Elab.MacroComputedExecutionTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @good """
  mod M
    use Std.Syntax

    macro Mk
      syntax mk computed by build_it
        example mk expands 0
      explain
        keyword "mk" =>
          "starts with mk"

    fn build_it(input: Syntax) -> Syntax =
      Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(0))

    fn f() -> Int = mk
  """

  @bad """
  mod M
    use Std.Syntax

    macro Bad
      syntax bad computed by build_bad
        example bad expands 0
      explain
        keyword "bad" =>
          "starts with bad"

    fn build_bad(input: Syntax) -> Syntax =
      Leaf(:literal, [KV(:subtype, SAtom(:boolean))], SInt(0))

    fn f() -> Int = bad
  """

  @hole """
  mod M
    use Std.Syntax

    macro Mk
      syntax mk <x: Code> computed by build_it
        example mk 1 expands 0
      explain
        Code =>
          "expects code"
        keyword "mk" =>
          "starts with mk"

    fn build_it(input: Syntax) -> Syntax =
      Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(0))

    fn f(n: Int) -> Int = mk n
  """

  test "a computed-by elab runs at compile time and its output is kernel-checked" do
    assert {:ok, _env} = Program.elaborate(@good)
  end

  test "an ill-typed computed expansion is rejected by ordinary elaboration" do
    assert {:error, reason} = Program.elaborate(@bad)
    assert reason != {:unsupported_expression, :computed_use}
  end

  test "a computed elab receives a reflected input for a hole-bearing rule" do
    assert {:ok, _env} = Program.elaborate(@hole)
  end
end

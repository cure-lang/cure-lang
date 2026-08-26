defmodule Cure.Compiler.WithSiblingDependencyTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  @source """
  mod DepSib
    type Req = A | B
    type Cap1(r: Req) indices ()
      MkC1 : Cap1(r)
    type Cap2(r: Req, c1: Cap1(r)) indices ()
      MkC2 : Cap2(r, c1)
    type Done = D
    fn handle(r: Req, c1: Cap1(r), c2: Cap2(r, c1)) -> Done = with r
      A() -> D
      B() -> D
  end
  """

  test "a refined sibling may depend on another sibling refined by the same with" do
    assert {:ok, _env} = Program.elaborate(@source, file: "dep_sib.cure")
  end

  test "removing the cross-sibling dependency compiles" do
    repaired =
      @source
      |> String.replace("type Cap2(r: Req, c1: Cap1(r))", "type Cap2(r: Req)")
      |> String.replace("Cap2(r, c1)", "Cap2(r)")

    assert {:ok, _env} = Program.elaborate(repaired, file: "dep_sib.cure")
  end
end

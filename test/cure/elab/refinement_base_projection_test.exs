defmodule Cure.Elab.RefinementBaseProjectionTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # A positive natural (a Sigma refinement) used where a base Nat is expected.
  @client """
  mod RefinementBaseClient
    use Std.Nat
    use Std.Proof.Math
    use Std.Refine

    fn underlying(p: PositiveNatural) -> Nat = p
  end
  """

  test "a refined value is usable directly where its base type is expected" do
    assert {:ok, _env} = Program.elaborate(@client)
  end

  @mismatch """
  mod RefinementBaseMismatch
    use Std.Nat
    use Std.Bool
    use Std.Refine
    use Std.Proof.Math

    fn wrong(p: PositiveNatural) -> Bool = p
  end
  """

  test "the coercion does not paper over a genuine type mismatch" do
    assert {:error, _} = Program.elaborate(@mismatch)
  end
end

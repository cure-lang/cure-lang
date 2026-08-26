defmodule Cure.Elab.NestedReturnPolyInferenceTest do
  @moduledoc """
  A return-ONLY lowercase type variable NESTED under a constructor (`List(t)`)
  must be solvable from the caller's expected type. `empty() -> List(t)` has `t`
  appearing only in the return type; calling it where `List(Int)` is expected must
  pin `t := Int` by descending structurally into `List(?t) ~ List(Int)`. Without
  that descent the call previously failed with `{:unsolved_metavariables, ...}`.

  This is kept self-contained (a local `empty`/`use` pair) rather than routed
  through `Std.Map`: parameterizing `Std.Map` to `Map(k, v)` means `keys`/`values`
  now pin their element type from the *argument*, so they no longer exercise the
  return-only-from-expected path this regression guards.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @repro """
  mod P
    fn empty() -> List(t) = []
    fn use() -> List(Int) = empty()
  end
  """

  test "nested return-only type var is solved from the expected type" do
    assert {:ok, _env} = Program.elaborate(@repro)
  end
end

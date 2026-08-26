defmodule Cure.Core.DiagnosticsTest do
  @moduledoc """
  Conversion-failure diagnostic (design spec §10): a type mismatch reports *both*
  normal forms, and those forms are serializable (C2) so a diagnostic renderer —
  or an independent checker — can display or re-check them.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Kernel, Serialize}

  test "checking Int against Bool reports both normal forms" do
    ctx = Context.empty(Builtins.seed(Env.empty()))

    assert {:error, {:conversion_failure, got, want}} =
             Kernel.check(ctx, {:int_lit, 1}, {:vdata, :Bool, []})

    assert got == {:data, :"Std.Int#Int", [], []}
    assert want == {:data, :Bool, [], []}

    # The reported normal forms are serializable (C2), so they can be rendered
    # or re-validated by an independent checker.
    assert Serialize.encode(got) == "(data Std.Int#Int () ())"
    assert Serialize.encode(want) == "(data Bool () ())"
  end
end

defmodule Cure.Elab.ElementShadowingRedTest do
  @moduledoc """
  RED — `elaborate_expr_typed/4` for `{:function_call, meta, args}`
  (`lib/cure/elab/elaborator.ex:727`) intercepts ANY call literally named
  `"element"` whose second argument is a static positive integer literal
  (`element_projection?/1`, `lib/cure/elab/elaborator.ex:1726`) and routes it
  straight to the `Std.Sigma` positional-projection path (`positional_projection/5`)
  — BEFORE ordinary name resolution / `elaborate_named_call/4` ever runs.

  This differs from how the sibling connectives `eq`/`sigma_first` are handled
  (see `test/cure/elab/connective_shadowing_test.exs`): those go through normal
  call resolution and are only inlined post-hoc, keyed off a marker on the
  owning def record, so a user def legitimately shadows them. `element` has no
  such guard — it is checked by NAME alone, ahead of def-registry lookup, so a
  user module that declares its own `fn element(x, i)` and calls `element(5, 2)`
  never reaches that function.

  RED until the `element` intrinsic checks the local def registry (shadowing)
  before forcing the call through the Sigma projection path. Currently this
  module fails to elaborate (or elaborates but the arithmetic def is bypassed)
  because `element(5, 2)` is forced into a positional-projection over the
  integer literal `5`, which is not a telescope/tuple value — a projection
  error, not the user's `x + i`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  @src """
  mod M
    fn element(x: Int, i: Int) -> Int = x + i
    fn t() -> Int = element(5, 2)
  end
  """

  test "a user-defined `element/2` shadows the positional-projection intrinsic" do
    assert {:ok, env} = Program.elaborate(@src)

    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.ElementShadow", functions: [:element, :t])

    assert apply(mod, :t, []) == 7
  end
end

defmodule Cure.Stdlib.TestModuleElaboratesTest do
  @moduledoc """
  `Std.Test` elaborates on the dependent pipeline. Two things had to land:

    * `use Std.Comparable` — `assert_lt`/`assert_gt` compare with `<`/`>`, which
      the elaborator desugars to `Std.Comparable.compare` + an `Ordering` check;
      `compare` and `Ordering` must be in scope (they are not in an auto-prelude).

    * a `where Comparable(t)` constraint on those generic asserts — comparing two
      values of an unconstrained type variable `t` has no `Comparable` instance
      (`{:no_instance, :Comparable, {:rigid, 0}}`); the constraint supplies it,
      exactly as `Std.Core`'s `min`/`max`/`clamp` do.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "Std.Test elaborates on the dependent pipeline" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/test.cure"))
  end
end

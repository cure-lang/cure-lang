defmodule Cure.Stdlib.CoreElaboratesTest do
  @moduledoc """
  `Std.Core` elaborates on the dependent pipeline. It constructs `Result` and
  `Option` values (`Ok`/`Error`/`Some`/`None`) but only imported `Std.Comparable`,
  so the `Result`/`Option` types and their constructors were out of scope
  (`:unknown_global`). Importing `Std.Result` and `Std.Option` brings them in;
  `merge_env` is idempotent and a module's own definition shadows a same-named
  import, so `Std.Core`'s local `ok`/`error`/`some`/… quietly shadow the imported
  ones rather than colliding — its public surface is unchanged.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "Std.Core elaborates on the dependent pipeline" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/core.cure"))
  end
end

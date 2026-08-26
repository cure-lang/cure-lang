defmodule Cure.Stdlib.JsonElaboratesTest do
  @moduledoc """
  `Std.Json` elaborates on the dependent pipeline. Two things had to land first:

    * nested strict positivity in the kernel — `Value`'s `Array(List(Value))`
      nests the family in `List`'s (strictly-positive) parameter; the old
      checker blanket-rejected it (`{:non_strictly_positive, :Arr}`);

    * the `use Std.String` / `use Std.Result` imports — `Value` and the
      encode/decode signatures reference `String` (`= List(Char)`) and
      `Result`, which are not in the auto-prelude.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "Std.Json elaborates on the dependent pipeline" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/json.cure"))
  end
end

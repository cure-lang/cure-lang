defmodule Cure.Stdlib.ImportGraduationTest do
  @moduledoc """
  Several stdlib modules were written for the classic pipeline, where an
  unqualified cross-module name resolves against the global registry with no
  `use` line. The dependent pipeline requires an explicit `use` for every
  module a source references, so these failed to elaborate standalone with a
  bare `:unknown_global` (or an operator that could not be typed until its
  operands' module was in scope).

  Adding the missing imports graduates them onto the dependent pipeline:
    * `Std.Time`     — `Result`/`Ok`/`Error` (`use Std.Result`) and the ISO
      string helpers (`use Std.String`).
    * `Std.NonEmpty` — its `List` conversions (`use Std.List`).
    * `Std.Gen`      — its `List` combinators (`use Std.List`).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  defp elaborates(path), do: Program.elaborate(File.read!(path))

  test "Std.Time elaborates on the dependent pipeline" do
    assert {:ok, _env} = elaborates("lib/std/time.cure")
  end

  test "Std.NonEmpty elaborates on the dependent pipeline" do
    assert {:ok, _env} = elaborates("lib/std/non_empty.cure")
  end

  test "Std.Gen elaborates on the dependent pipeline" do
    assert {:ok, _env} = elaborates("lib/std/gen.cure")
  end
end

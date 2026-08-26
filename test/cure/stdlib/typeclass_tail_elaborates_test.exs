defmodule Cure.Stdlib.TypeclassTailElaboratesTest do
  @moduledoc """
  The #21 typeclass tail — `Std.Equatable`, `Std.Comparable`, `Std.Show` — was
  written against the legacy `proto`/`impl` surface, which the dependent
  elaborator rejects with `{:unsupported_container, :protocol}`. All three are
  migrated to `interface`/`implementation`.

  `Std.Equatable` and `Std.Comparable` now elaborate end-to-end on the dependent
  pipeline (both ride `String = List(Char)` via `use Std.String`).

  `Std.Comparable`'s `Char` instance compares Unicode code points via
  `Std.Char.code_point` (a `Char -> Int` coercion) and Int `<`; its `String`
  instance is lexicographic over `List(Char)` through a top-level
  `compare_string` recursion. `compare` is the only method — the comparison
  *operators* `<`/`>`/`<=`/`>=` are the surface and route through it (a
  non-primitive `a < b` desugars to `compare(a, b) == LessThan()`), so there
  are no `lt`/`le`/`gt`/`ge` named helpers.

  `Std.Show` now elaborates end-to-end on the dependent pipeline too. It was
  blocked on two missing imports — its instance bodies use `<>` (which desugars
  to `Std.Semigroup.combine`) and name `String` (the `List(Char)` alias), so
  both `Std.Semigroup` and `Std.String` must be in scope — plus incoherent FFI
  helpers that returned a `Binary` instead of the `List(Char)` the `-> String`
  signatures promise (`integer_to_binary` → `integer_to_list`, etc.). The
  `:bad_motive` a prior attempt feared no longer arises. Run behaviour is pinned
  in `Cure.Elab.ShowDependentTest`.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  defp elaborates(path) do
    Program.elaborate(File.read!(path))
  end

  test "Std.Equatable elaborates on the dependent pipeline" do
    assert {:ok, _env} = elaborates("lib/std/equatable.cure")
  end

  test "Std.Comparable elaborates on the dependent pipeline (code-point + lexicographic)" do
    assert {:ok, _env} = elaborates("lib/std/comparable.cure")
  end

  test "Std.Show elaborates on the dependent pipeline" do
    assert {:ok, _env} = elaborates("lib/std/show.cure")
  end
end

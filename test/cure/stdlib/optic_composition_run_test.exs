defmodule Cure.Stdlib.OpticCompositionRunTest do
  @moduledoc """
  End-to-end run of `Vector.take`/`drop` and the optic COMPOSITION surface
  (`compose_trav` + the fully kind-polymorphic `compose`), which were deferred
  until the kernel discharged an impossible branch under a *reducible* scrutinee
  index (coverage up to definitional equality — see
  `Cure.Core.CoverageIndexNormalizationTest`).

  Each function is written in real Cure, elaborated through the dependent
  pipeline, emitted, loaded, and executed on the host BEAM, so a regression in
  either the coverage normalization or the cross-module lowering surfaces as a
  wrong runtime answer, not merely a type error.

  The two `bump`/`collect` traversal cases are the load-bearing ones: composing
  two traversals appends their focus vectors (length `plus(m, t)`) and the
  composed rebuilder splits a combined replacement vector back into per-focus
  chunks with `take`/`drop` — the exact shape the coverage fix unblocked.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @src """
  mod M
    use Std.Optic
    use Std.Vector
    use Std.List

    # ---- Vector.take / drop (length-indexed, via `with`) ----
    fn v3() -> Vector(Int, S(S(S(Z())))) = prepend(10, prepend(20, prepend(30, empty())))
    fn take2() -> List(Int) = to_list(Std.Vector.take(S(S(Z())), v3()))
    fn drop2() -> List(Int) = to_list(Std.Vector.drop(S(S(Z())), v3()))

    # ---- composed lens: focus {{x,y},z}.1.1 ----
    # Getters AND setters are written INLINE (`fn(x) -> x.1`): with both `lens`
    # arguments unannotated lambdas, the domain is fixed only by the declared
    # return `Optic(_, _, LensKind)` goal — the case the `.i`-projection fix
    # (goal-seeded implicit solving) unblocked.
    fn outer() -> Optic(Tuple(Tuple(Int, Int), Int), Tuple(Int, Int), LensKind) =
      lens(fn(x) -> x.1, fn(y) -> fn(x) -> %[y, x.2])

    fn inner() -> Optic(Tuple(Int, Int), Int, LensKind) =
      lens(fn(x) -> x.1, fn(y) -> fn(x) -> %[y, x.2])

    fn view_composed() -> Int = view(compose(outer(), inner()), %[%[7, 8], 9])
    fn set_composed() -> Tuple(Tuple(Int, Int), Int) = Std.Optic.set(compose(outer(), inner()), 42, %[%[7, 8], 9])

    # ---- composed traversal: exercises the take/drop rebuild-split ----
    fn idlens() -> Optic(Int, Int, LensKind) = lens(fn(x) -> x, fn(y) -> fn(x) -> y)
    fn idt() -> Optic(Int, Int, TraversalKind) = lens_to_trav(idlens())

    fn both_rebuild(w: Vector(Int, S(S(Z())))) -> Tuple(Int, Int) =
      %[Std.Vector.head(w), Std.Vector.head(Std.Vector.tail(w))]
    fn both_ext(x: Tuple(Int, Int)) -> TravRep(Int, Tuple(Int, Int)) =
      MkTravRep(%[S(S(Z())), %[prepend(x.1, prepend(x.2, empty())), fn(w) -> both_rebuild(w)]])
    fn both() -> Optic(Tuple(Int, Int), Int, TraversalKind) =
      MkTravO(MkTravExt(fn(x) -> both_ext(x)))

    fn collect() -> List(Int) = to_list_of(compose_trav(both(), idt()), %[3, 4])
    fn bump() -> Tuple(Int, Int) = over(compose_trav(both(), idt()), fn(v) -> v + 1, %[3, 4])
  end
  """

  setup_all do
    {:ok, env} = Program.elaborate(@src)

    fns = [
      :v3,
      :take2,
      :drop2,
      :outer,
      :inner,
      :view_composed,
      :set_composed,
      :idlens,
      :idt,
      :both_rebuild,
      :both_ext,
      :both,
      :collect,
      :bump
    ]

    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.Test.OpticComposition", functions: fns)
    {:ok, m: m}
  end

  test "Vector.take keeps the first n elements", %{m: m} do
    assert apply(m, :take2, []) == [10, 20]
  end

  test "Vector.drop discards the first n elements", %{m: m} do
    assert apply(m, :drop2, []) == [30]
  end

  test "compose views through a nested lens", %{m: m} do
    assert apply(m, :view_composed, []) == 7
  end

  test "compose sets through a nested lens, rebuilding both levels", %{m: m} do
    assert apply(m, :set_composed, []) == {{42, 8}, 9}
  end

  test "compose_trav collects every focus across both levels", %{m: m} do
    assert apply(m, :collect, []) == [3, 4]
  end

  test "compose_trav rebuilds via the take/drop split (over +1)", %{m: m} do
    assert apply(m, :bump, []) == {4, 5}
  end
end

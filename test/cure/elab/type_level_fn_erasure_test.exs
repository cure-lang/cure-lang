defmodule Cure.Elab.TypeLevelFnErasureTest do
  @moduledoc """
  A function whose type ends in a universe (`… -> Type`) is a TYPE-LEVEL function:
  a type synonym or type-level computation (e.g. `Std.Optic`'s kind selector
  `Optic(k, s, a)` and its `Lens`/`Affine`/`Traversal` aliases). It has no runtime
  content — its body is a type value like `{:data, LensOptic, …}` that cannot be
  lowered to a BEAM term. The dependent emitter must ERASE such definitions
  entirely (no BEAM function, no export), exactly as Idris/Agda/Lean drop
  type-level functions, while keeping every ordinary value function that merely
  MENTIONS those types in its signature.

  Regression for the codegen crash that blocked shipping `Std.Optic` (spec
  2026-07-11-std-optic-design): a large-elim kind selector emitted as a runtime
  function died with `{:pattern_error, "E074"}`, and a type alias applying it died
  with `{:cannot_emit, {:data, …}}`. The test drives the dependent emitter
  (`Emit.compile_forms/4`) directly — the path `dependent?` modules take.
  """
  use ExUnit.Case, async: false
  alias Cure.Elab.{Emit, Program}

  @src """
  type K = KA | KB
  type LBox(s: Type, a: Type) = MkL(s)
  type RBox(s: Type, a: Type) = MkR(a)
  fn Pick(k: K, s: Type, a: Type) -> Type = match k
    KA() -> LBox(s, a)
    KB() -> RBox(s, a)
  fn Left(s: Type, a: Type) -> Type = Pick(KA, s, a)
  fn make_l(x: Int) -> Left(Int, Bool) = MkL(x)
  fn read_l(w: LBox(Int, Bool)) -> Int = match w
    MkL(y) -> y
  """

  test "type-level (-> Type) functions are erased from emission; value functions remain" do
    {:ok, env} = Program.elaborate("mod TL\n" <> @src <> "end\n")
    names = [:Pick, :Left, :make_l, :read_l]

    {:ok, forms} = Emit.compile_forms(env, :"Cure.TLErase", names, %{})
    exports = for {:function, _l, n, a, _cls} <- forms, do: {n, a}

    # The type-level functions produced NO BEAM function (emit lowercases names).
    refute Keyword.has_key?(exports, :pick)
    refute Keyword.has_key?(exports, :left)
    # The ordinary value functions survive.
    assert Keyword.get(exports, :make_l) == 1
    assert Keyword.get(exports, :read_l) == 1
  end

  test "the surviving value functions load and run through the type-level types" do
    {:ok, mod} =
      Emit.compile_and_load(Program.elaborate("mod TL\n" <> @src <> "end\n") |> elem(1),
        module: :"Cure.TLEraseRun",
        functions: [:make_l, :read_l]
      )

    assert apply(mod, :read_l, [apply(mod, :make_l, [7])]) == 7
  end
end

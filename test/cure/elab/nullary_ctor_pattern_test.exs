defmodule Cure.Elab.NullaryCtorPatternTest do
  @moduledoc """
  A bare capitalized pattern that names a NULLARY constructor is a constructor
  pattern, not a fresh variable binding — `Lt` ≡ `Lt()` (Idris/Agda/Lean: an
  uppercase bare pattern is a nullary constructor). The parser emits
  `{:variable, _, "Lt"}` for a bare identifier (it has no type information), so
  the elaborator must disambiguate against the signature: when the name resolves
  to a nullary constructor of the scrutinee's family, route it to the
  constructor path.

  Before this, `match o | Lt -> … | Eq -> … | Gt -> …` treated each bare arm as
  a wildcard default and failed `{:duplicate_default_pattern, "Eq"}`, forcing the
  ugly `Lt()` / `Eq()` / `Gt()` spelling in patterns.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "bare nullary constructors in patterns are constructor patterns, not wildcards" do
    src = """
    mod M
      type Ord = Lt | Eq | Gt
      fn to_int(o: Ord) -> Int =
        match o
          Lt -> 0
          Eq -> 1
          Gt -> 2
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a lowercase bare pattern is still a wildcard/default binding" do
    src = """
    mod M
      type Ord = Lt | Eq | Gt
      fn is_lt(o: Ord) -> Int =
        match o
          Lt   -> 1
          rest -> 0
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "exhaustive bare nullary match needs no catch-all (all three arms distinct constructors)" do
    # If the bare arms were wildcards, arms 2 and 3 would be unreachable and the
    # match would not be exhaustive over Ord; as constructor patterns it is.
    src = """
    mod M
      type Color = Red | Green | Blue
      fn code(c: Color) -> Int =
        match c
          Red   -> 1
          Green -> 2
          Blue  -> 3
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end

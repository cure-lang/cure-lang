defmodule Cure.Elab.NestedAliasCtorTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # Regression guard for the ctor-at-alias-goal kernel fix (commit 6da5d85) plus
  # the conversion checker's δ-unfolding of a certified `typealias`. A bare
  # constructor / list-literal body checked at a goal whose (possibly NESTED)
  # element type is a `typealias` to a data family must δ-unfold that alias to
  # see the family before it can solve the constructor's parameters — otherwise
  # the element falls to inference mode and the kernel rejects the bare `List`
  # constructor with `:ctor_requires_checking_mode`.
  #
  # NOTE: the alias names here are deliberately NOT `S` or `String`. A `typealias`
  # named `S` collides with `Std.Nat`'s successor constructor `S`, and any name
  # that clashes with an in-scope constructor is a *separate shadowing* concern —
  # not a δ-unfold gap. Char/String/Text-style names (the value-surface work) do
  # not collide and exercise the real path.

  test "top-level: list literal at `Row` where Row = List(Int)" do
    src = """
    mod NA
      typealias Row = List(Int)
      fn f() -> Row = [1, 2]
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.NA", functions: [:f])
    assert apply(m, :f, []) == [1, 2]
  end

  test "nested: list-of-lists at List(Row) where Row = List(Int)" do
    src = """
    mod NA
      typealias Row = List(Int)
      fn f() -> List(Row) = [[1, 2], [3]]
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.NA", functions: [:f])
    assert apply(m, :f, []) == [[1, 2], [3]]
  end

  test "conv both directions: List(Row) <-> List(List(Int)) through a call" do
    fwd = """
    mod NA
      typealias Row = List(Int)
      fn mk() -> List(List(Int)) = [[1, 2]]
      fn f() -> List(Row) = mk()
    end
    """

    rev = """
    mod NA
      typealias Row = List(Int)
      fn mk() -> List(Row) = [[1, 2]]
      fn f() -> List(List(Int)) = mk()
    end
    """

    assert {:ok, _} = Program.elaborate(fwd)
    assert {:ok, _} = Program.elaborate(rev)
  end

  # Two alias levels under an outer family: the outer `List` sees `CodePoints`,
  # which unfolds to `List(CodePoint)`, whose own parameter unfolds again before
  # the innermost literals are checked.
  #
  # This used to be spelled `String = List(Char)` with `["hi", "yo"]`. That
  # equation is gone — `String` is its own nominal record, so a string literal
  # placed at `List(Char)` now fails on `ExpressibleByStringLiteral`, and the
  # local alias named `String` collides with the ambient constructor besides.
  # The innermost alias is a plain `Int`, not a `Bounded(n)`: bounded literals in
  # list-element position have their own unrelated gap.
  test "nested: lists of literals under two alias levels" do
    src = """
    mod NA
      typealias Count = Int
      typealias Counts = List(Count)
      fn f() -> List(Counts) = [[104, 105], [121, 111]]
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.NA", functions: [:f])
    assert apply(m, :f, []) == [[?h, ?i], [?y, ?o]]
  end
end

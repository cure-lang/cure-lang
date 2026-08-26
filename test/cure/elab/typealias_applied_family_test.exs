defmodule Cure.Elab.TypealiasAppliedFamilyTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # A `typealias` to an APPLIED data family (`List(Int)`, `String = List(Char)`)
  # used as a function's return type must drive checking mode for a bare-ctor body
  # (a list literal), exactly as the un-aliased `List(Int)` annotation does. The
  # checked-ctor bidirectional path solves the family/params from the expected
  # type, which it must δ-unfold through the alias first — otherwise the list
  # literal falls to inference mode and the kernel rejects the bare `List`
  # constructor with `:ctor_requires_checking_mode`.
  test "list literal checks against a typealias to List(Int)" do
    src = """
    mod TA
      typealias Ints = List(Int)
      fn f() -> Ints = [1, 2, 3]
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.TA", functions: [:f])
    assert apply(m, :f, []) == [1, 2, 3]
  end

  # A chain of aliases has to unfold all the way down, not one step: the outer
  # alias yields `List(CodePoint)`, whose parameter is itself an alias the
  # element literals are checked against.
  #
  # This used to be spelled `String = List(Char)` with a `"hi"` body. That
  # equation is gone — `String` is its own nominal record now, and a string
  # literal is placed by `ExpressibleByStringLiteral`, which `List` does not
  # implement — so spelling it that way tested literal-protocol resolution
  # rather than alias unfolding. The element alias is deliberately a plain `Int`
  # and not a `Bounded(n)`: bounded literals in list-element position have their
  # own unrelated gap, which would mask what this test is asking about.
  test "a chain of typealiases unfolds all the way before checking" do
    src = """
    mod TA
      typealias Count = Int
      typealias Counts = List(Count)
      fn f() -> Counts = [104, 105]
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.TA", functions: [:f])
    assert apply(m, :f, []) == [104, 105]
  end

  test "a parameterized typealias unfolds every argument before checking" do
    src = """
    mod TA
      typealias First(a, b) = a
      fn f(x: First(Int, Bool)) -> Int = x
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.TwoArgAlias", functions: [:f])
    assert apply(m, :f, [41]) == 41
  end
end

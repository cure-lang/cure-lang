defmodule Cure.Stdlib.DataSuffixTest do
  @moduledoc """
  The strict-suffix relation underlying `Std.Parse`: `Same` proves an unchanged
  remainder, while `Drop` changes the strictness index to `True` and extends the
  original input by exactly one head.
  """

  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @foundation """
    use Std.Bool
    use Std.List

    type Consumed(a: Type) indices (strict: Bool, rem: List(a), orig: List(a))
      Same : (xs: List(a)) -> Consumed(a, False, xs, xs)
      Drop : (head: a) -> Consumed(a, strict, rem, orig) -> Consumed(a, out, rem, Cons(head, orig))

    type Step(t: Type, e: Type, a: Type) indices (strict: Bool, orig: List(t))
      Succ : (value: a) -> (rest: List(t)) -> Consumed(t, strict, rest, orig) -> Step(t, e, a, strict, orig)
      Fail : (error: e) -> Step(t, e, a, strict, orig)

    type Acc(t: Type) indices (orig: List(t))
      MkAcc : (descend: ((rest: List(t)) -> Consumed(t, True, rest, orig) -> Acc(t, rest))) -> Acc(t, orig)

    fn drop({a: Type}, {strict: Bool}, {rem: List(a)}, {orig: List(a)}, head: a, proof: Consumed(a, strict, rem, orig)) -> Consumed(a, True, rem, Cons(head, orig)) =
      Drop(head, proof)

    fn trans({a: Type}, {left: Bool}, {right: Bool}, {orig: List(a)}, {mid: List(a)}, {rem: List(a)}, first: Consumed(a, left, mid, orig), second: Consumed(a, right, rem, mid)) -> Consumed(a, `or`(left, right), rem, orig) =
      match first
        Same(_) -> second
        Drop(head, previous) -> Drop(head, trans(previous, second))
  """

  defp verdict(definitions) do
    case Program.elaborate("mod SuffixProbe\n#{@foundation}#{definitions}\nend\n") do
      {:ok, _env} -> :accept
      {:error, _reason} -> :reject
    end
  end

  test "Same proves that the remainder is the original input" do
    assert verdict("fn p({a: Type}, xs: List(a)) -> Consumed(a, False, xs, xs) = Same(xs)") == :accept
  end

  test "Drop proves a strict suffix after discarding one head" do
    definition = """
      fn p({a: Type}, head: a, tail: List(a)) -> Consumed(a, True, tail, Cons(head, tail)) =
        Drop(head, Same(tail))
    """

    assert verdict(definition) == :accept
  end

  test "Same cannot fabricate a strict-consumption witness" do
    assert verdict("fn bad({a: Type}, xs: List(a)) -> Consumed(a, True, xs, xs) = Same(xs)") == :reject
  end

  test "Drop cannot claim an unrelated remainder" do
    definition = """
      fn bad({a: Type}, x: a, ys: List(a), zs: List(a)) -> Consumed(a, True, zs, Cons(x, ys)) =
        Drop(x, Same(ys))
    """

    assert verdict(definition) == :reject
  end

  test "trans composes two strict drops and preserves the final remainder" do
    definition = """
      fn p({a: Type}, x: a, y: a, tail: List(a)) -> Consumed(a, True, tail, Cons(x, Cons(y, tail))) =
        trans(drop(x, Same(Cons(y, tail))), drop(y, Same(tail)))
    """

    assert verdict(definition) == :accept
  end

  test "trans with Same on the left preserves the second proof's strictness" do
    definition = """
      fn p({a: Type}, x: a, tail: List(a)) -> Consumed(a, True, tail, Cons(x, tail)) =
        trans(Same(Cons(x, tail)), drop(x, Same(tail)))
    """

    assert verdict(definition) == :accept
  end

  test "False carries no guarantee and admits a proper suffix" do
    definition = """
      fn p({a: Type}, head: a, tail: List(a)) -> Consumed(a, False, tail, Cons(head, tail)) =
        Drop(head, Same(tail))
    """

    assert verdict(definition) == :accept
  end

  test "Succ retains the exact dependent remainder proof" do
    definition = """
      fn p({t: Type}, {e: Type}, {a: Type}, value: a, head: t, tail: List(t)) -> Step(t, e, a, True, Cons(head, tail)) =
        Succ(value, tail, Drop(head, Same(tail)))
    """

    assert verdict(definition) == :accept
  end

  test "Succ rejects a proof about a different remainder" do
    definition = """
      fn bad({t: Type}, {e: Type}, {a: Type}, value: a, head: t, tail: List(t), other: List(t)) -> Step(t, e, a, True, Cons(head, tail)) =
        Succ(value, other, Drop(head, Same(tail)))
    """

    assert verdict(definition) == :reject
  end

  test "Fail is polymorphic in strictness and original input" do
    definition = """
      fn p({t: Type}, {e: Type}, {a: Type}, error: e, input: List(t)) -> Step(t, e, a, True, input) =
        Fail(error)
    """

    assert verdict(definition) == :accept
  end
end

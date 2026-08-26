defmodule Cure.Core.PrinterTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Printer

  test "renders base types and literals" do
    assert Printer.print({:type, 0}) == "Type"
    assert Printer.print({:type, 2}) == "Type2"
    assert Printer.print({:int_type}) == "Int"
    assert Printer.print({:int_lit, -3}) == "-3"
    assert Printer.print({:atom_lit, :ok}) == ":ok"
    assert Printer.print({:binary_type}) == "Binary"
    assert Printer.print({:absurd}) == "absurd"
    assert Printer.print({:hole, "goal"}) == "?goal"
  end

  test "renders a non-dependent arrow without naming the binder" do
    # Int -> Int   (cod does not mention var 0)
    assert Printer.print({:pi, :unrestricted, {:int_type}, {:int_type}}) == "Int -> Int"
  end

  test "renders a type parameter as an implicit forall" do
    # (a : Type) -> List(a) -> Int   ==>  ∀ {a}. List(a) -> Int
    ty =
      {:pi, :unrestricted, {:type, 0}, {:pi, :unrestricted, {:data, :List, [{:var, 0}], []}, {:int_type}}}

    assert Printer.print(ty) == "∀ {a}. List(a) -> Int"
  end

  test "a non-dependent arrow still shifts indices for the binders around it" do
    # ∀ {a}. Int -> a
    #
    # The inner Pi binds a variable its codomain never uses, but omitting the
    # placeholder onto `names` misaligns every outer index by one. Verified
    # against the real implementation: dropping the `["_" | names]` push here
    # renders this as "∀ {a}. Int -> ?1" instead of "∀ {a}. Int -> a" — wrong,
    # and every other test in this file passes either way, because none of
    # them nest a non-dependent arrow inside a binder whose variable survives
    # past it.
    ty = {:pi, :unrestricted, {:type, 0}, {:pi, :unrestricted, {:int_type}, {:var, 1}}}
    assert Printer.print(ty) == "∀ {a}. Int -> a"
  end

  test "renders a dependent arrow with a named binder" do
    # (a : Int) -> Vec(a)
    ty = {:pi, :unrestricted, {:int_type}, {:data, :Vec, [{:var, 0}], []}}
    assert Printer.print(ty) == "(a : Int) -> Vec(a)"
  end

  test "flattens application spines" do
    t = {:app, {:app, {:global, :f}, {:int_lit, 1}}, {:int_lit, 2}}
    assert Printer.print(t) == "f 1 2"
  end

  test "renders let and lambda binders" do
    assert Printer.print({:lam, :unrestricted, {:int_type}, {:var, 0}}) == "\\a. a"

    assert Printer.print({:let, :unrestricted, {:int_type}, {:int_lit, 1}, {:var, 0}}) ==
             "let a : Int = 1 in a"
  end

  test "nested case branches do not reuse binder names" do
    # A case branch synthesised binders `x0, x1, …` without consulting the names
    # already in scope, so a case nested in a case printed the inner branch's
    # binders with the SAME labels as the outer — visually merging four distinct
    # de Bruijn indices into two. Here the outer Cons binds two vars, and its
    # body is another case that also binds two; the four labels must be distinct.
    inner = {:case, {:var, 0}, {:type, 0}, [{:Cons, 2, {:var, 1}}]}
    outer = {:case, {:global, :s}, {:type, 0}, [{:Cons, 2, inner}]}

    text = Printer.print(outer)
    labels = Regex.scan(~r/\b(x\d+|[a-z]\d*)\b/, text) |> Enum.map(&List.first/1)
    # The two Cons branches must not both introduce `x0`/`x1`.
    binder_labels = Enum.filter(labels, &String.starts_with?(&1, "x"))
    assert binder_labels == Enum.uniq(binder_labels), "case binders collide: #{text}"
  end

  test "raises on an unknown node rather than printing garbage" do
    assert_raise ArgumentError, ~r/unknown Core term/, fn ->
      Printer.print({:bogus, 1})
    end
  end
end

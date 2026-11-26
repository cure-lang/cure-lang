defmodule Cure.Core.Phase5BoundedReadbackTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Quote}

  test "First retains its symbolic bound through evaluation and readback" do
    term = {:ctor, :"Std.Bounded#First", [{:var, 0}]}
    env = [{:vneutral, {:nvar, 0}}]

    assert {:vctor, :"Std.Bounded#First", [vneutral: {:nvar, 0}]} = Eval.eval(term, env)
    assert ^term = term |> Eval.eval(env) |> Quote.reify(1)
  end

  test "Next retains both a symbolic bound and its predecessor" do
    term =
      {:ctor, :"Std.Bounded#Next", [{:ctor, :"Std.Nat#S", [{:var, 0}]}, {:ctor, :"Std.Bounded#First", [{:var, 0}]}]}

    env = [{:vneutral, {:nvar, 0}}]

    assert {:vctor, :"Std.Bounded#Next", [_, {:vctor, :"Std.Bounded#First", [_]}]} =
             Eval.eval(term, env)

    assert ^term = term |> Eval.eval(env) |> Quote.reify(1)
  end

  test "Next with a compact predecessor still retains its symbolic bound" do
    term = {:ctor, :"Std.Bounded#Next", [{:var, 0}, {:bounded_lit, 0}]}
    env = [{:vneutral, {:nvar, 0}}]

    assert {:vctor, :"Std.Bounded#Next", [vneutral: {:nvar, 0}, vbounded: 0]} =
             Eval.eval(term, env)

    assert ^term = term |> Eval.eval(env) |> Quote.reify(1)
  end

  test "readback uses the caller's depth rather than retaining the original index" do
    term = {:ctor, :"Std.Bounded#First", [{:var, 0}]}
    value = Eval.eval(term, [{:vneutral, {:nvar, 0}}])

    assert {:ctor, :"Std.Bounded#First", [{:var, 2}]} = Quote.reify(value, 3)
  end

  test "substitution of a concrete bound permits compact representation" do
    first = {:ctor, :"Std.Bounded#First", [{:var, 0}]}
    next = {:ctor, :"Std.Bounded#Next", [{:var, 0}, {:bounded_lit, 0}]}

    assert {:vbounded, 0} = Eval.eval(first, [{:vnat, 2}])
    assert {:vbounded, 1} = Eval.eval(next, [{:vnat, 2}])
    assert {:bounded_lit, 0} = first |> Eval.eval([{:vnat, 2}]) |> Quote.reify(0)
  end

  test "a noncanonical constructor owner is not treated as a builtin" do
    term = {:ctor, :"Other#First", [{:nat_lit, 0}]}

    assert {:vctor, :"Other#First", [vnat: 0]} = Eval.eval(term, [])
    assert ^term = term |> Eval.eval([]) |> Quote.reify(0)
  end
end

defmodule Cure.Compiler.DependentVecCodegenTest do
  @moduledoc """
  End-to-end Cure-language coverage for the currently supported length-indexed
  vector fragment: parse real `.cure` source, elaborate through the dependent
  kernel, erase indices, emit BEAM, and execute the result.
  """
  use ExUnit.Case, async: false

  @src """
  mod VecCg
    type Nat = Z | S(Nat)
    type Vector(a: Type) indices (n: Nat)
      empty : Vector(a, Z)
      prepend : a -> Vector(a, n) -> Vector(a, S(n))
    fn plus(m: Nat, n: Nat) -> Nat = match m
      Z() -> n
      S(k) -> S(plus(k, n))
    fn append({a: Type}, {m: Nat}, {n: Nat}, xs: Vector(a, m), ys: Vector(a, n)) -> Vector(a, plus(m, n)) = match xs
      empty() -> ys
      prepend(x, rest) -> prepend(x, append(rest, ys))
  end
  """

  test "length-indexed Vector append compiles and runs after erasure" do
    assert {:ok, mod} = Cure.Compiler.compile_and_load(@src, emit_events: false)
    assert mod == :"Cure.VecCg"

    xs = {:prepend, 1, {:prepend, 2, :empty}}
    ys = {:prepend, 3, :empty}

    assert apply(mod, :plus, [:Z, {:S, :Z}]) == {:S, :Z}
    assert apply(mod, :plus, [{:S, :Z}, {:S, :Z}]) == {:S, {:S, :Z}}
    assert apply(mod, :append, [:empty, ys]) == ys
    assert apply(mod, :append, [xs, ys]) == {:prepend, 1, {:prepend, 2, {:prepend, 3, :empty}}}
  end

  test "bad Vector append is rejected through the real compiler path" do
    bad =
      String.replace(
        @src,
        "prepend(x, rest) -> prepend(x, append(rest, ys))",
        "prepend(x, rest) -> rest"
      )

    assert {:error, _reason} = Cure.Compiler.compile_and_load(bad, emit_events: false)
  end

  # Under C1 the canonical stdlib is loaded and STICKY at suite startup
  # (test/test_helper.exs), compiled from these very sources through this same
  # `Cure.Compiler.compile_and_load` path by `mix cure.compile_stdlib`. Re-compiling
  # `lib/std/vector.cure` (and its Nat/Bounded deps) here would try to load over the
  # sticky `Cure.Std.Vector` slot and fail with `:sticky_directory`. The full
  # compiler path on a length-indexed vector is already proven by the first test
  # (inline `VecCg`); this test's distinct claim is the REAL stdlib `Std.Vector`'s
  # post-erasure runtime surface, which the sticky canonical embodies exactly. So
  # resolve the canonical modules directly rather than re-emitting them.
  test "Std.Vector is the length-indexed Vector module and runs after erasure" do
    assert {:module, nat} = :code.ensure_loaded(:"Cure.Std.Nat")
    assert function_exported?(nat, :plus, 2)

    assert {:module, _bounded} = :code.ensure_loaded(:"Cure.Std.Bounded")

    assert {:module, mod} = :code.ensure_loaded(:"Cure.Std.Vector")
    refute function_exported?(mod, :plus, 2)

    xs = {:prepend, 1, {:prepend, 2, :empty}}
    ys = {:prepend, 3, :empty}

    assert apply(mod, :append, [:empty, ys]) == ys
    assert apply(mod, :append, [xs, ys]) == {:prepend, 1, {:prepend, 2, {:prepend, 3, :empty}}}
    assert apply(mod, :singleton, [9]) == {:prepend, 9, :empty}
    assert apply(mod, :replicate, [2, 7]) == {:prepend, 7, {:prepend, 7, :empty}}
    assert apply(mod, :is_empty, [:empty]) == true
    assert apply(mod, :is_empty, [xs]) == false
    assert apply(mod, :head, [xs]) == 1
    assert apply(mod, :tail, [xs]) == {:prepend, 2, :empty}
    # `Bounded(n)` (the `index` type) is now a registered `@builtin(:bounded)`
    # family, so its `First`/`Next` values erase to compact integers exactly like
    # Nat's Z/S — `First` is 0, `Next(First)` is 1. (Before Bounded's builtin
    # registration these were the generic `:First` / `{:Next, :First}` atom-tuple
    # forms.) The behaviour — and every expected result below — is unchanged.
    assert apply(mod, :lookup, [xs, 0]) == 1
    assert apply(mod, :lookup, [xs, 1]) == 2

    assert apply(mod, :update, [xs, 1, fn x -> x + 100 end]) ==
             {:prepend, 1, {:prepend, 102, :empty}}

    assert apply(mod, :set, [xs, 0, 9]) == {:prepend, 9, {:prepend, 2, :empty}}
    assert apply(mod, :map, [xs, fn x -> x * 10 end]) == {:prepend, 10, {:prepend, 20, :empty}}

    assert apply(mod, :zip_with, [xs, {:prepend, 10, {:prepend, 20, :empty}}, fn x -> fn y -> x + y end end]) ==
             {:prepend, 11, {:prepend, 22, :empty}}

    assert apply(mod, :count, [xs]) == 2
    assert apply(mod, :length, [xs]) == 2
    assert apply(mod, :any, [xs, fn x -> x == 2 end]) == true
    assert apply(mod, :all, [xs, fn x -> x > 0 end]) == true
  end
end

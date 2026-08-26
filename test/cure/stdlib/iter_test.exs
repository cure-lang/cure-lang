defmodule Cure.Stdlib.IterTest do
  use ExUnit.Case, async: true

  # `Cure.Std.Iter` is loaded dynamically by `Cure.Stdlib.Preload` in
  # `setup_all` below; Elixir's compile-time checker doesn't see it,
  # so silence the otherwise correct "module not available" warnings.
  @compile {:no_warn_undefined, :"Cure.Std.Iter"}

  @iter :"Cure.Std.Iter"

  setup_all do
    Cure.Stdlib.Preload.preload(examples: false, kind: :all)
    :ok
  end

  # -- Helpers ---------------------------------------------------------------

  # `Std.Iter.fold` and friends expect a curried `elem -> acc -> acc`.
  defp curry2(f), do: fn a -> fn b -> f.(a, b) end end

  # `Std.Iter.zip_with` expects a curried `a -> b -> c`.
  defp curry_zip(f), do: fn a -> fn b -> f.(a, b) end end

  describe "Std.Iter -- constructors" do
    test "from_list + to_list is the identity" do
      it = @iter.from_list([1, 2, 3, 4])
      assert @iter.to_list(it) == [1, 2, 3, 4]
    end

    test "lazy/1 is an alias for from_list/1" do
      assert @iter.to_list(@iter.lazy([10, 20, 30])) == [10, 20, 30]
      assert @iter.to_list(@iter.lazy([])) == []
    end

    test "range enumerates inclusively" do
      it = @iter.range(1, 5)
      assert @iter.to_list(it) == [1, 2, 3, 4, 5]
    end

    test "range with lo > hi is empty" do
      assert @iter.to_list(@iter.range(5, 1)) == []
    end

    test "empty iterator is empty" do
      it = @iter.empty()
      assert @iter.to_list(it) == []
    end

    test "iterate produces an infinite stream sliced by take" do
      inc = fn x -> x + 1 end
      it = @iter.iterate(0, inc)
      assert @iter.take(it, 5) == [0, 1, 2, 3, 4]
    end

    test "unfold supports the Fibonacci recurrence" do
      # f({a, b}) -> Some(Emit(a, %[b, a + b]))
      # Option `Some/None` erase to OTP tags (`{:some, _}` / `:none`); Iter's own
      # `Emit` ctor keeps its declared PascalCase tag (`{:Emit, _, _}`).
      fib_step = fn {a, b} -> {:some, {:Emit, a, {b, a + b}}} end
      it = @iter.unfold({0, 1}, fib_step)
      assert @iter.take(it, 8) == [0, 1, 1, 2, 3, 5, 8, 13]
    end

    test "unfold terminates on None" do
      # Walk a counter down to zero, emitting each value.
      step = fn
        0 -> :none
        n -> {:some, {:Emit, n, n - 1}}
      end

      it = @iter.unfold(3, step)
      assert @iter.to_list(it) == [3, 2, 1]
    end

    test "repeat is an infinite stream of one value" do
      it = @iter.repeat(:x)
      assert @iter.take(it, 4) == [:x, :x, :x, :x]
    end

    test "cycle walks a list repeatedly" do
      it = @iter.cycle([1, 2, 3])
      assert @iter.take(it, 7) == [1, 2, 3, 1, 2, 3, 1]
    end

    test "cycle of empty list collapses to empty" do
      it = @iter.cycle([])
      assert @iter.to_list(it) == []
    end
  end

  describe "Std.Iter -- transformers" do
    test "map applies f lazily" do
      it = @iter.from_list([1, 2, 3])
      mapped = @iter.map(it, fn x -> x * x end)
      assert @iter.to_list(mapped) == [1, 4, 9]
    end

    test "filter keeps passing elements" do
      it = @iter.range(1, 10)
      evens = @iter.filter(it, fn x -> rem(x, 2) == 0 end)
      assert @iter.to_list(evens) == [2, 4, 6, 8, 10]
    end

    test "filter on a fully-failing predicate produces empty" do
      it = @iter.range(1, 5)
      none = @iter.filter(it, fn _ -> false end)
      assert @iter.to_list(none) == []
    end

    test "concat joins two iterators" do
      a = @iter.range(1, 3)
      b = @iter.from_list([10, 20])
      assert @iter.to_list(@iter.concat(a, b)) == [1, 2, 3, 10, 20]
    end

    test "concat with an empty left side returns the right side" do
      assert @iter.to_list(@iter.concat(@iter.empty(), @iter.range(1, 3))) ==
               [1, 2, 3]
    end

    test "flat_map flattens one level" do
      it = @iter.from_list([1, 2, 3])
      expand = fn n -> @iter.range(1, n) end

      assert @iter.to_list(@iter.flat_map(it, expand)) ==
               [1, 1, 2, 1, 2, 3]
    end

    test "zip_with stops at the shorter side" do
      a = @iter.range(1, 5)
      b = @iter.from_list([:a, :b, :c])
      pair = curry_zip(fn x, y -> {x, y} end)

      assert @iter.to_list(@iter.zip_with(a, b, pair)) ==
               [{1, :a}, {2, :b}, {3, :c}]
    end

    test "intersperse inserts a separator between elements" do
      it = @iter.from_list([1, 2, 3])
      assert @iter.to_list(@iter.intersperse(it, 0)) == [1, 0, 2, 0, 3]
    end

    test "intersperse on a single-element iterator is a no-op" do
      it = @iter.from_list([42])
      assert @iter.to_list(@iter.intersperse(it, 0)) == [42]
    end

    test "intersperse on the empty iterator is empty" do
      assert @iter.to_list(@iter.intersperse(@iter.empty(), 0)) == []
    end
  end

  describe "Std.Iter -- slicers" do
    test "take stops early without forcing the tail" do
      it = @iter.range(1, 10_000_000)
      assert @iter.take(it, 3) == [1, 2, 3]
    end

    test "take_while yields the leading prefix" do
      it = @iter.range(1, 100)
      lt5 = fn x -> x < 5 end
      assert @iter.to_list(@iter.take_while(it, lt5)) == [1, 2, 3, 4]
    end

    test "take_while on a non-matching head returns empty" do
      it = @iter.range(10, 20)
      lt5 = fn x -> x < 5 end
      assert @iter.to_list(@iter.take_while(it, lt5)) == []
    end

    test "drop skips the first n elements" do
      it = @iter.range(1, 5)
      assert @iter.to_list(@iter.drop(it, 2)) == [3, 4, 5]
    end

    test "drop with non-positive n is a no-op" do
      it = @iter.range(1, 3)
      assert @iter.to_list(@iter.drop(it, 0)) == [1, 2, 3]
      assert @iter.to_list(@iter.drop(@iter.range(1, 3), -5)) == [1, 2, 3]
    end

    test "drop past the end is empty" do
      it = @iter.range(1, 3)
      assert @iter.to_list(@iter.drop(it, 100)) == []
    end

    test "drop_while skips the leading prefix that satisfies pred" do
      it = @iter.range(1, 6)
      lt4 = fn x -> x < 4 end
      assert @iter.to_list(@iter.drop_while(it, lt4)) == [4, 5, 6]
    end

    test "drop_while on a fully-passing predicate is empty" do
      it = @iter.range(1, 5)
      assert @iter.to_list(@iter.drop_while(it, fn _ -> true end)) == []
    end
  end

  describe "Std.Iter -- consumers" do
    test "fold sums a range" do
      it = @iter.range(1, 5)
      add = fn x -> fn acc -> x + acc end end
      assert @iter.fold(it, 0, add) == 15
    end

    test "to_list materialises a finite iterator" do
      assert @iter.to_list(@iter.range(1, 4)) == [1, 2, 3, 4]
    end

    test "each runs f for every element and returns Done" do
      Process.put(:iter_each_acc, [])

      f = fn x ->
        Process.put(:iter_each_acc, [x | Process.get(:iter_each_acc)])
        :ok
      end

      assert @iter.each(@iter.from_list([1, 2, 3]), f) == :Done
      assert Process.get(:iter_each_acc) == [3, 2, 1]
    after
      Process.delete(:iter_each_acc)
    end

    test "count returns the number of matching elements" do
      it = @iter.range(1, 10)
      even? = fn x -> rem(x, 2) == 0 end
      assert @iter.count(it, even?) == 5
    end

    test "count on the empty iterator is 0" do
      assert @iter.count(@iter.empty(), fn _ -> true end) == 0
    end

    test "any returns true when at least one element matches" do
      it = @iter.range(1, 5)
      assert @iter.any(it, fn x -> x == 3 end) == true
      assert @iter.any(@iter.range(1, 5), fn x -> x > 100 end) == false
    end

    test "all returns true only when every element matches" do
      it = @iter.range(2, 6)
      assert @iter.all(it, fn x -> x > 1 end) == true
      assert @iter.all(@iter.range(2, 6), fn x -> x > 3 end) == false
    end

    test "all on empty is vacuously true" do
      assert @iter.all(@iter.empty(), fn _ -> false end) == true
    end

    test "find returns the first matching element" do
      it = @iter.range(1, 10)
      assert @iter.find(it, fn x -> x > 4 end, -1) == 5
    end

    test "find returns the default when nothing matches" do
      it = @iter.range(1, 5)
      assert @iter.find(it, fn x -> x > 100 end, -1) == -1
    end
  end

  describe "Std.Iter -- lazy pipeline (the headline use case)" do
    test "filter + map + take over an infinite producer" do
      # An infinite range of integers starting at 0.
      inc = fn x -> x + 1 end
      naturals = @iter.iterate(0, inc)

      # Squares of the first five even integers.
      result =
        naturals
        |> @iter.filter(fn x -> rem(x, 2) == 0 end)
        |> @iter.map(fn x -> x * x end)
        |> @iter.take(5)

      assert result == [0, 4, 16, 36, 64]
    end

    test "lazy/1 + map + filter + take_while + to_list reads left to right" do
      result =
        Enum.to_list(1..1_000)
        |> @iter.lazy()
        |> @iter.map(fn x -> x * x end)
        |> @iter.filter(fn x -> rem(x, 2) == 1 end)
        |> @iter.take_while(fn x -> x < 100 end)
        |> @iter.to_list()

      assert result == [1, 9, 25, 49, 81]
    end

    test "laziness verification: map's f is invoked exactly take(n) times" do
      Process.put(:iter_lazy_calls, 0)

      counted_double = fn x ->
        Process.put(:iter_lazy_calls, Process.get(:iter_lazy_calls) + 1)
        x * 2
      end

      result =
        @iter.range(1, 10_000_000)
        |> @iter.map(counted_double)
        |> @iter.take(5)

      assert result == [2, 4, 6, 8, 10]
      # `map`'s f is invoked exactly once per delivered element. If the
      # chain were eager, this would have run ten million times.
      assert Process.get(:iter_lazy_calls) == 5
    after
      Process.delete(:iter_lazy_calls)
    end

    test "fold can collapse a lazy chain in one pass" do
      sum =
        @iter.range(1, 100)
        |> @iter.filter(fn x -> rem(x, 3) == 0 end)
        |> @iter.fold(0, curry2(fn x, acc -> x + acc end))

      # 3 + 6 + ... + 99 = 3 * (1 + 2 + ... + 33) = 3 * 561 = 1683
      assert sum == 1683
    end
  end
end

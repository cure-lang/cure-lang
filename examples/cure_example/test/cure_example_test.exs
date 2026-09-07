defmodule CureExampleTest do
  use ExUnit.Case, async: true

  # `String` is a nominal Cure type, not a bare charlist -- it erases to the
  # tagged pair `{String, code_points}` (see `docs/FFI.md`). Calling a
  # compiled `.cure` function that takes or returns `String` directly (as
  # these raw tests do, bypassing `CureExample`'s own `to_cure_string`/
  # `from_cure_string` helpers) must use exactly that shape.
  describe "Greeter (cure module)" do
    test "hello/1 greets by name" do
      assert apply(:"Cure.Greeter", :hello, [{:String, ~c"World"}]) == {:String, ~c"Hello, World!"}
    end

    test "farewell/1 says goodbye" do
      assert apply(:"Cure.Greeter", :farewell, [{:String, ~c"Cure"}]) ==
               {:String, ~c"Goodbye, Cure. See you soon!"}
    end
  end

  describe "Calculator (cure module)" do
    test "basic arithmetic" do
      assert apply(:"Cure.Calculator", :add, [2, 3]) == 5
      assert apply(:"Cure.Calculator", :sub, [10, 4]) == 6
      assert apply(:"Cure.Calculator", :mul, [6, 7]) == 42
    end

    test "factorial/1 with pattern matching" do
      assert apply(:"Cure.Calculator", :factorial, [0]) == 1
      assert apply(:"Cure.Calculator", :factorial, [1]) == 1
      assert apply(:"Cure.Calculator", :factorial, [5]) == 120
      assert apply(:"Cure.Calculator", :factorial, [10]) == 3_628_800
    end

    test "fibonacci/1 with multi-clause patterns" do
      assert apply(:"Cure.Calculator", :fibonacci, [0]) == 0
      assert apply(:"Cure.Calculator", :fibonacci, [1]) == 1
      assert apply(:"Cure.Calculator", :fibonacci, [10]) == 55
    end

    test "classify/1 with guards" do
      assert apply(:"Cure.Calculator", :classify, [42]) == {:String, ~c"positive"}
      assert apply(:"Cure.Calculator", :classify, [-1]) == {:String, ~c"negative"}
      assert apply(:"Cure.Calculator", :classify, [0]) == {:String, ~c"zero"}
    end

    test "safe_divide/2 returns Result tuples" do
      assert {:ok, 5} = apply(:"Cure.Calculator", :safe_divide, [10, 2])
      assert {:error, {:String, ~c"division by zero"}} = apply(:"Cure.Calculator", :safe_divide, [10, 0])
    end
  end

  describe "CureExample wrapper" do
    test "delegates to cure modules" do
      assert CureExample.greet("Test") == "Hello, Test!"
      assert CureExample.factorial(5) == 120
      assert CureExample.fibonacci(10) == 55
      assert CureExample.classify(0) == "zero"
      assert {:ok, 5} = CureExample.safe_divide(10, 2)
    end
  end
end

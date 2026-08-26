defmodule Cure.Compiler.ImportTest do
  use ExUnit.Case, async: false

  setup_all do
    # Compile stdlib modules so they can be resolved
    for name <- ~w(list core math string io) do
      path = Path.join(["lib", "std", "#{name}.cure"])
      Cure.Compiler.compile_and_load(File.read!(path), file: path)
    end

    :ok
  end

  describe "use Module (import all)" do
    test "use Std.List resolves map and filter" do
      source = """
      mod ImportAll
        use Std.List

        fn doubled(xs: List(Int)) -> List(Int) = map(xs, fn(x) -> x * 2)
        fn total(xs: List(Int)) -> Int = sum(xs)
      """

      {:ok, m} = Cure.Compiler.compile_and_load(source)
      assert m.doubled([1, 2, 3]) == [2, 4, 6]
      assert m.total([1, 2, 3, 4, 5]) == 15
    after
      purge(:"Cure.ImportAll")
    end

    test "use Std.Math resolves abs and max" do
      source = """
      mod ImportMath
        use Std.Math

        fn get_abs(x: Int) -> Int = abs(x)
        fn bigger(a: Int, b: Int) -> Int = max(a, b)
      """

      {:ok, m} = Cure.Compiler.compile_and_load(source)
      assert m.get_abs(-5) == 5
      assert m.bigger(3, 7) == 7
    after
      purge(:"Cure.ImportMath")
    end
  end

  describe "use Namespace.{Mod1, Mod2} (selective)" do
    test "use Std.{List, Core} imports from both" do
      source = """
      mod ImportSelective
        use Std.{List, Core}

        fn doubled(xs: List(Int)) -> List(Int) = map(xs, fn(x) -> x * 2)
        fn get_id(x: Int) -> Int = identity(x)
      """

      {:ok, m} = Cure.Compiler.compile_and_load(source)
      assert m.doubled([1, 2, 3]) == [2, 4, 6]
      assert m.get_id(99) == 99
    after
      purge(:"Cure.ImportSelective")
    end
  end

  describe "local functions take priority over imports" do
    test "local fn shadows imported fn" do
      source = """
      mod ImportShadow
        use Std.Math

        fn abs(x: Int) -> Int = x * 100

        fn test() -> Int = abs(5)
      """

      {:ok, m} = Cure.Compiler.compile_and_load(source)
      # Local abs should be used, not Std.Math.abs
      assert m.test() == 500
    after
      purge(:"Cure.ImportShadow")
    end
  end

  describe "imports with qualified calls" do
    test "qualified calls still work alongside imports" do
      # Must-import: a qualified `Std.String.length` requires `Std.String` in
      # scope. Both List and String define `length`, so bare `length` is
      # ambiguous — the qualified spelling is exactly how you disambiguate.
      source = """
      mod ImportMixed
        use Std.{List, String}

        fn doubled(xs: List(Int)) -> List(Int) = map(xs, fn(x) -> x * 2)
        fn str_len(s: String) -> Int = Std.String.length(s)
      """

      {:ok, m} = Cure.Compiler.compile_and_load(source)
      assert m.doubled([1, 2]) == [2, 4]
      # `String` is nominal and erases to `{String, code_points}` — a raw BEAM
      # binary is a `Std.Binary`, not a `String`, and there is no marshalling
      # wrapper at the export boundary. Hand the function what it declares.
      assert m.str_len({:String, ~c"hello"}) == 5
    after
      purge(:"Cure.ImportMixed")
    end
  end

  describe "no imports" do
    test "module without imports works as before" do
      source = """
      mod NoImport
        fn add(a: Int, b: Int) -> Int = a + b
      """

      {:ok, m} = Cure.Compiler.compile_and_load(source)
      assert m.add(3, 4) == 7
    after
      purge(:"Cure.NoImport")
    end
  end

  defp purge(mod) do
    :code.purge(mod)
    :code.delete(mod)
  end
end

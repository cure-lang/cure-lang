defmodule Cure.Stdlib.OrdCompareTest do
  @moduledoc """
  Behavioral graduation of `Std.Comparable` onto the dependent pipeline.

  The `Char` instance compares Unicode code points via `Std.Char.code_point`
  (a `Char -> Int` coercion) and Int `<`; the `String` instance is lexicographic
  over `String = List(Char)` through the top-level `compare_string` recursion.
  These assert the *results* are correct, not merely that the module
  elaborates — comparing `compare(...)` against the `Ordering` constructors
  end-to-end (elaborate -> emit -> run).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  defp run(body, fname, mod) do
    src = """
    mod T
      use Std.Comparable
      use Std.Char
      use Std.String
      fn #{fname}() -> Bool = #{body}
    """

    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [fname])
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: fns)
    apply(m, fname, [])
  end

  describe "Char compare (code-point order)" do
    test "a < b" do
      assert run("compare('a', 'b') == LessThan()", :f, :"Cure.OrdCharLt")
    end

    test "a == a" do
      assert run("compare('a', 'a') == EqualTo()", :f, :"Cure.OrdCharEq")
    end

    test "b > a" do
      assert run("compare('b', 'a') == GreaterThan()", :f, :"Cure.OrdCharGt")
    end
  end

  describe "String compare (lexicographic)" do
    test "a prefix sorts before its extension" do
      assert run(~s|compare("ad", "ada") == LessThan()|, :f, :"Cure.OrdStrPrefix")
    end

    test "lexicographically smaller string is LessThan" do
      assert run(~s|compare("ada", "grace") == LessThan()|, :f, :"Cure.OrdStrLex")
    end

    test "equal strings are EqualTo" do
      assert run(~s|compare("cure", "cure") == EqualTo()|, :f, :"Cure.OrdStrEq")
    end
  end
end

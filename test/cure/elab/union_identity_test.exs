defmodule Cure.Elab.UnionIdentityTest do
  @moduledoc """
  Generated union families must use the same canonical member identities as
  ordinary declarations. Their content-derived names are metadata, not a
  reason to reconstruct identity after module elaboration.
  """

  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Union}

  defp union_families(env) do
    env.families |> Map.keys() |> Enum.filter(&Union.union_family?/1) |> Enum.sort()
  end

  test "two modules writing the same union share one canonical family" do
    src = """
    mod A
      fn mk(n: Int) -> Int | Bool = n
    end

    mod B
      fn mk2(n: Int) -> Bool | Int = n
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    assert union_families(env) == [:"Union<Std.Bool#Bool|Std.Int#Int>"]
  end

  test "a union value built in A typechecks and eliminates in B" do
    src = """
    mod A
      fn mk(n: Int) -> Int | Bool = n
    end

    mod B
      use A
      fn out(n: Int) -> Int = match A.mk(n)
        i: Int -> i
        b: Bool -> 0
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "generated union members do not leave bare family identities in the merged env" do
    src = """
    mod A
      fn mk(n: Int) -> Int | Bool = n
    end

    mod B
      use A
      fn out(n: Int) -> Int = match A.mk(n)
        i: Int -> i
        b: Bool -> 0
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    refute Enum.any?(Map.keys(env.families), fn key -> key in [:Bool, :Nat] end)
    refute Enum.any?(Map.keys(env.ctors), fn key -> key in [:True, :False, :Z, :S] end)
  end

  test "anonymous union identity is not qualified by its enclosing module" do
    src = """
    mod M
      fn mk(n: Int) -> Int | Bool = n
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    assert Map.has_key?(env.families, :"Union<Std.Bool#Bool|Std.Int#Int>")
    refute Enum.any?(Map.keys(env.families), &String.starts_with?(Atom.to_string(&1), "M#Union<"))
    assert Map.has_key?(env.ctors, :"Union<Std.Bool#Bool|Std.Int#Int>$Std.Int#Int")
  end
end

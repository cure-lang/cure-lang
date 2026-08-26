defmodule Cure.Elab.DependentLocalHelperContractTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.Program

  test "where helpers have no compiler arity ceiling" do
    source = """
    mod LocalArity
      fn outer(a: Int, b: Int, c: Int, d: Int, e: Int, f: Int, g: Int, h: Int) -> Int =
        helper(a, b, c, d, e, f, g, h)
      where
        fn helper(a: Int, b: Int, c: Int, d: Int, e: Int, f: Int, g: Int, h: Int) -> Int =
          a + b + c + d + e + f + g + h

      fn result() -> Int = outer(1, 2, 3, 4, 5, 6, 7, 8)
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 36
  end

  test "mutually recursive where helpers share one canonical lifted namespace" do
    source = """
    mod LocalMutual
      use Std.Nat

      fn parity(value: Nat) -> Bool = even(value)
      where
        fn even(value: Nat) -> Bool = match value
          Z() -> true
          S(previous) -> odd(previous)

        fn odd(value: Nat) -> Bool = match value
          Z() -> false
          S(previous) -> even(previous)

      fn result() -> Bool = parity(4)
    """

    assert {:ok, env} = Program.elaborate(source)

    lifted =
      env.defs
      |> Map.keys()
      |> Enum.filter(&(Atom.to_string(&1) =~ ~r/^LocalMutual#parity\$(even|odd)\$\d+$/))

    assert length(lifted) == 2, inspect(lifted)
    assert Enum.all?(lifted, &Env.certified?(env, &1))

    reachable = Program.reachable_def_names(env, [:parity])
    assert Enum.all?(lifted, &(&1 in reachable))
    assert Enum.all?(reachable, &Cure.Elab.Name.qualified?/1)
    assert Enum.all?(reachable, &Map.has_key?(env.defs, &1))

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == true
  end

  test "a where helper captures an erased outer index only at the type level" do
    source = """
    mod LocalErasedCapture
      use Std.Vector

      fn preserve({n: Nat}, values: Vector(Int, n)) -> Vector(Int, n) = helper(values)
      where
        fn helper(items: Vector(Int, n)) -> Vector(Int, n) = items

      fn result() -> Vector(Int, 2) = preserve(prepend(1, prepend(2, empty())))
    """

    assert {:ok, env} = Program.elaborate(source)

    [helper] =
      env.defs
      |> Map.keys()
      |> Enum.filter(&(Atom.to_string(&1) =~ "LocalErasedCapture#preserve$helper$"))

    assert Env.get_def(env, helper).plicities == [:implicit, :explicit]
    assert Env.certified?(env, helper)

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == {:prepend, 1, {:prepend, 2, :empty}}
  end

  test "a declaration macro may publish a proof-carrying local helper" do
    source = """
    mod GeneratedLocalProof
      use Std.Equivalent

      macro Publish
        syntax publish becomes local fn helper(value: Int) -> Equivalent(Int, value, value) = reflexive(value)

      publish
      fn prove(x: Int) -> Equivalent(Int, x, x) = helper(x)
    """

    assert {:ok, env} = Program.elaborate(source)

    [helper] =
      env.defs
      |> Map.keys()
      |> Enum.filter(&(Atom.to_string(&1) == "GeneratedLocalProof#helper"))

    assert Env.certified?(env, helper)
    assert Env.certified?(env, :"GeneratedLocalProof#prove")
    assert helper in Program.reachable_def_names(env, [:prove])
  end

  test "a lifted where helper preserves guarded multi-clause ordering" do
    source = """
    mod LocalGuardedClauses
      fn choose(left: Int, right: Int) -> Int = helper(left, right)
      where
        fn helper(left: Int, right: Int) -> Int
          | left, right when left == right -> left
          | _, right -> right

      fn equal() -> Int = choose(7, 7)
      fn different() -> Int = choose(3, 9)
    end
    """

    assert {:ok, env} = Program.elaborate(source)

    [helper] =
      env.defs
      |> Map.keys()
      |> Enum.filter(&(Atom.to_string(&1) =~ "LocalGuardedClauses#choose$helper$"))

    assert Env.certified?(env, helper)
    assert helper in Program.reachable_def_names(env, [:equal, :different])

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :equal, []) == 7
    assert apply(module, :different, []) == 9
  end
end

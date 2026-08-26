defmodule Cure.Elab.ResolveFirstOrderTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  defp run(src, mod, fun, args) do
    {:ok, env} = Program.elaborate(src)
    # Implementations synthesise mangled method globals (and, at abstract sites,
    # dictionary values) that the target function calls; emit them alongside it
    # exactly as the real pipeline's local-def set does.
    functions = Enum.uniq([fun | Program.impl_def_names(env)])
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: functions)
    apply(m, fun, args)
  end

  test "concrete method call inlines the implementation and runs" do
    src = """
    mod C1
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      fn test(x: Int, y: Int) -> Bool = eqs(x, y)
    end
    """

    assert run(src, :"Cure.C1", :test, [3, 3]) == true
    assert run(src, :"Cure.C1", :test, [3, 4]) == false
  end

  test "polymorphic constrained fn resolves via the implicit dictionary, two instances" do
    src = """
    mod C2
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      implementation Eqs for Bool
        fn eqs(x: Bool, y: Bool) -> Bool = eq(x, y)
      fn same({a: Type}, x: a, y: a) -> Bool where Eqs(a) = eqs(x, y)
      fn sameInt(x: Int, y: Int) -> Bool = same(x, y)
      fn sameBool(x: Bool, y: Bool) -> Bool = same(x, y)
    end
    """

    # `same`'s dict parameter is a real runtime argument, so it can't be called
    # via a bare 2-arg apply from outside Cure. `sameInt`/`sameBool` call `same`
    # from a concrete call site, where Resolve supplies the resolved dictionary;
    # those wrappers are what this test invokes.
    {:ok, env} = Program.elaborate(src)

    # `same`'s dictionary carries the instances' mangled method globals, so the
    # module must emit those alongside the wrappers — exactly the real pipeline's
    # local-def set (`Program.impl_def_names/1`).
    functions = Enum.uniq([:same, :sameInt, :sameBool | Program.impl_def_names(env)])
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.C2", functions: functions)

    assert apply(m, :sameInt, [1, 1]) == true
    assert apply(m, :sameBool, [true, false]) == false
  end

  test "a method call on a type with no instance is a clean no_instance error" do
    src = """
    mod C3
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      type Foo = MkFoo
      fn test(x: Foo, y: Foo) -> Bool = eqs(x, y)
    end
    """

    assert {:error, {:source_context, {:no_instance, :Eqs, _}, _}} = Program.elaborate(src)
  end

  test "an unused dictionary is erased (quantity 0), a used one is present" do
    src = """
    mod C4
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      fn ignore({a: Type}, x: a) -> a where Eqs(a) = x
      fn same({a: Type}, x: a, y: a) -> Bool where Eqs(a) = eqs(x, y)
    end
    """

    {:ok, env} = Program.elaborate(src)
    forms = Emit.module_forms(env, :"Cure.C4", [:ignore, :same])
    arities = for {:function, _line, name, arity, _clauses} <- forms, into: %{}, do: {name, arity}

    # ignore/1's body never calls `eqs` -> the dict is erased; only `x` survives.
    assert arities[:ignore] == 1
    # same/2 calls `eqs(x, y)` via the dict -> the dict stays present (arity 3).
    assert arities[:same] == 3
  end
end

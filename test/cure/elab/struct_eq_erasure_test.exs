defmodule Cure.Elab.StructEqErasureTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # Sole-route `==`: the operator desugars to the `Equatable` interface method, so a
  # comparison at an ABSTRACT/rigid type variable needs a `where Equatable(t)`
  # dictionary — there is no `struct_eq` escape hatch left for rigid operands. An
  # unconstrained `x == y` over `t` is rejected at elaboration, pointing at the
  # missing instance rather than silently lowering to `struct_eq`.
  test "== on an unconstrained abstract type variable is rejected (no Equatable escape hatch)" do
    src = """
    mod SE
      fn has(x: t, y: t) -> Bool = x == y
    end
    """

    assert {:error, {:source_context, {:no_instance, :Equatable, {:rigid, 0}}, _}} = Program.elaborate(src)
  end

  # With `where Equatable(t)`, the same comparison elaborates: `==` resolves to the
  # threaded `Equatable` dictionary, which the compiler passes as an extra runtime
  # argument (`has` becomes arity 3). A concrete-typed caller (`has_int`) forces
  # `t := Int`, resolves the `Equatable Int` instance at the call site, and threads
  # its dictionary — so the whole route runs and yields BEAM equality on ints.
  test "== on a `where Equatable(t)`-constrained variable elaborates, threads the dictionary, and runs" do
    src = """
    mod SE
      fn has(x: t, y: t) -> Bool where Equatable(t) = x == y
      fn has_int(a: Int, b: Int) -> Bool = has(a, b)
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.SE", functions: [:has, :has_int])

    assert apply(m, :has_int, [3, 3]) == true
    assert apply(m, :has_int, [3, 4]) == false
  end

  # `==` on a value of an INDEXED family (`Bounded(n)` — Char's underlying type)
  # lowers to the concrete `struct_eq` fast path, whose reified type argument is the
  # applied family `Bounded(n)`. That reification MUST carry the signature so the
  # index `n` is filed as an index and not a parameter; otherwise the kernel's
  # params/indices split arity-checks a 1-arg spine against Bounded's 0-param
  # telescope and rejects with `:arg_arity`. Nullary families (`Nat`) never hit this
  # because they have no arg to misfile. The `struct_eq` type argument is
  # computationally irrelevant (dropped at emit), and Bounded erases to a native int,
  # so `==` runs as BEAM integer equality.
  test "== on an indexed family (Bounded) elaborates and runs — index not misfiled as a param" do
    src = """
    mod SE
      use Std.Bounded
      fn eqb(x: Bounded(10), y: Bounded(10)) -> Bool = x == y
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.SE", functions: [:eqb])

    assert apply(m, :eqb, [3, 3]) == true
    assert apply(m, :eqb, [3, 4]) == false
  end
end

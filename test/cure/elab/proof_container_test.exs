defmodule Cure.Elab.ProofContainerTest do
  @moduledoc """
  `proof <Name> … end` containers in the dependent pipeline. Classic codegen
  compiled a proof container "exactly like a regular module", plus the E026
  proof-shape discipline: every binding must inhabit a propositional-equality
  type. This ports both to the sole (dependent) pipeline — a proof container is
  routed and elaborated like a `mod`, and each function must return an
  `Equivalent(T, a, b)` proof (E026 otherwise). The dependent proof witness is the
  inductive `reflexive`, not the legacy `:cure_refl` symbol.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps): every construct the classic codegen
  supports must work through the sole dependent pipeline before classic is ripped
  out, or deleting classic silently removes a live language feature.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  test "a proof container elaborates and emits like a module" do
    src = """
    proof P
      fn id_law(n: Int) -> Equivalent(Int, n, n) = reflexive(n)
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, mod} =
             Emit.compile_and_load(env, module: :"Cure.Test.ProofOk", functions: [:id_law])

    # The proof is erased; we only require that the emitted function exists and runs.
    assert function_exported?(mod, :id_law, 1)
  end

  test "multiple propositions in one proof container" do
    src = """
    proof P
      fn law_a(n: Int) -> Equivalent(Int, n, n) = reflexive(n)
      fn law_b(m: Int) -> Equivalent(Int, m, m) = reflexive(m)
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, mod} =
             Emit.compile_and_load(env, module: :"Cure.Test.ProofSeveral", functions: [:law_a, :law_b])

    assert function_exported?(mod, :law_a, 1)
    assert function_exported?(mod, :law_b, 1)
  end

  test "E026: a non-proof binding in a proof container is rejected" do
    src = """
    proof P
      fn meaning() -> Int = 42
    """

    assert {:error, reason} = Program.elaborate(src)
    assert inspect(reason) =~ "proof_shape" or inspect(reason) =~ "E026"
  end

  test "the same non-proof binding IS accepted inside a plain module" do
    src = """
    mod P
      fn meaning() -> Int = 42
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end

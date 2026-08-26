defmodule Antigen.AtomPrimAntibodyTest do
  @moduledoc """
  TCB antibody — adding the primitive base type `{:atom_type}` WITH a literal
  node `{:atom_lit, a}` (batch 2026-07-10) keeps the kernel SOUND and
  TERMINATING. `{:atom_type}` mirrors `{:int_type}`/`{:binary_type}` (evaluates
  to `{:vatom_type}`, infers to `Type 0`, canonical head / rigid index) and
  `{:atom_lit, a}` mirrors `{:int_lit, n}` (evaluates to `{:vatom, a}`, infers to
  `Atom`, canonical value).

  A new canonical head plus a new canonical value are dangerous in exactly two
  ways, and the antibody pins both non-collapse properties:

    * KINDED-ONCE — `{:atom_type}` infers to `Type 0`; `{:atom_lit, a}` infers to
      `Atom` (`{:vatom_type}`). No more, no less.

    * HEAD-DISTINCTNESS — `{:atom_type}` converts with ITSELF and nothing else
      (not Int/Float/Binary/Type/any data family). A collapse would license
      coercing a value of one base type to another. Oracle = full cartesian
      product of base heads.

    * LITERAL-DISTINCTNESS — the load-bearing property unique to a base type with
      OWN literals: two atom literals are convertible IFF the atoms are equal.
      A collapse (`:ok ≡ :error`) would make the type checker accept a proof that
      depends on atom identity being false — e.g. a `case` refinement keyed on a
      tag. Oracle = a cartesian product of distinct sample atoms; only the
      diagonal converts.

    * NF-STABLE — normalising either node yields itself; distinctness survives nf.

  Plus TERMINATION under a bounded Task harness. A SOUNDNESS violation means the
  base type is unsound: STOP — do not weaken it.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Kernel, Normalise, Quote, Eval}

  defp env, do: Env.empty()
  defp ctx, do: Context.empty(env())

  # The distinct canonical type heads that must never be conflated.
  @heads [
    {:atom_type},
    {:binary_type},
    {:int_type},
    {:float_type},
    {:type, 0},
    {:data, :Nat, [], []},
    {:data, :Bool, [], []}
  ]

  # Distinct sample atom literals whose identities must stay separate.
  @lits [{:atom_lit, :ok}, {:atom_lit, :error}, {:atom_lit, :millisecond}, {:atom_lit, :"$empty"}]

  test "KINDED-ONCE: Atom infers to Type 0, a literal infers to Atom" do
    assert {:ok, {:vtype, 0}} = Kernel.infer(ctx(), {:atom_type})
    assert {:ok, {:vatom_type}} = Kernel.infer(ctx(), {:atom_lit, :ok})
  end

  test "HEAD-DISTINCTNESS: Atom is convertible with itself and no other canonical head" do
    for a <- @heads, b <- @heads do
      convertible = Conv.conv?(a, b, [], 0, env())

      if a == b do
        assert convertible, "a canonical head must be convertible with itself: #{inspect(a)}"
      else
        refute convertible,
               "HEAD COLLAPSE: #{inspect(a)} ≡ #{inspect(b)} — distinct base/type heads must " <>
                 "never be definitionally equal, or a value of one is coercible to the other."
      end
    end
  end

  test "LITERAL-DISTINCTNESS: atom literals converge IFF the atoms are equal" do
    for a <- @lits, b <- @lits do
      convertible = Conv.conv?(a, b, [], 0, env())

      if a == b do
        assert convertible, "an atom literal must convert with itself: #{inspect(a)}"
      else
        refute convertible,
               "LITERAL COLLAPSE: #{inspect(a)} ≡ #{inspect(b)} — distinct atoms must never be " <>
                 "definitionally equal, or a tag-keyed refinement is forgeable."
      end
    end
  end

  test "NF-STABLE: Atom type and literal normalise to themselves and stay distinct" do
    assert Normalise.nf(ctx(), {:atom_type}) == {:atom_type}
    assert Normalise.nf(ctx(), {:atom_lit, :ok}) == {:atom_lit, :ok}
    assert Quote.reify(Eval.eval({:atom_type}, [])) == {:atom_type}
    assert Quote.reify(Eval.eval({:atom_lit, :ok}, [])) == {:atom_lit, :ok}

    for other <- @heads, other != {:atom_type} do
      refute Conv.conv?(Normalise.nf(ctx(), {:atom_type}), Normalise.nf(ctx(), other), [], 0, env()),
             "post-nf HEAD COLLAPSE: Atom ≡ #{inspect(other)}"
    end

    refute Conv.conv?(
             Normalise.nf(ctx(), {:atom_lit, :ok}),
             Normalise.nf(ctx(), {:atom_lit, :error}),
             [],
             0,
             env()
           ),
           "post-nf LITERAL COLLAPSE: :ok ≡ :error"
  end

  test "Atom inference, normalization and conversion halt (bounded)" do
    jobs = [
      fn -> Kernel.infer(ctx(), {:atom_type}) end,
      fn -> Kernel.infer(ctx(), {:atom_lit, :ok}) end,
      fn -> Normalise.nf(ctx(), {:atom_lit, :ok}) end,
      fn -> Conv.conv?({:atom_lit, :ok}, {:atom_lit, :error}, [], 0, env()) end
    ]

    for {job, i} <- Enum.with_index(jobs) do
      task = Task.async(job)

      assert Task.yield(task, 5_000) || Task.shutdown(task),
             "job #{i} (Atom infer/nf/conv) did not return within budget"
    end
  end
end

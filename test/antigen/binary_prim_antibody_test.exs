defmodule Antigen.BinaryPrimAntibodyTest do
  @moduledoc """
  TCB antibody — adding the primitive base type `{:binary_type}` (#3, batch
  2026-07-10) as a new CANONICAL TYPE HEAD keeps the kernel SOUND and
  TERMINATING. It mirrors `{:int_type}`/`{:float_type}`: it evaluates to
  `{:vbinary_type}`, infers to `Type 0`, and is a canonical head / rigid index.

  A new canonical head is dangerous in exactly one way: if conversion ever
  identifies it with a DIFFERENT head, a value of one base type could be coerced
  to another (e.g. an `Int` used where a `Binary` is demanded, feeding a BEAM
  binary BIF a raw integer). So the load-bearing soundness property is
  NON-COLLAPSE:

    * KINDED-ONCE — `{:binary_type}` infers to `Type 0`, no more, no less.

    * HEAD-DISTINCTNESS — `{:binary_type}` is convertible with ITSELF and with
      NOTHING else: not `Int`, not `Float`, not `Type`, not any data family. The
      independent oracle is the FULL cartesian product of the base heads — every
      cross pair must be non-convertible, every self pair convertible. A
      violation is a definitional-equality collapse that licenses a coercion.

    * NF-STABLE — normalising `{:binary_type}` yields itself (a canonical head is
      already a normal form); conversion after nf still separates it from the
      other heads.

  Plus TERMINATION under a bounded Task harness. If any construction violates a
  SOUNDNESS assertion, the base type is unsound: STOP — do not weaken it.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Kernel, Normalise, Quote}

  defp env, do: Env.empty()
  defp ctx, do: Context.empty(env())

  # The distinct canonical type heads that must never be conflated.
  @heads [
    {:binary_type},
    {:int_type},
    {:float_type},
    {:type, 0},
    {:data, :Nat, [], []},
    {:data, :Bool, [], []}
  ]

  test "KINDED-ONCE: Binary infers to Type 0 exactly" do
    assert {:ok, {:vtype, 0}} = Kernel.infer(ctx(), {:binary_type})
  end

  test "HEAD-DISTINCTNESS: Binary is convertible with itself and no other canonical head" do
    for a <- @heads, b <- @heads do
      convertible = Conv.conv?(a, b, [], 0, env())

      if a == b do
        assert convertible,
               "a canonical head must be convertible with itself: #{inspect(a)}"
      else
        refute convertible,
               "HEAD COLLAPSE: #{inspect(a)} ≡ #{inspect(b)} — distinct base/type heads must " <>
                 "never be definitionally equal, or a value of one is coercible to the other."
      end
    end
  end

  test "NF-STABLE: Binary normalises to itself and stays distinct after nf" do
    assert Normalise.nf(ctx(), {:binary_type}) == {:binary_type}
    assert Quote.reify(Cure.Core.Eval.eval({:binary_type}, [])) == {:binary_type}

    # Non-collapse survives normalization of both sides.
    for other <- @heads, other != {:binary_type} do
      nb = Normalise.nf(ctx(), {:binary_type})
      no = Normalise.nf(ctx(), other)

      refute Conv.conv?(nb, no, [], 0, env()),
             "post-nf HEAD COLLAPSE: Binary ≡ #{inspect(other)}"
    end
  end

  test "Binary inference, normalization and conversion halt (bounded)" do
    jobs = [
      fn -> Kernel.infer(ctx(), {:binary_type}) end,
      fn -> Normalise.nf(ctx(), {:binary_type}) end,
      fn -> Conv.conv?({:binary_type}, {:int_type}, [], 0, env()) end
    ]

    for {job, i} <- Enum.with_index(jobs) do
      task = Task.async(job)

      assert Task.yield(task, 5_000) || Task.shutdown(task),
             "job #{i} (Binary infer/nf/conv) did not return within budget"
    end
  end
end

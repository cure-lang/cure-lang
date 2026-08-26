defmodule Antigen.HoleNeutralAntibodyTest do
  @moduledoc """
  TCB antibody — making a hole a first-class stuck neutral `{:nhole, id}`
  (first-class-holes design, Slice 1) keeps the kernel SOUND and TERMINATING.

  A hole is an assumable term: `Kernel.check/3` accepts `{:hole,_}` at ANY goal
  type. Once holes flow through conversion, the one dangerous collapse is two
  DISTINCT holes becoming definitionally equal: `refl : ?a = ?b` would then
  type-check, and filling `?a := 0`, `?b := 1` later would have proven `0 = 1`.
  The design defends against this by giving every source `?` a UNIQUE id; this
  antibody pins the non-collapse property at the kernel's conversion layer.

    * HOLE-DISTINCTNESS — two holes are convertible IFF their ids are equal.
      A collapse licenses a proof of equality between two unrelated unknowns.
      Oracle = the full cartesian product of distinct hole ids; only the
      diagonal converts.

    * HOLE-VS-CONCRETE — a hole is convertible to NO non-hole term (nor a
      non-hole to a hole). A collapse would let a hole stand definitionally for a
      specific value it was never filled with. Oracle = holes × concrete heads.

    * REFLEXIVITY-PRESERVED — a hole IS convertible to itself (same id), even
      applied to identical spines. The change adds distinctness without breaking
      the reflexivity every conversion relation must have.

    * NF-STABLE — distinctness survives normalization: nf of a hole is stuck, and
      two distinct holes stay non-convertible after nf.

  Plus TERMINATION under a bounded Task harness: evaluating, normalizing, and
  converting hole-bearing terms halts (they get stuck, they do not crash or
  diverge). A SOUNDNESS violation here means holes are unsound: STOP.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Normalise, Quote, Eval}

  defp env, do: Env.empty()
  defp ctx, do: Context.empty(env())

  # Distinct sample hole ids whose identities must stay separate.
  @hole_ids ["M.f:3:10", "M.f:4:12", "M.g#goal", "Other.h:1:1"]

  # Concrete (non-hole) canonical terms a hole must never converge with.
  @concrete [
    {:type, 0},
    {:int_type},
    {:int_lit, 0},
    {:atom_type},
    {:atom_lit, :ok},
    {:data, :Nat, [], []}
  ]

  test "HOLE-DISTINCTNESS: two holes converge IFF their ids are equal" do
    for a <- @hole_ids, b <- @hole_ids do
      convertible = Conv.conv?({:hole, a}, {:hole, b}, [], 0, env())

      if a == b do
        assert convertible, "a hole must convert with itself: #{inspect(a)}"
      else
        refute convertible,
               "HOLE COLLAPSE: ?#{a} ≡ ?#{b} — distinct holes must never be definitionally " <>
                 "equal, or `refl : ?a = ?b` type-checks and a false equality is forgeable."
      end
    end
  end

  test "HOLE-VS-CONCRETE: a hole is convertible to no non-hole term, either direction" do
    for id <- @hole_ids, c <- @concrete do
      refute Conv.conv?({:hole, id}, c, [], 0, env()),
             "COLLAPSE: ?#{id} ≡ #{inspect(c)} — a hole must not equal a concrete term."

      refute Conv.conv?(c, {:hole, id}, [], 0, env()),
             "COLLAPSE: #{inspect(c)} ≡ ?#{id} — a concrete term must not equal a hole."
    end
  end

  test "REFLEXIVITY-PRESERVED: a hole applied to identical spines converts with itself" do
    applied = {:app, {:app, {:hole, "M.f:3:10"}, {:int_lit, 1}}, {:int_lit, 2}}
    assert Conv.conv?(applied, applied, [], 0, env())
  end

  test "REFLEXIVITY-PRESERVED: same hole, differing spines do NOT converge" do
    a = {:app, {:hole, "M.f:3:10"}, {:int_lit, 1}}
    b = {:app, {:hole, "M.f:3:10"}, {:int_lit, 2}}
    refute Conv.conv?(a, b, [], 0, env())
  end

  test "NF-STABLE: nf of a hole is stuck and distinctness survives nf" do
    assert Normalise.nf(ctx(), {:hole, "M.f:3:10"}) == {:hole, "M.f:3:10"}
    assert Quote.reify(Eval.eval({:hole, "M.f:3:10"}, [])) == {:hole, "M.f:3:10"}

    refute Conv.conv?(
             Normalise.nf(ctx(), {:hole, "M.f:3:10"}),
             Normalise.nf(ctx(), {:hole, "M.f:4:12"}),
             [],
             0,
             env()
           ),
           "post-nf HOLE COLLAPSE: two distinct holes became convertible after nf"
  end

  test "hole eval / nf / conv halt (bounded)" do
    applied = {:app, {:hole, "M.f:3:10"}, {:int_lit, 1}}

    jobs = [
      fn -> Eval.eval(applied, []) end,
      fn -> Normalise.nf(ctx(), applied) end,
      fn -> Conv.conv?({:hole, "a"}, {:hole, "b"}, [], 0, env()) end,
      fn -> Conv.conv?(applied, applied, [], 0, env()) end
    ]

    for {job, i} <- Enum.with_index(jobs) do
      task = Task.async(job)

      assert Task.yield(task, 5_000) || Task.shutdown(task),
             "job #{i} (hole eval/nf/conv) did not return within budget"
    end
  end
end

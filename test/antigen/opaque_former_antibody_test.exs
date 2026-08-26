defmodule Antigen.OpaqueFormerAntibodyTest do
  @moduledoc """
  TCB antibody — the `opaque type Name(params)` inert-carrier former (batch
  2026-07-10, spec 2026-07-10-length-indexed-binary-design sibling) keeps the
  kernel SOUND. An opaque family is a `postulate`: it is an INHABITED type (its
  values carry through, e.g. a BEAM op smuggled from a macro/@extern to codegen)
  but it is NON-ELIMINABLE — the kernel must refuse to `case` on it, so its
  contents are never inspected or unfolded by the TCB.

  The load-bearing subtlety: an opaque family has ZERO constructors, and a
  zero-constructor family passes coverage VACUOUSLY (an empty branch list is
  ex-falso, §H). So a naive kernel would let `case e { }` eliminate an opaque
  value into ANY type — the classic postulate-is-not-Void unsoundness. The guard
  keys the `opaque: true` MARKER, not the constructor count, which is exactly
  what distinguishes an opaque postulate (non-eliminable) from a genuine empty
  inductive `type Void = |` (still ex-falso-eliminable). This file pins that
  distinction with an INDEPENDENT contrast: the same `{:case, scrut, motive, []}`
  shape is REFUSED on an opaque scrutinee and ACCEPTED on a Void scrutinee.

  Three soundness properties:

    * NON-ELIMINABLE — `Kernel.infer` on `{:case, e, motive, []}` with `e` of an
      opaque family returns `{:error, :opaque_not_eliminable}`. A violation lets
      the payload be scrutinised / coerced, defeating the whole inert-carrier
      contract.

    * MARKER-NOT-COUNT — the IDENTICAL zero-branch case shape on a genuine empty
      inductive `Void` is NOT refused for opaqueness (it ex-falso-eliminates).
      Proves the guard keys the marker, so ordinary empty inductives keep their
      elimination.

    * CARRIER-BY-NAME — conversion on opaque values is purely structural: two
      DISTINCT opaque families are non-convertible, and an opaque value's payload
      is compared but never UNFOLDED (there is no delta rule for a postulate).

  Plus TERMINATION under a bounded Task harness. If any construction violates a
  SOUNDNESS assertion, the former is unsound: STOP — do not weaken the assertion.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Kernel, Context, Conv, Eval, Inductive}
  alias Cure.Elab.Program

  @nat {:data, :Nat, [], []}

  # A signature seeding two DISTINCT opaque families (both 1-param, 0-index) plus
  # a genuine empty inductive Void — the three players in the contrast.
  defp sig do
    {:ok, env} =
      Program.elaborate("mod M\n  opaque type Effect(a)\n  opaque type Widget(a)\n  type Void =\n    |\nend\n")

    env
  end

  # Evaluate a data type to its value form in the empty context of `sig`.
  defp data_val(sig, name, params, indices),
    do: Eval.eval({:data, name, params, indices}, Context.env(Context.empty(sig)))

  # ---- SOUNDNESS: opaque is NON-ELIMINABLE -----------------------------------

  test "NON-ELIMINABLE: case on an opaque-typed scrutinee is refused before coverage" do
    sig = sig()
    # Confirm the family really is marked opaque (guards against a silent rename).
    assert Inductive.opaque_family?(Inductive.get_family(sig, :Effect))

    # A hypothetical `e : Effect(Nat)` in context; scrutinise it with an empty
    # branch list — the ex-falso shape a zero-ctor family would otherwise admit.
    effect_val = data_val(sig, :Effect, [@nat], [])
    ctx = Context.extend(Context.empty(sig), effect_val)
    motive = {:lam, Cure.Core.Grade.unrestricted(), {:data, :Effect, [@nat], []}, @nat}

    assert {:error, :opaque_not_eliminable} =
             Kernel.infer(ctx, {:case, {:var, 0}, motive, []}),
           "SOUNDNESS VIOLATION: an opaque (postulate) value was eliminated. Its zero " <>
             "constructors make coverage vacuous, so without the marker guard `case e {}` " <>
             "coerces the carrier into any type — the payload must stay uninspectable."
  end

  # ---- SOUNDNESS: the MARKER, not the ctor count, forbids elimination --------

  test "MARKER-NOT-COUNT: the same zero-branch case on genuine empty Void is NOT refused for opaqueness" do
    sig = sig()
    # Void is a real empty inductive — zero ctors, but NOT marked opaque.
    refute Inductive.opaque_family?(Inductive.get_family(sig, :Void))

    void_val = data_val(sig, :Void, [], [])
    ctx = Context.extend(Context.empty(sig), void_val)
    motive = {:lam, Cure.Core.Grade.unrestricted(), {:data, :Void, [], []}, @nat}

    result = Kernel.infer(ctx, {:case, {:var, 0}, motive, []})

    # The load-bearing contrast: Void is NEVER refused for opaqueness. (It in fact
    # ex-falso-eliminates to the motive's codomain, Nat.)
    refute match?({:error, :opaque_not_eliminable}, result),
           "MARKER VIOLATION: a genuine empty inductive was refused as if opaque — the guard " <>
             "must key the `opaque: true` marker, not the constructor count, or ordinary " <>
             "empty inductives lose their ex-falso elimination."

    nat_val = data_val(sig, :Nat, [], [])

    assert {:ok, ^nat_val} = result,
           "Void must ex-falso-eliminate to the motive codomain (Nat), proving elimination " <>
             "is intact for non-opaque zero-ctor families."
  end

  # ---- SOUNDNESS: opaque conversion is structural-by-name, never unfolded -----

  test "CARRIER-BY-NAME: distinct opaque families are non-convertible; payload compared not unfolded" do
    sig = sig()
    len = 0

    effect_nat = data_val(sig, :Effect, [@nat], [])
    widget_nat = data_val(sig, :Widget, [@nat], [])

    refute Conv.conv_values?(effect_nat, widget_nat, len, sig),
           "CARRIER VIOLATION: two distinct opaque families were judged convertible — opaque " <>
             "identity is the family name; conflating them lets a value cross carrier types."

    # Same family, same payload: convertible (structural reflexivity, no unfolding needed).
    assert Conv.conv_values?(effect_nat, data_val(sig, :Effect, [@nat], []), len, sig),
           "an opaque value must be convertible with itself"

    # Same family, DISTINCT payload: non-convertible. The payload is COMPARED
    # structurally — it is never unfolded (there is no delta rule for a postulate).
    bool_ty = {:data, :Bool, [], []}

    refute Conv.conv_values?(effect_nat, data_val(sig, :Effect, [bool_ty], []), len, sig),
           "distinct opaque payloads must be distinguished by structural comparison of the args"
  end

  # ---- TERMINATION -----------------------------------------------------------

  test "opaque-case inference and opaque conversion halt (bounded)" do
    sig = sig()
    effect_val = data_val(sig, :Effect, [@nat], [])
    ctx = Context.extend(Context.empty(sig), effect_val)
    motive = {:lam, Cure.Core.Grade.unrestricted(), {:data, :Effect, [@nat], []}, @nat}

    jobs = [
      fn -> Kernel.infer(ctx, {:case, {:var, 0}, motive, []}) end,
      fn -> Conv.conv_values?(effect_val, data_val(sig, :Widget, [@nat], []), 0, sig) end
    ]

    for {job, i} <- Enum.with_index(jobs) do
      task = Task.async(job)

      assert Task.yield(task, 5_000) || Task.shutdown(task),
             "job #{i} (opaque case/conv) did not return within budget"
    end
  end
end

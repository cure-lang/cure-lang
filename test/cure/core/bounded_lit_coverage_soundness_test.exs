defmodule Cure.Core.BoundedLitCoverageSoundnessTest do
  @moduledoc """
  Regression: `{:bounded_lit, k}` <-> ctor-tower bridge in the index unifier
  (`Kernel.unify_one/4`). The `Bounded` twin of
  `nat_lit_coverage_soundness_test.exs`.

  Background: `Bounded(n)` (Std.Bounded, `lib/std/bounded.cure`) has TWO
  interconvertible value representations, exactly like `Nat`:

    * the compact literal `{:bounded_lit, k}` / `{:vbounded, k}`
    * the `First`/`Next` constructor tower (`Eval.bounded_to_ctor/1`)

  `test/cure/core/compact_bounded_test.exs` proves the two are DEFINITIONALLY
  EQUAL (`Conv.conv_values?`, both directions). `Nat` has the identical dual
  representation (`{:nat_lit, n}` vs. `Z`/`S`), and `Kernel.unify_one/4`
  carries THREE dedicated clauses bridging it for index unification
  (lib/cure/core/kernel.ex, the `{:nat_lit, ...}` clauses immediately above
  `unify_one({:ctor, c, as}, {:ctor, c, bs}, ...)`), added specifically to
  close a documented coverage-soundness hole (see
  `nat_lit_coverage_soundness_test.exs`: "a case on Vone(0) could omit vz,
  its only inhabitant, and still pass coverage").

  When `Bounded` was introduced (425f0bb) `{:bounded_lit, k}` did NOT receive the
  analogous bridge, reintroducing the bug class the Nat bridge had been built to
  close. It fell through every specific `unify_one` clause to the generic
  rigid-head-clash `cond`, where `head_key/1`'s catch-all (`elem(t, 0)`) gives it
  the head `:bounded_lit` — which can never equal a ctor's `{:ctor, name}` head —
  so the clash rule fired `:impossible` on two DEFINITIONALLY EQUAL indices.

  Agda/Lean/Idris: clash detection (the `Conflict`/`Injectivity` step of a
  first-order unifier over canonical forms) is only sound when the two sides
  are genuinely distinct CANONICAL heads. A literal and its own tower
  expansion are the same canonical value under two different surface
  spellings, not a clash.

  The third test pins the direct soundness consequence: `check_coverage` must not
  accept a `case` that omits the scrutinee's own (reachable) constructor, which it
  did while the unifier wrongly proved that branch `:impossible`.

  Keep the bridge clauses in `kernel.ex` in lock-step with `conv.ex`'s
  cross-representation `conv_struct?` arms — they must agree on ignoring the
  erased implicit bound `m`.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel}
  alias Cure.Elab.Program

  @nat {:data, :Nat, [], []}

  # A minimal family `Bx(k: Bounded(10))`, one constructor per Bounded value,
  # each constructor's result index written with the COMPACT literal form
  # (exactly how a statically-known Bounded index is naturally represented —
  # `{:bounded_lit, k}` is the kernel's own canonical literal typing rule,
  # `Kernel.check/3`'s `{:bounded_lit, k}` clause). Built on the REAL
  # `Std.Bounded` family (not a hand-rolled stand-in), so `Eval.
  # bounded_to_ctor/1` below produces the genuine production `First`/`Next`
  # shape.
  defp sig do
    {:ok, elaborated} =
      Program.elaborate("mod M\n  use Std.Bounded\n  fn f(x: Bounded(10)) -> Bounded(10) = x\nend\n")

    # Elaborating `mod M` leaves `module_owner: "M"` on the env; declaring the
    # synthetic `Bx` family on it would owner-qualify its ctors (`M#bx0`), so the
    # bare `:Bx`/`:bx0` the tests name below would no longer resolve. Strip the
    # owner first — `Bx` is a hand-rolled stand-in, not a member of any module.
    base = Env.with_owner(elaborated, nil)
    bounded_fid = Inductive.builtin(base, :bounded)
    bounded10 = {:data, bounded_fid, [], [{:nat_lit, 10}]}

    Inductive.declare(base, Inductive.family(:Bx, [], [{:k, bounded10}], 0), [
      Inductive.ctor(:bx0, [], [{:bounded_lit, 0}]),
      Inductive.ctor(:bx1, [], [{:bounded_lit, 1}])
    ])
  end

  defp ctx, do: Context.empty(sig())

  test "KB1: bx0 is reachable when the scrutinee index is the definitionally-equal First-tower value" do
    # Eval.bounded_to_ctor({:vbounded, 0}) == {:vctor, :First, [{:vnat, 0}]},
    # proven convertible with {:vbounded, 0} by compact_bounded_test.exs. bx0's
    # OWN result index is the compact {:bounded_lit, 0} form of the SAME
    # value, so this must verdict :trivial (an exact, var-free match) exactly
    # as the all-compact form already does today
    # (`Kernel.branch_unify(ctx(), :Bx, :bx0, [{:vbounded, 0}])` == :trivial).
    tower_zero = Eval.bounded_to_ctor({:vbounded, 0})

    assert :trivial == Kernel.branch_unify(ctx(), :Bx, :bx0, [tower_zero]),
           "SOUNDNESS: unify_one's rigid-clash rule mistook the First-tower spelling of 0 " <>
             "for a head clash against bx0's compact {:bounded_lit, 0} result index — the " <>
             "missing bounded_lit<->ctor bridge (Nat's {:nat_lit, _} got one in unify_one; " <>
             "Bounded's {:bounded_lit, _} never did)."
  end

  test "KB1: bx1 is reachable when the scrutinee index is the definitionally-equal Next-tower value" do
    # Eval.bounded_to_ctor({:vbounded, 1}) == {:vctor, :Next, [{:vnat, 1}, {:vbounded, 0}]}.
    tower_one = Eval.bounded_to_ctor({:vbounded, 1})

    assert :trivial == Kernel.branch_unify(ctx(), :Bx, :bx1, [tower_one]),
           "SOUNDNESS: same gap as the First case, reproduced for Next."
  end

  test "KB2: coverage soundness hole — a case omitting the scrutinee's own reachable constructor still passes coverage" do
    # The real-world consequence of KB1. A `case` on a `Bx` scrutinee whose
    # index IS bx0's value (the First-tower form — exactly what a genuine
    # scrutinee looks like after one layer of Bounded elimination) that lists
    # ONLY the bx1 branch must be REJECTED for incomplete coverage: bx0 is
    # reachable (it is, in fact, the scrutinee's own constructor). Because
    # unify_one wrongly verdicts bx0 :impossible against the tower form,
    # `check_coverage` currently accepts this as exhaustive — a partial
    # eliminator admitted as total, the load-bearing precondition of a
    # False-inhabiting "proof" (ex-falso on an inhabited type).
    tower_zero = Eval.bounded_to_ctor({:vbounded, 0})
    signature = sig()
    scrut_ty = {:vdata, :Bx, [tower_zero]}
    case_ctx = Context.extend(Context.empty(signature), scrut_ty)

    bounded_fid = Inductive.builtin(signature, :bounded)
    bounded10 = {:data, bounded_fid, [], [{:nat_lit, 10}]}
    # motive : (k : Bounded(10)) -> Bx(k) -> Type, constant at Nat.
    motive =
      {:lam, Cure.Core.Grade.unrestricted(), bounded10,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bx, [], [{:var, 0}]}, @nat}}

    case_term = {:case, {:var, 0}, motive, [{:bx1, 0, {:ctor, :Z, []}}]}

    assert {:error, :coverage} == Kernel.infer(case_ctx, case_term),
           "SOUNDNESS VIOLATION: case omits bx0 (the scrutinee's OWN, reachable constructor) " <>
             "and still typechecks as exhaustive — the KB1 unification gap lets an incomplete " <>
             "eliminator through, exactly the ex-falso-on-an-inhabited-type hole already fixed " <>
             "once for Nat (see nat_lit_coverage_soundness_test.exs)."
  end
end

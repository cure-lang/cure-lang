defmodule Cure.Core.HoleNeutralTest do
  @moduledoc """
  A hole is a first-class STUCK NEUTRAL (Slice 1 of the first-class-holes design,
  docs/superpowers/specs/2026-07-18-first-class-holes-design.md).

  Before this change `Eval.eval` had no `{:hole,_}` clause: a body-position hole
  survived only because it was the whole body and never evaluated, but a hole in
  ARGUMENT position (embedded in an enclosing application the elaborator
  normalizes) crashed the evaluator with a `FunctionClauseError`. A hole is a
  stuck computation, so it evaluates to a neutral `{:nhole, id}` and rides every
  existing neutral pathway — application accumulates a spine, read-back inverts
  it, normalization leaves it stuck.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Eval, Normalise, Quote}

  defp ctx, do: Context.empty(Env.empty())

  describe "eval" do
    test "a bare hole evaluates to a hole neutral" do
      assert Eval.eval({:hole, "h"}, []) == {:vneutral, {:nhole, "h"}}
    end

    test "an applied hole accumulates its arguments on the neutral spine" do
      assert Eval.eval({:app, {:hole, "h"}, {:type, 0}}, []) ==
               {:vneutral, {:napp, {:nhole, "h"}, {:vtype, 0}}}
    end

    test "a hole under a beta-redex argument does not crash" do
      # (λ.#0) ?h  β⤳  ?h — the argument-position hole reaches apply/eval.
      redex = {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:hole, "h"}}
      assert Eval.eval(redex, []) == {:vneutral, {:nhole, "h"}}
    end
  end

  describe "read-back" do
    test "reify inverts a bare hole neutral" do
      assert Quote.reify(Eval.eval({:hole, "h"}, [])) == {:hole, "h"}
    end

    test "reify inverts an applied hole to the original application" do
      applied = {:app, {:hole, "h"}, {:type, 0}}
      assert Quote.reify(Eval.eval(applied, [])) == applied
    end
  end

  describe "normalization leaves a hole stuck" do
    test "nf of a bare hole is the hole itself" do
      assert Normalise.nf(ctx(), {:hole, "h"}) == {:hole, "h"}
    end

    test "nf of an applied hole preserves the spine" do
      applied = {:app, {:hole, "h"}, {:type, 0}}
      assert Normalise.nf(ctx(), applied) == applied
    end

    test "whnf_value on a hole neutral is stuck (returns it unchanged) under a real signature" do
      hole_val = {:vneutral, {:nhole, "h"}}
      assert Normalise.whnf_value(hole_val, Env.empty()) == hole_val
    end
  end
end

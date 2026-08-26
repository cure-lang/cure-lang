defmodule Cure.Elab.SubstEffectTraversalTest do
  @moduledoc """
  `Cure.Elab.Subst` must traverse the whole of `Core.Term`, including the Effect formers.

  `replace/4` and `shift/3` enumerated `:effect_type` but had no clause for `{:effect_pure, a}`
  or `{:effect_bind, e, k}`, so both fell to the identity catch-all and were returned
  byte-identical — **with zero recursion into their subterms**. A `{:var, i}` nested inside an
  effect payload was left completely unrenumbered by an operation whose entire purpose is
  renumbering. The trusted `Core.Term.shift`/`subst` (`term.ex:204-206`, `:293-295`) always
  handled both; only the elaborator's meta-aware copy was missed. `Erase.erase` had already
  been patched for exactly these two formers, with a comment naming this failure mode —
  `Subst.instantiate`, called eight lines above it in the same file, had not.

  Two call sites reach it, and they fail in opposite ways:

  * `wrap_join` (`elaborator.ex:4619`) shifts every branch body of a join-eligible `case`. An
    effectful arm's free variables were not bumped past the inserted join binder, so a
    well-typed program was REJECTED (`:branch_type`) purely because a default arm made the
    join fire. Loud, and the regression test below pins it at the surface.

  * `Erase.erase`'s collapsible-case optimisation (`erase.ex:146-154`) calls
    `Subst.instantiate` on a branch body. There the job that gets skipped is the
    STRENGTHENING — collapsing the case deletes `arity` binders, so every outer `{:var, i}`
    with `i >= arity` must become `{:var, i - arity}`. Inside an effect node it never did, so
    the variable silently resolved to the WRONG enclosing binder. Erasure runs after the
    kernel and its output is never re-verified (`emit.ex:354` feeds it straight to codegen),
    so that route is a silent miscompilation with nothing downstream to catch it. It is pinned
    here at the `Subst` contract, which is where the defect actually lives.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Subst}

  describe "shift/3 renumbers variables inside effect nodes" do
    test "effect_bind's effect and continuation are both shifted" do
      term = {:effect_bind, {:var, 0}, {:lam, :unrestricted, {:int_type}, {:var, 1}}}

      # The `lam` binds one variable, so its body's cutoff moves to 1: `{:var, 1}` is free and
      # shifts, exactly as it would under any other binder-bearing former.
      assert Subst.shift(term, 1, 0) ==
               {:effect_bind, {:var, 1}, {:lam, :unrestricted, {:int_type}, {:var, 2}}}
    end

    test "effect_pure's payload is shifted" do
      assert Subst.shift({:effect_pure, {:var, 0}}, 2, 0) == {:effect_pure, {:var, 2}}
    end

    test "a variable below the cutoff inside an effect node is left alone" do
      assert Subst.shift({:effect_pure, {:var, 0}}, 1, 1) == {:effect_pure, {:var, 0}}
    end
  end

  describe "instantiate/2 substitutes AND strengthens inside effect nodes" do
    test "a telescope binder referenced inside an effect node is substituted" do
      # One binder in the telescope; `{:var, 0}` inside the effect is that binder.
      assert Subst.instantiate({:effect_pure, {:var, 0}}, [{:global, :v}]) ==
               {:effect_pure, {:global, :v}}
    end

    test "an OUTER variable inside an effect node is strengthened past the telescope" do
      # This is the job `Erase`'s collapsible-case optimisation depends on: the telescope's
      # binders are being deleted, so `{:var, 1}` — which pointed past them — must become
      # `{:var, 0}`. Skipping it does not dangle; it silently resolves to the wrong binder.
      assert Subst.instantiate({:effect_pure, {:var, 1}}, [{:global, :v}]) ==
               {:effect_pure, {:var, 0}}
    end

    test "effect_bind strengthens in both the effect and the continuation" do
      term = {:effect_bind, {:var, 1}, {:lam, :unrestricted, {:int_type}, {:var, 2}}}

      assert Subst.instantiate(term, [{:global, :v}]) ==
               {:effect_bind, {:var, 0}, {:lam, :unrestricted, {:int_type}, {:var, 1}}}
    end
  end

  describe "surface regression — an effectful arm of a join-eligible match" do
    @extern "  @extern(:erlang, :display, 1)\n  fn emit(x: Int) -> Effect(Int)\n"

    test "an effectful arm in a match WITH a default arm (join fires) elaborates" do
      # Identical to the control below except for the `_` arm, which is what makes
      # `join_point?` fire and sends every branch body through `Subst.shift`.
      src = """
      mod SEF
      #{@extern}  type C = A | B | D | E | G | H
        fn f(x: C, n: Int) -> Effect(Int) = match x
          A() ->
            let r = emit(n)
            emit(n)
          _ -> emit(n)
      """

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "control — the same arm with every constructor explicit (no join) elaborates" do
      src = """
      mod SEF
      #{@extern}  type C = A | B
        fn f(x: C, n: Int) -> Effect(Int) = match x
          A() ->
            let r = emit(n)
            emit(n)
          B() -> emit(n)
      """

      assert {:ok, _env} = Program.elaborate(src)
    end
  end
end

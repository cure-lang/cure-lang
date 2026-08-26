defmodule Cure.Core.GradeBinderTest do
  @moduledoc """
  Graded Core binders: `{:pi, g, dom, cod}`, `{:lam, g, dom, body}`,
  `{:let, g, ty, val, body}`.

  The load-bearing claim is that **conversion compares grades**. Idris's
  `convBinders` does exactly this (`src/Core/Normalise/Convert.idr:328`):

      if sameBinders bx by && multiplicity bx == multiplicity by

  so `(1 x : A) -> B` is a *different type* from `(x : A) -> B`. Comparison is by
  EQUALITY, never by the subusaging preorder — `Grade.leq/2` belongs to the usage
  check, not to conversion. If `Conv` ignored the grade, a linear function could
  be passed where an unrestricted one is demanded and the whole discipline would
  be decorative.

  Also pinned: `Term.term?/1` REJECTS the old 3-tuple binders. Elixir does not
  raise on a stale `{:pi, Cure.Core.Grade.unrestricted(), a, b}` — it falls through to a catch-all and behaves
  silently wrong — so `term?/1` is the net that makes the migration loud.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Conv, Env, Eval, Grade, Kernel, Serialize, Term}

  @nat {:int_type}

  defp pi(g, dom \\ @nat, cod \\ @nat), do: {:pi, g, dom, cod}

  # `Conv.conv?/5` takes TERMS plus an env/depth; `conv_values?/4` takes values.
  defp conv?(t1, t2), do: Conv.conv?(t1, t2, [], 0)

  describe "shape" do
    test "term?/1 accepts graded binders" do
      assert Term.term?({:pi, :linear, @nat, @nat})
      assert Term.term?({:lam, :unrestricted, @nat, {:var, 0}})
      assert Term.term?({:let, :affine, @nat, {:int_lit, 1}, {:var, 0}})
    end

    test "term?/1 REJECTS the old ungraded 3-tuple binders" do
      # Written with `Tuple`-free literals on purpose: these are the STALE shapes,
      # and a mechanical grade-insertion pass must not "fix" them.
      refute Term.term?(:erlang.list_to_tuple([:pi, @nat, @nat]))
      refute Term.term?(:erlang.list_to_tuple([:lam, @nat, {:var, 0}]))
      refute Term.term?(:erlang.list_to_tuple([:let, @nat, {:int_lit, 1}, {:var, 0}]))
    end

    test "term?/1 rejects a non-grade in the grade slot" do
      refute Term.term?({:pi, Cure.Core.Grade.unrestricted(), :bogus, @nat, @nat})
      refute Term.term?({:lam, Cure.Core.Grade.unrestricted(), 1, @nat, {:var, 0}})
    end
  end

  describe "de Bruijn (grade is not a term and must not be traversed)" do
    test "shift/3 leaves the grade alone" do
      # `:pi` binds in its codomain, so `cod` shifts at cutoff + 1.
      assert Term.shift({:pi, :linear, {:var, 0}, {:var, 1}}, 1, 0) ==
               {:pi, :linear, {:var, 1}, {:var, 2}}
    end

    test "subst/3 leaves the grade alone" do
      # `:lam` binds in its body: index 1 there is the outer 0, and the
      # replacement lifts by one.
      assert Term.subst({:lam, :affine, {:var, 0}, {:var, 1}}, 0, {:var, 7}) ==
               {:lam, :affine, {:var, 7}, {:var, 8}}
    end
  end

  describe "conversion compares grades (Idris Convert.idr:328)" do
    test "identical grades are convertible" do
      for g <- Grade.all(), do: assert(conv?(pi(g), pi(g)))
    end

    test "a linear Pi is NOT convertible with an unrestricted one" do
      refute conv?(pi(:linear), pi(:unrestricted))
      refute conv?(pi(:unrestricted), pi(:linear))
    end

    test "an affine Pi is NOT convertible with a linear one" do
      refute conv?(pi(:affine), pi(:linear))
    end

    test "conversion uses EQUALITY, not the subusaging preorder" do
      # `Grade.leq(:linear, :affine)` holds, but the TYPES are still distinct.
      assert Grade.leq(:linear, :affine)
      refute conv?(pi(:linear), pi(:affine))
    end
  end

  describe "typing" do
    test "a graded Pi is a well-formed type" do
      assert {:ok, {:vtype, _}} = Kernel.infer(Context.empty(), pi(:linear))
    end

    test "a lambda checks against a Pi of the SAME grade" do
      assert :ok =
               Kernel.check(
                 Context.empty(),
                 {:lam, :linear, @nat, {:var, 0}},
                 Eval.eval(pi(:linear), [])
               )
    end

    test "a lambda does NOT check against a Pi of a different grade" do
      assert {:error, _} =
               Kernel.check(
                 Context.empty(),
                 {:lam, :unrestricted, @nat, {:var, 0}},
                 Eval.eval(pi(:linear), [])
               )
    end

    test "a graded let still ζ-reduces" do
      assert Eval.eval({:let, :linear, @nat, {:int_lit, 3}, {:var, 0}}, []) == {:vint, 3}
    end

    test "infer/2 types a graded let by its body's type" do
      # Typing the `{:int_lit, 3}` reads the seeded `:int` builtin, and the let's
      # declared type must be the canonical `Std.Int#Int` family the literal
      # inhabits (the inert `{:int_type}` facade no longer converts against it).
      ctx = Context.empty(Builtins.seed(Env.empty()))
      int = {:data, :"Std.Int#Int", [], []}

      assert {:ok, {:vdata, :"Std.Int#Int", []}} =
               Kernel.infer(ctx, {:let, :linear, int, {:int_lit, 3}, {:var, 0}})
    end
  end

  describe "round-trips carry the grade" do
    test "serialize/decode preserves each grade" do
      for g <- Grade.all() do
        t = {:lam, g, @nat, {:var, 0}}
        assert {:ok, ^t} = t |> Serialize.encode() |> Serialize.decode()
      end
    end

    test "external form preserves the grade" do
      t = {:pi, :affine, @nat, @nat}
      assert t |> Term.to_external() |> Term.from_external() == t
    end

    test "reify ∘ eval is the identity on a graded Pi" do
      for g <- Grade.all() do
        t = pi(g)
        assert Cure.Core.Quote.reify(Eval.eval(t, []), 0) == t
      end
    end
  end
end

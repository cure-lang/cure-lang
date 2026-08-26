defmodule Cure.Core.LetBinderTest do
  @moduledoc """
  The Core `{:let, Cure.Core.Grade.unrestricted(), ty, val, body}` binder (Idris `Core/TT/Binder.idr:93-98`
  `Let : FC -> RigCount -> val -> ty -> Binder`; Lean `Expr.letE` +
  `kernel/type_checker.cpp:475`).

  A `let` binds its value **once** in the term (sharing) while remaining
  definitionally transparent (ζ-reduction), which surface substitution and a
  β-redex each supply only one half of. `body` binds exactly one variable.

  Cure's kernel is an NbE kernel, so ζ is *pushing the evaluated value into the
  environment* (Idris `Core/Normalise/Eval.idr:124-130`) rather than Lean's
  free-variable-plus-re-abstraction. Consequently a `let` never survives
  evaluation: there is no `let` value form, and `Conv`/`Quote` need no clause.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Env, Eval, Kernel, Serialize, Term, Validator}

  # A context whose env seeds the `:int` builtin, needed to type int literals.
  defp seeded_ctx, do: Context.empty(Builtins.seed(Env.empty()))

  # `let T : Type 0 := Int in <body>`
  defp let_int(body), do: {:let, Cure.Core.Grade.unrestricted(), {:type, 0}, {:int_type}, body}

  describe "shape" do
    test "term?/1 accepts a well-formed let and rejects a malformed one" do
      assert Term.term?(let_int({:var, 0}))
      refute Term.term?({:let, Cure.Core.Grade.unrestricted(), {:type, 0}, {:int_type}})
      refute Term.term?({:let, Cure.Core.Grade.unrestricted(), {:type, 0}, {:int_type}, {:var, -1}})
    end
  end

  describe "de Bruijn" do
    test "shift/3 treats body as one binder deeper than ty and val" do
      # ty and val at cutoff c; body at c + 1.
      assert Term.shift({:let, Cure.Core.Grade.unrestricted(), {:var, 0}, {:var, 0}, {:var, 1}}, 1, 0) ==
               {:let, Cure.Core.Grade.unrestricted(), {:var, 1}, {:var, 1}, {:var, 2}}
    end

    test "shift/3 leaves the body's own binder alone" do
      assert Term.shift({:let, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_lit, 1}, {:var, 0}}, 5, 0) ==
               {:let, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_lit, 1}, {:var, 0}}
    end

    test "subst/3 goes under the body's binder and lifts the replacement" do
      # subst j=0, r={:var,7}: ty/val get r; body's index 1 is the outer 0.
      assert Term.subst({:let, Cure.Core.Grade.unrestricted(), {:var, 0}, {:var, 0}, {:var, 1}}, 0, {:var, 7}) ==
               {:let, Cure.Core.Grade.unrestricted(), {:var, 7}, {:var, 7}, {:var, 8}}
    end
  end

  describe "ζ-reduction" do
    test "extend_def/3 binds the variable to its value, not to a neutral" do
      ctx = Context.extend_def(Context.empty(), {:vtype, 0}, {:vint_type})
      assert Eval.eval({:var, 0}, Context.env(ctx)) == {:vint_type}
    end

    test "extend/2 still binds a fresh neutral (no regression)" do
      ctx = Context.extend(Context.empty(), {:vtype, 0})
      assert Eval.eval({:var, 0}, Context.env(ctx)) == {:vneutral, {:nvar, 0}}
    end

    test "env/1 of an extend-only context is unchanged from neutral_env/1" do
      ctx =
        Context.empty()
        |> Context.extend({:vtype, 0})
        |> Context.extend({:vint_type})
        |> Context.extend({:vtype, 1})

      assert Context.env(ctx) == Context.neutral_env(3)
    end

    test "eval/2 ζ-reduces a let to its body under the bound value" do
      assert Eval.eval({:let, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_lit, 3}, {:var, 0}}, []) == {:vint, 3}
    end

    test "a let never survives evaluation into a value" do
      # The body is a lambda; the result is a closure, never a `let` value form.
      assert {:vlam, _g, _, _} = Eval.eval(let_int({:lam, Cure.Core.Grade.unrestricted(), {:var, 0}, {:var, 0}}), [])
    end
  end

  describe "typing" do
    test "infer/2 types a let by its body's type" do
      assert {:ok, {:vdata, :"Std.Int#Int", []}} =
               Kernel.infer(
                 seeded_ctx(),
                 {:let, Cure.Core.Grade.unrestricted(), {:data, :"Std.Int#Int", [], []}, {:int_lit, 3}, {:var, 0}}
               )
    end

    test "a let-bound TYPE variable is transparent in the body (the dependent let)" do
      # let T : Type 0 := Int in (\x : T. x)   ==>   Int -> Int
      #
      # This is the discriminating case. With ζ the λ's domain evaluates to
      # `{:vint_type}`; with an opaque λ-binder it would be a neutral, and the
      # inferred Π would have a stuck domain.
      assert {:ok, {:vpi, _g, {:vint_type}, _cod}} =
               Kernel.infer(Context.empty(), let_int({:lam, Cure.Core.Grade.unrestricted(), {:var, 0}, {:var, 0}}))
    end

    test "check/3 propagates the expected type into the body" do
      # `{:hole, _}` is check-only: it has no inferable type. A β-redex encoding
      # would have to INFER the λ, and so could not admit a hole in the body.
      assert :ok = Kernel.check(Context.empty(), let_int({:hole, :h}), {:vint_type})
    end

    test "the value is checked against the ascribed type" do
      assert {:error, _} =
               Kernel.infer(
                 Context.empty(),
                 {:let, Cure.Core.Grade.unrestricted(), {:int_type}, {:type, 0}, {:int_lit, 1}}
               )
    end

    test "the ascribed type must be a sort" do
      assert {:error, _} =
               Kernel.infer(
                 seeded_ctx(),
                 {:let, Cure.Core.Grade.unrestricted(), {:int_lit, 1}, {:int_lit, 1}, {:int_lit, 1}}
               )
    end
  end

  describe "round-trips" do
    test "serialize/deserialize preserves a let" do
      t = let_int({:lam, Cure.Core.Grade.unrestricted(), {:var, 0}, {:var, 0}})
      assert {:ok, ^t} = t |> Serialize.encode() |> Serialize.decode()
    end

    test "external form round-trips" do
      t = let_int({:var, 0})
      assert t |> Term.to_external() |> Term.from_external() == t
    end

    test "the validator accepts a let with no violations" do
      assert {:ok, []} = Validator.validate(let_int({:var, 0}))
    end
  end
end

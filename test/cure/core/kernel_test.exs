defmodule Cure.Core.KernelTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Kernel, Context, Eval}

  describe "infer/check for Type / var / Pi (M2.2)" do
    test "infer Type0 : Type1" do
      assert {:ok, {:vtype, 1}} == Kernel.infer(Context.empty(), {:type, 0})
    end

    test "infer a variable returns its context type" do
      ctx = Context.extend(Context.empty(), {:vtype, 0})
      assert {:ok, {:vtype, 0}} == Kernel.infer(ctx, {:var, 0})
    end

    test "infer Pi uses the max-level rule" do
      assert {:ok, {:vtype, 1}} ==
               Kernel.infer(Context.empty(), {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}})
    end

    test "check is cumulative on sorts: Type0 : Type1 <= Type2" do
      assert :ok == Kernel.check(Context.empty(), {:type, 0}, {:vtype, 2})
    end

    test "check fails on a real mismatch (Type1 : Type2 is not <= Type0)" do
      assert {:error, _} = Kernel.check(Context.empty(), {:type, 1}, {:vtype, 0})
    end
  end

  describe "infer/check for lambda + application (M2.3)" do
    test "check a lambda against a Pi type" do
      pi = Eval.eval({:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:type, 0}}, [])
      assert :ok == Kernel.check(Context.empty(), {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, pi)
    end

    test "application substitutes the argument into a dependent codomain" do
      # ctx: S : Type0 (a small type, var 1); f : Π(x:Type0).x (var 0).
      ctx0 = Context.extend(Context.empty(), {:vtype, 0})
      pi_val = Eval.eval({:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, Context.env(ctx0))
      ctx1 = Context.extend(ctx0, pi_val)
      # infer (f S) : the codomain is the bound var, so the result type is S itself
      # (the neutral standing for the small-type variable at level 0).
      assert {:ok, {:vneutral, {:nvar, 0}}} ==
               Kernel.infer(ctx1, {:app, {:var, 0}, {:var, 1}})
    end

    test "simple application yields the (constant) codomain" do
      f = {:lam, Cure.Core.Grade.unrestricted(), {:type, 1}, {:var, 0}}
      assert {:ok, {:vtype, 1}} == Kernel.infer(Context.empty(), {:app, f, {:type, 0}})
    end

    test "negative: applying a non-function" do
      assert {:error, :not_a_function} =
               Kernel.infer(Context.empty(), {:app, {:type, 0}, {:type, 0}})
    end

    test "negative: argument type mismatch" do
      # λ(x:Type0).x expects a small type; Type0 itself is in Type1, not Type0.
      app = {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:type, 0}}
      assert {:error, {:conversion_failure, _inferred, _expected}} = Kernel.infer(Context.empty(), app)
    end
  end
end

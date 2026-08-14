defmodule Antigen.BuiltinBoolMigrationTest do
  @moduledoc """
  Migration-soundness antibody for retiring the `bool_elim` primitive in favor of
  a `:case` on the inductive Bool. Guards the three properties the retirement rests
  on: the primitive term form is gone, the general `:case` certifier still catches a
  self-call hidden in a Bool branch (the soundness property `bool_elim`'s bespoke
  clauses used to carry), and primitive ops construct the inductive Bool.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Kernel, Term}

  test "the retired bool_elim term form is no longer a well-formed Core term" do
    refute Term.term?({:bool_elim, {:int_lit, 0}, {:int_type}, {:int_lit, 1}, {:int_lit, 2}})
  end

  test "a self-call hidden in a :case-on-Bool branch is NOT certified terminating" do
    # f = λn:Int. case (n == 0) of { True -> 0 ; False -> f n }  (diverges for n != 0)
    body =
      {:lam, Cure.Core.Grade.unrestricted(), {:int_type},
       {:case, {:app, {:app, {:global, :int_eq}, {:var, 0}}, {:int_lit, 0}},
        {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bool, [], []}, {:int_type}},
        [{:True, 0, {:int_lit, 0}}, {:False, 0, {:app, {:global, :f}, {:var, 0}}}]}}

    env = Builtins.seed(Env.empty()) |> Env.add_def(:f, {:int_type}, body)
    refute Cure.Elab.TotalityClosure.provably_total?(env, :f)
  end

  test "a comparison constructs the inductive Bool, not a primitive Bool value" do
    ctx = Context.empty(Builtins.seed(Env.empty()))

    bool_family = Cure.Elab.Name.qualify("Std.Bool", :Bool)

    assert {:ok, {:vdata, ^bool_family, []}} =
             Kernel.infer(ctx, {:app, {:app, {:global, :int_lt}, {:int_lit, 3}}, {:int_lit, 5}})
  end
end

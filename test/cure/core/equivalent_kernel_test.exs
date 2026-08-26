defmodule Cure.Core.EquivalentKernelTest do
  @moduledoc """
  Inductive-identity twins of the retiring primitive kernel pins (Phase C
  Step 2, add-then-retire protocol). `test/cure/core/eq_test.exs` and
  `test/cure/core/rewrite_test.exs` pin formation/introduction/elimination
  properties of the PRIMITIVE `{:eq}`/`{:refl}`/`{:rewrite}` forms; those forms
  retire in Phase C, so each load-bearing property is re-pinned here against
  the genuine inductive `Equivalent`/`reflexive` and the J/subst `:case`
  transport. This file runs green SIDE BY SIDE with the originals while the
  primitives still round-trip — the cross-check that licenses deleting the
  originals in the removal commits.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Env, Eval, Inductive, Kernel}

  # `Builtins.seed` registers Equivalent/reflexive under owner-qualified keys
  # (`Env.with_owner(env, "Std.Equivalent")`), and the elaborator emits those same
  # canonical names — a real `reflexive(x)` becomes `{:ctor, :"Std.Equivalent#reflexive", …}`.
  # These hand-built Core terms must use the canonical identities too, or the kernel's
  # ctor↔family check sees a bare name against a qualified family and reports `:foreign_ctor`.
  @equiv :"Std.Equivalent#Equivalent"
  @refl :"Std.Equivalent#reflexive"

  @dec {:data, :Dec, [], []}
  @causal {:ctor, :Causal, []}
  @dcoupled {:ctor, :Dcoupled, []}

  defp env do
    Env.empty()
    |> Builtins.seed(MapSet.new())
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
    |> Inductive.declare(Inductive.family(:Box, [], [{:d, @dec}], 0), [
      Inductive.ctor(:mk, [{:x, @dec}], [{:var, 0}])
    ])
  end

  defp eq_val(ty, a, b), do: Eval.eval({:data, @equiv, [ty], [a, b]}, [])
  defp box(d), do: Eval.eval({:data, :Box, [], [d]}, [])

  # J/subst transport for CLOSED ty/motive/l (shifts of closed terms elided) —
  # mirrors the elaborator's `transport_case/4` and the antibody's twin helper.
  defp transport(proof, ty, motive, l) do
    scrut_ty = {:data, @equiv, [ty], [{:var, 1}, {:var, 0}]}
    arrow = {:pi, Cure.Core.Grade.unrestricted(), {:app, motive, {:var, 2}}, {:app, motive, {:var, 2}}}

    arrow_motive =
      {:lam, Cure.Core.Grade.unrestricted(), ty,
       {:lam, Cure.Core.Grade.unrestricted(), ty, {:lam, Cure.Core.Grade.unrestricted(), scrut_ty, arrow}}}

    {:case, proof, arrow_motive, [{@refl, 1, {:lam, Cure.Core.Grade.unrestricted(), {:app, motive, l}, {:var, 0}}}]}
  end

  # motive (x.M) = λx. Box(x)
  @motive {:lam, Cure.Core.Grade.unrestricted(), @dec, {:data, :Box, [], [{:var, 0}]}}

  # ---- formation / introduction (eq_test twins) ------------------------------

  test "Equivalent formation is a type at the level of its carrier" do
    assert {:ok, {:vtype, 0}} ==
             Kernel.infer(Context.empty(env()), {:data, @equiv, [@dec], [@causal, @causal]})
  end

  test "reflexive checks against a reflexive equation" do
    assert :ok ==
             Kernel.check(
               Context.empty(env()),
               {:ctor, @refl, [@causal]},
               eq_val(@dec, @causal, @causal)
             )
  end

  test "reflexive uses real conversion (beta), not name matching" do
    # Equivalent(Dec, (λx:Dec.x) Causal, Causal) — endpoints equal only after β.
    lhs = {:app, {:lam, Cure.Core.Grade.unrestricted(), @dec, {:var, 0}}, @causal}

    assert :ok ==
             Kernel.check(
               Context.empty(env()),
               {:ctor, @refl, [@causal]},
               eq_val(@dec, lhs, @causal)
             )
  end

  test "negative: reflexive rejects a non-reflexive equation (the audit bug)" do
    assert {:error, _} =
             Kernel.check(
               Context.empty(env()),
               {:ctor, @refl, [@causal]},
               eq_val(@dec, @causal, @dcoupled)
             )
  end

  test "infers a params-on-spine reflexive as a reflexive equation (K6 §E.1)" do
    assert {:ok, {:vdata, @equiv, [{:vdata, :Dec, []}, {:vctor, :Causal, []}, {:vctor, :Causal, []}]}} =
             Kernel.infer(Context.empty(env()), {:ctor, @refl, [@dec, @causal]})
  end

  # ---- elimination: the J/subst transport (rewrite_test twins) ---------------

  test "the :case transport along reflexive types at M[b/x]" do
    ctx = Context.extend(Context.empty(env()), box(@causal))
    proof = {:ctor, @refl, [@dec, @causal]}
    node = {:app, transport(proof, @dec, @motive, @causal), {:var, 0}}
    assert {:ok, {:vdata, :Box, [{:vctor, :Causal, []}]}} = Kernel.infer(ctx, node)
  end

  test "the :case transport reduces at runtime to its body (proof irrelevance)" do
    proof = {:ctor, @refl, [@causal]}
    node = {:app, transport(proof, @dec, @motive, @causal), {:var, 0}}
    assert Eval.eval(node, [{:vneutral, {:nvar, 0}}]) == {:vneutral, {:nvar, 0}}
  end

  test "negative: a transported body not of type M[a/x] is rejected" do
    ctx = Context.extend(Context.empty(env()), box(@dcoupled))
    proof = {:ctor, @refl, [@dec, @causal]}
    node = {:app, transport(proof, @dec, @motive, @causal), {:var, 0}}
    assert {:error, _} = Kernel.infer(ctx, node)
  end
end

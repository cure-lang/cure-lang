defmodule Cure.Elab.EmitHoleFirewallTest do
  # The emit/release boundary is the single trusted enforcement point for "no
  # unfilled obligation ships" (K3). It must validate the *pre-erase* Core body:
  # `Erase.erase` drops erased subterms (the collapsible :case transport's
  # proof scrutinee vanishes wholesale), so a hole hidden in an erased position
  # is invisible to the old erase-then-`has_hole?` gate and shipped silently (#102).
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.Emit

  # (The primitive `{:rewrite}`-proof versions of the #102 tests were retired
  # with the form itself — group-A removal commit; the :case-transport twins
  # below were cross-checked side by side first.)

  test "emit still refuses a plain body hole" do
    env = Env.empty() |> Env.add_def(:h, {:type, 0}, {:hole, "body"}, [])
    assert {:error, {:unfilled_hole, :h}} = Emit.compile_forms(env, :M, [:h])
  end

  test "emit still accepts a hole-free def (no false positive)" do
    env = Env.empty() |> Env.add_def(:clean, {:type, 0}, {:int_lit, 42}, [])
    assert {:ok, _forms} = Emit.compile_forms(env, :M, [:clean])
  end

  # Phase C twins (add-then-retire): the `{:rewrite}` node retires; the erased
  # position a hole can hide in is now the PROOF SCRUTINEE of the J/subst
  # `:case` transport — `Erase` drops the whole collapsible case (single
  # all-erased-fields `reflexive` branch), so the pre-erase `has_hole?` gate is
  # still all that stands between an unfilled proof obligation and a shipped
  # binary. Same #102 property, new vehicle.
  defp case_transport_with_hole_proof do
    id_branch = {:reflexive, 1, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}}
    {:app, {:case, {:hole, "p"}, {:type, 0}, [id_branch]}, {:int_lit, 0}}
  end

  test "emit refuses a hole hiding in the erased proof scrutinee of a :case transport" do
    env = Env.empty() |> Env.add_def(:tainted3, {:type, 0}, case_transport_with_hole_proof(), [])
    assert {:error, {:unfilled_hole, :tainted3}} = Emit.compile_forms(env, :M3, [:tainted3])
  end

  test "compile_and_load refuses a :case-transport proof hole too (same gate)" do
    env = Env.empty() |> Env.add_def(:tainted4, {:type, 0}, case_transport_with_hole_proof(), [])

    assert {:error, {:unfilled_hole, :tainted4}} =
             Emit.compile_and_load(env, module: :M4, functions: [:tainted4])
  end
end

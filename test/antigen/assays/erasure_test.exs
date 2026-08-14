defmodule Antigen.Assays.ErasureTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.Erasure, Challenge}
  alias Antigen.Generators.ErasureTerm
  alias Cure.Core.{Env, Inductive}

  defp il(n), do: {:int_lit, n}

  defp ctor_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:P, [], [], 0), [
      Inductive.ctor(:MkQ, [{:a, {:int_type}}, {:b, {:int_type}}], [], [:unrestricted, :erased]),
      Inductive.ctor(:MkP, [{:a, {:int_type}}, {:b, {:int_type}}], [], [:erased, :unrestricted])
    ])
  end

  defp idem_ch(env, t) do
    Challenge.new(
      kind: :erasure_term,
      assay: "erasure/idempotent",
      label: :positive,
      payload: %{env: env, term: t},
      seed: 1
    )
  end

  # app-head defs: f present-first (clean), g erased-first (the finding). Defined
  # once here at module level (NOT re-declared by Task 2's describe block) so both
  # this task's app-head known-finding test and Task 2's selective tests share it.
  defp app_env(env) do
    ty =
      {:pi, Cure.Core.Grade.unrestricted(), {:int_type},
       {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}}}

    env
    |> Env.add_def(:f, ty, {:int_lit, 0}, [:unrestricted, :erased])
    |> Env.add_def(:g, ty, {:int_lit, 0}, [:erased, :unrestricted])
  end

  defp app2(head, x0, x1), do: {:app, {:app, head, x0}, x1}

  defp runtime_case(scrutinee) do
    {:case, scrutinee, il(0), [{:MkQ, 2, il(0)}, {:MkP, 2, il(0)}]}
  end

  test "idempotent baseline: present-first ctor erases idempotently" do
    env = ctor_env()
    assert Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]})) == :ok
  end

  test "hole-preservation baseline: a hole-free term stays hole-free after erase" do
    env = ctor_env()
    assert Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]})) == :ok
  end

  test "idempotent negative control: a wrapping erase stub is not a fixpoint" do
    env = ctor_env()
    k = %{Erasure.__real__() | erase: fn _e, t -> {:ctor, :Wrap, [t]} end}
    assert {:violation, {:erase_not_idempotent, _}} = Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]}), k)
  end

  test "hole negative control: an erase stub that introduces a hole is caught" do
    env = ctor_env()
    k = %{Erasure.__real__() | erase: fn _e, _t -> {:hole, :x} end}
    assert {:violation, {:hole_introduced, _}} = Erasure.run(idem_ch(env, {:ctor, :MkQ, [il(1), il(2)]}), k)
  end

  describe "erase/2 non-idempotence — FIXED, now a regression guard (spec §3, §9-2/§9-3)" do
    # These terms are NOT in erase_challenges/0 (reconciliation #1). They once
    # surfaced a genuine erase/2 defect (the :ctor/:app-head clauses re-filtered
    # already-shrunk args by re-zipping the full quantity vector). The fix added an
    # arity guard to Cure.Elab.Erase (only filter full-form args); these two cases —
    # the erased-before-present `:MkP` ctor and `g` def — are now idempotent, so the
    # assay reports :ok. They stay here as regression guards: they go red again if
    # the arity guard is removed and the zip-realignment hazard returns.
    test "ctor erased-before-present ordering is now idempotent (regression guard)" do
      env = ctor_env()
      assert Erasure.run(idem_ch(env, {:ctor, :MkP, [il(1), il(2)]})) == :ok
    end

    test "app-head erased-before-present ordering is now idempotent (regression guard)" do
      env = app_env(ctor_env())
      assert Erasure.run(idem_ch(env, app2({:global, :g}, il(1), il(2)))) == :ok
    end
  end

  describe "erasure/selective (V4a)" do
    defp sel_ch(env, t, surface) do
      Challenge.new(
        kind: :erasure_term,
        assay: "erasure/selective",
        label: :positive,
        payload: %{env: env, term: t, surface: surface},
        seed: 1
      )
    end

    test "ctor selective baseline: keeps exactly the :unrestricted positions (leaf args)" do
      env = ctor_env()
      assert Erasure.run(sel_ch(env, {:ctor, :MkQ, [il(1), il(2)]}, :ctor)) == :ok
    end

    test "app-head selective baseline: keeps exactly the :unrestricted def positions (leaf args)" do
      env = app_env(ctor_env())
      assert Erasure.run(sel_ch(env, app2({:global, :f}, il(1), il(2)), :app)) == :ok
    end

    test "ctor selective negative control: an erase stub dropping the :unrestricted position" do
      env = ctor_env()
      k = %{Erasure.__real__() | erase: fn _e, {:ctor, c, _args} -> {:ctor, c, []} end}

      assert {:violation, {:wrong_positions_kept, :MkQ}} =
               Erasure.run(sel_ch(env, {:ctor, :MkQ, [il(1), il(2)]}, :ctor), k)
    end

    test "app-head selective negative control: an erase stub dropping a :unrestricted arg" do
      env = app_env(ctor_env())
      # drops all args
      k = %{Erasure.__real__() | erase: fn _e, _t -> {:global, :f} end}

      assert {:violation, {:wrong_positions_kept, :f}} =
               Erasure.run(sel_ch(env, app2({:global, :f}, il(1), il(2)), :app), k)
    end
  end

  describe "erasure/wellformed (V4a)" do
    defp wf_ch(env, t) do
      Challenge.new(
        kind: :erasure_term,
        assay: "erasure/wellformed",
        label: :positive,
        payload: %{env: env, term: t},
        seed: 1
      )
    end

    test "baseline: term?(t) => term?(erase t)" do
      env = ctor_env()
      assert Erasure.run(wf_ch(env, {:ctor, :MkQ, [il(1), il(2)]})) == :ok
    end

    test "negative control: an erase stub returning a malformed term" do
      env = ctor_env()
      k = %{Erasure.__real__() | erase: fn _e, _t -> {:not_a_node, :garbage, 999} end}
      assert {:violation, {:erase_ill_formed, _}} = Erasure.run(wf_ch(env, {:ctor, :MkQ, [il(1), il(2)]}), k)
    end
  end

  describe "relevance/soundness (V4b)" do
    # quantities = [:erased] — binder 0 is erased; a body using {:var, 0} relevantly must be rejected.
    defp rel_ch(env, body, site) do
      Challenge.new(
        kind: :erasure_term,
        assay: "relevance/soundness",
        label: :negative,
        payload: %{env: env, name: :d, quantities: [:erased], body: body, site: site},
        seed: 1
      )
    end

    test "returned site: erased binder is the body result — rejected" do
      assert Erasure.run(rel_ch(Env.empty(), {:var, 0}, :returned)) == :ok
    end

    test "applied site: erased binder applied as a function head — rejected" do
      assert Erasure.run(rel_ch(Env.empty(), {:app, {:var, 0}, {:int_lit, 0}}, :applied)) == :ok
    end

    test "scrutinee site: erased binder matched in a case — rejected" do
      # An empty case is erased as unreachable and therefore does not inspect its
      # scrutinee at runtime.  Use a genuine two-alternative runtime case so this
      # fixture tests the relevant discriminant path rather than the collapsible
      # proof-elimination exemption.
      assert Erasure.run(rel_ch(ctor_env(), runtime_case({:var, 0}), :scrutinee)) == :ok
    end

    test "present_arg site: erased binder passed in a :unrestricted ctor position — rejected" do
      env = ctor_env()
      # MkQ position 0 is :unrestricted; putting {:var,0} there is a relevant use of an erased binder
      assert Erasure.run(rel_ch(env, {:ctor, :MkQ, [{:var, 0}, {:int_lit, 0}]}, :present_arg)) == :ok
    end

    test "clean-body control: erased binder unused is accepted" do
      ch =
        Challenge.new(
          kind: :erasure_term,
          assay: "relevance/soundness",
          label: :positive,
          payload: %{env: Env.empty(), name: :d, quantities: [:erased], body: {:int_lit, 7}, site: nil},
          seed: 1
        )

      assert Erasure.run(ch) == :ok
    end

    test "negative control: a relevance_check stub that accepts a relevant body" do
      k = %{Erasure.__real__() | relevance_check: fn _e, _n, _q, _b -> :ok end}
      assert {:violation, {:relevance_unsound, :returned}} = Erasure.run(rel_ch(Env.empty(), {:var, 0}, :returned), k)
    end

    test "clean-body negative control: a relevance_check stub that rejects a clean body" do
      ch =
        Challenge.new(
          kind: :erasure_term,
          assay: "relevance/soundness",
          label: :positive,
          payload: %{env: Env.empty(), name: :d, quantities: [:erased], body: {:int_lit, 7}, site: nil},
          seed: 1
        )

      k = %{
        Erasure.__real__()
        | relevance_check: fn _e, _n, _q, _b ->
            {:error, {:erased_used_relevantly, %{def: :d, binder: 0, site: :returned}}}
          end
      }

      assert {:violation, {:clean_body_rejected, :d}} = Erasure.run(ch, k)
    end

    test "wrong-site negative control: a relevance_check stub reporting a mismatched site" do
      k = %{
        Erasure.__real__()
        | relevance_check: fn _e, _n, _q, _b ->
            {:error, {:erased_used_relevantly, %{def: :d, binder: 0, site: :applied}}}
          end
      }

      assert {:violation, {:relevance_wrong_site, :returned, :applied}} =
               Erasure.run(rel_ch(Env.empty(), {:var, 0}, :returned), k)
    end
  end

  describe "generator + runner wiring" do
    alias Antigen.Runner

    test "each catalog is non-empty and correctly tagged" do
      assert length(ErasureTerm.erase_challenges()) > 0
      assert length(ErasureTerm.relevance_challenges()) > 0
      ids = MapSet.new(ErasureTerm.erase_challenges(), & &1.assay)
      assert "erasure/idempotent" in ids and "erasure/selective" in ids and "erasure/wellformed" in ids
      assert Enum.all?(ErasureTerm.relevance_challenges(), &(&1.assay == "relevance/soundness"))
    end

    test "runner dispatches all four ids and the whole clean catalog is :ok" do
      all = ErasureTerm.erase_challenges() ++ ErasureTerm.relevance_challenges()
      assert Enum.all?(all, fn c -> Runner.replay_one(c) == :ok end)
    end
  end
end

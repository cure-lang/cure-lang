defmodule Cure.Core.ValidatorTest do
  # async: false — Task 5 adds a test that calls `Application.put_env(:cure,
  # :final_core_config, …)`. That key is process-independent GLOBAL state read
  # by `Kernel.check_def/2` (the shared TCB entry point every other `test/cure/core/`
  # suite also calls). Running this file concurrently with another async suite
  # while the override is live would risk a spurious cross-file rejection the
  # moment any other suite's checked def contains a hole. Given this codebase's
  # own history of kernel-related test-concurrency hazards (see Global
  # Constraints), keep this whole file serial rather than relying on no other
  # suite ever adding a hole-bearing `check_def` call.
  use ExUnit.Case, async: false
  alias Cure.Core.Validator

  describe "clause registry and Wave-0 config" do
    test "wave0_config assigns a mode to every registered clause and no others" do
      assert MapSet.new(Map.keys(Validator.wave0_config())) == MapSet.new(Validator.clauses())
    end

    test "only the retired-primitive clauses are :reject in Wave 0" do
      # Wave 0 was pure instrumentation until Phase C retired the primitive
      # identity forms; a smuggled {:eq}/{:refl} node now rejects even in the
      # dev-time default (the kernel has no clauses for them, so any such node
      # is a firewall breach, not tech debt). D2 retired the primitive Sigma
      # the same way, so {:sigma}/{:pair}/{:fst}/{:snd} join the reject set.
      # K2 completes the same ratchet for {:prim}: builtin-op globals replace
      # the node, the kernel clauses are stripped, so no_prim_node joins the set.
      # `grade_on_binders` joined the rejecting set when Core binders gained a QTT
      # grade: an ungraded 3-tuple binder is now a stale shape, not a current one.
      rejecting = for {c, :reject} <- Validator.wave0_config(), do: c

      assert Enum.sort(rejecting) ==
               [:grade_on_binders, :no_eq_node, :no_prim_node, :no_sigma_node]
    end

    test "legacy-detecting clauses warn; retired-primitive and stale-binder clauses reject" do
      cfg = Validator.wave0_config()
      assert cfg.no_hole == :warn
      assert cfg.no_eq_node == :reject
      assert cfg.no_rewrite_node == :warn
      assert cfg.no_prim_node == :reject
      assert cfg.no_absurd_node == :warn
      assert cfg.grade_on_binders == :reject
      assert cfg.qualified_syms == :off
      assert cfg.level_expr == :off
    end
  end

  describe "nodes/1 walker" do
    test "enumerates the term and all sub-terms pre-order" do
      term = {:app, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}, {:int_lit, 3}}
      got = Cure.Core.Validator.nodes(term)
      assert hd(got) == term
      assert {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}} in got
      assert {:type, 0} in got
      assert {:var, 0} in got
      assert {:int_lit, 3} in got
    end

    test "descends into case scrut/motive/branch bodies without yielding branch tuples" do
      # a branch for a constructor literally named :refl must NOT surface as a {:refl, _} node
      term = {:case, {:var, 0}, {:type, 0}, [{:refl, 1, {:var, 0}}]}
      got = Cure.Core.Validator.nodes(term)
      assert {:var, 0} in got
      assert {:type, 0} in got
      refute Enum.any?(got, &match?({:refl, _}, &1))
    end

    test "descends into data params/indices and ctor args" do
      term = {:data, :Vec, [{:int_type}], [{:int_lit, 2}]}
      got = Cure.Core.Validator.nodes(term)
      assert {:int_type} in got
      assert {:int_lit, 2} in got
    end
  end

  describe "validate/2 (Wave-0 active clauses)" do
    test "a clean current-grammar term yields no diagnostics" do
      assert {:ok, []} = Validator.validate({:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}})
    end

    test "a smuggled legacy :eq node REJECTS even under the Wave-0 default (Phase C flip)" do
      assert {:error, [r]} = Validator.validate({:eq, {:type, 0}, {:var, 0}, {:var, 0}})
      assert r.clause == :no_eq_node and r.mode == :reject

      assert {:error, [r2]} = Validator.validate({:refl, {:var, 0}})
      assert r2.clause == :no_eq_node and r2.mode == :reject
    end

    test "a hole warns under Wave-0 config (does not reject yet)" do
      assert {:ok, [w]} = Validator.validate({:hole, :h0})
      assert w.clause == :no_hole and w.mode == :warn
    end

    test "an :absurd node warns; a :prim node rejects (K2 ratchet complete)" do
      assert {:ok, [%{clause: :no_absurd_node}]} = Validator.validate({:absurd})

      assert {:error, [%{clause: :no_prim_node, mode: :reject}]} =
               Validator.validate({:prim, :add, [{:int_lit, 1}, {:int_lit, 2}]})

      assert {:error, [%{clause: :no_prim_node, mode: :reject}]} =
               Validator.validate(
                 {:prim, :add, [{:int_lit, 1}, {:int_lit, 2}]},
                 Validator.release_config()
               )
    end

    # D2 T4b: the ratchet completed — Wave-0 now REJECTS the primitive Sigma
    # nodes too (the kernel grammar no longer contains them; a node here is
    # smuggled non-grammar, exactly like Phase C's no_eq_node endgame).
    test "each primitive Sigma node rejects under Wave-0 AND release_config (D2 ratchet complete)" do
      for node <- [
            {:sigma, {:type, 0}, {:type, 0}},
            {:pair, {:var, 0}, {:var, 0}},
            {:fst, {:var, 0}},
            {:snd, {:var, 0}}
          ] do
        assert {:error, [%{clause: :no_sigma_node, mode: :reject}]} = Validator.validate(node)

        assert {:error, [%{clause: :no_sigma_node, mode: :reject}]} =
                 Validator.validate(node, Validator.release_config())
      end
    end

    test "config override to :reject flips admission (the per-wave flip mechanism)" do
      cfg = Map.put(Validator.wave0_config(), :no_hole, :reject)
      assert {:error, [r]} = Validator.validate({:hole, :h0}, cfg)
      assert r.clause == :no_hole and r.mode == :reject
    end
  end

  describe "grade_on_binders detects a STALE ungraded binder" do
    # Built with `list_to_tuple/1` on purpose: these are the pre-QTT shapes, and a
    # mechanical grade-insertion pass must not be able to "fix" them into 4-tuples.
    defp stale_pi, do: :erlang.list_to_tuple([:pi, {:type, 0}, {:var, 0}])

    test "fires on a stale ungraded binder when set to :warn" do
      cfg = Map.put(Validator.wave0_config(), :grade_on_binders, :warn)
      assert {:ok, ws} = Validator.validate(stale_pi(), cfg)
      assert Enum.any?(ws, &(&1.clause == :grade_on_binders))
    end

    test "rejects a stale ungraded binder under the Wave-0 default" do
      assert Validator.wave0_config().grade_on_binders == :reject
      assert {:error, _} = Validator.validate(stale_pi())
    end

    test "does NOT fire on a graded binder" do
      cfg = Map.put(Validator.wave0_config(), :grade_on_binders, :warn)
      graded = {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}
      assert {:ok, ws} = Validator.validate(graded, cfg)
      refute Enum.any?(ws, &(&1.clause == :grade_on_binders))
    end

    test "qualified_syms fires on a bare-atom global; level_expr fires on an integer level" do
      cfg =
        Validator.wave0_config()
        |> Map.put(:qualified_syms, :warn)
        |> Map.put(:level_expr, :warn)

      assert {:ok, ws} = Validator.validate({:app, {:global, :foo}, {:type, 2}}, cfg)
      assert Enum.any?(ws, &(&1.clause == :qualified_syms))
      assert Enum.any?(ws, &(&1.clause == :level_expr))
    end

    test "in Wave-0 config these deferred clauses stay silent (are :off)" do
      assert {:ok, []} = Validator.validate({:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:global, :foo}})
    end
  end

  describe "check_def_config/0 and kernel wiring" do
    alias Cure.Core.{Validator, Env, Kernel}

    test "check_def_config defaults to the Wave-0 config" do
      assert Validator.check_def_config() == Validator.wave0_config()
    end

    test "a clean def still admits under the default (non-breaking)" do
      # idty : Type 0 -> Type 0  ;  body = λx. x  (clean, admits)
      env =
        Env.add_def(
          Env.empty(),
          :idty,
          {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:type, 0}},
          {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}
        )

      assert :ok == Kernel.check_def(env, :idty)
    end

    test "with a reject-override config, a hole-bearing def fails admission" do
      env =
        Env.add_def(
          Env.empty(),
          :withhole,
          {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:type, 0}},
          {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:hole, :h}}
        )

      Application.put_env(:cure, :final_core_config, Map.put(Validator.wave0_config(), :no_hole, :reject))
      on_exit(fn -> Application.delete_env(:cure, :final_core_config) end)

      assert {:error, {:final_core_violation, [%{clause: :no_hole}]}} = Kernel.check_def(env, :withhole)
    end

    # (The legacy-node-in-TYPE test — {:eq} type / {:refl} body through
    # check_def — was retired in the group-B removal commit: the kernel now
    # rejects those forms as unknown grammar BEFORE the validator scan can run.
    # Its wiring property, "the final-core scan covers the declared TYPE", is
    # carried by the post-retirement probe below, added + cross-checked in the
    # Step-2 commit while the legacy forms still round-tripped.)

    test "a violating node in the declared TYPE is caught too — post-retirement probe" do
      # Phase C twin of the legacy-node test above (added FIRST, per the
      # add-then-retire protocol): once the primitive `{:eq}`/`{:refl}` kernel
      # clauses are removed, that fixture can no longer REACH the validator —
      # `check_def` kernel-typechecks type and body BEFORE the final-Core scan,
      # and a primitive node is then unknown grammar there. The wiring property
      # it proved (the scan covers the declared TYPE, not just the body) is
      # re-proved here with current-grammar nodes: `natalias`'s TYPE is a
      # bare-atom `{:global, …}` reference (a `qualified_syms` violation), its
      # body a hole (kernel-accepted at any goal; only a `no_hole` WARN under
      # this config). Under a `qualified_syms: :reject` override the rejection
      # can therefore only originate in the type_term scan.
      {:ok, env0} = Cure.Elab.Program.elaborate("mod M\nend\n")

      env =
        env0
        |> Env.add_def(:natty, {:type, 0}, {:data, :Nat, [], []})
        |> Env.add_def(:natalias, {:global, :natty}, {:hole, "inhabit"})

      cfg = Map.put(Validator.wave0_config(), :qualified_syms, :reject)
      Application.put_env(:cure, :final_core_config, cfg)
      on_exit(fn -> Application.delete_env(:cure, :final_core_config) end)

      assert {:error, {:final_core_violation, rejections}} = Kernel.check_def(env, :natalias)
      assert Enum.any?(rejections, &(&1.clause == :qualified_syms))
    end
  end

  describe "release_config/0 (the strict ratchet, K3)" do
    test "no_hole is :reject in release mode" do
      assert Validator.release_config()[:no_hole] == :reject
    end

    test "no_prim_node is :reject in wave0 AND release (K2 — {:prim} stripped, builtin-op globals canonical)" do
      assert Validator.wave0_config()[:no_prim_node] == :reject
      assert Validator.release_config()[:no_prim_node] == :reject
    end

    test "no_absurd_node is :reject in release mode (K4 — the node is gone from final Core)" do
      assert Validator.release_config()[:no_absurd_node] == :reject
      assert {:error, rejections} = Validator.validate({:absurd}, Validator.release_config())
      assert Enum.any?(rejections, &(&1.clause == :no_absurd_node))
    end

    test "every registered clause has a mode in release_config, and none is looser than Wave-0" do
      rel = Validator.release_config()
      assert MapSet.new(Map.keys(rel)) == MapSet.new(Validator.clauses())
      # release only tightens: a clause never becomes :off/:warn where Wave-0 was stricter
      rank = %{off: 0, warn: 1, reject: 2}
      w0 = Validator.wave0_config()
      for c <- Validator.clauses(), do: assert(rank[rel[c]] >= rank[w0[c]], "clause #{c} loosened")
    end

    test "rejects a hole hidden in an erased (rewrite-proof) position — the #102 leak" do
      # Erase would drop the rewrite proof, but the validator descends into it.
      term = {:rewrite, {:hole, "p"}, {:type, 0}, {:ctor, :ok, []}}
      assert {:error, rejections} = Validator.validate(term, Validator.release_config())
      assert Enum.any?(rejections, &(&1.clause == :no_hole))
    end

    test "still admits a hole-free, node-clean term" do
      assert {:ok, _warnings} = Validator.validate({:ctor, :ok, []}, Validator.release_config())
    end

    test "no_eq_node is :reject in release (K1a — primitive eq/refl retired from produced Core)" do
      assert Validator.release_config()[:no_eq_node] == :reject
      # primitive refl: dead-producer (bridge_step migrated to inductive refl,
      # f3b0e73; surface refl + symmetry_proof already inductive) → rejected.
      assert {:error, rj_refl} = Validator.validate({:refl, {:int_lit, 1}}, Validator.release_config())
      assert Enum.any?(rj_refl, &(&1.clause == :no_eq_node))
      # primitive :eq type-former: no producers (mk_eq builds inductive {:data,:Eq}) → rejected.
      eq = {:eq, {:int_type}, {:int_lit, 1}, {:int_lit, 1}}
      assert {:error, rj_eq} = Validator.validate(eq, Validator.release_config())
      assert Enum.any?(rj_eq, &(&1.clause == :no_eq_node))
    end

    test "primitive :rewrite REJECTS in release (Phase B landed — no producers remain)" do
      # Phase B retired the {:rewrite} producers (rewrite → J/subst :case
      # transport) and Phase C stripped the kernel clauses; a {:rewrite} node in
      # final Core is now a smuggled non-grammar node and must block release.
      rw = {:rewrite, {:ctor, :refl, [{:int_type}, {:int_lit, 1}]}, {:type, 0}, {:ctor, :ok, []}}
      assert {:error, rejections} = Validator.validate(rw, Validator.release_config())
      assert Enum.any?(rejections, &(&1.clause == :no_rewrite_node and &1.mode == :reject))
    end
  end
end

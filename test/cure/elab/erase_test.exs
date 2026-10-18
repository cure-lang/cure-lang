defmodule Cure.Elab.EraseTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Grade}
  alias Cure.Elab.{Declarations, Erase, Subst}

  @src """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  fn andd(x: Dec, y: Dec) -> Dec = x
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  """

  defp build_env do
    alias Cure.Compiler.{Lexer, Parser}
    {:ok, toks} = Lexer.tokenize(@src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)

    items =
      case ast do
        {:block, _, xs} -> xs
        x -> [x]
      end

    Enum.reduce(items, Env.empty(), fn d, e ->
      {:ok, e2} = Declarations.elaborate(d, e)
      e2
    end)
  end

  test "erases the erased index arguments from a seq value, keeping l and r" do
    env = build_env()
    nil_ = {:ctor, :SVNil, []}
    causal = {:ctor, :Causal, []}

    seq = {:ctor, :seq, [nil_, nil_, causal, nil_, causal, {:global, :l}, {:global, :r}]}
    assert Erase.erase(env, seq) == {:ctor, :seq, [{:global, :l}, {:global, :r}]}
  end

  test "erases prim to a nullary runtime constructor" do
    env = build_env()
    prim = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}
    assert Erase.erase(env, prim) == {:ctor, :prim, []}
  end

  test "erases recursively inside nested constructors" do
    env = build_env()
    inner = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}

    seq =
      {:ctor, :seq,
       [
         {:ctor, :SVNil, []},
         {:ctor, :SVNil, []},
         {:ctor, :Causal, []},
         {:ctor, :SVNil, []},
         {:ctor, :Causal, []},
         inner,
         inner
       ]}

    assert Erase.erase(env, seq) ==
             {:ctor, :seq, [{:ctor, :prim, []}, {:ctor, :prim, []}]}
  end

  test "erase is idempotent: re-erasing an already-erased seq is a no-op" do
    env = build_env()
    nil_ = {:ctor, :SVNil, []}
    causal = {:ctor, :Causal, []}
    seq = {:ctor, :seq, [nil_, nil_, causal, nil_, causal, {:global, :l}, {:global, :r}]}

    once = Erase.erase(env, seq)
    assert Erase.erase(env, once) == once
  end

  test "erase is idempotent on an application-spine with an erased-before-present def" do
    # g : (@0 Int) -> Int -> Int  (param 0 erased, param 1 present)
    env =
      Env.add_def(
        Env.empty(),
        :g,
        {:pi, Cure.Core.Grade.unrestricted(), {:int_type},
         {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}}},
        {:int_lit, 0},
        [:erased, :unrestricted]
      )

    app = {:app, {:app, {:global, :g}, {:int_lit, 1}}, {:int_lit, 2}}
    once = Erase.erase(env, app)
    assert Erase.erase(env, once) == once
  end

  test "detects holes in a term" do
    assert Erase.has_hole?({:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:hole, "body"}})
    assert Erase.has_hole?({:ctor, :seq, [{:hole, "x"}]})
    refute Erase.has_hole?({:ctor, :prim, []})
  end

  test "detects a hole inside a builtin-op spine argument (K3 completeness; K2 re-spell)" do
    assert Erase.has_hole?({:app, {:app, {:global, :int_add}, {:hole, "x"}}, {:int_lit, 1}})
    refute Erase.has_hole?({:app, {:app, {:global, :int_add}, {:int_lit, 2}}, {:int_lit, 1}})
  end

  # ---------------------------------------------------------------------
  # §8.3 — erasure commutes with reduction.
  #
  # docs/SOUNDNESS.md §8.3 records that the soundness argument ASSUMES
  # `Erase.erase` drops only `:erased`-graded binders, but never proves that
  # erasure commutes with reduction. These tests turn that assumption into
  # executable evidence for the β case, which is the one that actually
  # substitutes into a body (and so the one where a dropped binder could be
  # captured or a kept one wrongly dropped).
  #
  # The property: erasing a β-redex and reducing it must give the same term
  # as reducing it and then erasing. Both sides are computed independently —
  # `Erase.erase/2` on the left, `Subst.instantiate/2` on the right — so a
  # disagreement is a real defect, not a tautology.
  # ---------------------------------------------------------------------

  describe "erasure commutes with β-reduction (§8.3)" do
    # The property under test: for a β-redex `(λx. body) arg`,
    #
    #     erase(reduce(redex))  ==  reduce(erase(redex))
    #
    # where `reduce` is `Subst.instantiate(body, [arg])` — the Core-level β
    # step. Both sides are computed independently, so a disagreement is a
    # real defect rather than a restatement.
    #
    # Two facts about `Erase.erase/2` that these tests pin down (both were
    # confirmed by running them, not assumed):
    #
    #   * erase RECURSES into an application's argument, so an erased-field
    #     constructor in argument position is already erased on both paths;
    #   * erase does NOT perform β — it preserves the `{:app, {:lam, …}}`
    #     shape, so the right-hand side still contains the redex.

    test "erased argument: both paths agree" do
      env = build_env()
      u = Grade.unrestricted()

      # (λ(@0 x : Dec). prim) Causal — the bound var is unused, so the body
      # is argument-independent.
      body = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}
      arg = {:ctor, :Causal, []}
      redex = {:app, {:lam, u, {:data, :Dec, [], []}, body}, arg}

      # erase(β-reduct): substitute, then erase.
      left = Erase.erase(env, Subst.instantiate(body, [arg]))
      # β-reduct(erase(redex)): erase the redex, then substitute its body.
      {:app, {:lam, _g, _dom, erased_body}, erased_arg} = Erase.erase(env, redex)
      right = Subst.instantiate(erased_body, [erased_arg])

      assert left == right
      assert left == {:ctor, :prim, []}
    end

    test "present argument: the argument survives erasure on both paths" do
      env = build_env()
      u = Grade.unrestricted()

      # (λ(x : SF). x) (prim …) — identity body, so the reduct IS the arg.
      arg = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}
      body = {:var, 0}
      redex = {:app, {:lam, u, {:data, :SF, [], []}, body}, arg}

      # erase(β-reduct): substitute, then erase — the reduct is the argument,
      # whose erased fields are dropped.
      left = Erase.erase(env, Subst.instantiate(body, [arg]))
      # β-reduct(erase(redex)): erase first (which also erases the argument in
      # place), then substitute.
      {:app, {:lam, _g, _dom, erased_body}, erased_arg} = Erase.erase(env, redex)
      right = Subst.instantiate(erased_body, [erased_arg])

      assert left == right
      assert left == {:ctor, :prim, []}
    end

    test "nested redex: erasing inside-out agrees with erasing once" do
      env = build_env()
      u = Grade.unrestricted()

      inner_arg = {:ctor, :Causal, []}
      inner_body = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}
      inner_redex = {:app, {:lam, u, {:data, :Dec, [], []}, inner_body}, inner_arg}

      # Reduce the inner redex first, then erase.
      left = Erase.erase(env, Subst.instantiate(inner_body, [inner_arg]))

      # Erase the inner redex (recursing into its argument), then reduce it.
      {:app, {:lam, _g, _dom, erased_body}, erased_arg} = Erase.erase(env, inner_redex)
      right = Subst.instantiate(erased_body, [erased_arg])

      assert left == right
      assert left == {:ctor, :prim, []}
    end
  end

  # ---------------------------------------------------------------------
  # §8.3 — ζ (let) commutation.
  #
  # ζ: `let x = v in b` reduces to `b[x := v]`, the same top substitution β
  # uses. Erasure has an extra rule here — the administrative identity
  # `let x = v in x` erases to `erase(v)` — so the interesting question is
  # whether that shortcut agrees with reducing first and then erasing.
  # ---------------------------------------------------------------------
  describe "erasure commutes with ζ-reduction (§8.3)" do
    test "let-identity: erasing the redex equals erasing the reduct" do
      env = build_env()
      u = Grade.unrestricted()
      val = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}

      # let x = prim(...) in x   —  the administrative identity.
      redex = {:let, u, {:data, :SF, [], []}, val, {:var, 0}}

      # Erasure's own shortcut: the whole let collapses to the erased value.
      assert Erase.erase(env, redex) == {:ctor, :prim, []}

      # Reduce (ζ) then erase, vs erase then reduce, must agree.
      reduced = Subst.instantiate({:var, 0}, [val])
      left = Erase.erase(env, reduced)
      right = Erase.erase(env, val)
      assert left == right
      assert left == {:ctor, :prim, []}
    end

    test "non-identity let: the binder survives on both paths" do
      env = build_env()
      u = Grade.unrestricted()
      val = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}

      # let x = prim(...) in prim(...)  —  body ignores x, but is not `x`, so
      # erasure KEEPS the let (the value must still be evaluated once).
      body = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}
      redex = {:let, u, {:data, :SF, [], []}, val, body}

      erased = Erase.erase(env, redex)
      assert match?({:let, _, _, _, _}, erased)

      # Reduce then erase vs erase then reduce.
      reduced = Subst.instantiate(body, [val])
      left = Erase.erase(env, reduced)
      right = Erase.erase(env, body)
      assert left == right
      assert left == {:ctor, :prim, []}
    end
  end

  # ---------------------------------------------------------------------
  # §8.3 — ι (case) commutation.
  #
  # ι: `case (ctor c args) of …` reduces to the matching branch body with the
  # fields substituted. Note `Erase.erase/2` does NOT perform ι — it keeps a
  # `:runtime` case intact (only a COLLAPSIBLE case, whose sole constructor's
  # fields are all erased, is dropped). So the property here is the honest
  # one for a non-collapsible case: erasing the ι-REDUCT must equal erasing
  # the branch body that ι selects, i.e. erasure is insensitive to whether
  # the case has already been discharged.
  # ---------------------------------------------------------------------
  describe "erasure commutes with ι-reduction (§8.3)" do
    test "case on a constructor: erasing the reduct equals erasing the branch" do
      env = build_env()

      # `Causal` is nullary, so ι substitutes no fields and the reduct IS the
      # branch body.
      branch_body = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}
      branches = [{:Causal, 0, branch_body}]
      redex = {:case, {:ctor, :Causal, []}, {:data, :Dec, [], []}, branches}

      # Erasure keeps the case (it is not collapsible), so the two sides are
      # compared at the level that matters: the REDUCT.
      reduced = Subst.instantiate(branch_body, [])
      left = Erase.erase(env, reduced)
      right = Erase.erase(env, branch_body)

      assert left == right
      # `prim`'s two fields are erased-graded in this env, so both sides drop
      # them — this assertion is what makes the test non-vacuous.
      assert left == {:ctor, :prim, []}
    end

    test "the case itself is preserved by erasure (not silently discharged)" do
      env = build_env()
      branch_body = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}
      branches = [{:Causal, 0, branch_body}]
      redex = {:case, {:ctor, :Causal, []}, {:data, :Dec, [], []}, branches}

      # Pins the behaviour the test above depends on: erase keeps the case
      # (erasing only inside it), so "erase then ι" and "ι then erase" are
      # related by the REDUCT, not by erasure performing ι.
      assert {:case, {:ctor, :Causal, []}, _motive, [{:Causal, 0, erased_body}]} =
               Erase.erase(env, redex)

      assert erased_body == {:ctor, :prim, []}
    end
  end

  # ---------------------------------------------------------------------
  # §8.3 — δ (certified global unfolding) commutation.
  #
  # δ: `global f` reduces to `body(f)` once `f` is certified total. Erasure
  # has NO clause for a bare `{:global, name}` — it falls through to the
  # identity catch-all — so erasure never performs δ itself.
  #
  # FINDING (this is a negative result, not a commutation proof): δ does NOT
  # commute with erasure in general, and it must not be expected to. Erasure
  # drops an argument when the CALLEE's signature marks that position erased;
  # after δ the callee's signature is gone (the head is the body), so the
  # positions can no longer be identified. Here `certified_prim` takes two
  # ERASED parameters, so erasing the call drops both; but its body `prim` is
  # NULLARY, so erasing the unfolded form treats the two arguments as
  # over-application and keeps them.
  #
  # The consequence for the soundness argument: erasure must run on the
  # UNFOLDED Core (which is what the pipeline does), and "erasure commutes
  # with δ" is the WRONG property to prove. The right one is that erasure is
  # insensitive to δ only for globals whose arity matches their body's — or,
  # more simply, that erasure is applied once, after all unfolding.
  # ---------------------------------------------------------------------
  describe "erasure and δ-reduction (§8.3)" do
    test "a global call: erasure drops the callee's erased args, δ destroys that information" do
      env = build_env()

      # `certified_prim` takes two ERASED parameters and returns a prim.
      body = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}

      env =
        Env.add_def(
          env,
          :certified_prim,
          {:pi, Grade.unrestricted(), {:data, :Sig, [], []},
           {:pi, Grade.unrestricted(), {:data, :Sig, [], []}, {:data, :SF, [], []}}},
          body,
          [:erased, :erased]
        )

      # `certified_prim(cs, es)` — both arguments occupy erased positions.
      call = {:app, {:app, {:global, :certified_prim}, {:ctor, :CSig, []}}, {:ctor, :ESig, []}}

      # Erase the CALL (the global is not unfolded).
      erased_call = Erase.erase(env, call)
      # Erase the same call after δ has replaced the head with the body.
      unfolded = {:app, {:app, body, {:ctor, :CSig, []}}, {:ctor, :ESig, []}}
      erased_unfolded = Erase.erase(env, unfolded)

      # Erasing the CALL drops both erased arguments, leaving the bare global.
      assert erased_call == {:global, :certified_prim}

      # Erasing the UNFOLDED form is different, and correctly so: `prim` is
      # NULLARY, so `prim(cs)(es)` is an over-application — the two arguments
      # apply to the RESULT and are always kept. δ therefore does not commute
      # with erasure here, which is exactly why erasure must run on the
      # UNFOLDED core: the erased-argument positions are a property of the
      # callee's signature, and after δ that signature is gone.
      assert erased_unfolded ==
               {:app, {:app, {:ctor, :prim, []}, {:ctor, :CSig, []}}, {:ctor, :ESig, []}}
    end

    test "erasure does NOT unfold a bare global (δ stays a runtime reference)" do
      env = build_env()
      body = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}
      env = Env.add_def(env, :certified_prim2, {:data, :SF, [], []}, body, [])

      # Pins the behaviour the test above depends on: erase leaves a bare
      # global alone rather than substituting its body.
      assert Erase.erase(env, {:global, :certified_prim2}) == {:global, :certified_prim2}
    end
  end
end

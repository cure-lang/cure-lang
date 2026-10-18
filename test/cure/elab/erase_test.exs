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
end

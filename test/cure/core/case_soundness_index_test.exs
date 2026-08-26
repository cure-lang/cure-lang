defmodule Cure.Core.CaseSoundnessIndexTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}

  @dec {:data, :Dec, [], []}

  # Dec with two nullary ctors; Ix(n:Dec) with wrap:(p:Dec)->Ix(Causal).
  defp base_env do
    Env.empty()
    |> Inductive.declare(
      Inductive.family(:Dec, [], [], 0),
      [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
    )
    |> Inductive.declare(
      Inductive.family(:Ix, [], [{:n, @dec}], 0),
      [Inductive.ctor(:wrap, [{:p, @dec}], [{:ctor, :Causal, []}])]
    )
  end

  # de Bruijn (innermost = 0): in def_type Π(n).Π(h:Ix n).Π(ix:Ix n). Ix n,
  # n is var0 under its own binder, var1 under h, var2 under ix.
  @ix0 {:data, :Ix, [], [{:var, 0}]}
  @ix1 {:data, :Ix, [], [{:var, 1}]}
  @ix2 {:data, :Ix, [], [{:var, 2}]}

  # Test 1 — Positive refinement (4.3 core): reusing h : Ix n as Ix Causal.
  test "Test 1: an outer hypothesis h : Ix n is reusable as Ix Causal in the wrap branch" do
    def_type =
      {:pi, Cure.Core.Grade.unrestricted(), @dec,
       {:pi, Cure.Core.Grade.unrestricted(), @ix0, {:pi, Cure.Core.Grade.unrestricted(), @ix1, @ix2}}}

    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:lam, Cure.Core.Grade.unrestricted(), @ix0, @ix1}}
    # wrap branch adds one binder (p), so h (was var1 before the case) is var2 inside.
    body =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), @ix0,
        {:lam, Cure.Core.Grade.unrestricted(), @ix1, {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 2}}]}}}}

    env = Env.add_def(base_env(), :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # Test 2 — Refinement soundness (§5.1): the machinery does not fabricate a false
  # equation. SAME shape and SAME def_type/body as Test 1 (reusing outer hypothesis
  # `h : Ix n` in the wrap branch), but the motive now hard-demands the WRONG ground
  # index: `Ix Dcoupled` instead of `Ix Causal`. wrap's own result index is always
  # Causal, so a sound unifier can only ever derive `n := Causal` (the TRUE,
  # entailed fact) — never `n := Dcoupled`. `h`, refined to `Ix Causal`, then does
  # NOT match the required `Ix Dcoupled` (both rigid ground terms of the SAME
  # family Ix, per design §8 item 2), so the case must still be rejected. This is
  # the direction Test 1 does not cover: Test 1 shows a previously-rejected good
  # program now accepts; this shows the same machinery does not go on to fabricate
  # an equation the match never actually established.
  test "Test 2: a body relying on an unentailed index equation is still rejected" do
    def_type =
      {:pi, Cure.Core.Grade.unrestricted(), @dec,
       {:pi, Cure.Core.Grade.unrestricted(), @ix0,
        {:pi, Cure.Core.Grade.unrestricted(), @ix1, {:data, :Ix, [], [{:ctor, :Dcoupled, []}]}}}}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), @ix0, {:data, :Ix, [], [{:ctor, :Dcoupled, []}]}}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), @ix0,
        {:lam, Cure.Core.Grade.unrestricted(), @ix1, {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 2}}]}}}}

    env = Env.add_def(base_env(), :probe, def_type, body)
    assert {:error, _} = Kernel.check_def(env, :probe)
  end

  # Test 4 — Occurs-check (§5.3), regression half. Given the proven disjoint-range
  # invariant (§4.4: r-side vars always < arity, s-side vars always >= arity after
  # reify+shift), a real cyclic pair cannot arise from any legitimate case branch —
  # so no adversarial construction exists to positively exercise occurs_index?/2
  # returning true on real input while keeping this test green pre-fix (any
  # fixture that meaningfully drives the new var-var solving path is, by
  # construction, a NEW-capability case like Test 1/2, not a same-behavior
  # regression). This test instead documents the honest, weaker claim: a
  # legitimate bare-ctor-arg-var match (the one case today's kernel already
  # handles) keeps checking unchanged under the new unifier — i.e. the occurs-check
  # machinery, even though present on every bind, adds no false rejections on
  # ordinary structural-recursion input. It does NOT prove the guard would
  # actually catch a genuine cycle (no such input is constructible here); that
  # guarantee rests on the disjoint-range proof in §4.4, not on this test.
  test "Test 4: structural-recursion refinement of a nested-index family still checks" do
    # Two(i:Dec) with pack:(y:Dec)->Two(y); match Two(m) with variable m → bind m := y.
    env =
      Env.empty()
      |> Inductive.declare(
        Inductive.family(:Dec, [], [], 0),
        [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
      )
      |> Inductive.declare(
        Inductive.family(:Two, [], [{:i, @dec}], 0),
        [Inductive.ctor(:pack, [{:y, @dec}], [{:var, 0}])]
      )

    two0 = {:data, :Two, [], [{:var, 0}]}
    # Π(m:Dec). Π(t:Two m). Dec
    def_type = {:pi, Cure.Core.Grade.unrestricted(), @dec, {:pi, Cure.Core.Grade.unrestricted(), two0, @dec}}
    # λm'.λt'. Dec
    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:lam, Cure.Core.Grade.unrestricted(), two0, @dec}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), two0, {:case, {:var, 0}, motive, [{:pack, 1, {:var, 0}}]}}}

    env = Env.add_def(env, :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # Test 5b — Undecidable half (§5.4, monotonic degradation): a pairing the
  # unifier cannot classify as either a solvable variable or a rigid clash must
  # stay :undecided (never :impossible) and the branch must NOT be discharged.
  # A "good body, assert :ok" framing CANNOT prove this: a wrongly-discharged
  # branch and a correctly-checked-and-accepted branch are both observably :ok,
  # so no such test can distinguish them. Instead: a fresh family `Stray(n:Dec)`
  # whose only constructor's result index is one opaque global (`h`); the
  # scrutinee's own index is a DIFFERENT opaque global (`g`). Neither side is a
  # de Bruijn variable (so unify_one's var-solving clauses never fire) and
  # neither is `rigid_index?/1` (a bare `{:global, _}` is not in that predicate's
  # clauses), so the pair is genuinely :undecided in BOTH Task 1 and Task 2 —
  # it can never become :impossible. The branch is given a deliberately
  # ill-typed body (`{:type, 0}`); a kernel that wrongly discharged this branch,
  # or wrongly fabricated a binding from it, would return :ok. The correct,
  # conservative kernel does not discharge it, checks the body against the
  # constant motive's `Dec` requirement, and rejects it.
  test "Test 5b: an undecidable index does not skip the body check" do
    env =
      base_env()
      |> Inductive.declare(
        Inductive.family(:Stray, [], [{:n, @dec}], 0),
        [Inductive.ctor(:mkStray, [{:p, @dec}], [{:global, :h}])]
      )
      |> Env.add_def(:g, @dec, {:ctor, :Causal, []})

    stray_g = {:data, :Stray, [], [{:global, :g}]}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :Stray, [], [{:var, 0}]}, @dec}}

    # Π(s: Stray(global g)). Dec
    def_type = {:pi, Cure.Core.Grade.unrestricted(), stray_g, @dec}
    body = {:lam, Cure.Core.Grade.unrestricted(), stray_g, {:case, {:var, 0}, motive, [{:mkStray, 1, {:type, 0}}]}}
    env = Env.add_def(env, :probe, def_type, body)
    assert {:error, :branch_type} = Kernel.check_def(env, :probe)
  end

  # Test 7 — Regression: the legit Box/Dec matches (mirrors case_typing_test) still
  # check; here we just re-assert a ground-indexed match refines the ctor arg.
  test "Test 7: ground-indexed Box match still refines the ctor argument (no regression)" do
    env =
      Env.empty()
      |> Inductive.declare(
        Inductive.family(:Dec, [], [], 0),
        [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
      )
      |> Inductive.declare(
        Inductive.family(:Box, [], [{:d, @dec}], 0),
        [Inductive.ctor(:mk, [{:x, @dec}], [{:var, 0}])]
      )

    box_causal = {:data, :Box, [], [{:ctor, :Causal, []}]}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :Box, [], [{:var, 0}]}, @dec}}

    # Π(b:Box Causal). Dec
    def_type = {:pi, Cure.Core.Grade.unrestricted(), box_causal, @dec}
    body = {:lam, Cure.Core.Grade.unrestricted(), box_causal, {:case, {:var, 0}, motive, [{:mk, 1, {:var, 0}}]}}
    env = Env.add_def(env, :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # Test 3 — Impossible-branch discharge: scrutinee Ix Dcoupled, wrap builds
  # Ix Causal ⇒ the wrap branch is unreachable; its (deliberately ill-typed) body
  # is NOT checked. Companion: a REACHABLE Ix Causal scrutinee with the same body
  # is still rejected (discharge is not a blanket bypass).
  test "Test 3: an impossible wrap branch is discharged without checking its body" do
    ix_dcoupled = {:data, :Ix, [], [{:ctor, :Dcoupled, []}]}
    # λn'.λix'. Dec
    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:lam, Cure.Core.Grade.unrestricted(), @ix0, @dec}}
    # Π(s:Ix Dcoupled). Dec
    def_type = {:pi, Cure.Core.Grade.unrestricted(), ix_dcoupled, @dec}
    # body is {:type,0} where Dec is expected — only accepted because the branch is dead.
    body = {:lam, Cure.Core.Grade.unrestricted(), ix_dcoupled, {:case, {:var, 0}, motive, [{:wrap, 1, {:type, 0}}]}}
    env = Env.add_def(base_env(), :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  test "Test 3 companion: the SAME ill-typed body in a REACHABLE branch is rejected" do
    ix_causal = {:data, :Ix, [], [{:ctor, :Causal, []}]}
    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:lam, Cure.Core.Grade.unrestricted(), @ix0, @dec}}
    # Π(s:Ix Causal). Dec — wrap IS reachable
    def_type = {:pi, Cure.Core.Grade.unrestricted(), ix_causal, @dec}
    body = {:lam, Cure.Core.Grade.unrestricted(), ix_causal, {:case, {:var, 0}, motive, [{:wrap, 1, {:type, 0}}]}}
    env = Env.add_def(base_env(), :probe, def_type, body)
    assert {:error, :branch_type} = Kernel.check_def(env, :probe)
  end

  # Test 5a — Clash half (§5.2 "only" direction), DIRECT positional clash: a
  # definite rigid head clash between a ground ctor-result-index term and a
  # ground scrutinee index discharges the branch, WITHOUT going through
  # bind_index's same-key merge path (that path is Test 6, a DIFFERENT code
  # route: unify_one's own catch-all fires here, not a same-key conflict).
  # Foo(a:Dec, b:Dec) with mk2:(y:Dec)->Foo(Causal, y) — position `a` is a
  # HARDCODED ground index (Causal), position `b` is the ctor's own arg y (no
  # shared key with `a`). Scrutinee Foo(Dcoupled, Dcoupled): position `a`
  # clashes directly (Causal vs Dcoupled, two distinct rigid ground terms, no
  # variable involved on either side) — verifying clash-detection also works
  # positionally within a multi-index family, complementing Test 3's
  # single-index Ix clash.
  test "Test 5a: a direct positional clash (no shared key) discharges the branch" do
    env =
      base_env()
      |> Inductive.declare(
        Inductive.family(:Foo, [], [{:a, @dec}, {:b, @dec}], 0),
        [Inductive.ctor(:mk2, [{:y, @dec}], [{:ctor, :Causal, []}, {:var, 0}])]
      )

    foo_dd = {:data, :Foo, [], [{:ctor, :Dcoupled, []}, {:ctor, :Dcoupled, []}]}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), @dec,
        {:lam, Cure.Core.Grade.unrestricted(), {:data, :Foo, [], [{:var, 1}, {:var, 0}]}, @dec}}}

    def_type = {:pi, Cure.Core.Grade.unrestricted(), foo_dd, @dec}
    body = {:lam, Cure.Core.Grade.unrestricted(), foo_dd, {:case, {:var, 0}, motive, [{:mk2, 1, {:type, 0}}]}}
    env = Env.add_def(env, :probe, def_type, body)
    # mk2 can only build Foo(Causal,_) ⇒ discharged
    assert :ok == Kernel.check_def(env, :probe)
  end

  # K4 (§H) — ex-falso by empty branch list. A scrutinee whose family's every
  # constructor is impossible at its actual indices may be eliminated by a `case`
  # with NO branches; the case takes the motive's type though no branch produces
  # a value. Mirrors Test 3 (Ix Dcoupled, wrap builds Ix Causal ⇒ impossible) but
  # OMITS the dead wrap branch instead of giving it a placeholder body.
  test "K4: an all-impossible family admits an empty-branch case (ex-falso)" do
    ix_dcoupled = {:data, :Ix, [], [{:ctor, :Dcoupled, []}]}
    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:lam, Cure.Core.Grade.unrestricted(), @ix0, @dec}}
    def_type = {:pi, Cure.Core.Grade.unrestricted(), ix_dcoupled, @dec}
    body = {:lam, Cure.Core.Grade.unrestricted(), ix_dcoupled, {:case, {:var, 0}, motive, []}}
    env = Env.add_def(base_env(), :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # Soundness pin: omitting a constructor that could STILL match is a coverage
  # error. Scrutinee Ix Causal ⇒ wrap IS reachable, so the empty branch list is
  # invalid ex-falso and must be rejected (not a blanket "empty case is fine").
  test "K4: an empty-branch case is rejected when a constructor is still reachable" do
    ix_causal = {:data, :Ix, [], [{:ctor, :Causal, []}]}
    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:lam, Cure.Core.Grade.unrestricted(), @ix0, @dec}}
    def_type = {:pi, Cure.Core.Grade.unrestricted(), ix_causal, @dec}
    body = {:lam, Cure.Core.Grade.unrestricted(), ix_causal, {:case, {:var, 0}, motive, []}}
    env = Env.add_def(base_env(), :probe, def_type, body)
    assert {:error, _} = Kernel.check_def(env, :probe)
  end

  # Test 6 — Merge consistency (§5.5): mk:(p:Dec)->Foo(p,p) matched against
  # Foo(Causal, Dcoupled) gives p two candidate bindings (Causal, Dcoupled) that
  # are not equal ⇒ :impossible (discharge), NOT a silently-overwritten unsound
  # subst. Unlike Test 5a (a DIRECT positional clash via unify_one's own
  # catch-all, no shared key), this construction specifically routes through
  # bind_index's SAME-KEY conflict path (both index positions solve the one
  # telescope var `p`), by giving the branch a body that is ill-typed under BOTH
  # candidate refinements, so a silent-overwrite kernel would reject and only a
  # correct merge-conflict→impossible kernel accepts.
  test "Test 6: conflicting shared-key bindings yield impossible, not a silent overwrite" do
    env =
      base_env()
      |> Inductive.declare(
        Inductive.family(:Foo, [], [{:a, @dec}, {:b, @dec}], 0),
        [Inductive.ctor(:mk, [{:p, @dec}], [{:var, 0}, {:var, 0}])]
      )

    foo_cd = {:data, :Foo, [], [{:ctor, :Causal, []}, {:ctor, :Dcoupled, []}]}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), @dec,
        {:lam, Cure.Core.Grade.unrestricted(), {:data, :Foo, [], [{:var, 1}, {:var, 0}]}, @dec}}}

    def_type = {:pi, Cure.Core.Grade.unrestricted(), foo_cd, @dec}
    body = {:lam, Cure.Core.Grade.unrestricted(), foo_cd, {:case, {:var, 0}, motive, [{:mk, 1, {:type, 0}}]}}
    env = Env.add_def(env, :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end
end

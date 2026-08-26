defmodule Antigen.EqInductiveAntibodyTest do
  @moduledoc """
  TCB antibody — retiring the faking-era primitive identity type in favour of a
  genuine inductive `Eq` (spec 2026-07-04-identity-type-as-inductive) keeps the
  kernel SOUND and TERMINATING.

  Guards the coordinated change that seeds `Eq : (a:Type) -> a -> a -> Type` with
  the single erased-witness constructor `refl : {w:a} -> Equivalent(a,w,w)` as an ordinary
  builtin inductive, retargets surface `Eq`/`refl`, and WIDENS the two rewrite
  transport consumers — `Cure.Core.Kernel.ensure_eq/1` and the elaborator's
  `eq_parts/1` — to accept the inductive `{:vdata, :Equivalent, [ty, a, b]}` value
  alongside the retiring primitive `{:veq, ty, a, b}`.

  Two load-bearing soundness properties, each pinned with an INDEPENDENT oracle
  that never consults the machinery under test:

    * REFL-IS-REFLEXIVE — a `refl` proof inhabits `Equivalent(ty, x, y)` **iff** `x` and
      `y` are convertible. The independent oracle is `Cure.Core.Conv.conv_within?`
      (deep conversion, no refl-check involvement). A violation would let a proof
      of a FALSE equation be manufactured, and rewrite/transport along it would
      coerce between distinct normal forms — the classic identity-type unsoundness.

    * TRANSPORT-IS-Eq-PRECISE — elimination treats a value as an equality
      **iff** it is genuinely the `Eq` family, and reads its endpoints in the
      right order (`a` then `b`). Pinned by the J/subst `:case` transport with
      an ENDPOINT-DISTINGUISHING motive: the result type must be `motive @ b`,
      never `motive @ a`. A same-shaped decoy family (`Fake`, 1 parameter + 2
      indices) must be REJECTED (`:foreign_ctor`) — the family key, not the
      3-element arity, decides. (The original `{:rewrite}`-node versions of
      these tests were retired with the primitive form — group-A removal
      commit — after their :case twins were cross-checked side by side.)

  Plus TERMINATION under a bounded Task harness. If any construction violates a
  SOUNDNESS assertion, the retarget is unsound: STOP — do not weaken the assertion.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Kernel, Context, Conv, Eval}
  alias Cure.Elab.Program
  import Cure.TestSupport.RetiredNode, only: [opaque: 1]

  @fuel 100_000

  # Default signature: every program's env seeds the builtin inductives, incl. the
  # new `Eq`/`refl` and `Nat`/`Bool` used below.
  defp base_sig do
    {:ok, sig} = Program.elaborate("mod M\nend\n")
    sig
  end

  # A signature that ALSO declares a decoy family `Fake(a) indices (x,y)` — the
  # exact 1-param/2-index shape of `Eq`, so a `{:vdata, :Fake, [ty,a,b]}` value is
  # byte-shaped like an `Eq` value but is NOT the identity type.
  defp fake_sig do
    {:ok, sig} =
      Program.elaborate("mod M\n  type Fake(a: Type) indices (x: a, y: a)\nend\n")

    sig
  end

  # ---- term helpers (closed Core) -------------------------------------------
  @nat {:data, :"Std.Nat#Nat", [], []}
  @bool {:data, :"Std.Bool#Bool", [], []}
  defp z, do: {:ctor, :Z, []}
  defp s(n), do: {:ctor, :S, [n]}
  defp nat_lit(0), do: z()
  defp nat_lit(n), do: s(nat_lit(n - 1))
  defp tru, do: {:ctor, :True, []}
  defp fls, do: {:ctor, :False, []}

  defp eq_ty(sig, ty, a, b),
    do:
      Eval.eval(
        {:data, :"Std.Equivalent#Equivalent", [ty], [a, b]},
        Context.env(Context.empty(sig))
      )

  # ---- SOUNDNESS: refl inhabits Equivalent(ty,x,y) IFF conv?(x,y) --------------------

  test "refl proves Equivalent(ty,x,y) iff x and y are genuinely convertible (independent Conv oracle)" do
    sig = base_sig()
    ctx = Context.empty(sig)

    # {label, ty, x, y}. Mixed equal / distinct pairs over two builtin types.
    scenarios = [
      {"Z = Z", @nat, z(), z()},
      {"S Z = S Z", @nat, s(z()), s(z())},
      {"2 = 2", @nat, nat_lit(2), nat_lit(2)},
      {"Z = S Z", @nat, z(), s(z())},
      {"S Z = Z", @nat, s(z()), z()},
      {"S Z = 2", @nat, s(z()), nat_lit(2)},
      {"2 = 3", @nat, nat_lit(2), nat_lit(3)},
      {"True = True", @bool, tru(), tru()},
      {"False = False", @bool, fls(), fls()},
      {"True = False", @bool, tru(), fls()},
      {"False = True", @bool, fls(), tru()}
    ]

    for {label, ty, x, y} <- scenarios do
      # Kernel judgement: does `refl x` check at `Eq ty x y`?
      accepts = Kernel.check(ctx, {:ctor, :reflexive, [x]}, eq_ty(sig, ty, x, y)) == :ok

      # Independent oracle: are the two endpoints convertible? (No refl involved.)
      # conv_within? takes Core terms and evaluates them itself.
      convertible = match?({:ok, true}, Conv.conv_within?(x, y, [], 0, sig, @fuel))

      assert accepts == convertible,
             "REFL-IS-REFLEXIVE VIOLATION for #{label}: kernel accepts refl=#{accepts} but " <>
               "endpoints convertible=#{convertible}. A refl proof must inhabit Equivalent(ty,x,y) " <>
               "iff x≡y — otherwise a false equation is provable and transport is unsound."
    end
  end

  # ---- :case-based twins of the {:rewrite}-node tests (Phase C Step 2) -------
  #
  # The three tests above that construct a raw `{:rewrite, …}` Core node probe
  # properties of the TRANSPORT MECHANISM (endpoint fidelity, :Equivalent-
  # precision, termination). Phase C retires that node; the elaborator now emits
  # the J/subst transport — a single-branch `:case` on the proof with the arrow
  # motive `λx y p. (M@x) -> (M@y)` and identity branch, applied to the body.
  # Each twin below asserts the IDENTICAL soundness property through the :case
  # vehicle. They run SIDE BY SIDE with the originals while `{:rewrite}` still
  # round-trips (this commit) — the cross-check that licenses deleting the
  # originals in the removal commit (they become unconstructable there).
  #
  # `transport/4` mirrors the elaborator's `transport_case/4` for CLOSED
  # ty/motive/l (de Bruijn shifts of closed terms elided).
  defp transport(proof, ty, motive, l) do
    scrut_ty = {:data, :"Std.Equivalent#Equivalent", [ty], [{:var, 1}, {:var, 0}]}
    arrow = {:pi, Cure.Core.Grade.unrestricted(), {:app, motive, {:var, 2}}, {:app, motive, {:var, 2}}}

    arrow_motive =
      {:lam, Cure.Core.Grade.unrestricted(), ty,
       {:lam, Cure.Core.Grade.unrestricted(), ty, {:lam, Cure.Core.Grade.unrestricted(), scrut_ty, arrow}}}

    {:case, proof, arrow_motive,
     [
       {:"Std.Equivalent#reflexive", 1, {:lam, Cure.Core.Grade.unrestricted(), {:app, motive, l}, {:var, 0}}}
     ]}
  end

  test ":case transport over an inductive Equivalent(Nat,Z,S Z) hypothesis lands at motive @ b (not motive @ a)" do
    sig = base_sig()
    ctx = Context.extend(Context.empty(sig), eq_ty(sig, @nat, z(), s(z())))

    # Endpoint-distinguishing motive:  λ x:Nat. Equivalent(Nat, x, Z)
    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @nat, {:data, :"Std.Equivalent#Equivalent", [@nat], [{:var, 0}, z()]}}

    # transport (h : Eq Nat Z (S Z)) : (motive @ Z) -> (motive @ S Z), applied
    # to (refl Z : motive @ Z) — result must be motive @ b, never motive @ a.
    node = {:app, transport({:var, 0}, @nat, motive, z()), {:ctor, :reflexive, [z()]}}

    result = Kernel.infer(ctx, node)

    expected_b = eq_ty(sig, @nat, s(z()), z())
    expected_a = eq_ty(sig, @nat, z(), z())

    assert {:ok, ^expected_b} = result,
           "ENDPOINT FIDELITY VIOLATION (:case transport): result was #{inspect(result)}, " <>
             "expected motive @ b = #{inspect(expected_b)}. If it were motive @ a = " <>
             "#{inspect(expected_a)}, the case rule read the scrutinee indices in the wrong order."

    refute match?({:ok, ^expected_a}, result),
           ":case transport landed at motive @ a — endpoints read in the wrong order"
  end

  test "a :case transport whose proof has a same-shaped non-Eq family type is rejected" do
    sig = fake_sig()

    # h : Fake(Nat, Z, Z) — byte-shaped like Equivalent(Nat,Z,Z) but a different
    # family. A `reflexive` branch cannot eliminate it: the kernel keys the
    # branch constructor's FAMILY (:foreign_ctor), the :case analog of
    # ensure_eq keying on the :Equivalent atom.
    fake_val = Eval.eval({:data, :Fake, [@nat], [z(), z()]}, Context.env(Context.empty(sig)))
    ctx = Context.extend(Context.empty(sig), fake_val)

    node = {:app, transport({:var, 0}, @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, z()), z()}

    assert {:error, _} = Kernel.infer(ctx, node),
           "SOUNDNESS VIOLATION: a reflexive-branch :case eliminated the non-Eq family Fake — " <>
             "only the genuine Eq family may be eliminated as an equality."

    # Positive control on the SAME signature: a real Eq hypothesis transports.
    ctx_eq = Context.extend(Context.empty(sig), eq_ty(sig, @nat, z(), z()))

    assert {:ok, _} =
             Kernel.infer(
               ctx_eq,
               {:app, transport({:var, 0}, @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, z()), z()}
             ),
           "a genuine Eq hypothesis should transport through the :case vehicle"
  end

  test ":case-transport inference over inductive Eq halts (bounded)" do
    sig = base_sig()
    ctx_h = Context.extend(Context.empty(sig), eq_ty(sig, @nat, z(), z()))

    job = fn ->
      Kernel.infer(
        ctx_h,
        {:app, transport({:var, 0}, @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, z()), z()}
      )
    end

    task = Task.async(job)

    assert Task.yield(task, 5_000) || Task.shutdown(task),
           ":case transport inference did not return within budget"
  end

  # ---- TERMINATION -----------------------------------------------------------

  # (Job 3 — a raw {:rewrite}-node inference — was retired with the primitive
  # form in the group-A removal commit; its :case-transport twin above carries
  # the same bounded-termination obligation. Jobs 1-2 are inductive and stay.)
  test "refl-check over inductive Eq halts (bounded)" do
    sig = base_sig()
    ctx = Context.empty(sig)

    jobs = [
      fn -> Kernel.check(ctx, {:ctor, :reflexive, [nat_lit(3)]}, eq_ty(sig, @nat, nat_lit(3), nat_lit(3))) end,
      fn -> Kernel.check(ctx, {:ctor, :reflexive, [z()]}, eq_ty(sig, @nat, z(), s(z()))) end
    ]

    for {job, i} <- Enum.with_index(jobs) do
      task = Task.async(job)

      assert Task.yield(task, 5_000) || Task.shutdown(task),
             "job #{i} (inductive Eq refl/rewrite) did not return within budget"
    end
  end

  # ---- GATE C EXTENSIONS (Phase C complete: primitives retired) --------------
  #
  # Three obligations from spec Gate C. (i) and (ii) are regression ANTIBODIES:
  # they hold today and exist to go red under a future kernel mutation (they
  # cannot be made red-first without breaking the kernel — Antigen's standing
  # antibody pattern). (iii) re-asserts the C1 red tests' post-removal truth as
  # a permanent antibody: the retired forms are unreachable grammar.

  # (i) Refl-matching discharges/refines EXACTLY as the index unifier dictates,
  # and equates NO distinct normal forms. The reflexive branch's fate on a
  # scrutinee Equivalent(ty, x, y) is decided by unifying its result indices
  # [w,w] against [x,y]: distinct rigid endpoints ⇒ :impossible (discharged,
  # body skipped — matching a false equation proves nothing); convertible
  # endpoints ⇒ the witness is pinned. And matching NEVER back-feeds x ≡ y into
  # definitional equality: conversion on distinct normal forms still rejects
  # after the whole retirement.
  test "GATE C (i): reflexive-branch verdicts follow the index unifier; defeq does not collapse" do
    sig = base_sig()
    ctx = Context.empty(sig)

    distinct_pairs = [
      {@nat, z(), s(z())},
      {@nat, s(z()), nat_lit(2)},
      {@nat, nat_lit(2), nat_lit(3)},
      {@bool, tru(), fls()}
    ]

    for {ty, x, y} <- distinct_pairs do
      x_val = Eval.eval(x, Context.env(ctx))
      y_val = Eval.eval(y, Context.env(ctx))

      # discharge exactly per the unifier: distinct rigid indices ⇒ :impossible
      assert :impossible ==
               Kernel.branch_unify(ctx, :"Std.Equivalent#Equivalent", :reflexive, [x_val, y_val]),
             "reflexive branch on Equivalent(#{inspect(ty)}, #{inspect(x)}, #{inspect(y)}) " <>
               "must be discharged :impossible (distinct rigid endpoints)"

      # defeq non-collapse: conversion still distinguishes the normal forms
      refute match?({:ok, true}, Conv.conv_within?(x, y, [], 0, sig, @fuel)),
             "DEFEQ COLLAPSE: #{inspect(x)} ≡ #{inspect(y)} after retirement — " <>
               "refl-matching machinery must never equate distinct normal forms"
    end

    # refine exactly per the unifier: convertible endpoints pin the witness
    z_val = Eval.eval(z(), Context.env(ctx))

    assert Kernel.branch_unify(ctx, :"Std.Equivalent#Equivalent", :reflexive, [z_val, z_val]) !=
             :impossible,
           "a genuinely reflexive equation's branch must stay live"
  end

  # (ii) Termination unaffected by the retirement: transport over a
  # hypothetical (uninhabited) distinct-endpoint equation still returns within
  # budget — the discharged branch must not send inference into a loop.
  test "GATE C (ii): transport over a distinct-endpoint hypothesis halts (bounded)" do
    sig = base_sig()
    ctx_h = Context.extend(Context.empty(sig), eq_ty(sig, @nat, z(), s(z())))

    job = fn ->
      Kernel.infer(
        ctx_h,
        {:app, transport({:var, 0}, @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, z()), z()}
      )
    end

    task = Task.async(job)

    assert Task.yield(task, 5_000) || Task.shutdown(task),
           "transport over an uninhabited equation did not return within budget"
  end

  # (iii) The retired nodes are unreachable grammar (permanent antibody form of
  # the C1 retirement pins: rewrite_retirement_test / eq_refl_retirement_test).
  test "GATE C (iii): the retired primitive nodes are unreachable" do
    sig = base_sig()
    ctx = Context.empty(sig)

    assert_raise FunctionClauseError, fn -> Kernel.infer(ctx, opaque({:eq, @nat, z(), z()})) end
    assert_raise FunctionClauseError, fn -> Kernel.infer(ctx, opaque({:refl, z()})) end

    ctx_h = Context.extend(ctx, eq_ty(sig, @nat, z(), z()))

    assert_raise FunctionClauseError, fn ->
      Kernel.infer(ctx_h, opaque({:rewrite, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, z()}))
    end
  end
end

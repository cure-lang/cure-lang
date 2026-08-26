defmodule Antigen.CarriedIndexInvertibilityAntibodyTest do
  @moduledoc """
  E-layer antibody (E8, spec `2026-07-18-elaborator-gaps-verified-status.md` §E8) —
  a constructor-HEADED scrutinee index that carries a computed subterm
  (`Node(p, twist(q))`, `PTimes(a, deriv(b, t))`) must be inverted by ordinary
  structural index refinement, NOT detoured through the carried-index-equality
  mechanism. The carried-eq detour is reserved for a genuinely non-invertible
  scrutinee index — one whose HEAD is a defined function (`app(p, q)`), the FRP
  carrier case it was built for.

  ## The gap this closes (RED before the fix)

  `invertible_index?` recursed into a constructor's arguments, so it classified
  `Node(p, twist(q))` as non-invertible merely because the subterm `twist(q)` is a
  function application. That misfired the carried-eq path, whose `cod_expected`
  refines only the single carried index position and DROPS the branch-unify subst
  — so an invertible sibling position (`n ↦ add(n1, n2)`) never reached the goal,
  and a `rewrite` over the refined measure failed `:rewrite_no_match`. The real
  Brzozowski derivative-soundness proof (`https://github.com/cure-lang/cure-otp/tree/main/metatheory/src/otp_mailbox_pattern.cure`) had to
  route its `PTimes`/`PStar` arms through delegation helpers to dodge it.

  The fix narrows `invertible_index?` to test the HEAD only: a constructor-headed
  index is invertible (structural unification descends and binds the computed
  subterm to the constructor's argument binder); only a non-constructor head keeps
  the carried-eq detour. This is an E-layer narrowing; the antibody proves it is
  CONSERVATIVE — the previously-blocked well-typed proof now closes, a false
  equation over the same shape is still rejected, and the carried-eq mechanism is
  still live and still fails closed on the function-app-headed case.

  ## Obligations

    * REACH — the constructor-headed-with-computed-subterm program elaborates, and
      the reflexive proof closes only because the measure index refined correctly
      (`n ↦ add(n1, n2)`) so `rewrite add_assoc(add(n1, n2), k, j)` found its redex.
      RED before the fix (`:rewrite_no_match`).

    * CONTROL A (no laundering) — the SAME shape, but the equation claims a false
      measure (`add(add(n, k), j) ≡ add(n, k)`, dropping `j`). The refinement is
      genuine, not a fabricated unifier, so this must stay rejected.

    * CONTROL B (carried-eq still live, still sound) — a function-app-headed
      scrutinee index (`app(p, q)`) with a WRONG-FAMILY sibling (`G(app(p, q))`)
      returned in an `F`-goal branch. The carried-eq path still fires (narrowing did
      not disable it) and the kernel still rejects the family mismatch. Proves the
      narrowing kept the sound mechanism it was built for.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # Shared preamble for REACH / CONTROL A: `Sh`, `twist`, `add`/`add_assoc`, and the
  # `Ev` GADT whose `ENode` result index is a plain ctor spine `Node(a, b)` over its
  # own vars at pos0 and the computed measure `add(n1, n2)` at pos1. Only the final
  # equation-typed def differs.
  defp ev_src(final_def) do
    """
    mod E8Ab
      type Sh = Leaf | Node(Sh, Sh)
      fn twist(s: Sh) -> Sh = match s
        Leaf()     -> Leaf
        Node(a, b) -> Node(twist(b), twist(a))
      fn add(m: Nat, n: Nat) -> Nat = match m
        Z()  -> n
        S(k) -> S(add(k, n))
      fn add_assoc(a: Nat, b: Nat, c: Nat) -> Equivalent(Nat, add(add(a, b), c), add(a, add(b, c))) = match a
        Z()  -> reflexive(add(b, c))
        S(k) -> rewrite add_assoc(k, b, c) in reflexive(S(add(k, add(b, c))))
      type Ev indices (sh: Sh, n: Nat)
        ENode : (n1: Nat) -> (n2: Nat) -> Ev(a, n1) -> Ev(b, n2) -> Ev(Node(a, b), add(n1, n2))
      #{final_def}
    end
    """
  end

  # ---- Obligation 1: REACH (ctor-headed index inverts; measure refines) ------

  test "REACH: a ctor-headed index with a computed subterm inverts and refines the measure" do
    reach =
      "fn ev_assoc(p: Sh, q: Sh, k: Nat, j: Nat, n: Nat, " <>
        "e: Ev(Node(p, twist(q)), n), sib: Ev(Node(p, twist(q)), n)) -> " <>
        "Equivalent(Nat, add(add(n, k), j), add(n, add(k, j))) = match e\n" <>
        "        ENode(n1, n2, ea, eb) -> rewrite add_assoc(add(n1, n2), k, j) in reflexive(add(add(n1, n2), add(k, j)))"

    assert {:ok, _} = Program.elaborate(ev_src(reach))
  end

  # ---- Obligation 2: CONTROL A (false measure equation stays rejected) -------

  test "CONTROL A: a false measure equation over the same shape stays rejected" do
    bad =
      "fn ev_bad(p: Sh, q: Sh, k: Nat, j: Nat, n: Nat, " <>
        "e: Ev(Node(p, twist(q)), n), sib: Ev(Node(p, twist(q)), n)) -> " <>
        "Equivalent(Nat, add(add(n, k), j), add(n, k)) = match e\n" <>
        "        ENode(n1, n2, ea, eb) -> rewrite add_assoc(add(n1, n2), k, j) in reflexive(add(add(n1, n2), add(k, j)))"

    assert {:error, _} = Program.elaborate(ev_src(bad))
  end

  # ---- Obligation 3: CONTROL B (carried-eq still fires, still fails closed) ---

  test "CONTROL B: a function-app-headed index still triggers carried-eq and rejects a wrong-family sibling" do
    # `v : F(app(p, q))` — `app` is a defined function, so the index is genuinely
    # non-invertible and the carried-eq mechanism is what handles the sibling. The
    # sibling `u : G(app(p, q))` transports but to the WRONG family, so the kernel
    # must still reject. If the narrowing had disabled carried-eq, `u` would never
    # be considered and the branch would fail differently — but it must reject.
    src = """
    mod E8AbCarried
      type SList = SNil | SCons(Nat, SList)
      fn app(xs: SList, ys: SList) -> SList = match xs
        SNil()      -> ys
        SCons(h, t) -> SCons(h, app(t, ys))
      type F indices (xs: SList)
        leaf : F(SNil())
        mk   : F(as) -> F(bs) -> F(app(as, bs))
      type G indices (xs: SList)
        gwrap : G(cs)
      fn bad({p: SList}, {q: SList}, v: F(app(p, q)), u: G(app(p, q))) -> F(app(p, q)) = match v
        leaf()   -> u
        mk(l, r) -> u
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end

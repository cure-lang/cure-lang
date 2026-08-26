defmodule Cure.E2E.FrpBeamTest do
  @moduledoc """
  Task B5 — the FRP slice RUNS on the BEAM under checked {0,ω} erasure.

  The founding spec §8 promises: the descriptors (`SVDesc`/`Sig`/`Dec` and `SF`'s
  index arguments) have ZERO runtime footprint; `SF`'s value-relevant structure
  (constructor tags + payloads) survives as tagged tuples; a `step`-like
  eliminator pattern-matches it at runtime; and the drop is *licensed by the
  `{0,ω}` relevance check*. Track A + B1–B4 built every ingredient; this test
  proves the composition end-to-end — elaborate → relevance-check → erase → emit
  → load → RUN — which no other single test does.

  The probe is a self-contained 2-signal FRP fragment (NOT the full paper
  library): `Dec` decoupledness, `SVDesc` signal descriptors, `SF` with a
  concrete `unit`, a general `prim`, and `seq` (whose result index computes
  `andd`). The `step`-like eliminator is split into two faithful halves:
  `observe` pattern-MATCHES the `SF` and yields an observable `Dec`, and `step`
  packages that observation with the (one-step, identity) continuation in a
  dependent `Σ` pair. `start/0` builds a tiny net `seq(unit(), unit())`, drives
  it one step, and projects the observable — the value the test asserts
  (observation via `apply/3` stands in for printing; the BEAM runs the emitted
  bytecode, including the `Σ` projection `.1`).

  `step`'s continuation is a GENUINE reconstructed refined-index continuation:
  `recon` pattern-matches `s` and rebuilds each constructor at the branch-refined
  index (`match s | seq(l,r) -> seq(l,r) : SF(as,bs,d)`), exercising the
  dependent-match rebuild that oracle `frp/frp07` pins at parity — no longer the
  identity workaround. The test asserts `recon` actually rebuilds `seq` on the
  BEAM.

  (Scope note, recorded honestly: the net uses the concrete `unit` primitive
  because constructing `prim()`/`seq(…)` with free erased index descriptors leaves
  those metavariables unsolved — real programs always carry concrete descriptors,
  so this is not a limitation of the runtime slice. Inlining `recon` directly into
  the `Σ`-pair inside a match branch — `match s → %[observe(s), seq(l,r)]` — hits a
  further Σ-intro × motive-refinement composition gap, so the reconstruction is
  factored into `recon` and applied in a direct Σ-intro.)
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.{Program, Emit}

  @src """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  fn andd(x: Dec, y: Dec) -> Dec = match x
    Dcoupled() -> y
    Causal() -> Causal()
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    unit : SF(SVNil, SVNil, Causal)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  fn observe({as: SVDesc}, {bs: SVDesc}, {d: Dec}, s: SF(as, bs, d)) -> Dec = match s
    unit() -> Causal()
    prim() -> Causal()
    seq(l, r) -> Dcoupled()
  fn recon({as: SVDesc}, {bs: SVDesc}, {d: Dec}, s: SF(as, bs, d)) -> SF(as, bs, d) = match s
    unit() -> unit()
    prim() -> prim()
    seq(l, r) -> seq(l, r)
  fn step({as: SVDesc}, {bs: SVDesc}, {d: Dec}, s: SF(as, bs, d)) -> Sigma(o: Dec, SF(as, bs, d)) = %[observe(s), recon(s)]
  fn start() -> Dec =
    let net = seq(unit(), unit())
    step(net).1
  """

  test "the FRP slice elaborates + passes the {0,ω} relevance check" do
    # Program.elaborate runs the relevance check as part of every function
    # declaration (declarations.ex → Relevance.check); {:ok, env} therefore
    # certifies the erased SF indices are used only in type/index positions —
    # the precondition that *licenses* the erasure below.
    assert {:ok, %Cure.Core.Env{}} = Program.elaborate(@src)
  end

  test "the FRP slice erases, emits, loads, and RUNS on the BEAM" do
    {:ok, env} = Program.elaborate(@src)

    {:ok, mod} =
      Emit.compile_and_load(env,
        module: :"Cure.FrpBeamE2E",
        functions: [:start, :step, :observe, :recon]
      )

    # start/0 builds `seq(unit(), unit())` and steps it once. `seq` matches the
    # seq branch of observe → Dcoupled; step packages it → Σ pair; `.1` projects
    # the observable. The whole thing executes as real BEAM bytecode.
    assert apply(mod, :start, []) == :Dcoupled

    # observe run directly on both a primitive and a composed net.
    assert apply(mod, :observe, [:unit]) == :Causal
    assert apply(mod, :observe, [{:seq, :unit, :unit}]) == :Dcoupled

    # recon GENUINELY reconstructs the continuation constructor at its refined
    # index (the dependent-match rebuild, oracle frp07) — the seq branch rebuilds
    # `{seq, unit, unit}`, not an identity passthrough dodging the type.
    assert apply(mod, :recon, [{:seq, :unit, :unit}]) == {:seq, :unit, :unit}
    assert apply(mod, :recon, [:unit]) == :unit
  end

  test "descriptor zero-footprint: emitted SF constructors carry no index args" do
    {:ok, env} = Program.elaborate(@src)
    forms = Emit.module_forms(env, :"Cure.FrpBeamE2EForms", [:start, :step, :observe])

    # `seq` has 2 present payload args (l, r) and 5 erased indices
    # (as, bs, cs, d1, d2) → it must emit as the 3-tuple `{seq, L, R}`, never
    # carrying an SVDesc/Dec argument.
    seq_tuples = collect_ctor_tuples(forms, :seq)
    assert seq_tuples != [], "expected at least one emitted seq constructor"

    Enum.each(seq_tuples, fn elements ->
      assert length(elements) == 3,
             "seq must emit as {seq, L, R} (5 erased indices dropped), got payload arity #{length(elements) - 1}"
    end)

    # `unit`/`prim` erase every argument (all indices) → bare atoms, never a
    # tuple carrying descriptor arguments.
    assert collect_ctor_tuples(forms, :unit) == [],
           "unit must emit as a bare atom, not a tuple carrying erased indices"

    assert collect_ctor_tuples(forms, :prim) == [],
           "prim must emit as a bare atom, not a tuple carrying erased indices"
  end

  # Walk the abstract forms collecting every `{:tuple, _, [{:atom,_,tag} | rest]}`
  # whose tag is `ctor` — returning the tuple's element list per occurrence.
  defp collect_ctor_tuples(forms, ctor) do
    forms
    |> List.wrap()
    |> Enum.flat_map(&tuples_in(&1, ctor))
  end

  defp tuples_in({:tuple, _l, [{:atom, _, tag} | _] = elems}, ctor) when tag == ctor do
    [elems | Enum.flat_map(elems, &tuples_in(&1, ctor))]
  end

  defp tuples_in(node, ctor) when is_tuple(node),
    do: node |> Tuple.to_list() |> Enum.flat_map(&tuples_in(&1, ctor))

  defp tuples_in(list, ctor) when is_list(list),
    do: Enum.flat_map(list, &tuples_in(&1, ctor))

  defp tuples_in(_leaf, _ctor), do: []
end

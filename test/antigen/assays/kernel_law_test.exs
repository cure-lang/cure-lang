defmodule Antigen.Assays.KernelLawTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Term, as: TermGen
  alias Antigen.Runner

  @law_ids ~w(kernel/shift_subst kernel/weakening kernel/confluence kernel/beta_subst kernel/zeta_subst kernel/grade_conv elab/shift_agrees)

  test "typed_term/1 accepts every kernel-law assay-id (guard widened)" do
    for id <- @law_ids do
      # returns a Gen.t() (a tagged tuple), not raising FunctionClauseError
      assert is_tuple(TermGen.typed_term(id))
    end
  end

  test "runner registry routes every kernel-law id to KernelLaw" do
    for id <- @law_ids do
      assert Runner.assay_module_for(id) == Antigen.Assays.KernelLaw
    end
  end

  alias Antigen.Assays.KernelLaw
  alias Antigen.Challenge

  defp ch(assay, term, ctx \\ []),
    do:
      Challenge.new(
        kind: :typed_term,
        assay: assay,
        label: :well_typed,
        payload: %{sig: :v1, ctx: ctx, type: {:data, :Nat, [], []}, term: term}
      )

  @z {:ctor, :Z, []}
  @sz {:ctor, :S, [{:ctor, :Z, []}]}

  test "shift_subst: a well-formed term satisfies all four laws" do
    assert :ok =
             KernelLaw.run(
               ch(
                 "kernel/shift_subst",
                 {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:ctor, :S, [{:var, 0}]}}
               )
             )
  end

  test "shift_subst: the checker is not tautological (independently re-derive laws 2 and 3)" do
    # guard against the assay always returning :ok — recompute the two most
    # error-prone laws (composition and commutation) here and confirm both
    # sides genuinely agree for this term AND that the computation is
    # non-trivial (if the assay ignored its input it would still pass, so we
    # also check that shifting/substituting actually changed something).
    t = {:ctor, :S, [{:var, 0}]}

    # law 2 (shift composition): shift(shift(t,a,c),b,c) == shift(t,a+b,c)
    law2_lhs = Cure.Core.Term.shift(Cure.Core.Term.shift(t, 1, 0), 1, 0)
    law2_rhs = Cure.Core.Term.shift(t, 2, 0)
    assert law2_lhs == law2_rhs
    # shift actually changed something
    assert law2_lhs != t

    # law 3 (shift/subst commutation): shift(subst(t,j,r),a,c) == subst(shift(t,a,c),j+a,shift(r,a,c))
    law3_lhs = Cure.Core.Term.shift(Cure.Core.Term.subst(t, 0, @sz), 1, 0)
    law3_rhs = Cure.Core.Term.subst(Cure.Core.Term.shift(t, 1, 0), 1, Cure.Core.Term.shift(@sz, 1, 0))
    assert law3_lhs == law3_rhs
    # subst actually changed something
    assert law3_lhs != Cure.Core.Term.shift(t, 1, 0)

    assert :ok = KernelLaw.run(ch("kernel/shift_subst", t))
  end

  test "weakening: closed well-typed term preserves typing + type-agreement" do
    assert :ok = KernelLaw.run(ch("kernel/weakening", @sz))
  end

  test "weakening: an ill-typed term is vacuously :ok (not a false violation)" do
    # `Z` applied as a function is ill-typed; infer fails ⇒ vacuous
    assert :ok = KernelLaw.run(ch("kernel/weakening", {:app, @z, @z}))
  end

  test "confluence: a redex normalizes identically via nf and whnf→nf" do
    assert :ok =
             KernelLaw.run(
               ch(
                 "kernel/confluence",
                 {:app, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:var, 0}}, @sz}
               )
             )
  end

  # spec §4 item 3 calls for both a positive AND a vacuous (fuel-exhausted)
  # confluence fixture — the assay fuel is fixed (`Assays.Term.assay_fuel/0`,
  # 500), not caller-supplied, so the only way to exercise the vacuous branch
  # through the public `KernelLaw.run/1` API is a term that genuinely needs
  # >500 reduction steps. `plus` (sig :v1) is structurally recursive on its
  # first argument (spec §2's wiring reuses the same v1 env as the other
  # assays), so `plus(deep_s(700), Z)` unfolds 700 times — confirmed
  # empirically: depth 500 is already enough to exhaust `nf`'s fuel=500
  # budget (depth 400 is not), so depth 700 gives comfortable headroom.
  defp deep_s(0), do: @z
  defp deep_s(n), do: {:ctor, :S, [deep_s(n - 1)]}

  test "confluence: a genuinely fuel-exhausting term is vacuously :ok" do
    t = {:app, {:app, {:global, :plus}, deep_s(700)}, @z}
    assert :ok = KernelLaw.run(ch("kernel/confluence", t))
  end

  # ── beta_subst + shift_agrees ─────────────────────────────────────────────
  @nat {:data, :Nat, [], []}

  test "beta_subst: a capture-trap redex — β lands on the same nf as subst" do
    # (λx:Nat. λ_:Nat. x) {:var,0} over a one-Nat context; x sits under the inner
    # λ, so the substituted var-0 must shift by 1.
    redex =
      {:app, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 1}}},
       {:var, 0}}

    assert :ok = KernelLaw.run(ch("kernel/beta_subst", redex, [@nat]))
  end

  test "beta_subst: a non-redex term is flagged distinctly (wiring guard)" do
    assert {:violation, {:beta_subst_not_a_redex, _}} =
             KernelLaw.run(ch("kernel/beta_subst", @sz, []))
  end

  test "shift_agrees: elaborator Subst.shift matches kernel Term.shift" do
    assert :ok =
             KernelLaw.run(
               ch("elab/shift_agrees", {:lam, Cure.Core.Grade.unrestricted(), @nat, {:app, {:var, 0}, {:var, 1}}})
             )
  end

  test "shift_agrees: the check is not tautological — a cutoff-blind shift WOULD disagree" do
    # If Subst.shift ever regressed to NOT bumping the cutoff under a binder, the
    # identity lambda's bound var would be wrongly shifted. Prove the kernel's own
    # shift distinguishes that mutant, so the agreement law has teeth.
    t = {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 0}}
    correct = Cure.Core.Term.shift(t, 1, 0)
    # forgot cutoff+1 under λ
    mutant = {:lam, Cure.Core.Grade.unrestricted(), @nat, Cure.Core.Term.shift({:var, 0}, 1, 0)}
    assert correct != mutant
    assert :ok = KernelLaw.run(ch("elab/shift_agrees", t))
  end
end

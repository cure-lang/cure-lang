defmodule Antigen.Generators.ZetaSubst do
  @moduledoc """
  Capture-trap generator for the `kernel/zeta_subst` law
  (`Antigen.Assays.KernelLaw`): ζ-reduction of a Core `:let` agrees with
  capture-avoiding substitution. Each challenge is a `:typed_term` carrying

      L = {:let, Cure.Core.Grade.unrestricted(), T, e, body}

  where `e` holds a free `{:var, k}` pointing into the ambient context and `body`
  places the bound occurrence of `x` UNDER one or more binders.

  This is the antibody for the `:let` binder's TCB entry, and it is a *stronger*
  probe than its sibling `kernel/beta_subst`. The kernel's ζ
  (`Cure.Core.Eval.eval/2`) pushes the **evaluated value** of `e` into the NbE
  environment and never shifts anything; `Term.subst/3` must shift `e` by the
  binder depth. The two mechanisms are entirely different, yet
  `nf(L) == nf(subst(body, 0, e))` must hold on every trap. It refutes at once:

    * a ζ that equates terms substitution does not (unsound: distinct normal
      forms collapsed);
    * a ζ that fails to unfold the bound variable (incomplete: `let n = 3` would
      leave `n` stuck, and the dependent `let` would not typecheck);
    * an off-by-one in `Term.shift`/`subst` under the new `:let` binder, since
      the substituted side would capture `e`'s free variable.

  The case menu is deliberately the same set of capture traps used by
  `Antigen.Generators.BetaSubst`, so ζ and β are attacked with identical shapes
  and a divergence between them is attributable to the `:let` node alone.
  """
  alias Antigen.{Gen, Challenge}
  alias Cure.Core.Grade

  @nat {:data, :Nat, [], []}
  @ty0 {:type, 0}

  # {ctx_types, result_type, T (let's ascription), e (has a free ambient var), body, note}
  @cases [
    {[@nat], {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, @nat, {:var, 0},
     {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 1}},
     "lam depth 1: x under one λ — subst shifts e by 1, ζ shifts nothing"},
    {[@nat], {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}, @nat,
     {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 2}}},
     "lam depth 2: x under two λ — subst shifts e by 2, ζ shifts nothing"},
    {[@nat],
     {:pi, Cure.Core.Grade.unrestricted(), @nat,
      {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}}, @nat, {:var, 0},
     {:lam, Cure.Core.Grade.unrestricted(), @nat,
      {:lam, Cure.Core.Grade.unrestricted(), @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 3}}}},
     "lam depth 3: x under three λ — subst shifts e by 3, ζ shifts nothing"},
    {[@ty0], @ty0, @ty0, {:var, 0}, {:pi, Cure.Core.Grade.unrestricted(), @nat, {:var, 1}},
     "pi codomain: x under a Π binder — the let-bound TYPE var must be transparent"},
    {[@ty0], @ty0, @ty0, {:var, 0},
     {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 1}}], []},
     "sigma codomain: x under a Σ binder"},
    {[@nat], @nat, @nat, {:var, 0},
     {:case, {:var, 1}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [{:Z, 0, {:var, 0}}, {:S, 1, {:var, 1}}]},
     "case branch: x under the S branch's arity-1 binder"},
    # `x` used THREE times under a binder — scrutinee plus both branches, at two
    # different depths. This is the shape where surface substitution duplicates
    # `e`; ζ must agree with `subst` on it while binding `e` exactly once.
    {[@nat], {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, @nat, {:var, 0},
     {:lam, Cure.Core.Grade.unrestricted(), @nat,
      {:case, {:var, 1}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [{:Z, 0, {:var, 1}}, {:S, 1, {:var, 2}}]}},
     "multi-use trap: x as scrutinee and in both branches, at two depths"},
    # The `:let` binder's GRADE (slice 2+3). The kernel deliberately ignores it —
    # `infer`/`check` bind it as `_g`, and Idris's `sameBinders` lists only `Pi` and
    # `Lam`, so a `Let`'s rig never enters conversion there either. What must hold is
    # that ζ is grade-INDEPENDENT and that `Term.shift`/`Term.subst` PRESERVE the
    # grade: the law compares `nf(let)` against `nf(subst(body, 0, e))`, and the
    # substituted side never carries the grade at all. Before these cells every
    # generated `:let` was `ω`, so the 5th field was never varied.
    {[@nat], {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, @nat, {:var, 0},
     {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 1}},
     "erased let: ζ agrees with subst regardless of the binder's grade"},
    {[@nat], {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, @nat, {:var, 0},
     {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 1}},
     "linear let: ζ agrees with subst regardless of the binder's grade"},
    {[@nat], {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, @nat, {:var, 0},
     {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 1}},
     "affine let: ζ agrees with subst regardless of the binder's grade"}
  ]

  @cells [
    :lam_depth1,
    :lam_depth2,
    :lam_depth3,
    :pi_codomain,
    :sigma_codomain,
    :case_branch,
    :used_twice,
    :grade_erased,
    :grade_linear,
    :grade_affine
  ]

  @doc """
  Shape-coverage cells for the manifest gate (`Antigen.CoverManifest`) — one per
  capture-trap depth/binder shape; the gate confirms every cell is produced by
  `gen/0`.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells, do: for(cell <- @cells, do: {"kernel/zeta_subst", cell})

  # The grade the `:let` binder carries, per cell. Everything else defaults to `ω`,
  # which is what every cell used before the graded cells were added.
  defp let_grade(:grade_erased), do: Grade.zero()
  defp let_grade(:grade_linear), do: Grade.one()
  defp let_grade(:grade_affine), do: Grade.affine()
  defp let_grade(_cell), do: Grade.unrestricted()

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(Enum.zip(@cases, @cells)), fn {{ctx, type, t, e, body, note}, cell} ->
      Gen.return(
        Challenge.new(
          kind: :typed_term,
          assay: "kernel/zeta_subst",
          label: :well_typed,
          payload: %{sig: :v1, ctx: ctx, type: type, term: {:let, let_grade(cell), t, e, body}},
          note: note,
          cover_tag: cell
        )
      )
    end)
  end

  @doc "The literal case menu (for the generator's coverage self-test)."
  def cases, do: @cases
end

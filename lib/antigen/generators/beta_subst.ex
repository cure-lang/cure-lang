defmodule Antigen.Generators.BetaSubst do
  @moduledoc """
  Capture-trap redex generator for the `kernel/beta_subst` law
  (`Antigen.Assays.KernelLaw`): β-reduction agrees with capture-avoiding
  substitution. Each challenge is a `:typed_term` carrying a redex

      R = {:app, {:lam, Cure.Core.Grade.unrestricted(), T, body}, e}

  where `e` holds a free `{:var, k}` pointing into the ambient context and `body`
  places the bound occurrence of `x` UNDER one or more binders, so substituting
  `e` for `x` happens at depth `d > 0` and REQUIRES shifting `e` by `d`. A subst
  that forgot the shift would capture `e`'s free variable under `body`'s binder —
  the exact bug the assay's `nf(R) == nf(subst(body,0,e))` check refutes.

  The menu varies the trap depth (1–3) and the binder kind crossed
  (`:lam`/`:pi`/`:sigma` codomains and a `:case` branch, whose ctor arity adds to
  the depth). Every case is closed-form well-typed over its stated context, so the
  kernel accepts the redex and both sides normalize to the same value.

  Kept as a fixed `:typed_term` menu (no new challenge kind) so it reuses the
  existing typed-term serialization/coverage wiring; only the assay-id dispatch is
  new. See ledger #4/#26 — the elaborator's bind-once β-redex fix relies on this
  substitution being capture-safe.
  """
  alias Antigen.{Gen, Challenge}

  @nat {:data, :Nat, [], []}
  @ty0 {:type, 0}

  # {ctx_types, result_type, T (redex binder), e (has a free ambient var), body, note}
  @cases [
    {[@nat], {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, @nat, {:var, 0},
     {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 1}}, "lam depth 1: x under one λ — e shifts by 1"},
    {[@nat], {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}, @nat,
     {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 2}}},
     "lam depth 2: x under two λ — e shifts by 2"},
    {[@nat],
     {:pi, Cure.Core.Grade.unrestricted(), @nat,
      {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}}, @nat, {:var, 0},
     {:lam, Cure.Core.Grade.unrestricted(), @nat,
      {:lam, Cure.Core.Grade.unrestricted(), @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 3}}}},
     "lam depth 3: x under three λ — e shifts by 3"},
    {[@ty0], @ty0, @ty0, {:var, 0}, {:pi, Cure.Core.Grade.unrestricted(), @nat, {:var, 1}},
     "pi codomain: x under a Π binder — e shifts by 1"},
    {[@ty0], @ty0, @ty0, {:var, 0},
     {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 1}}], []},
     "sigma codomain: x under a Σ binder — e shifts by 1"},
    {[@nat], @nat, @nat, {:var, 0},
     {:case, {:var, 1}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [{:Z, 0, {:var, 0}}, {:S, 1, {:var, 1}}]},
     "case branch: x under the S branch's arity-1 binder — e shifts by 1 there"}
  ]

  # Shape-coverage cell per @cases entry, same order (kept parallel so `cases/0`'s
  # 6-tuple shape, which the self-test destructures, stays intact).
  @cells [
    :lam_depth1,
    :lam_depth2,
    :lam_depth3,
    :pi_codomain,
    :sigma_codomain,
    :case_branch
  ]

  @doc """
  Shape-coverage cells for the manifest gate (`Antigen.CoverManifest`) — one per
  capture-trap depth/binder shape; the gate confirms every cell is produced by
  `gen/0`.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells, do: for(cell <- @cells, do: {"kernel/beta_subst", cell})

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(Enum.zip(@cases, @cells)), fn {{ctx, type, t, e, body, note}, cell} ->
      Gen.return(
        Challenge.new(
          kind: :typed_term,
          assay: "kernel/beta_subst",
          label: :well_typed,
          payload: %{sig: :v1, ctx: ctx, type: type, term: {:app, {:lam, Cure.Core.Grade.unrestricted(), t, body}, e}},
          note: note,
          cover_tag: cell
        )
      )
    end)
  end

  @doc "The literal case menu (for the generator's coverage self-test)."
  def cases, do: @cases
end

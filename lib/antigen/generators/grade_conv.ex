defmodule Antigen.Generators.GradeConv do
  @moduledoc """
  Generator for the `kernel/grade_conv` law (`Antigen.Assays.KernelLaw`): a Core
  binder's QTT **grade is part of type identity**.

  Idris settles this — `convBinders` compares `multiplicity`
  (`src/Core/Normalise/Convert.idr:328`):

      if sameBinders bx by && multiplicity bx == multiplicity by

  so `(1 x : A) -> B` is a *different type* from `(x : A) -> B`. Each challenge
  carries a single `{:pi, g, dom, cod}`; the assay derives its siblings by
  regrading, and asserts:

    * `conv?(t, t)` — reflexivity, so the law cannot pass vacuously by rejecting
      everything;
    * `conv?(t, regrade(t, g'))` is FALSE for every `g' ≠ g` — the property;
    * a λ checks against a Π of the same grade and is REJECTED against any other,
      which is where the discipline actually bites at a use site.

  Comparison must be by **equality**, never by `Grade.leq/2`. The preorder says a
  linear value is acceptable where an affine one is demanded — a fact about
  *usage*, not about type identity. A `Conv` that consulted `leq/2` would let a
  linear function be passed where an unrestricted one is expected, and the whole
  discipline would be decorative. The `linear_vs_affine` cell exists to catch
  exactly that mistake, since `leq(:linear, :affine)` holds while the types differ.
  """
  alias Antigen.{Gen, Challenge}
  alias Cure.Core.Grade

  @nat {:data, :Nat, [], []}
  @ty0 {:type, 0}

  # {ctx_types, result_type, term, note}
  @cases [
    {[], @ty0, {:pi, :erased, @nat, @nat}, "erased Pi: distinct from 1, <=1 and w"},
    {[], @ty0, {:pi, :linear, @nat, @nat}, "linear Pi: the QTT `1`"},
    {[], @ty0, {:pi, :affine, @nat, @nat}, "affine Pi: leq(:linear, :affine) holds, yet the TYPES differ"},
    {[], @ty0, {:pi, :unrestricted, @nat, @nat}, "unrestricted Pi: the default `w`"},
    {[], @ty0, {:pi, :linear, @ty0, @ty0}, "linear Pi over a universe domain"},
    {[], @ty0, {:pi, :linear, @nat, {:pi, :unrestricted, @nat, @nat}},
     "nested: the OUTER grade differs, the inner agrees"},
    {[], @ty0, {:pi, :unrestricted, @nat, {:pi, :linear, @nat, @nat}},
     "nested: the INNER grade differs, the outer agrees"},
    # ── λ, not just Π ────────────────────────────────────────────────────────
    # Idris compares the multiplicity of a `Lam` binder exactly as it does a `Pi`'s:
    # `sameBinders (Lam {}) (Lam {}) = True` and `multiplicity bx == multiplicity by`
    # (`Core/Normalise/Convert.idr:328-337`), reached from `convGen` on Bind-vs-Bind.
    # The η clause at `:351` only ever fires for Lam-vs-NON-Bind. Cure's `Conv` routed
    # EVERY `{:vlam, …}` on the left straight to η, so two λs differing only in grade
    # were convertible — and this generator emitted no λ cell, so nothing noticed.
    {[], {:pi, :erased, @nat, @nat}, {:lam, :erased, @nat, {:var, 0}}, "erased λ: distinct from 1, <=1 and w"},
    {[], {:pi, :linear, @nat, @nat}, {:lam, :linear, @nat, {:var, 0}}, "linear λ: the QTT `1` on a term binder"},
    {[], {:pi, :affine, @nat, @nat}, {:lam, :affine, @nat, {:var, 0}},
     "affine λ: leq(:linear, :affine) holds, yet the TERMS differ"},
    {[], {:pi, :unrestricted, @nat, @nat}, {:lam, :unrestricted, @nat, {:var, 0}}, "unrestricted λ: the default `w`"},
    {[], {:pi, :unrestricted, @nat, {:pi, :linear, @nat, @nat}},
     {:lam, :unrestricted, @nat, {:lam, :linear, @nat, {:var, 0}}},
     "nested λ: the INNER grade differs, the outer agrees"}
  ]

  @cells [
    :pi_erased,
    :pi_linear,
    :linear_vs_affine,
    :pi_unrestricted,
    :pi_universe_dom,
    :nested_outer,
    :nested_inner,
    :lam_erased,
    :lam_linear,
    :lam_affine,
    :lam_unrestricted,
    :lam_nested_inner
  ]

  @doc """
  Shape-coverage cells for the manifest gate (`Antigen.CoverManifest`) — one per
  grade/shape; the gate confirms every cell is produced by `gen/0`.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells, do: for(cell <- @cells, do: {"kernel/grade_conv", cell})

  @doc "Every grade other than `g` — the siblings a `{:pi, g, …}` / `{:lam, g, …}` must not convert with."
  @spec others(Grade.t()) :: [Grade.t()]
  def others(g), do: Grade.all() -- [g]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(Enum.zip(@cases, @cells)), fn {{ctx, type, term, note}, cell} ->
      Gen.return(
        Challenge.new(
          kind: :typed_term,
          assay: "kernel/grade_conv",
          label: :well_typed,
          payload: %{sig: :v1, ctx: ctx, type: type, term: term},
          note: note,
          cover_tag: cell
        )
      )
    end)
  end

  @doc "The literal case menu (for the generator's coverage self-test)."
  def cases, do: @cases
end

defmodule Antigen.Generators.DotForcing do
  @moduledoc """
  Known-label generator for the `forcing/dot` vertical
  (`Antigen.Assays.DotForcing`): the forced/dot-pattern ("dot-forcing") soundness
  test — ledger row #24.

  The feature under test (already shipped; commits 5409184 / 852742a / f01742e) is
  the CHECK-AND-DISCARD named-implicit dot annotation `{name = .e}` on a
  constructor pattern: it asserts the forced (index-unification-pinned) value at
  the named erased index position equals `e`, binds nothing, emits no runtime
  term, and only ever REJECTS a wrong forced value. The soundness property, per
  case, is a correct-by-construction label the assay checks against the live
  elaborator/kernel via the public `Elaborator.forced_check_probe/7` shim:

    * `:accept`   — written value `t` convertible to the pinned forced value `d`
    * `:reject`   — `t` rigidly distinct from `d` (→ `forced_pattern_mismatch`)
    * `:unforced` — the named position is not a pinned index (→ `named_implicit_unforced`)

  Cases reuse the v1 SigMenu families (Vec's erased length index `n`; Sq's
  diagonal two-index constructor), so the true `d` is computable by construction
  from the same `branch_unify` substitution the kernel produces.
  """
  alias Antigen.{Gen, Challenge}

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`): one per distinct forced-value
  case shape (family × verdict), so the gate confirms every `:accept`/`:reject`/
  `:unforced` shape the assay checks is actually produced by sampling `@cases`.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for cell <- [
          :vec_accept_syntactic,
          :vec_accept_convertible,
          :vec_reject_ctor_clash,
          :vec_reject_field_var,
          :vec_unforced_field,
          :vec_unforced_absent,
          :sq_accept_diagonal,
          :sq_reject_multi_index,
          :vec_accept_nontrivial,
          :vec_reject_differing,
          :h_accept_carried,
          :h_reject_carried
        ],
        do: {"forcing/dot", cell}
  end

  @z {:ctor, :Z, []}
  # (λx:Nat. x) Z — β-reduces to Z: convertible to a forced Z WITHOUT being
  # syntactically equal, so Conv.conv? must actually decide (not just `==`).
  @lam_id_z {:app, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:var, 0}}, @z}

  # {ctx_vars, family, cname, scrut_index_terms, name, written_value, label, note}.
  # Coverage cells are kept OUT of this tuple (in @case_cells, positionally aligned)
  # so the 8-tuple shape stays stable for the corpus-roundtrip / menu tests.
  @cases [
    {0, :Vec, :vcons, [{:ctor, :S, [@z]}], "n", @z, :accept, "Vec vcons {n=.Z} vs forced Z — syntactic match"},
    {0, :Vec, :vcons, [{:ctor, :S, [@z]}], "n", @lam_id_z, :accept,
     "Vec vcons {n=.((λx.x) Z)} vs forced Z — convertible, non-syntactic (Conv decides)"},
    {0, :Vec, :vcons, [{:ctor, :S, [@z]}], "n", {:ctor, :S, [@z]}, :reject,
     "Vec vcons {n=.(S Z)} vs forced Z — rigid ctor clash (forced_pattern_mismatch)"},
    {0, :Vec, :vcons, [{:ctor, :S, [@z]}], "n", {:var, 1}, :reject,
     "Vec vcons {n=.x} vs forced Z — distinct field var (forced_pattern_mismatch)"},
    {0, :Vec, :vcons, [{:ctor, :S, [@z]}], "x", @z, :unforced,
     "Vec vcons {x=.Z} — x is a non-pinned field (named_implicit_unforced)"},
    {0, :Vec, :vcons, [{:ctor, :S, [@z]}], "bogus", @z, :unforced,
     "Vec vcons {bogus=.Z} — name absent from telescope (named_implicit_unforced)"},
    {0, :Sq, :mksq, [@z, @z], "n", @z, :accept, "Sq mksq {n=.Z} vs forced Z — multi-index family, diagonal pin"},
    {0, :Sq, :mksq, [@z, @z], "n", {:ctor, :S, [@z]}, :reject, "Sq mksq {n=.(S Z)} vs forced Z — multi-index reject"},
    {0, :Vec, :vcons, [{:ctor, :S, [{:ctor, :S, [@z]}]}], "n", {:ctor, :S, [@z]}, :accept,
     "Vec vcons {n=.(S Z)} vs forced S Z — non-trivial forced value"},
    {0, :Vec, :vcons, [{:ctor, :S, [{:ctor, :S, [@z]}]}], "n", @z, :reject,
     "Vec vcons {n=.Z} vs forced S Z — reject on differing forced value"},
    # Carried-shaped subst (vertical #24, spec 2026-07-08): H's second index is
    # the stuck `app(as, bs)`, dropped `:undecided` by branch_unify, so only the
    # first (invertible) index pins `m`. Exercises the shared forced-value /
    # convertibility PRIMITIVES under a multi-index carried shape the Vec/Sq
    # cases don't reach — NOT the carried-eq dispatch wiring (forced_check_probe
    # rebuilds its frame from the supplied telescope/subst directly).
    {0, :H, :hmk, [{:ctor, :S, [@z]}, {:ctor, :SNil, []}], "m", @z, :accept,
     "H hmk {m=.Z} under a multi-sibling carried-index subst — forced-check primitives, not the dispatch wiring"},
    {0, :H, :hmk, [{:ctor, :S, [@z]}, {:ctor, :SNil, []}], "m", {:ctor, :S, [@z]}, :reject,
     "H hmk {m=.(S Z)} under a multi-sibling carried-index subst — rigid clash on the forced-check primitives, not the dispatch wiring"}
  ]

  # Coverage cell per @cases entry, positionally aligned (one per distinct family ×
  # verdict shape). Kept out of @cases so its 8-tuple shape stays stable.
  @case_cells [
    :vec_accept_syntactic,
    :vec_accept_convertible,
    :vec_reject_ctor_clash,
    :vec_reject_field_var,
    :vec_unforced_field,
    :vec_unforced_absent,
    :sq_accept_diagonal,
    :sq_reject_multi_index,
    :vec_accept_nontrivial,
    :vec_reject_differing,
    :h_accept_carried,
    :h_reject_carried
  ]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(Enum.zip(@cases, @case_cells)), fn {{n, fam, c, idx, name, written, label, note}, cell} ->
      Gen.return(
        Challenge.new(
          kind: :dot_forcing,
          assay: "forcing/dot",
          label: label,
          cover_tag: cell,
          payload: %{
            ctx_vars: n,
            family: fam,
            cname: c,
            indices: idx,
            name: name,
            written: written
          },
          note: note
        )
      )
    end)
  end

  @doc "The literal case menu (for the generator's coverage self-test)."
  def cases, do: @cases
end

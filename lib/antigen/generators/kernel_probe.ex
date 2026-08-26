defmodule Antigen.Generators.KernelProbe do
  @moduledoc """
  Generator for the `kernel/probe` vertical (`Antigen.Assays.KernelProbe`): a fixed
  menu of def-level / inference-mode probes driving *defensive* clauses across the
  trusted kernel modules that no term-shaped generator reaches — `Kernel.check_def`'s
  unknown-global and body-less builtin-op arms, `validate_certificate`'s builtin-op
  certification, `check_family`'s universe-ceiling rejection, `normalize/3`'s opts
  arity, the Final-Core validator's warning-emit fold, `infer`'s `{:absurd}` /
  fields-only-ctor / ctor-arity rejections, `remap_index_error`'s non-family
  passthrough, plus the sibling-module cold clauses: `Quote.split_data_args`'s
  foreign-family fallback, `Inductive.occurs_deep?`'s through-constructor recursion,
  `Serialize.sym_atom`'s un-interned-symbol rejection, and `Certificate`'s
  under-application (`arg_relation(nil,_)`) and dangling-callee (`callees_env` /
  `reaches?` leaf) paths.

  Each challenge carries only a probe tag (`Coverage.terms_of` → `[]`, bypassing the
  term-well-formedness gate the way `check/verdict` and `serialize/decode` do); the
  assay reconstructs the input and asserts the kernel's documented verdict.
  """
  alias Antigen.{Gen, Challenge}

  @probes [
    :infer_absurd,
    :infer_fields_only_ctor,
    :check_ctor_arity,
    :check_def_unknown,
    :check_def_builtin_op,
    :validate_cert_builtin_op,
    :family_ceiling,
    :normalize_opts,
    :validator_warn_emit,
    :remap_index_passthrough,
    :quote_foreign_vdata,
    :positivity_through_ctor,
    :decode_unknown_symbol,
    :cert_under_application,
    :cert_dangling_callee,
    # Adversarial "backstop" probes — feed malformed input straight at a kernel
    # boundary and assert the defensive guard fires (rather than assuming it does).
    :eval_no_branch,
    :eval_nondata_scrutinee,
    :apply_nonfun,
    :conv_unknown_ctor_fallback,
    :validator_rejects_hole_body,
    # Value-surface probes — the atom / bounded / binary-type / bitwise family the
    # dependent value surface added, driven through eval / conv / quote / serialize /
    # infer / check / branch_unify / positivity (no term generator produces these).
    :eval_value_literals,
    :eval_negative_debruijn,
    :eval_bounded_no_branch,
    :eval_bounded_iota,
    :eval_bounded_peel,
    :eval_bitwise_fold,
    :quote_value_surface,
    :conv_atom_binary,
    :conv_bounded_crossrep,
    :conv_no_delta_value_surface,
    :serialize_value_surface,
    :serialize_special_atoms,
    :serialize_malformed_symbol,
    :infer_value_type_formers,
    :infer_bounded_unregistered,
    :infer_bounded_registered,
    :check_bounded_in_range,
    :check_bounded_out_of_range,
    :check_bounded_tower,
    :check_bounded_not_concrete,
    :check_bounded_wrong_family,
    :check_ctor_via_infer,
    :sort_value_type_formers,
    :unify_bounded_bridge,
    :unify_rigid_value_heads,
    :opaque_family_positivity,
    :positivity_alias_expansion,
    :occurs_bare_global,
    :whnf_arity2_direct,
    :whnf_nested_fuel_restore,
    :cert_unknown_tuple_node,
    :cert_unknown_list_node,
    :cert_nontuple_call_arg,
    :cert_nontuple_list_elem,
    :cert_calls_nontuple_head,
    # Editions-facility probes — the edition-derived keyword set and the migrate
    # fixpoint loop, driven through Cure.Edition.retired_keywords/2 and
    # Cure.Migrate.run_to_fixpoint/2 (no term generator reaches this surface).
    :edition_retired_keywords,
    :migrate_fixpoint_converges
  ]

  @doc """
  Shape-coverage cells for the manifest gate. One cell per probe; the gate confirms
  every probe is actually produced by sampling `gen/0`.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells, do: for(p <- @probes, do: {"kernel/probe", p})

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@probes), fn probe ->
      Gen.return(
        Challenge.new(
          kind: :kernel_probe,
          assay: "kernel/probe",
          label: :probe,
          payload: %{probe: probe},
          note: "kernel def-level probe: #{probe}",
          cover_tag: probe
        )
      )
    end)
  end
end

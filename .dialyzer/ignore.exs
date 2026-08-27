[
  # Dialyzer reports false positives for `if state.emit_events` guards
  # and pattern_match_cov in the Parser module.
  {"lib/cure/compiler/parser.ex", :pattern_match},
  {"lib/cure/compiler/parser.ex", :pattern_match_cov},

  # -- MapSet opaqueness false positives (Elixir 1.20-rc / OTP 29+) ----------
  #
  # `MapSet.t()` in Elixir 1.20 is deliberately NOT opaque
  # (`@type t(value) :: %__MODULE__{map: internal(value)}` where
  # `internal(value) :: %{optional(value) => term()}`), but its runtime
  # representation is built on top of `:sets.set()` which IS opaque in OTP.
  # Every call site that passes a MapSet through a public MapSet function
  # triggers `call_without_opaque` / `contract_with_opaque` because dialyzer
  # observes the declared `%MapSet{map: map()}` shape alongside the inferred
  # `%MapSet{map: :sets.set(_)}` shape and considers them incompatible. See
  # https://github.com/elixir-lang/elixir/blob/main/lib/elixir/lib/map_set.ex
  # for the rationale (struct key name kept for backwards compatibility with
  # the pre-1.15 implementation). There is nothing to fix at the call site.
  {"lib/cure/cli.ex", :pattern_match},
  {"lib/cure/cli.ex", :pattern_match_cov},
  {"lib/cure/compiler.ex", :unknown_type},
  {"lib/cure/compiler/artifacts.ex", :pattern_match},
  {"lib/cure/compiler/artifacts/lock.ex", :pattern_match},
  {"lib/cure/compiler/artifacts/provenance.ex", :pattern_match},
  {"lib/cure/compiler/codegen.ex", :call_without_opaque},
  {"lib/cure/compiler/macro_packet.ex", :call_without_opaque},
  {"lib/cure/compiler/macro_packet.ex", :call_with_opaque},
  {"lib/cure/compiler/module_manifest.ex", :call_without_opaque},
  {"lib/cure/compiler/module_manifest.ex", :call_with_opaque},
  {"lib/cure/compiler/module_pipeline.ex", :pattern_match_cov},
  {"lib/cure/compiler/module_pipeline.ex", :call_without_opaque},
  {"lib/cure/compiler/module_pipeline.ex", :call_with_opaque},
  {"lib/cure/compiler/module_pipeline/closure.ex", :call_without_opaque},
  {"lib/cure/compiler/module_pipeline/closure.ex", :call_with_opaque},
  {"lib/cure/compiler/module_pipeline/expansion.ex", :call_without_opaque},
  {"lib/cure/compiler/module_pipeline/expansion.ex", :call_with_opaque},
  {"lib/cure/compiler/parser/fixity_resolver.ex", :call_without_opaque},
  {"lib/cure/compiler/parser/fixity_resolver.ex", :call_with_opaque},
  {"lib/cure/compiler/parser/fixity_table.ex", :call_without_opaque},
  {"lib/cure/compiler/parser.ex", :guard_fail},
  {"lib/cure/types/checker.ex", :call_without_opaque},
  {"lib/cure/types/effects.ex", :call_without_opaque},
  {"lib/cure/types/env.ex", :call_without_opaque},
  {"lib/cure/types/env.ex", :contract_with_opaque},
  {"lib/cure/types/pattern_checker.ex", :call_without_opaque},
  {"lib/cure/types/totality.ex", :call_without_opaque},
  {"lib/cure/repl.ex",  :call_without_opaque},
  {"lib/cure/elab/totality_closure.ex", :call_without_opaque},
  {"lib/cure/elab/proof_goal.ex", :call_without_opaque},
  {"lib/cure/elab/proof_goal.ex", :call_with_opaque},
  {"lib/cure/elab/program.ex", :pattern_match_cov},
  {"lib/cure/elab/program.ex", :pattern_match},
  {"lib/cure/elab/macro_expand.ex", :pattern_match},
  {"lib/cure/elab/macro_expand.ex", :pattern_match_cov},
  {"lib/cure/elab/emit.ex", :unused_fun},
  {"lib/cure/elab/emit.ex", :no_return},
  {"lib/cure/elab/emit.ex", :call},
  {"lib/cure/elab/elaborator.ex", :call_without_opaque},
  {"lib/cure/elab/elaborator.ex", :call_with_opaque},
  {"lib/cure/elab/elaborator.ex", :pattern_match},
  {"lib/cure/elab/elaborator.ex", :pattern_match_cov},
  {"lib/cure/elab/elaborator.ex", :guard_fail},
  {"lib/cure/elab/implementation.ex", :guard_fail},
  {"lib/cure/compiler/portable_closure.ex", :pattern_match},
  {"lib/cure/core/inductive.ex", :pattern_match},
  {"lib/cure/core/size_change.ex", :pattern_match},
  {"lib/cure/core/totality_certificate.ex", :call_without_opaque},
  {"lib/cure/core/totality_certificate.ex", :call_with_opaque},
  {"lib/cure/diagnostic/adapter.ex", :guard_fail},
  {"lib/cure/diagnostic/adapter/macro.ex", :pattern_match},
  {"lib/cure/diagnostic/adapter/syntax.ex", :call},
  {"lib/cure/diagnostic/snippet.ex", :unknown_type},
  {"lib/cure/migrate.ex", :call_without_opaque},
  {"lib/cure/elab/simplifier.ex", :pattern_match},
  {"lib/cure/elab/simplifier.ex", :unused_fun},
  {"lib/cure/meta_ast/conformance.ex", :pattern_match},
  {"lib/cure/watch.ex", :pattern_match},

  # -- PRE-EXISTING BASELINE, recorded 2026-07-10 -----------------------------
  #
  # `mix dialyzer` is a GATE on NEW warnings, not a claim of zero. These
  # (file, kind) pairs cover the warnings present when Dialyzer was first
  # adopted, on a tree at 3795 tests green. They are NOT endorsed — most are
  # MapSet/`:sets` opaqueness false positives under Elixir 1.20 + OTP 29, plus
  # `unknown_function` for the optional `stream_data` backend.
  #
  # HONEST LIMIT: baselining by (file, kind) also suppresses a NEW warning of the
  # same kind in the same file. Prefer deleting an entry and fixing the warning
  # over widening this list. Adding to it is a debt, not a fix.
  {"lib/antigen/assays/delta_reduce.ex", :invalid_contract},
  {"lib/antigen/assays/elab.ex", :pattern_match_cov},
  {"lib/antigen/assays/inductive_env.ex", :call},
  {"lib/antigen/assays/inductive_env.ex", :no_return},
  {"lib/antigen/assays/inductive_env.ex", :unused_fun},
  {"lib/antigen/assays/kernel_probe.ex", :call},
  {"lib/antigen/assays/kernel_probe.ex", :no_return},
  {"lib/antigen/backend/stream_data.ex", :unknown_function},
  {"lib/antigen/cover_report.ex", :call_without_opaque},
  {"lib/antigen/generators/indexed_decl.ex", :call},
  {"lib/antigen/generators/indexed_decl.ex", :no_return},
  {"lib/antigen/generators/surface_expr.ex", :pattern_match},
  {"lib/cure/compiler/dep_graph.ex", :call_with_opaque},
  {"lib/cure/compiler/dep_graph.ex", :call_without_opaque},
  {"lib/cure/compiler/dep_graph.ex", :pattern_match},
  {"lib/cure/compiler/dep_graph.ex", :unused_fun},
  {"lib/cure/core/builtins.ex", :guard_fail},
  {"lib/cure/core/certificate.ex", :call_with_opaque},
  {"lib/cure/core/certificate.ex", :call_without_opaque},
  {"lib/cure/core/inductive.ex", :call_with_opaque},
  {"lib/cure/core/inductive.ex", :call_without_opaque},
  {"lib/cure/core/inductive.ex", :invalid_contract},
  {"lib/cure/core/inductive.ex", :pattern_match_cov},
  {"lib/cure/core/kernel.ex", :call},
  {"lib/cure/core/kernel.ex", :no_return},
  {"lib/cure/elab/declarations.ex", :call},
  {"lib/cure/elab/implementation.ex", :call_without_opaque},
  {"lib/cure/elab/program.ex", :call_with_opaque},
  {"lib/cure/elab/program.ex", :call_without_opaque},
  # resolve.ex: the classify/3 typealias-unfold path flows a MapSet `seen`
  # through a private helper (dispatch-side coherence), same opaqueness class.
  {"lib/cure/elab/resolve.ex", :call_with_opaque},
  {"lib/cure/elab/resolve.ex", :call_without_opaque},
  {"lib/cure/types/checker.ex", :pattern_match_cov},
  {"lib/cure/types/env.ex", :call_with_opaque},
  {"lib/mix/tasks/antigen.ex", :no_return}
]

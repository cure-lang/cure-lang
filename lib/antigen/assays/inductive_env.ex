defmodule Antigen.Assays.InductiveEnv do
  @moduledoc """
  `inductive/env_roundtrip` — drives `Cure.Core.Inductive`'s Env-registration
  API (`declare/3`, `register_builtin/3`) and reads every declared family's/
  constructor's metadata back through the accessor layer (`family?/2`,
  `ctor_result_indices/2`, `arg_telescope/2`, `field_count/2`,
  `ctor_quantities/2`, `index_telescope/2`, `param_telescope/2`,
  `ctor_result_params/2`) — the seam production code (the elaborator, erasure,
  relevance, `Conv`) reads through but no other assay exercises directly.

  Four independent, non-tautological properties per challenge (never "read
  back the literal we just wrote and call it a test" — each one can fail for a
  reason the roundtrip alone would not catch):

    1. **Kernel soundness** (the same check `Assays.Universes` runs):
       `Kernel.check_family/2` + `Kernel.check_ctor/3` must accept a
       `:well_typed` declaration — the accessor layer is only interesting to
       exercise over a declaration the real kernel actually agrees is valid.

    2. **Accessor roundtrip + negative space**: every targeted accessor,
       called on the name it was declared under, must return exactly what was
       declared (a write-then-read consistency law — catches a `declare/3`
       mis-key, e.g. storing a ctor under the wrong atom, or an accessor
       reading the wrong struct field); called on a name that was NEVER
       declared, every accessor must return its documented "not found"
       sentinel (`nil` or `false`) — catches an accessor that accidentally
       aliases an unknown name to some other entry (e.g. `Map.get/2` without
       a default, or a fallback clause ordered before the `nil` clause).

    3. **Legacy-record back-compat**: `ctor_quantities/2` and
       `ctor_result_params/2` both carry a defaulting `_ -> nil` / `_ -> []`
       clause for a ctor record that predates those fields (mirrors
       `Antigen.Challenge`'s own private `ctor_result_params/1` helper and its
       "tolerant of legacy records lacking the field" rationale). A hand-built
       ctor map missing both keys — `declare/3` has no schema requirement
       beyond `:name`, so this is legitimate data, not a malformed input —
       must still read back the documented defaults.

    4. **`register_builtin/3` single-registration invariant** (its own
       doc-comment's contract): re-binding an already-bound key to the SAME
       family-id is an idempotent no-op; re-binding to a DIFFERENT family-id
       raises `ArgumentError`. Every other caller in the codebase
       (`Builtins.seed_ops`, `sig_menu.ex`) only ever registers a key ONCE, so
       neither branch of the guarded clause is reachable except here.
  """
  alias Antigen.Challenge
  alias Cure.Core.{Env, Inductive, Kernel}

  # "Never declared" sentinels for the negative half of the roundtrip. Fixed
  # literals in THIS module's source — never routed through a challenge's
  # `payload`/scaffold — so they need no `Antigen.Challenge.@known_atoms` entry
  # (that whitelist is only for atoms `to_pieces`/`from_pieces` reconstruct via
  # `String.to_existing_atom/1`; see the module's own doc on the point).
  @absent_family :__antigen_absent_family__
  @absent_ctor :__antigen_absent_ctor__

  @builtin_probe_key :antigen_builtin_probe
  @builtin_probe_other :antigen_builtin_probe_other

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{
        kind: :family,
        assay: "inductive/env_roundtrip",
        label: label,
        payload: %{family: fam, ctors: [ctor] = ctors}
      }) do
    env = Inductive.declare(Antigen.CanonBuiltins.seed(Env.empty()), fam, ctors)

    with :ok <- check_kernel_accepts(env, fam, ctors, label),
         :ok <- check_roundtrip(env, fam, ctor),
         :ok <- check_negative_space(env, fam),
         :ok <- check_legacy_record(env),
         :ok <- check_builtin_invariant(env, fam) do
      :ok
    end
  end

  # -- 1. kernel soundness ------------------------------------------------------

  defp check_kernel_accepts(env, fam, ctors, :well_typed) do
    with :ok <- Kernel.check_family(env, fam),
         :ok <- run_ctors(env, fam, ctors) do
      :ok
    else
      {:error, reason} -> {:violation, {:wrongly_rejected, fam.name, reason}}
    end
  end

  defp run_ctors(env, fam, ctors) do
    Enum.reduce_while(ctors, :ok, fn c, :ok ->
      case Kernel.check_ctor(env, fam, c) do
        :ok -> {:cont, :ok}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # -- 2a. roundtrip (positive space) -------------------------------------------

  defp check_roundtrip(env, fam, ctor) do
    cond do
      not Inductive.family?(env, fam.name) ->
        {:violation, {:roundtrip_family_missing, fam.name}}

      Inductive.index_telescope(env, fam.name) != fam.indices ->
        {:violation, {:roundtrip_index_telescope, fam.name}}

      Inductive.param_telescope(env, fam.name) != fam.params ->
        {:violation, {:roundtrip_param_telescope, fam.name}}

      Inductive.arg_telescope(env, ctor.name) != ctor.args ->
        {:violation, {:roundtrip_arg_telescope, ctor.name}}

      Inductive.field_count(env, ctor.name) != length(ctor.args) ->
        {:violation, {:roundtrip_field_count, ctor.name}}

      Inductive.ctor_result_indices(env, ctor.name) != ctor.result_indices ->
        {:violation, {:roundtrip_result_indices, ctor.name}}

      Inductive.ctor_quantities(env, ctor.name) != ctor.quantities ->
        {:violation, {:roundtrip_quantities, ctor.name}}

      Inductive.ctor_result_params(env, ctor.name) != ctor.result_params ->
        {:violation, {:roundtrip_result_params, ctor.name}}

      true ->
        :ok
    end
  end

  # -- 2b. negative space --------------------------------------------------------

  defp check_negative_space(env, fam) do
    cond do
      fam.name == @absent_family ->
        {:violation, {:generator_bug_sentinel_collision, fam.name}}

      Inductive.family?(env, @absent_family) ->
        {:violation, {:family_false_positive, @absent_family}}

      Inductive.index_telescope(env, @absent_family) != nil ->
        {:violation, {:index_telescope_false_positive, @absent_family}}

      Inductive.param_telescope(env, @absent_family) != nil ->
        {:violation, {:param_telescope_false_positive, @absent_family}}

      Inductive.arg_telescope(env, @absent_ctor) != nil ->
        {:violation, {:arg_telescope_false_positive, @absent_ctor}}

      Inductive.field_count(env, @absent_ctor) != nil ->
        {:violation, {:field_count_false_positive, @absent_ctor}}

      Inductive.ctor_result_indices(env, @absent_ctor) != nil ->
        {:violation, {:result_indices_false_positive, @absent_ctor}}

      Inductive.ctor_quantities(env, @absent_ctor) != nil ->
        {:violation, {:quantities_false_positive, @absent_ctor}}

      Inductive.ctor_result_params(env, @absent_ctor) != nil ->
        {:violation, {:result_params_false_positive, @absent_ctor}}

      true ->
        :ok
    end
  end

  # -- 3. legacy-record back-compat ---------------------------------------------

  # A ctor record built before `result_params`/`quantities` existed (a raw map,
  # not `Inductive.ctor/3..5`, which always defaults both). `declare/3` accepts
  # it (its only requirement is `:name`), so both accessors must fall back to
  # their documented defaults on it, never crash or misreport.
  defp check_legacy_record(env) do
    legacy_fam = Inductive.family(:AntigenLegacy, [], [], 0)
    legacy_ctor = %{name: :antigen_legacy_ctor, args: [], result_indices: []}
    legacy_env = Inductive.declare(env, legacy_fam, [legacy_ctor])

    cond do
      Inductive.ctor_quantities(legacy_env, :antigen_legacy_ctor) != nil ->
        {:violation, {:legacy_quantities_not_nil, :antigen_legacy_ctor}}

      Inductive.ctor_result_params(legacy_env, :antigen_legacy_ctor) != [] ->
        {:violation, {:legacy_result_params_not_empty, :antigen_legacy_ctor}}

      true ->
        :ok
    end
  end

  # -- 4. register_builtin/3 single-registration invariant ----------------------

  defp check_builtin_invariant(env, fam) do
    env1 = Inductive.register_builtin(env, @builtin_probe_key, fam.name)
    env2 = Inductive.register_builtin(env1, @builtin_probe_key, fam.name)

    cond do
      Inductive.builtin(env2, @builtin_probe_key) != fam.name ->
        {:violation, {:builtin_lookup_mismatch, fam.name}}

      env2.builtins != env1.builtins ->
        {:violation, {:builtin_rebind_not_idempotent, fam.name}}

      true ->
        try do
          Inductive.register_builtin(env1, @builtin_probe_key, @builtin_probe_other)
          {:violation, {:builtin_rebind_should_have_raised, fam.name}}
        rescue
          ArgumentError -> :ok
        end
    end
  end
end

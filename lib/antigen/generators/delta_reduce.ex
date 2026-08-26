defmodule Antigen.Generators.DeltaReduce do
  @moduledoc """
  Known-normal-form generator for the `delta/nf` vertical
  (`Antigen.Assays.DeltaReduce`): δ-reduction (unfolding of CERTIFIED global
  definitions) under the trusted normalizer, checked against a
  correct-by-construction normal form.

  This is the definitional-equality path nothing else in the suite drives — the
  closed-`typed_term` verticals normalize terms over the v1 menu, which has no
  global definitions, so `Normalise.unfold_certified_head` (δ-unfold a certified
  global) and its ι-follow-through on the unfolded body (a projection landing on
  the pair a def expands to) stay cold. Over a fixed certified env
  (`idnat = λx.x`, `kpair = (Z, S Z)`, `donly` below) the true normal form is
  computable by construction, so each `:reduces` case pins `nf(term)` exactly.

  Three sub-verticals share this one generator/assay pair (one challenge `kind`,
  per the operator's steer — extend `DeltaReduce` rather than mint a new kind),
  distinguished by `label`:

    * `:reduces` (original) — the known-normal-form menu above, extended with
      builtin-op-fold and branch-miss-freeze probes.
    * `:fuel_probe` — drives `Normalise.nf/3` with an EXPLICIT, non-default
      `fuel:` budget: sufficient fuel must agree with the unbounded result;
      insufficient fuel must report `:fuel_exhausted`, never a truncated wrong
      value. The always-cold fuel-accounting plumbing (`with_fuel/2`,
      `fuel_key/0`, `spend_fuel/1`) only fires under a finite budget — nothing
      else in the suite ever passes `fuel:`.
    * `:opts_reject` — deliberately malformed `normalize_opts/1` input (bad
      `:delta`/`:mode`/`:fuel`/`:stuck_cases`) must always raise `ArgumentError`,
      never be silently coerced. Routed through `Normalise.whnf_value/3`
      directly rather than the public `nf/3`/`whnf/3` — those force `:mode`
      themselves before it ever reaches the validator, so a bad `:mode` value
      never survives to be checked through the public entry points.
  """
  alias Antigen.{Gen, Challenge}

  @z {:ctor, :Z, []}
  @nat {:data, :Nat, [], []}
  @motive {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}
  @int_type {:int_type}

  # `kpair : Sigma(Nat, const-Nat) = mk_pair(Z, S Z)` (the inductive dependent pair,
  # D2). Projections are single-branch `:case`s over `mk_pair` — the ncase form the
  # δ+ι engine reduces now that the primitive `{:fst}`/`{:snd}` nodes are retired
  # (`case (mk_pair x y) of mk_pair(x,y) -> x|y` ι-reduces exactly as nfst/nsnd did).
  # Motive is the constant `Nat` (the pair is non-dependent); fields bind x=`{:var,1}`,
  # y=`{:var,0}` in the branch frame.
  @kpair_sigma {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}
  @kfst {:case, {:global, :kpair}, {:lam, Cure.Core.Grade.unrestricted(), @kpair_sigma, @nat},
         [{:mk_pair, 2, {:var, 1}}]}
  @ksnd {:case, {:global, :kpair}, {:lam, Cure.Core.Grade.unrestricted(), @kpair_sigma, @nat},
         [{:mk_pair, 2, {:var, 0}}]}

  # A direct `case` whose scrutinee is a certified global's application (neutral
  # at eval-time, resolves to `S Z` only once forced) and whose branch menu is
  # MISSING the `S` arm. Once forced, `unfold_certified_head`'s OWN `:ncase`
  # clause finds no matching branch — the "no branch, but never crash" freeze
  # (mirrors `eval`'s ctor-branch, but returns `:stuck` instead of raising).
  @case_missing_branch {:case, {:app, {:global, :idnat}, {:ctor, :S, [@z]}}, @motive, [{:Z, 0, @z}]}

  # `donly : Nat -> Nat = λx. case (idnat x) { Z -> Z }` — a certified global
  # (env below) whose δ-unfold re-exposes a case that is ITSELF stuck on a
  # missing `S` branch. The twin of `@case_missing_branch`, but reached through
  # `reduce_unfolded`'s post-unfold ι follow-through (the lazy-unfolding path)
  # rather than `unfold_certified_head`'s own clause — both branch-miss sites
  # must independently freeze, never crash.
  @donly_arg {:ctor, :S, [@z]}
  @donly_term {:app, {:global, :donly}, @donly_arg}

  # {term, expected_nf, note}
  @cases [
    {{:app, {:global, :idnat}, @z}, @z, "δ+β: idnat Z → Z (unfold certified global, then β)"},
    {{:app, {:global, :idnat}, {:ctor, :S, [@z]}}, {:ctor, :S, [@z]}, "δ+β: idnat (S Z) → S Z"},
    {@kfst, @z, "δ+ι: fst kpair → Z (unfold to a pair, project first via ι-on-case)"},
    {@ksnd, {:ctor, :S, [@z]}, "δ+ι: snd kpair → S Z (project second via ι-on-case)"},
    {{:app, {:global, :idnat}, @kfst}, @z, "nested: idnat (fst kpair) → Z (two unfolds + a projection)"},
    # idnat's δ-unfold exposes a `snd kpair` case under reduce_unfolded (not the
    # direct unfold_certified_head path the bare case takes) — the post-unfold ι
    # follow-through.
    {{:app, {:global, :idnat}, @ksnd}, {:ctor, :S, [@z]},
     "nested: idnat (snd kpair) → S Z (unfold exposes the case, reduce_unfolded)"},
    # Builtin-op-fold (Amendment A1): struct_eq/struct_ne fold a SATURATED
    # literal spine via the audited table — the polymorphic-equality twin of the
    # int/float binop fold (already warm via the Primitive generator).
    {{:app, {:app, {:app, {:global, :struct_eq}, @int_type}, {:int_lit, 3}}, {:int_lit, 4}},
     {:ctor, :"Std.Bool#False", []},
     "builtin/struct_eq: struct_eq Int 3 4 → False (δ-fold via the audited literal table)"},
    {{:app, {:app, {:app, {:global, :struct_ne}, @int_type}, {:int_lit, 5}}, {:int_lit, 5}},
     {:ctor, :"Std.Bool#False", []},
     "builtin/struct_ne: struct_ne Int 5 5 → False (δ-fold via the audited literal table)"},
    # Unsaturated struct op (2 of 3 args) — neither builtin_op_fold clause
    # matches (not a full [_tyval,l,r] spine, and the op IS a struct op), so it
    # falls to the arity-mismatch catch-all: :stuck, never a bogus fold.
    {{:app, {:app, {:global, :struct_eq}, @int_type}, {:int_lit, 5}},
     {:app, {:app, {:global, :struct_eq}, @int_type}, {:int_lit, 5}},
     "builtin/arity_stuck: struct_eq Int 5 (unsaturated, 2 of 3 args) stays neutral — never a bogus fold"},
    {@case_missing_branch, @case_missing_branch,
     "ncase/branch_miss (direct): case (idnat (S Z)) {Z->Z} has no S arm — unfold_certified_head freezes it, never crashes"},
    {@donly_term, @donly_term,
     "ncase/branch_miss (unfolded): donly (S Z) unfolds to a case with no S arm — reduce_unfolded freezes it, never crashes"}
  ]

  # Shape-coverage cell per @cases entry, same order (kept parallel so `cases/0`'s
  # 3-tuple shape, which the self-test destructures, stays intact).
  @cells [
    :delta_beta_id,
    :delta_beta_succ,
    :delta_iota_fst,
    :delta_iota_snd,
    :nested_fst,
    :nested_snd_reduce_unfolded,
    :builtin_struct_eq_lit,
    :builtin_struct_ne_lit,
    :builtin_struct_arity_stuck,
    :ncase_branch_miss_direct,
    :ncase_branch_miss_unfolded
  ]

  # Fuel-probe menu: {term, opts, want, expected, note}. `want` is `:ok` (the
  # budget suffices; result must equal `expected`, matching the unbounded/
  # default nf) or `:fuel_exhausted` (the budget is one step short; result must
  # be exactly that atom). `idnat^3 Z` needs exactly 3 δ-unfold steps (one
  # `spend_fuel/1` call per unfold) to reach `Z`.
  @idnat3 {:app, {:global, :idnat}, {:app, {:global, :idnat}, {:app, {:global, :idnat}, @z}}}

  @fuel_cases [
    {@idnat3, [fuel: 3], :ok, @z,
     "fuel/ok: idnat^3 Z completes within its exact 3-δ-step budget (agrees with the unbounded result)"},
    {@idnat3, [fuel: 2], :fuel_exhausted, @z,
     "fuel/exhausted: idnat^3 Z needs 3 δ-steps; a 2-step budget reports :fuel_exhausted, never a truncated wrong value"}
  ]

  @fuel_cells [:fuel_probe_ok, :fuel_probe_exhausted]

  # Opts-rejection menu: {opts, note}. Each is a single malformed key,
  # otherwise-default opts; `normalize_opts/1` must raise `ArgumentError` on
  # every one — ill-typed opts are a validator BUG surface, not a silent
  # fallback. Values are picked from atoms/literals ALREADY interned by
  # `Cure.Core.Normalise`'s own source (a valid :mode value used as :delta and
  # vice versa; 0 and `false` need no interning at all) — no new atoms needed.
  @opts_reject_cases [
    {[delta: :whnf], "opts/reject: :delta must be :certified|:none (rejects a valid :mode atom used as :delta)"},
    {[mode: :certified], "opts/reject: :mode must be :whnf|:nf (rejects a valid :delta atom used as :mode)"},
    {[fuel: 0], "opts/reject: :fuel must be a positive integer or :infinity (0 is rejected)"},
    {[stuck_cases: false],
     "opts/reject: :stuck_cases must be :preserve (any other value is rejected — MatchError, rescued and re-raised)"}
  ]

  @opts_reject_cells [:opts_reject_delta, :opts_reject_mode, :opts_reject_fuel, :opts_reject_stuck_cases]

  @doc """
  Shape-coverage cells for the manifest gate (`Antigen.CoverManifest`) — one per
  δ-reduction/fuel-probe/opts-reject shape; the gate confirms every cell is
  produced by `gen/0`.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells, do: for(cell <- @cells ++ @fuel_cells ++ @opts_reject_cells, do: {"delta/nf", cell})

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.frequency([
      {6, reduces_gen()},
      {2, fuel_probe_gen()},
      {2, opts_reject_gen()}
    ])
  end

  defp reduces_gen do
    Gen.bind(Gen.member_of(Enum.zip(@cases, @cells)), fn {{term, expected, note}, cell} ->
      Gen.return(
        Challenge.new(
          kind: :delta_reduce,
          assay: "delta/nf",
          label: :reduces,
          payload: %{term: term, expected: expected},
          note: note,
          cover_tag: cell
        )
      )
    end)
  end

  defp fuel_probe_gen do
    Gen.bind(Gen.member_of(Enum.zip(@fuel_cases, @fuel_cells)), fn {{term, opts, want, expected, note}, cell} ->
      Gen.return(
        Challenge.new(
          kind: :delta_reduce,
          assay: "delta/nf",
          label: :fuel_probe,
          payload: %{term: term, expected: expected, opts: opts, want: want},
          note: note,
          cover_tag: cell
        )
      )
    end)
  end

  defp opts_reject_gen do
    Gen.bind(Gen.member_of(Enum.zip(@opts_reject_cases, @opts_reject_cells)), fn {{opts, note}, cell} ->
      Gen.return(
        Challenge.new(
          kind: :delta_reduce,
          assay: "delta/nf",
          label: :opts_reject,
          payload: %{opts: opts},
          note: note,
          cover_tag: cell
        )
      )
    end)
  end

  @doc "The literal :reduces case menu (for the generator's coverage self-test)."
  def cases, do: @cases

  @doc "The literal fuel-probe menu (for the generator's coverage self-test)."
  def fuel_cases, do: @fuel_cases

  @doc "The literal opts-rejection menu (for the generator's coverage self-test)."
  def opts_reject_cases, do: @opts_reject_cases
end

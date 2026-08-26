defmodule Antigen.Assays.DeltaReduce do
  @moduledoc """
  `delta/nf` — the known-normal-form oracle for δ-reduction (unfolding of
  certified global definitions), extended with two sibling probes over the SAME
  certified env: fuel-budget accounting and opts-validation robustness. Three
  labels share this one assay (per `Antigen.Generators.DeltaReduce`'s
  moduledoc):

    * `:reduces` — builds the v1 menu extended with three CERTIFIED globals,
      normalizes the challenge term with the trusted `Normalise.nf`, and
      requires the result to equal the correct-by-construction normal form. A
      disagreement is a definitional-equality (δ/ι) soundness infection.
    * `:fuel_probe` — normalizes with an EXPLICIT `opts` (a small `fuel:`
      budget). Sufficient fuel must agree with the unbounded result;
      insufficient fuel must report exactly `:fuel_exhausted` — never a
      truncated, wrong-but-terminating value. Also asserts the fuel counter
      never leaks in the process dictionary past the call (`with_fuel`'s
      `after Process.delete`), reading it back through the public
      `Normalise.fuel_key/0` accessor.
    * `:opts_reject` — a deliberately malformed `opts` keyword list must make
      `Normalise`'s validator raise `ArgumentError`, never silently coerce or
      crash some other way. Routed through `Normalise.whnf_value/3` directly:
      the public `nf/3`/`whnf/3` force their own `:mode` key before opts ever
      reach the validator, so a bad `:mode` value would never actually be
      checked if this went through them.

  Certified env: `idnat : Nat -> Nat = λx. x`, `kpair : Σ Nat. Nat = (Z, S Z)`,
  and `donly : Nat -> Nat = λx. case (idnat x) {Z -> Z}` (a case missing its `S`
  arm — the reduce_unfolded branch-miss-freeze probe). All three are closed and
  total, so `Env.certify` licenses δ-unfolding — the exact precondition
  `unfold_certified_head` guards on (`Env.certified?` + closed body).
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.{Context, Env, Normalise}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  @motive {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}
  # kpair : Sigma(Nat, const-Nat) = mk_pair(Z, S Z) — the inductive dependent pair (D2).
  @kpair_sigma {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}
  # donly's body re-exposes a case stuck on a missing S branch under
  # reduce_unfolded's post-unfold ι follow-through — see the generator moduledoc.
  @donly_body {:lam, Cure.Core.Grade.unrestricted(), @nat,
               {:case, {:app, {:global, :idnat}, {:var, 0}}, @motive, [{:Z, 0, @z}]}}

  # v1 menu + three certified globals (see moduledoc). Declared here, not in the
  # shared SigMenu, because no other vertical needs global definitions.
  defp env do
    Generators.SigMenu.env_of(:v1)
    |> Env.add_def(
      :idnat,
      {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat},
      {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 0}}
    )
    |> Env.certify(:idnat)
    |> Env.add_def(:kpair, @kpair_sigma, {:ctor, :mk_pair, [@z, {:ctor, :S, [@z]}]})
    |> Env.certify(:kpair)
    |> Env.add_def(:donly, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, @donly_body)
    |> Env.certify(:donly)
  end

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :delta_reduce, label: :reduces, payload: %{term: term, expected: expected}}) do
    ctx = Context.empty(env())

    case Normalise.nf(ctx, term) do
      ^expected ->
        :ok

      other ->
        {:violation, {:delta_nf_disagreement, %{term: term, expected: expected, got: other}}}
    end
  end

  def run(%Challenge{
        kind: :delta_reduce,
        label: :fuel_probe,
        payload: %{term: term, expected: expected, opts: opts, want: want}
      }) do
    ctx = Context.empty(env())
    result = Normalise.nf(ctx, term, opts)
    leaked = Process.get(Normalise.fuel_key())

    cond do
      leaked != nil ->
        {:violation, {:fuel_counter_leaked, %{term: term, opts: opts, leaked: leaked}}}

      result == fuel_probe_expect(want, expected) ->
        :ok

      true ->
        {:violation, {:fuel_probe_disagreement, %{term: term, opts: opts, want: want, expected: expected, got: result}}}
    end
  end

  def run(%Challenge{kind: :delta_reduce, label: :opts_reject, payload: %{opts: opts}}) do
    sig = Context.signature(Context.empty(env()))
    # Opts validation runs before any term is touched, so the scrutinee's
    # content is irrelevant — a fixed dummy neutral is enough to reach it via
    # `whnf_value/3`.
    dummy = {:vneutral, {:nglobal, :idnat}}

    try do
      result = Normalise.whnf_value(dummy, sig, opts)
      {:violation, {:malformed_opts_not_rejected, %{opts: opts, got: result}}}
    rescue
      ArgumentError -> :ok
      other -> {:violation, {:wrong_error_kind, %{opts: opts, raised: other}}}
    end
  end

  defp fuel_probe_expect(:ok, expected), do: expected
  defp fuel_probe_expect(:fuel_exhausted, _expected), do: :fuel_exhausted
end

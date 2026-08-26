defmodule Antigen.Assays.StuckElimDelta do
  @moduledoc """
  `stuck-eliminator δ soundness` — the antibody guarding the `Normalise`
  seam that δ-reduces a stuck eliminator's TARGET (`ncase`/`nfst`/`nsnd`) when
  that target is a certified-total global application that unfolds to a
  constructor/pair.

  A `:stuck_elim` challenge carries a certified-total definition group
  (`defs`/`focus`) and a pair of terms `(t, t')` whose reduction exercises that
  seam. The challenge's `label` is the COMMITTED expected verdict:

    * `:positive` — `t` and `t'` are genuinely β/ι/δ-equal (the seam must fire
      and the reduction must complete);
    * `:negative` — `t` and `t'` reduce to DISTINCT normal forms and must NOT be
      equated (the soundness control: a buggy clause that collapses two distinct
      eliminator results would flip this to `{:ok, true}` and be caught here).

  The assay reports `:ok` only when the checker (a) HALTS within the fixed fuel
  budget (never `:fuel_exhausted` for a corpus term — the termination guard) and
  (b) returns the committed expected verdict (the soundness guard). Fuel is a
  fixed committed constant so a banked antibody replays identically everywhere
  (spec §8).
  """
  alias Antigen.Challenge
  alias Cure.Core.{Conv, Env}

  # Fixed δ-unfold budget (spec §8) — identical to the reflexivity assay. A
  # genuinely-normalizing conversion of these terms resolves in a handful of
  # unfolds; this margin only ever trips on non-normalization.
  @fuel 500_000

  # Real kernel op, the byte-identical default for `run/1`.
  @real_kernel %{conv_within: &Conv.conv_within?/6}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :stuck_elim} = c), do: run(c, @real_kernel)

  @doc "Same as `run/1` but with an injectable kernel-op map (sensitivity test seam)."
  def run(%Challenge{kind: :stuck_elim, label: label, payload: %{t: t, tprime: tprime} = p}, k) do
    env = certified_env_of(p)
    expected = label == :positive

    case k.conv_within.(t, tprime, [], 0, env, @fuel) do
      :fuel_exhausted ->
        {:violation, {:non_normalizing, :conv_exceeded_fuel}}

      {:ok, ^expected} ->
        :ok

      {:ok, other} ->
        {:violation, {:unsound_verdict, %{expected: expected, got: other}}}
    end
  end

  # Rebuild the signature from the challenge's definition group and certify each
  # focus member. The members here are crafted to be genuinely total, so we
  # certify them directly: the property under test is that whnf/conv stays sound
  # and terminating GIVEN a certified-total signature — not the certifier itself.
  @spec certified_env_of(map()) :: Env.t()
  defp certified_env_of(%{defs: defs, focus: focus}) do
    env = Enum.reduce(defs, Env.empty(), fn d, e -> Env.add_def(e, d.name, d.type, d.body) end)
    Enum.reduce(focus, env, fn name, e -> Env.certify(e, name) end)
  end
end

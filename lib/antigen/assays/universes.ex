defmodule Antigen.Assays.Universes do
  @moduledoc """
  `universes` (pre-port banking spec §4 W5). Oracle = the known label. Def-shaped
  challenges run `Kernel.check_def`; family-shaped ones run `Kernel.check_family`
  plus `Kernel.check_ctor` per constructor. The kernel must accept iff
  `:well_typed`: an accepted `:ill_typed` (e.g. Type-in-Type) is a soundness
  infection; a rejected `:well_typed` (e.g. cumulativity) is an incompleteness bug.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.{Env, Inductive, Kernel}

  # Real kernel op, the byte-identical default for the `:indexed_case` `run/1`
  # clause (the def-shaped path checked by `Kernel.check_def`).
  @real_kernel %{check_def: &Kernel.check_def/2}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :indexed_case} = c), do: run(c, @real_kernel)

  def run(%Challenge{kind: :family, label: label, payload: %{family: fam, ctors: ctors}}) do
    env = Inductive.declare(base_env(), fam, ctors)

    verdict =
      with :ok <- Kernel.check_family(env, fam) do
        Enum.reduce_while(ctors, :ok, fn ctor, :ok ->
          case Kernel.check_ctor(env, fam, ctor) do
            :ok -> {:cont, :ok}
            {:error, _} = err -> {:halt, err}
          end
        end)
      end

    judge(label, verdict, fam.name)
  end

  @doc "Same as the `:indexed_case` `run/1` clause but with an injectable kernel-op map (sensitivity test seam)."
  def run(%Challenge{kind: :indexed_case, label: label, payload: %{def_name: dn}} = c, k) do
    env = Generators.Universes.env_of(c)
    judge(label, k.check_def.(env, dn), dn)
  end

  defp judge(:well_typed, :ok, _n), do: :ok
  defp judge(:ill_typed, {:error, _}, _n), do: :ok
  defp judge(:well_typed, {:error, reason}, n), do: {:violation, {:wrongly_rejected, {n, reason}}}
  defp judge(:ill_typed, :ok, n), do: {:violation, {:wrongly_accepted, n}}

  # The base env a family-shaped challenge is checked in. Since the 2026-07-18 surface
  # flip retired the primitive `{:vint_type}`, the kernel's compact-literal typing rules
  # (`infer({:int_lit})` → `int_type_value`, `infer({:nat_lit})` → `nat_type_value`) read
  # the `:int`/`:nat` builtins — a challenge carrying an int-literal result index (the
  # `indexed_ctor` probe: `IdxI (n:Int)`, `mki : IdxI 7`) needs them seeded or the kernel
  # raises "builtin :int not seeded". `Antigen.CanonBuiltins` owns that canonical bare-name
  # seed (the SAME shapes the v1 signature menu declares); an empty env can no longer type
  # an integer literal. Extra families are inert to every other probe.
  defp base_env, do: Antigen.CanonBuiltins.seed(Env.empty())
end

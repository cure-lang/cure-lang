defmodule Antigen.CanonBuiltins do
  @moduledoc """
  Canonical bare-name builtin seeder for Antigen kernel envs.

  The 2026-07-18 surface flip retired the primitive `{:vint_type}` node: the
  kernel's compact-literal typing rules now read the `:int`/`:nat` builtins
  (`infer({:int_lit})` → `int_type_value` → `Inductive.builtin(sig, :int)`;
  `infer({:nat_lit})` likewise). An env built from `Env.empty()` plus only a
  challenge's own families can therefore no longer type an integer (or nat)
  literal — the kernel raises `"builtin :int not seeded"`.

  Every bare-env assay/generator that asks the kernel to type a term carrying an
  `{:int_lit, _}` / `{:nat_lit, _}` (a literal-carrying result index, an int-op
  result, a literal-typed ctor field) must seed these first. This module is the
  ONE place that shape lives so it cannot drift from the real seeds.

  The families are BARE-named (`:Nat`, `:Int`, `:Bool`) rather than
  owner-qualified (`Std.Nat#Nat` …) — the Antigen convention its signature menus
  and universes probes already use — but their ctor/field/index shapes
  byte-mirror `Cure.Core.Builtins`' real seeds:

    * `Nat  : Type0 = Z | S(Nat)`                          (S's field is Nat)
    * `Int  : Type0 = FromNat(Nat) | NegativeSuccessor(Nat)` (both fields Nat)
    * `Bool : Type0 = False | True`                        (both nullary)

  Nat is declared before Int because Int's constructor fields reference the Nat
  family. All three are inert to every probe that does not type a literal, so
  routing a probe's env through `seed/2` never perturbs its own families.
  """
  alias Cure.Core.{Env, Inductive}

  @nat {:data, :Nat, [], []}

  @doc """
  Seed the canonical bare-name `Nat` and `Int` builtin families onto `env`
  (Nat first — Int's fields reference it), plus `Bool` when `bool: true`.
  """
  @spec seed(Env.t(), keyword()) :: Env.t()
  def seed(%Env{} = env, opts \\ []) do
    env =
      env
      |> Inductive.declare(
        Inductive.family(:Nat, [], [], 0),
        [Inductive.ctor(:Z, [], []), Inductive.ctor(:S, [{:n, @nat}], [])]
      )
      |> Inductive.register_builtin(:nat, :Nat)
      |> Inductive.declare(
        Inductive.family(:Int, [], [], 0),
        [
          Inductive.ctor(:FromNat, [{:n, @nat}], []),
          Inductive.ctor(:NegativeSuccessor, [{:n, @nat}], [])
        ]
      )
      |> Inductive.register_builtin(:int, :Int)

    if Keyword.get(opts, :bool, false), do: seed_bool(env), else: env
  end

  defp seed_bool(env) do
    env
    |> Inductive.declare(
      Inductive.family(:Bool, [], [], 0),
      [Inductive.ctor(:False, [], []), Inductive.ctor(:True, [], [])]
    )
    |> Inductive.register_builtin(:bool, :Bool)
  end
end

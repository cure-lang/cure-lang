defmodule Cure.Elab.AppliedDefResolutionTest do
  @moduledoc """
  An applied plain DEFINITION in a dependent index (`plus(a, b)` inside `Equivalent(...)`) must
  resolve its head to the EXACT owned registry key. Before this fix, `lower_applied_type_head`'s
  catch-all did `Env.resolve_key(env, env.defs, atom)`, which for an ambiguous bare name
  (`plus` is defined in several stdlib modules) degraded to an unresolvable `{:global, :plus}`
  that never δ-unfolds — so a using-module annotation mentioning it silently failed conversion,
  and even the qualified spelling (resolved only through the `:type` namespace) degraded the
  same way.

  Now: a qualified head resolves through the value namespace to its exact key (and unfolds); a
  bare, uniquely-provided name resolves to its key; a bare name provided by ≥2 modules is a clean
  ambiguity error rather than a downstream conversion failure. Since E11 (type-directed overload
  in index position) the bare ambiguous case is routed through the SAME overload machinery term
  position uses, so it surfaces the precise `:ambiguous_overload` — index and term now agree.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  defp verdict(src) do
    case Program.elaborate(src) do
      {:ok, _} -> :accept
      {:error, e} -> {:error, e}
    end
  end

  test "a QUALIFIED applied def in a type annotation resolves and δ-unfolds" do
    # `Std.Proof.Math.multiply` names a specific (ambiguous-by-base) def; qualified it must land
    # on `Std.Proof.Math#multiply` and reduce `multiply(S(Z), S(Z))` to `S(Z)`.
    src = """
    mod A
      use Std.Proof.Math
      fn h() -> Equivalent(Nat, Std.Proof.Math.multiply(S(Z()), S(Z())), S(Z())) = reflexive(S(Z()))
    end
    """

    assert verdict(src) == :accept
  end

  test "a UNIQUE imported applied def in a type annotation still resolves and unfolds" do
    src = """
    mod B
      use Std.Nat
      fn h() -> Equivalent(Nat, plus(S(Z()), Z()), S(Z())) = reflexive(S(Z()))
    end
    """

    assert verdict(src) == :accept
  end

  test "a BARE ambiguous applied def in a type annotation is a clean :ambiguous_overload error" do
    # `multiply` is defined by ≥2 DIRECTLY imported modules with no unique winner: reject it as
    # ambiguous (the SAME clean error term position gives), not as a silent conversion failure.
    # Post-E11 the index path routes through the overload resolver, so this is the precise
    # `:ambiguous_overload` (identical to term position) rather than the older `:ambiguous_name`.
    src = """
    mod C
      use Std.Proof.Math
      use Std.Proof.IntOrder
      fn h() -> Equivalent(Nat, multiply(S(Z()), S(Z())), S(Z())) = reflexive(S(Z()))
    end
    """

    assert {:error, {:ambiguous_overload, :multiply, _}} = verdict(src)
  end

  test "a directly imported bare applied def resolves to its canonical owner" do
    # Regression lock: `restrict_env_to(env, :all)` used to pass a whole-
    # module provider's OWN `import_modules` through, which made every dependency of a prelude
    # provider (`Std.Equatable`'s `use Std.Nat`, …) count as a DIRECT import of every module.
    # Canonical direct ownership keeps this applied definition reducible.
    src = """
    mod D
      use Std.Proof.Math
      fn h() -> Equivalent(Nat, multiply(S(Z()), S(Z())), S(Z())) = reflexive(S(Z()))
    end
    """

    assert verdict(src) == :accept
  end
end

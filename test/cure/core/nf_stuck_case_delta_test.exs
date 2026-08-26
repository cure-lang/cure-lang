defmodule Cure.Core.NfStuckCaseDeltaTest do
  @moduledoc """
  `nf` must fully normalize a STUCK case, including δ-unfolding certified globals
  that appear inside its motive and branch bodies. Before the fix, `nf_neutral`'s
  `{:ncase, …}` arm returned the motive and branch closures verbatim — so a
  certified global inside a stuck-case motive/branch stayed FOLDED while the same
  global unfolded everywhere else, and `nf` was not a δ-normal form.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Env, Normalise}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  defp s(x), do: {:ctor, :S, [x]}

  # plus a b = case a of Z => b | S k => S (plus k b)   (recursion on 1st arg)
  defp plus_body do
    z_branch = {:Z, 0, {:var, 0}}
    s_branch = {:S, 1, s({:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 1}})}

    {:lam, Cure.Core.Grade.unrestricted(), @nat,
     {:lam, Cure.Core.Grade.unrestricted(), @nat,
      {:case, {:var, 1}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [z_branch, s_branch]}}}
  end

  defp plus_type, do: {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}
  defp plus(a, b), do: {:app, {:app, {:global, :plus}, a}, b}

  defp env do
    Builtins.seed(Env.empty())
    |> Env.add_def(:plus, plus_type(), plus_body())
    |> Env.certify(:plus)
  end

  # A context holding one free Nat variable, so `{:var, 0}` is a STUCK neutral
  # scrutinee — the `case` cannot ι-reduce and stays an `ncase`.
  defp ctx, do: Context.extend(Context.empty(env()), @nat)

  test "nf δ-unfolds a certified global inside a stuck-case branch body" do
    # case x of Z => plus (S Z) Z | S k => Z    — x free ⇒ stuck.
    # The Z-branch body `plus 1 0` must δ/ι-normalize to `S Z`.
    node =
      {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [{:Z, 0, plus(s(@z), @z)}, {:S, 1, @z}]}

    assert {:case, {:var, 0}, _motive, branches} = Normalise.nf(ctx(), node)
    z_body = Enum.find_value(branches, fn {c, _ar, b} -> if c == :Z, do: b end)
    assert z_body == s(@z), "stuck-case Z-branch body must δ-normalize; got #{inspect(z_body)}"
  end

  test "nf δ-unfolds a certified global inside a stuck-case motive" do
    # motive λ(_:Nat). plus (S Z) Z — its body must normalize to `S Z`.
    node =
      {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, plus(s(@z), @z)}, [{:Z, 0, @z}, {:S, 1, @z}]}

    assert {:case, {:var, 0}, {:lam, _g, _dom, motive_body}, _branches} = Normalise.nf(ctx(), node)
    assert motive_body == s(@z), "stuck-case motive body must δ-normalize; got #{inspect(motive_body)}"
  end
end

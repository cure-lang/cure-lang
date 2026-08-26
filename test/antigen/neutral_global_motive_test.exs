defmodule Antigen.NeutralGlobalMotiveTest do
  @moduledoc """
  Companion antibody to `Antigen.NeutralAppMotiveTest`, for the `{:nglobal, _}`
  clause of `infer_type_value_sort`. A `case`/`match` result type that is a bare
  typealias global — motive body `{:vneutral, {:nglobal, g}}`, e.g. `String` in
  `match … -> String` — must be ACCEPTED (the enlarged accept set), while a
  global standing for a VALUE (a non-type) must still be REJECTED with
  `:bad_motive`. Pinned through the REAL kernel: the clause reifies the neutral to
  `{:global, g}` and re-`infer`s it, trusting only the kernel's own judgement, so
  nothing an untrusted elaborator supplies can smuggle a non-type into a motive.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Grade, Kernel}
  alias Cure.Elab.Program

  # A real Nat env, extended with:
  #   AliasNat : Type := Nat   (a typealias — global standing for a TYPE)
  #   valNat   : Nat  := Z     (a global standing for a VALUE, NOT a type)
  defp env do
    {:ok, base} = Program.elaborate("mod P\n  type Nat = Z | S(Nat)\nend\n")
    nat = {:data, :"P#Nat", [], []}

    base
    |> Env.add_def(:AliasNat, {:type, 0}, nat)
    |> Env.certify(:AliasNat)
    |> Env.add_def(:valNat, nat, {:ctor, :"P#Z", []})
    |> Env.certify(:valNat)
  end

  test "accept pin: a motive whose body is a typealias global sorts (no :bad_motive)" do
    ctx = Context.empty(env())
    nat = {:data, :"P#Nat", [], []}
    # motive λ(_ : Nat). AliasNat — body is the neutral global {:nglobal, :AliasNat}.
    # AliasNat δ-unfolds to Nat, so the Z/S branches returning {:ctor, :Z, []} : Nat
    # inhabit the result type; the whole case type-checks.
    motive = {:lam, Grade.unrestricted(), nat, {:global, :AliasNat}}

    kase =
      {:case, {:ctor, :"P#Z", []}, motive, [{:"P#Z", 0, {:ctor, :"P#Z", []}}, {:"P#S", 1, {:ctor, :"P#Z", []}}]}

    assert {:ok, _} = Kernel.infer(ctx, kase)
  end

  test "reject pin: a motive whose body is a VALUE global still fails :bad_motive" do
    ctx = Context.empty(env())
    nat = {:data, :"P#Nat", [], []}
    # motive λ(_ : Nat). valNat — valNat : Nat is a value, not a type. The reify +
    # infer yields Nat (not {:vtype, _}), so the motive is refused.
    motive = {:lam, Grade.unrestricted(), nat, {:global, :valNat}}

    kase =
      {:case, {:ctor, :"P#Z", []}, motive, [{:"P#Z", 0, {:ctor, :"P#Z", []}}, {:"P#S", 1, {:ctor, :"P#Z", []}}]}

    assert {:error, :bad_motive} = Kernel.infer(ctx, kase)
  end
end

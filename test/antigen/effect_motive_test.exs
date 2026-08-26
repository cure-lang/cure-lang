defmodule Antigen.EffectMotiveTest do
  @moduledoc """
  Antibody for the `{:veffect_type, _}` clause of `infer_type_value_sort`, the
  companion to `Antigen.NeutralGlobalMotiveTest`. A `case`/`match` result type that is
  a direct `Effect(T)` — motive body `{:veffect_type, …}`, e.g. the erased effect
  contract of a transparent OTP callback — must be ACCEPTED (the enlarged accept set),
  while an `Effect` head over a NON-type must still be REJECTED with `:bad_motive`.

  The TCB bar for this change has three obligations, one pin each below:

    1. ENLARGED ACCEPT SET is real (accept pin) and BOUNDED (reject pin) — an `Effect`
       head cannot launder a non-type payload into a motive.
    2. NO NEW EQUATIONS. The clause is an acceptance predicate on the SORTER. It adds
       no reduction rule and does not touch `Conv`/`Normalise`, so it cannot equate
       distinct normal forms. Pinned directly: `Effect` stays congruence-only, and
       `Effect(A)` is still not convertible with `A` nor with `Effect(B)` for `A ≠ B`.
    3. TERMINATION. The recursion is structural — it descends strictly into the
       payload value and bottoms out in the pre-existing clauses. Pinned by a nested
       `Effect(Effect(T))` motive, which must sort (and preserve the level) rather than
       diverge.

  All pins run through the REAL kernel over a REAL elaborated environment.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Grade, Kernel}
  alias Cure.Elab.Program

  @nat {:data, :"P#Nat", [], []}
  @bool {:data, :"P#Bool2", [], []}

  # A real elaborated env (Nat, Bool2), extended with:
  #   valNat : Nat := Z    (a global standing for a VALUE, NOT a type)
  defp env do
    {:ok, base} =
      Program.elaborate("mod P\n  type Nat = Z | S(Nat)\n  type Bool2 = T2 | F2\nend\n")

    base
    |> Env.add_def(:valNat, @nat, {:ctor, :"P#Z", []})
    |> Env.certify(:valNat)
  end

  defp case_on_nat(motive_body) do
    motive = {:lam, Grade.unrestricted(), @nat, motive_body}

    {:case, {:ctor, :"P#Z", []}, motive,
     [
       {:"P#Z", 0, {:effect_pure, {:ctor, :"P#Z", []}}},
       {:"P#S", 1, {:effect_pure, {:ctor, :"P#Z", []}}}
     ]}
  end

  # (1) ACCEPT PIN — the whole point of the clause.
  test "accept pin: a motive whose body is Effect(T) sorts (no :bad_motive)" do
    assert {:ok, _} = Kernel.infer(Context.empty(env()), case_on_nat({:effect_type, @nat}))
  end

  # (1) REJECT PIN — the accept set is bounded. `Effect(valNat)` is not a type, because
  # `valNat` is a value. The payload recursion reifies + infers it, gets `Nat` rather
  # than `{:vtype, _}`, and refuses the motive. Nothing an untrusted elaborator supplies
  # can smuggle a non-type into a motive behind an `Effect` head.
  test "reject pin: a motive whose body is Effect(<value global>) still fails :bad_motive" do
    body = {:effect_type, {:global, :valNat}}

    assert {:error, :bad_motive} = Kernel.infer(Context.empty(env()), case_on_nat(body))
  end

  # (3) TERMINATION PIN — structural descent, so a nested head cannot diverge. Level is
  # preserved at every layer (`Effect : Type ℓ → Type ℓ`), so `Effect(Effect(Nat))`
  # sorts exactly where `Nat` does.
  test "termination pin: a nested Effect(Effect(T)) motive body sorts" do
    body = {:effect_type, {:effect_type, @nat}}

    kase =
      {:case, {:ctor, :"P#Z", []}, {:lam, Grade.unrestricted(), @nat, body},
       [
         {:"P#Z", 0, {:effect_pure, {:effect_pure, {:ctor, :"P#Z", []}}}},
         {:"P#S", 1, {:effect_pure, {:effect_pure, {:ctor, :"P#Z", []}}}}
       ]}

    assert {:ok, _} = Kernel.infer(Context.empty(env()), kase)
  end

  # (2) NO-NEW-EQUATIONS PIN. The sorter clause must not have made `Effect` transparent.
  # `Effect` remains an INERT former compared by structural congruence only: reflexive
  # on itself, and distinct from both its own payload and a differently-payloaded
  # sibling. If a future "fix" ever δ-unfolds or erases `Effect` to make motives sort,
  # these go red — which is the intended alarm.
  test "no-new-equations pin: Effect stays congruence-only and equates nothing new" do
    e = env()
    sig = Context.signature(Context.empty(e))

    assert Conv.conv?({:effect_type, @nat}, {:effect_type, @nat}, e, 0, sig),
           "Effect(Nat) must be convertible with itself"

    refute Conv.conv?({:effect_type, @nat}, @nat, e, 0, sig),
           "Effect(Nat) must NOT be convertible with its payload Nat"

    refute Conv.conv?({:effect_type, @nat}, {:effect_type, @bool}, e, 0, sig),
           "Effect(Nat) must NOT be convertible with Effect(Bool2)"
  end
end

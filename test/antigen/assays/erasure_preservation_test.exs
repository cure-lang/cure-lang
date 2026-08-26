defmodule Antigen.Assays.ErasurePreservationTest do
  use ExUnit.Case, async: false
  alias Antigen.Assays.Term, as: TermAssay
  alias Antigen.Challenge

  defp ch(term, type) do
    Challenge.new(
      kind: :typed_term,
      assay: "term/erasure_preservation",
      label: :positive,
      payload: %{term: term, type: type, ctx: [], sig: :v1},
      seed: 1
    )
  end

  # n is a CLOSED beta-redex ((λy:Nat.y) Z), not a bare Z literal — Eval.eval
  # (used by Kernel.check_ctor_app_rec to compute xs's expected index type)
  # fully reduces it via NbE, so the term is well-typed (xs=vnil : Vec(Z)
  # matches Vec(n_redex_value) = Vec(Z)) even though `n` is syntactically
  # unreduced. This is essential: it's what makes the witness term exercise
  # `nf`'s actual reduction machinery instead of being a no-op no-redex value.
  defp n_redex, do: {:app, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:var, 0}}, {:ctor, :Z, []}}
  defp t, do: {:ctor, :vcons, [n_redex(), {:ctor, :S, [{:ctor, :Z, []}]}, {:ctor, :vnil, []}]}
  defp ty, do: {:data, :Vec, [], [{:ctor, :S, [{:ctor, :Z, []}]}]}

  test "real erase preserves nf on a vcons term with a genuine redex on the erased n slot" do
    assert TermAssay.run(ch(t(), ty())) == :ok
  end

  test "negative control: a shape-sniffing (not position-fixed) erase stub infects" do
    # Drops the FIRST argument that is ALREADY a literal Z-shaped ctor, rather
    # than consulting the ctor's static quantity vector. Pre-normalization, `n`
    # is an unreduced :app (not Z-shaped) so this stub drops NOTHING; post-
    # normalization `n` has reduced to a literal Z and IS dropped — the two
    # branches diverge (nf(erase(t)) keeps 3 args, erase(nf(t)) keeps 2 —
    # different arities, so no reduction-independence coincidence is possible).
    bad_erase = fn
      _env, {:ctor, c, args} ->
        case Enum.find_index(args, &match?({:ctor, :Z, []}, &1)) do
          nil -> {:ctor, c, args}
          i -> {:ctor, c, List.delete_at(args, i)}
        end

      _env, other ->
        other
    end

    k = %{TermAssay.__real__() | erase: bad_erase}
    assert {:violation, {:erasure_not_preserved, _}} = TermAssay.run(ch(t(), ty()), k)
  end
end

defmodule Cure.Core.MotiveWfIndexedDomainTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}

  # Completeness gap in `check_motive_wf` / `infer_type_value_sort`: a motive body
  # that is a Π whose DOMAIN is an INDEXED family (the convoy encoding of `with`
  # sibling refinement, e.g. `λs. Π(SNat s). Dec`) used to be re-inferred by
  # reifying the Π value and calling `infer_sort`. `Quote.reify` collapses
  # `{:vdata, name, args}` → `{:data, name, args, []}` (all args in the *params*
  # slot — it has no inductive signature to recover the param/index split), so an
  # indexed family in the domain re-inferred with an arity error (`:arg_arity`) and
  # the whole motive was wrongly rejected as `:bad_motive`. This is a completeness
  # gap (false negative), NOT unsoundness.
  #
  # The fix recurses on the Π/Σ/Eq *values* directly (mirroring `infer/2`'s
  # type-formation rules) instead of reifying, so the `{:vdata,…}` domain is
  # classified by its family's declared level with no lossy round-trip. Acceptance
  # must be identical to what a NON-lossy reify+infer would have decided: it must
  # still REJECT a Π whose domain is genuinely not a type (negative control).

  @dec {:data, :Dec, [], []}

  # Dec: two nullary ctors. SNat(d:Dec): an INDEXED family (one Dec index) — this is
  # the family that appears as the Π *domain* inside the motive.
  defp base_env do
    Env.empty()
    |> Inductive.declare(
      Inductive.family(:Dec, [], [], 0),
      [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
    )
    |> Inductive.declare(
      Inductive.family(:SNat, [], [{:d, @dec}], 0),
      [Inductive.ctor(:snat0, [], [{:ctor, :Dcoupled, []}])]
    )
  end

  # SNat(s) with s = the motive/def binder (de Bruijn var0).
  @snat_s {:data, :SNat, [], [{:var, 0}]}

  # POSITIVE: motive `λs. Π(SNat s). Dec` — indexed family as a Π domain. Was
  # rejected (`:bad_motive`) by the reify path; must be accepted by value-recursion.
  test "an indexed family as a Π-domain motive is well-formed (was :bad_motive)" do
    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:pi, Cure.Core.Grade.unrestricted(), @snat_s, @dec}}
    def_type = {:pi, Cure.Core.Grade.unrestricted(), @dec, {:pi, Cure.Core.Grade.unrestricted(), @snat_s, @dec}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:case, {:var, 0}, motive,
        [
          {:Dcoupled, 0,
           {:lam, Cure.Core.Grade.unrestricted(), {:data, :SNat, [], [{:ctor, :Dcoupled, []}]}, {:ctor, :Dcoupled, []}}},
          {:Causal, 0,
           {:lam, Cure.Core.Grade.unrestricted(), {:data, :SNat, [], [{:ctor, :Causal, []}]}, {:ctor, :Dcoupled, []}}}
        ]}}

    env = Env.add_def(base_env(), :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # NEGATIVE CONTROL: motive `λs. Π(Dcoupled). Dec` — the Π domain is a *value*
  # (a Dec constructor), NOT a type. The value-recursion must still reject it, so
  # the fix removes false negatives WITHOUT introducing false positives. This is
  # rejected both before and after the fix; it proves the new path is a real sort
  # check, not a blanket accept.
  test "a Π-domain motive whose domain is not a type is still rejected (:bad_motive)" do
    neg_motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec, {:pi, Cure.Core.Grade.unrestricted(), {:ctor, :Dcoupled, []}, @dec}}

    def_type = {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:case, {:var, 0}, neg_motive, [{:Dcoupled, 0, {:type, 0}}, {:Causal, 0, {:type, 0}}]}}

    env = Env.add_def(base_env(), :probe, def_type, body)
    assert {:error, :bad_motive} = Kernel.check_def(env, :probe)
  end
end

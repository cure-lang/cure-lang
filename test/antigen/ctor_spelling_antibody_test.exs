defmodule Antigen.CtorSpellingAntibodyTest do
  @moduledoc """
  TCB antibody — fields-only is the canonical constructor-value spelling
  (ledger #28). The K6 params-on-spine ctor TERM (inference-only) must not
  cause a de Bruijn misalignment if it reaches the ι-rule (A1), and Conv must
  equate the two spellings of one ctor value under a shared type (A2).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Conv, Eval}
  alias Cure.Elab.Program

  defp base_sig do
    {:ok, sig} = Program.elaborate("mod M\nend\n")
    sig
  end

  @nat {:data, :Nat, [], []}
  defp z, do: {:ctor, :Z, []}

  # A1 — reflexive has ONE field (w); Equivalent has ONE param (a). The K6
  # params-on-spine term {:ctor, :reflexive, [ty, w]} infers OK and evals to a
  # 2-arg vctor. Under a case whose reflexive branch (arity 1) body references
  # the branch-EXTERNAL binder ({:var,1} past the single field binder), a
  # correct fields-only ι binds [w] and {:var,1} resolves to the outer env slot;
  # WITHOUT A1 the 2-arg spine binds [w, ty] and {:var,1} wrongly resolves to ty.
  test "A4.i: ι over a params-on-spine ctor term matches the fields-only result" do
    # a distinct outer binder value in the eval env
    env = [{:vint, 42}]
    # K6 params-on-spine
    scrut = {:ctor, :reflexive, [@nat, z()]}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), @nat,
        {:lam, Cure.Core.Grade.unrestricted(), {:data, :Equivalent, [@nat], [{:var, 1}, {:var, 0}]}, @nat}}}

    # branch-external reference
    body = {:var, 1}
    node = {:case, scrut, motive, [{:reflexive, 1, body}]}
    # Expected: the outer binder (42), NOT the coerced-away param (@nat value).
    assert Eval.eval(node, env) == {:vint, 42}
  end

  # A2 — Conv equates the fields-only and params-on-spine spellings of the SAME
  # reflexive value at a shared Equivalent type.
  test "A4.ii: Conv equates the two spellings of one ctor value" do
    sig = base_sig()
    fields_only = Eval.eval({:ctor, :reflexive, [z()]}, Context.env(Context.empty(sig)))
    spine = Eval.eval({:ctor, :reflexive, [@nat, z()]}, Context.env(Context.empty(sig)))
    assert Conv.conv_values?(fields_only, spine, 0, sig)
  end

  # A4.iii — the SAME de Bruijn-misalignment repro as A4.i, but entered via
  # `Normalise.nf` instead of a raw `Eval.eval` call. IMPORTANT (verified by
  # hand-trace, 2026-07-09 review): `Eval.eval({:case,...}, env)` resolves a
  # concrete (non-neutral) scrutinee's ι-reduction DIRECTLY inside `eval.ex`'s
  # own `:case` clause (eval.ex:55-61) — `Normalise.nf`'s `eval_in` calls
  # `Eval.eval` on the WHOLE node in one pass, so for a scrutinee that is a
  # closed ctor literal (as here), `Normalise.nf`'s OWN `:ncase` sites
  # (normalise.ex:235-246, :269-288) are NEVER reached — those only fire when
  # `Eval.eval` first leaves a genuinely NEUTRAL `{:vneutral,{:ncase,...}}`
  # (e.g. an unresolved global/free-var scrutinee), which requires machinery
  # (a certified global) disproportionate for this antibody. A4.iii therefore
  # does NOT independently exercise normalise.ex's two ι sites — it re-drives
  # the SAME eval.ex site as A4.i, through the `Normalise.nf` entry point, and
  # is only a meaningful (non-vacuous) regression check if its branch body
  # actually references the branch-external binder (a literal-only body like
  # `z()` is insensitive to the extra param and would be GREEN unconditionally,
  # before and after A1 — not a valid antibody). Coverage of normalise.ex's own
  # two `:ncase` sites is instead achieved STRUCTURALLY: Step 1.3 below MANDATES
  # that both sites call the exact SAME exported helper A1 introduces in
  # eval.ex, so a bug in the shared algorithm is caught by A4.i regardless of
  # which call site would eventually execute it (no untested duplicate).
  test "A4.iii: nf of the params-on-spine case, entered via Normalise.nf, agrees with fields-only" do
    sig = base_sig()
    # Context.extend/2 wants a VALUE, not a term — {:vdata, :Nat, []}, not @nat.
    # one outer binder
    ctx = Context.extend(Context.empty(sig), {:vdata, :Nat, []})

    node =
      {:case, {:ctor, :reflexive, [@nat, z()]},
       {:lam, Cure.Core.Grade.unrestricted(), @nat,
        {:lam, Cure.Core.Grade.unrestricted(), @nat,
         {:lam, Cure.Core.Grade.unrestricted(), {:data, :Equivalent, [@nat], [{:var, 1}, {:var, 0}]}, @nat}}},
       [{:reflexive, 1, {:var, 1}}]}

    # WITHOUT A1: the 2-arg spine binds [w, ty] ahead of the outer binder, so
    # {:var,1} wrongly resolves to `ty` (a Nat data value), not the outer var.
    # WITH A1: fields-only binds [w] only, so {:var,1} resolves to the outer
    # context variable, which reifies back to itself ({:var,0} at depth 1).
    assert Cure.Core.Normalise.nf(ctx, node) == {:var, 0}
  end
end

defmodule Antigen.CycleRuleAntibodyTest do
  @moduledoc """
  TCB antibody — the Agda Cycle-rule discharge in the kernel index unifier
  (`Cure.Core.Kernel.unify_indices`/`bind_index`/`strongly_rigid_occurs?`) stays
  SOUND and TERMINATING.

  Guards the change that lets a strongly-rigid cyclic index equation `x =?= v`
  (where the datatype variable `x` occurs under constructor/data spines ONLY in
  `v`) discharge the branch as `:impossible`, mirroring Agda's Cycle rule
  (Rules/LHS/Unify.hs `ifOccursStronglyRigid` → `NoUnify`). Fixes oracle cyc01.

  The load-bearing soundness property is **NO REACHABLE-BRANCH DISCHARGE**: the
  kernel may only answer `:impossible` when the branch's index equation genuinely
  has no solution. This antibody pins it with an INDEPENDENT reachability oracle
  that never consults kernel internals: for the family `same : SameLen(k, k)`
  matched against `SameLen(a, t[a])`, the induced equation is `a = t[a]`, which is
  reachable iff some closed `Nat` value `v` makes `v ≡ t[v]` convertible. The
  antibody searches for such a witness (`Cure.Core.Conv.conv_within?`) and asserts:

    * SOUNDNESS — if a witness EXISTS (reachable), the verdict is NEVER
      `:impossible`. This is the property whose violation would be unsound.
    * COMPLETENESS-WITH-JUSTIFICATION — if NO witness exists up to a generous
      depth (a strongly-rigid cycle `a = Sᵏ(a)`, k ≥ 1), the verdict IS
      `:impossible` — and the absence of a witness independently justifies it.
    * TERMINATION — the strengthened unifier returns (never loops) on
      strongly-rigid cycles at every S-depth 1..8, under a bounded Task harness.
    * GUARD CONSERVATISM — an occurrence under a NON-constructor (neutral `:app`)
      head is not strongly rigid, so it is NEVER discharged `:impossible`.

  If any construction violates SOUNDNESS (a reachable branch discharged), the port
  is unsound: STOP — do not weaken the assertion.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Kernel, Context, Conv, Env, Eval, Inductive}
  alias Cure.Elab.Program

  # `SameLen`/`same` are declared inside `mod M`, so they elaborate to the
  # owner-qualified identities `M#SameLen`/`M#same`. `branch_unify` resolves a
  # bare family name but NOT a bare constructor name, so a bare `:same` finds no
  # ctor and every branch degrades to a uniform `:impossible` — which would both
  # violate the soundness pin (reachable branch wrongly discharged) and let the
  # termination pin pass for the wrong reason. Name them canonically.
  defp q(owner, name), do: Cure.Elab.Name.qualify(owner, name)

  @fuel 1000
  @search_depth 12

  # same : SameLen(k, k) — arity 1; matching against SameLen(a, t) forces a = t.
  defp samelen_sig,
    do:
      (fn ->
         {:ok, s} =
           Program.elaborate(
             "mod M\n  type Nat = Z | S(Nat)\n  type SameLen indices (n: Nat, m: Nat)\n    same : SameLen(k, k)\nend\n"
           )

         s
       end).()

  defp one_var_ctx(s), do: Context.extend(Context.empty(s), {:vdata, :Nat, []})
  defp a_lvl, do: {:vneutral, {:nvar, 0}}

  # ---- independent reachability oracle (no kernel internals) -----------------

  # Closed Nat term literals 0..d.
  defp nat_lit(0), do: {:ctor, :Z, []}
  defp nat_lit(n), do: {:ctor, :S, [nat_lit(n - 1)]}
  defp nats_upto(d), do: Enum.map(0..d, &nat_lit/1)

  # Substitute a CLOSED term `v` for the single outer var (de Bruijn 0) in a term
  # written over that one var. No shifting needed: `v` is closed and there is no
  # other free var in these one-var index terms.
  defp subst_var0({:var, 0}, v), do: v
  defp subst_var0({:var, k}, _v), do: {:var, k}

  defp subst_var0(t, v) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&subst_var0(&1, v)) |> List.to_tuple()

  defp subst_var0(l, v) when is_list(l), do: Enum.map(l, &subst_var0(&1, v))
  defp subst_var0(x, _v), do: x

  # Is `a = term_over_a` solvable? Search closed Nat witnesses v with v ≡ term[v].
  defp reachable?(term_over_a, sig) do
    Enum.any?(nats_upto(@search_depth), fn v ->
      match?({:ok, true}, Conv.conv_within?(v, subst_var0(term_over_a, v), [], 0, sig, @fuel))
    end)
  end

  # Scenarios: {label, second-index VALUE over a, second-index TERM over var 0}.
  # The kernel is driven with the VALUE; the oracle reasons over the TERM.
  defp scenarios do
    [
      {"a (identity, reachable)", a_lvl(), {:var, 0}},
      {"Z (reachable a:=Z)", {:vctor, :Z, []}, {:ctor, :Z, []}},
      {"S(a) (cycle)", {:vctor, :S, [a_lvl()]}, {:ctor, :S, [{:var, 0}]}},
      {"S(S(a)) (nested cycle)", {:vctor, :S, [{:vctor, :S, [a_lvl()]}]}, {:ctor, :S, [{:ctor, :S, [{:var, 0}]}]}},
      {"S(S(S(a))) (deep cycle)", {:vctor, :S, [{:vctor, :S, [{:vctor, :S, [a_lvl()]}]}]},
       {:ctor, :S, [{:ctor, :S, [{:ctor, :S, [{:var, 0}]}]}]}}
    ]
  end

  # ---- SOUNDNESS + completeness-with-justification ---------------------------

  test "discharge is :impossible IFF the induced equation is genuinely unreachable" do
    s = samelen_sig()
    ctx = one_var_ctx(s)

    for {label, value, term} <- scenarios() do
      verdict = Kernel.branch_unify(ctx, q("M", :SameLen), q("M", :same), [a_lvl(), value])
      reachable = reachable?(term, s)

      if reachable do
        refute verdict == :impossible,
               "SOUNDNESS VIOLATION: reachable branch #{label} discharged :impossible"
      else
        assert verdict == :impossible,
               "expected :impossible for unreachable cyclic branch #{label}, got #{inspect(verdict)}"
      end
    end
  end

  # ---- TERMINATION -----------------------------------------------------------

  test "strongly-rigid cycle a = Sᵏ(a) returns :impossible (no loop) for k = 1..8" do
    s = samelen_sig()
    ctx = one_var_ctx(s)

    for k <- 1..8 do
      value = Enum.reduce(1..k, a_lvl(), fn _, acc -> {:vctor, :S, [acc]} end)
      task = Task.async(fn -> Kernel.branch_unify(ctx, q("M", :SameLen), q("M", :same), [a_lvl(), value]) end)
      result = Task.yield(task, 5_000) || Task.shutdown(task)

      assert {:ok, :impossible} = result,
             "branch_unify did not return :impossible within budget at S-depth #{k}: #{inspect(result)}"
    end
  end

  # ---- GUARD CONSERVATISM ----------------------------------------------------

  test "occurrence under a NEUTRAL app head is not strongly rigid ⇒ never :impossible" do
    # Adversarial signature: a ctor whose result index wraps the dangling outer
    # var under a neutral application `(x x)`, NOT a constructor. The Cycle rule
    # must NOT discharge it.
    wr = {:data, :Wr, [], []}

    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Wr, [], [], 0), [Inductive.ctor(:MkWr, [], [])])
      |> Inductive.declare(Inductive.family(:IA, [], [{:w, wr}], 0), [
        Inductive.ctor(:ia, [], [{:app, {:var, 1}, [{:var, 1}]}])
      ])

    ctx = Context.empty(env) |> Context.extend(Eval.eval(wr, []))
    refute :impossible == Kernel.branch_unify(ctx, :IA, :ia, [{:vneutral, {:nvar, 0}}])
  end
end

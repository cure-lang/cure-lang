defmodule Antigen.Assays.BranchUnify do
  @moduledoc """
  `branchunify/verdict` — the known-label oracle for the kernel's index-refinement
  unifier. Builds a v1-menu context with `ctx_vars` outer `Nat` variables, evaluates
  the scrutinee index terms (and family parameter terms) to values, and asks
  `Cure.Core.Kernel.branch_unify/5` to refine; the returned verdict category (`:trivial` | `:solved` | `:impossible`)
  must match the correct-by-construction label. A disagreement is an
  index-unification soundness/completeness infection.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.{Context, Eval, Inductive, Kernel}

  @nat_type {:vdata, :Nat, []}
  @bd_type {:vdata, :Bd, []}
  @nat {:data, :Nat, [], []}
  @bd {:data, :Bd, [], []}
  @z {:ctor, :Z, []}
  @s1 {:ctor, :S, [@z]}

  # v1 menu extended with a crossing 4-index family `Cyc4` whose constructor
  # `mkcyc : (a b : Nat) -> Cyc4 a a b b` induces a multi-key unification cycle
  # (`i := j`, later `j := i`) when matched against a crossing scrutinee
  # `Cyc4 i j j i` — the spec §4.1 resolve-before-bind obligation. Not in the shared
  # v1 menu (no other generator needs it), so it is declared here.
  #
  # Also extended with the PARAMETERISED GADT `Foo (a : Nat) : Nat -> Type0` whose
  # constructor `MkFoo : Foo a (S a)` buries the family parameter `a` inside a
  # result-index constructor spine. Matching `MkFoo` against a scrutinee with a free
  # index MUST be `:solved` (i := S a) — but the parameter var, living at de Bruijn
  # `>= arity`, collides with a shifted scrutinee index var, so the pre-fix unifier
  # mistook it for a cyclic self-occurrence and verdicted `:impossible` (finding S9).
  # `branch_unify/5` with the scrutinee's actual param VALUES is required to exercise
  # this; the paramless `branch_unify/4` never reaches it.
  #
  # Dependent-matching TAILS extension (coverage-plateau follow-up):
  #   - `Cyc1 (a:Nat) : Nat -> Type0`, `idcyc : Cyc1 a a` — the parameter buries
  #     directly into the ONE index; matched with the scrutinee's actual param VALUE
  #     equal to the shifted scrutinee index var itself, this is the textbook
  #     occurs-check equation `x =?= S x` (var_cycle?/strongly_rigid_occurs?).
  #   - `Cyc4b`, `mkcyc2 : (a d:Nat) -> Cyc4b a d a d` — the SAME crossing scrutinee
  #     as Cyc4 but with the repeated ctor-vars INTERLEAVED, forcing bind_index's
  #     union-find chase to land a later constraint on a key whose representative is
  #     already equal to the incoming term (the `rterm == {:var, key}` no-op, not
  #     Cyc4's "old==rterm consistent" arm).
  #   - `Nl : Nat -> Type0` with ctors `nlc : Nl {nat_lit 2}` and `nlt : Nl (S Z)` —
  #     drives every arm of unify_one's compact-Nat-literal <-> ctor-tower bridge
  #     (literal==literal, literal-vs-ctor peel, ctor-vs-literal peel).
  #   - `CaseIdx : Nat -> Type0`, `mkci (b:Bd) : CaseIdx (case b {T=>Z;F=>S Z})` — a
  #     result index that is itself a `:case` term, so `subst_params` must recurse
  #     into scrutinee/motive/branches (960/961), not just :data/:ctor/:pi/:lam/:app.
  #   - `SpineU : Nat -> Type0`, `spu (k:Nat) : SpineU (S (plus k k))` — a result
  #     index headed by a stuck application spine; `unify_spine`'s element-wise
  #     match against a ctor-headed scrutinee element leaves that pair `:undecided`,
  #     which unify_spine drops (keeps solving) rather than failing (kernel.ex:1047).
  #   - `Dboth : Nat -> Type0`, `mkboth : Dboth (Vec[Z][S Z])` — a result index that
  #     is itself a nested `:data` term with BOTH a non-empty params list and a
  #     non-empty indices list, so `subst_params`'s `:data` clause maps over both
  #     (952/953), not just one.
  defp env do
    Generators.SigMenu.env_of(:v1)
    |> Inductive.declare(
      Inductive.family(:Cyc4, [], [{:i, @nat}, {:j, @nat}, {:k, @nat}, {:l, @nat}], 0),
      [Inductive.ctor(:mkcyc, [{:a, @nat}, {:b, @nat}], [{:var, 1}, {:var, 1}, {:var, 0}, {:var, 0}])]
    )
    |> Inductive.declare(
      Inductive.family(:Foo, [{:a, @nat}], [{:i, @nat}], 0),
      [Inductive.ctor(:MkFoo, [], [{:ctor, :S, [{:var, 0}]}])]
    )
    |> Inductive.declare(
      Inductive.family(:Cyc1, [{:a, @nat}], [{:i, @nat}], 0),
      [Inductive.ctor(:idcyc, [], [{:var, 0}])]
    )
    |> Inductive.declare(
      Inductive.family(:Cyc4b, [], [{:i, @nat}, {:j, @nat}, {:k, @nat}, {:l, @nat}], 0),
      [Inductive.ctor(:mkcyc2, [{:a, @nat}, {:d, @nat}], [{:var, 1}, {:var, 0}, {:var, 1}, {:var, 0}])]
    )
    |> Inductive.declare(
      Inductive.family(:Nl, [], [{:i, @nat}], 0),
      [
        Inductive.ctor(:nlc, [], [{:nat_lit, 2}]),
        Inductive.ctor(:nlt, [], [@s1])
      ]
    )
    |> Inductive.declare(
      Inductive.family(:CaseIdx, [], [{:i, @nat}], 0),
      [
        Inductive.ctor(:mkci, [{:b, @bd}], [
          {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @bd, @nat}, [{:T, 0, @z}, {:F, 0, @s1}]}
        ])
      ]
    )
    |> Inductive.declare(
      Inductive.family(:SpineU, [], [{:i, @nat}], 0),
      [
        Inductive.ctor(:spu, [{:k, @nat}], [
          {:ctor, :S, [{:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 0}}]}
        ])
      ]
    )
    |> Inductive.declare(
      Inductive.family(:Dboth, [], [{:i, @nat}], 0),
      [Inductive.ctor(:mkboth, [], [{:data, :Vec, [@z], [@s1]}])]
    )
  end

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :branch_unify, label: expected, payload: %{motive_probe: shape}}) do
    got = motive_probe_result(shape)

    if got == expected do
      :ok
    else
      {:violation, {:motive_probe_disagreement, %{shape: shape, expected: expected, got: got}}}
    end
  end

  def run(%Challenge{kind: :branch_unify, label: expected, payload: p}) do
    env = env()

    ctx =
      Enum.reduce(1..p.ctx_vars//1, Context.empty(env), fn _, c ->
        Context.extend(c, @nat_type)
      end)

    index_vals = Enum.map(p.indices, &Eval.eval(&1, Context.env(ctx)))
    param_vals = Enum.map(Map.get(p, :params, []), &Eval.eval(&1, Context.env(ctx)))

    category =
      case Kernel.branch_unify(ctx, p.dname, p.cname, index_vals, param_vals) do
        {:solved, _} -> :solved
        other -> other
      end

    if category == expected do
      :ok
    else
      {:violation, {:branch_unify_disagreement, %{payload: p, expected: expected, got: category}}}
    end
  end

  # Drives `Kernel.infer`'s `:case` clause directly (hence `apply_motive_checked`,
  # kernel.ex 630-638) with a deliberately ill-formed motive over the v1 menu's
  # non-indexed `Bd` family (siblings T/F, already whitelisted). Both shapes are
  # sound-by-construction `:bad_motive` cases: a non-Pi neutral variable can never
  # check as a case motive, and a concrete non-function value cannot be applied at
  # all — `apply_motive_checked`'s own doc comment names exactly these two halts.
  defp motive_probe_result(:neutral) do
    ctx =
      Context.empty(env())
      |> Context.extend(@bd_type)
      |> Context.extend(@bd_type)

    case Kernel.infer(ctx, {:case, {:var, 0}, {:var, 1}, []}) do
      {:error, :bad_motive} -> :bad_motive
      other -> other
    end
  end

  defp motive_probe_result(:nonfun) do
    ctx = Context.extend(Context.empty(env()), @bd_type)

    case Kernel.infer(ctx, {:case, {:var, 0}, @nat, []}) do
      {:error, :bad_motive} -> :bad_motive
      other -> other
    end
  end
end

defmodule Antigen.Generators.BranchUnify do
  @moduledoc """
  Known-label generator for the `branchunify/verdict` vertical
  (`Antigen.Assays.BranchUnify`): direct calls to the public
  `Cure.Core.Kernel.branch_unify/4` (the elaborator's index-refinement delegation)
  over the v1 menu's indexed families, with a correct-by-construction verdict
  (`:trivial` | `:solved` | `:impossible`).

  This drives the kernel's first-order index unifier past what a well-typed `case`
  reaches on its own: every `unify_one` arm, `bind_index` (fresh solve, consistent
  re-bind, and same-key merge conflict), `unify_spine`, `rigid_index?`
  (constructor / data / **`Type`** / int-literal heads), `head_key`, and forced
  equations between two outer index variables — each with a fixed verdict the assay
  checks against the live kernel.

  Also reaches the dependent-matching TAILS the head-only cases above never touch
  (coverage-plateau follow-up): the occurs-check (`var_cycle?`/`strongly_rigid_occurs?`),
  the compact-Nat-literal ↔ ctor-tower bridge in `unify_one` (both peel directions and
  the literal==literal fast path), `unify_spine`'s `:undecided`-drop arm, the
  multi-key union-find self-loop no-op in `bind_index`, and `subst_params`'s `:data`/
  `:case` recursion arms (a result index that is itself a nested `:data`- or
  `:case`-headed term). `@motive_cases` separately drives `apply_motive_checked`'s two
  bad-motive halts (a non-function motive, and a motive that never becomes a function)
  through `Kernel.infer`'s `:case` clause directly — those don't fit the
  `branch_unify/4,5` call shape, so they carry a distinct `%{motive_probe: shape}`
  payload dispatched by a separate assay clause.
  """
  alias Antigen.{Gen, Challenge}

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`): the three paramless verdict
  classes, the two parameterised-GADT verdict classes, and `:bad_motive` (the
  `@motive_cases` vertical).
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for cell <- [:trivial, :solved, :impossible, :param_solved, :param_impossible, :bad_motive],
        do: {"branchunify/verdict", cell}
  end

  # The coverage cell for a case: paramless cases are named by their verdict; the
  # parameterised-GADT cases (finding S9) get a distinct `:param_*` cell so the gate
  # sees the branch_unify/5 param path as its own coverage obligation.
  defp cover_cell([], verdict), do: verdict
  defp cover_cell(_params, :solved), do: :param_solved
  defp cover_cell(_params, :impossible), do: :param_impossible
  defp cover_cell(_params, verdict), do: verdict

  # {ctx_vars, dname, cname, index_terms, verdict, note}
  @cases [
    {0, :Vec, :vnil, [{:ctor, :Z, []}], :trivial, "Vec vnil [Z] — syntactic match"},
    {0, :Vec, :vnil, [{:ctor, :S, [{:ctor, :Z, []}]}], :impossible, "Vec vnil [S Z] — rigid Z/S clash"},
    {0, :Vec, :vcons, [{:ctor, :S, [{:ctor, :Z, []}]}], :solved, "Vec vcons [S Z] — bind ctor arg"},
    {1, :Vec, :vcons, [{:var, 0}], :solved, "Vec vcons [outer var] — bind outer index var"},
    {0, :Sq, :mksq, [{:ctor, :Z, []}, {:ctor, :Z, []}], :solved, "Sq mksq [Z,Z] — consistent re-bind"},
    {0, :Sq, :mksq, [{:ctor, :Z, []}, {:ctor, :S, [{:ctor, :Z, []}]}], :impossible, "Sq mksq [Z,S Z] — merge conflict"},
    {2, :Sq, :mksq, [{:var, 0}, {:var, 1}], :solved, "Sq mksq [var0,var1] — forced equation (Solution step)"},
    {0, :Ty, :tnat, [{:type, 0}], :impossible, "Ty tnat [Type0] — rigid data/Type clash"},
    {0, :Tg, :tg0, [{:int_lit, 0}], :trivial, "Tg tg0 [0] — int_lit==int_lit fast path (equal)"},
    {0, :Tg, :tg0, [{:int_lit, 1}], :impossible,
     "Tg tg0 [1] — int_lit!=int_lit fast path (distinct); the int_lit<->ctor bridge (kernel.ex) now decides distinct Int literals :impossible, mirroring the nat_lit bridge (Nl below), closing the coverage-soundness gap where they were left :undecided"},
    # crossing 4-index family: mkcyc : Cyc4 a a b b matched against Cyc4 i j j i
    # induces the multi-key cycle (i:=j then j:=i) → resolve-before-bind collapse.
    {2, :Cyc4, :mkcyc, [{:var, 0}, {:var, 1}, {:var, 1}, {:var, 0}], :solved,
     "Cyc4 crossing — multi-key cycle collapse"},
    {4, :Cyc4, :mkcyc, [{:var, 0}, {:var, 1}, {:var, 2}, {:var, 3}], :solved, "Cyc4 distinct — 4-index spine solve"},
    # Cyc4b interleaves the repeated ctor-vars ([a,d,a,d], not [a,a,b,b]) against
    # the same [i,j,j,i] scrutinee crossing. Unlike Cyc4's grouped pattern (which
    # never re-derives a key already in `subst`), the interleaving forces the
    # union-find chase to land the 4th constraint back on an ALREADY-BOUND key
    # whose representative is EQUAL to the incoming term — bind_index's
    # `rterm == {:var, key}` no-op (kernel.ex:1073), not the "old==rterm consistent"
    # arm Cyc4 hits.
    {2, :Cyc4b, :mkcyc2, [{:var, 0}, {:var, 1}, {:var, 1}, {:var, 0}], :solved,
     "Cyc4b interleaved crossing — union-find self-loop collapse (bind_index 1073)"},
    # Nl: a Nat-indexed family with both a compact-nat_lit-literal and a ctor-tower
    # result index, exercising every arm of unify_one's nat_lit<->ctor bridge.
    {0, :Nl, :nlc, [{:nat_lit, 2}], :trivial, "Nl nat_lit==nat_lit fast path (unify_one 1003, equal)"},
    {0, :Nl, :nlc, [{:nat_lit, 3}], :impossible, "Nl nat_lit!=nat_lit fast path (unify_one 1003, distinct)"},
    {0, :Nl, :nlc, [{:ctor, :S, [{:ctor, :S, [{:ctor, :Z, []}]}]}], :trivial,
     "Nl nat_lit result index vs ctor-tower scrutinee — peel nat_lit->ctor (unify_one 1005/1006)"},
    {0, :Nl, :nlt, [{:nat_lit, 1}], :trivial,
     "Nl ctor-tower result index vs nat_lit scrutinee — peel ctor->nat_lit (unify_one 1008/1009)"},
    # CaseIdx: a result index that is itself a :case term — subst_params must
    # recurse into the scrutinee/motive/branches (kernel.ex 960/961), not just the
    # simple :data/:ctor/:pi/:lam/:app arms every other case here already reaches.
    {0, :CaseIdx, :mkci, [{:ctor, :Z, []}], :trivial,
     "CaseIdx :case-headed result index — subst_params :case recursion (960/961)"},
    # SpineU: a result index headed by a stuck application spine (S applied over a
    # global `plus` neutral) — unify_spine's element-wise :undecided arm drops the
    # pair and keeps going rather than failing (kernel.ex:1047).
    {0, :SpineU, :spu, [{:ctor, :S, [{:ctor, :Z, []}]}], :trivial,
     "SpineU stuck plus-application spine element — unify_spine :undecided drop (1047)"},
    # Dboth: a result index that is itself a nested :data term with BOTH its
    # parameter list and index list populated — subst_params must map over both
    # (kernel.ex 952/953), not just one or the other. Vec's head differs from the
    # scrutinee's Z head, so this is a definite rigid data/ctor clash (Conflict
    # rule) — :impossible, independent of the recursion itself.
    {0, :Dboth, :mkboth, [{:ctor, :Z, []}], :impossible,
     "Dboth nested :data result index (ps and is both non-empty) — subst_params :data recursion (953), rigid head clash"}
  ]

  # Parameterised-GADT cases (finding S9): `{ctx_vars, dname, cname, indices,
  # params, verdict, note}`. `Foo (a:Nat) : Nat -> Type0` with `MkFoo : Foo a (S a)`
  # buries the family parameter in a result-index spine. With ctx_vars=2 the frame
  # is [level0 = param a, level1 = free index i]; de Bruijn 1 → level 0 (param), 0 →
  # level 1 (index). Matching `MkFoo` against a free index is SOLVABLE (i := S a),
  # NOT impossible — the pre-fix unifier collided the param var with a shifted
  # scrutinee var and verdicted `:impossible`. These carry scrutinee `params`, so the
  # assay drives `branch_unify/5`.
  @param_cases [
    {2, :Foo, :MkFoo, [{:var, 0}], [{:var, 1}], :solved,
     "Foo MkFoo over a free index — param in result-index spine is SOLVABLE (S9)"},
    {2, :Foo, :MkFoo, [{:ctor, :Z, []}], [{:var, 1}], :impossible,
     "Foo MkFoo vs rigid Z index — genuine S/Z clash (S9 control)"},
    # Cyc1: a family whose ONE parameter is buried directly into its ONE index
    # (`Cyc1 (a:Nat) : Nat -> Type0`, `idcyc : Cyc1 a a`). Matched against a
    # scrutinee index `S x` where the scrutinee's actual param value IS the same
    # outer var `x`, the equation reduces to the textbook occurs-check example
    # `x =?= S x` — x occurs strongly rigid in its own successor, absurd by
    # acyclicity of Nat (Agda Cycle rule; kernel.ex var_cycle?/strongly_rigid_occurs?
    # at 1028/1038). Requires branch_unify/5 (a bare param var would otherwise
    # collide with the shifted scrutinee var — finding S9's own trap).
    {1, :Cyc1, :idcyc, [{:ctor, :S, [{:var, 0}]}], [{:var, 0}], :impossible,
     "Cyc1 self-cycle — param buries into own successor, occurs-check (var_cycle? 1028/1038)"}
  ]

  # Motive-probe cases: `{shape, note}`. These drive `Kernel.infer`'s `:case` clause
  # (hence `apply_motive_checked`) directly rather than `branch_unify/4,5` — a
  # dependent case's motive is checked BEFORE any branch unification runs, so
  # there is no `dname`/`cname`/indices shape to reuse here. Both verdict
  # `:bad_motive`.
  @motive_cases [
    {:neutral,
     "motive = an opaque outer variable — apply_motive_checked's :vneutral arm keeps applying (kernel.ex:634); the motive never becomes a well-typed Pi, so infer still rejects with :bad_motive"},
    {:nonfun,
     "motive = a concrete non-function value (a Nat type-value) — apply_motive_checked halts on the very first application, its catch-all arm (kernel.ex:635)"}
  ]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    branch_tagged =
      Enum.map(@cases, fn {n, d, c, idx, verdict, note} -> {:branch, n, d, c, idx, [], verdict, note} end) ++
        Enum.map(@param_cases, fn {n, d, c, idx, params, verdict, note} ->
          {:branch, n, d, c, idx, params, verdict, note}
        end)

    motive_tagged = Enum.map(@motive_cases, fn {shape, note} -> {:motive, shape, note} end)

    Gen.bind(Gen.member_of(branch_tagged ++ motive_tagged), fn
      {:branch, n, d, c, idx, params, verdict, note} ->
        Gen.return(
          Challenge.new(
            kind: :branch_unify,
            assay: "branchunify/verdict",
            label: verdict,
            payload: %{ctx_vars: n, dname: d, cname: c, indices: idx, params: params},
            note: note,
            cover_tag: cover_cell(params, verdict)
          )
        )

      {:motive, shape, note} ->
        Gen.return(
          Challenge.new(
            kind: :branch_unify,
            assay: "branchunify/verdict",
            label: :bad_motive,
            payload: %{motive_probe: shape},
            note: note,
            cover_tag: :bad_motive
          )
        )
    end)
  end

  @doc "The literal paramless case menu (for the generator's coverage self-test)."
  def cases, do: @cases

  @doc "The parameterised-GADT case menu (finding S9 + Cyc1 coverage self-test)."
  def param_cases, do: @param_cases

  @doc "The motive-probe case menu (apply_motive_checked bad-motive coverage self-test)."
  def motive_cases, do: @motive_cases
end

defmodule Antigen.Generators.DepMatch do
  @moduledoc """
  Structure-directed generator for **dependent pattern matching** — well-typed
  `case` over the indexed family `Vec`, with an index-refining branch structure
  and (optionally) a dependent type-former motive. This is the reachability lever
  for the kernel's dependent-matching core, which no value-term generator reaches:
  `check_motive_wf` → `infer_type_value_sort` (dependent motive), `check_case_branches`,
  `unify_indices` (`bind_index` / `unify_one` / `unify_spine` / `rigid_index?`,
  including the `:impossible` unreachable-branch path), `specialize_branch_context`,
  `check_result_indices`, and `replace_branch_vars`.

  Three scrutinee shapes, all well-typed by construction over the v1 menu:

    * **variable index** `xs : Vec n` (ctx `[Vec n, Nat]`) — both branches
      reachable; `unify_indices` refines `n := Z` / `n := S k`.
    * **closed `Vec Z`** — the `vcons` branch is `:impossible` (unify `S k` ~ `Z`).
    * **closed `Vec (S Z)`** — the `vnil` branch is `:impossible` (unify `Z` ~ `S Z`).

  Motives: constant (`λm.λv. Nat|Bd`) or dependent (`λm.λv. Vec m`, whose body is
  a type-former over the bound index — the `infer_type_value_sort` driver). Branch
  bodies inhabit the motive at the refined index. The claimed `type` is exactly
  what `infer` returns (verified in the soundness test).
  """
  alias Antigen.{Gen, Challenge}

  @nat {:data, :Nat, [], []}
  @bd {:data, :Bd, [], []}
  @z {:ctor, :Z, []}
  @assays ["term/infer_check", "term/subject_reduction", "term/normalization"]

  # Ty's constructor index terms + matching branches (declaration order). Defined
  # at module top so every generator below reads them (module attributes resolve at
  # the textual point of use, so a later assignment would read nil).
  @ty_indices [
    @nat,
    @bd,
    {:int_type},
    {:float_type},
    {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat},
    {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []},
    {:data, :Vec, [@z], []}
  ]
  @ty_branches [
    {:tnat, 0, @z},
    {:tbd, 0, @z},
    {:tint, 0, @z},
    {:tflt, 0, @z},
    {:tpi, 0, @z},
    {:tsig, 0, @z},
    {:tvec, 0, @z}
  ]

  defp vec(i), do: {:data, :Vec, [], [i]}

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@assays), fn assay ->
      Gen.bind(case_challenge(), fn {ctx, term, type} ->
        Gen.return(
          Challenge.new(
            kind: :typed_term,
            assay: assay,
            label: :well_typed,
            payload: %{sig: :v1, ctx: ctx, type: type, term: term},
            note: "dependent match (indexed Vec case)"
          )
        )
      end)
    end)
  end

  defp case_challenge do
    Gen.frequency([
      # variable index, both branches reachable — constant-motive flavours whose
      # result type drives a distinct infer_type_value_sort clause via check_motive_wf
      {3, var_const(@nat, numeral())},
      {2, var_const(@bd, bd_lit())},
      {2, var_const({:type, 0}, small_type())},
      {2, var_const({:data, :Int, [], []}, int_lit())},
      {2, var_const({:float_type}, float_lit())},
      # dependent motives: Vec m (type-former) and Eq Nat m m (propositional)
      {3, var_index(:vec)},
      {2, var_index(:eq)},
      # D1 neutral-application motive λm.λv. b(m) — the napp sort clause
      {2, neutral_app_motive_case()},
      # closed indices — force an :impossible branch (constant Nat motive)
      {2, closed_index(@z)},
      {2, closed_index({:ctor, :S, [@z]})},
      # extra context variable whose TYPE mentions the scrutinee index — branch
      # refinement specializes it via specialize_branch_context, driving
      # replace_branch_vars over Equivalent-data / Σ / Π type shapes.
      {2, var_index_extra({:data, :Equivalent, [@nat], [{:var, 1}, {:var, 1}]})},
      {2, var_index_extra({:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, vec({:var, 2})}], []})},
      {2, var_index_extra({:pi, Cure.Core.Grade.unrestricted(), @nat, vec({:var, 2})})},
      # extra context types carrying stuck value-level subterms (λ / pair / reflexive)
      # so specialize_branch_context's replace_branch_vars descends those arms.
      {2,
       var_index_extra(
         {:data, :Equivalent, [{:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}],
          [
            {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 0}},
            {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 0}}
          ]}
       )},
      {2,
       var_index_extra(
         {:data, :Equivalent, [{:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}],
          [{:ctor, :mk_pair, [{:var, 1}, {:var, 1}]}, {:ctor, :mk_pair, [{:var, 1}, {:var, 1}]}]}
       )},
      {2,
       var_index_extra(
         {:data, :Equivalent, [{:data, :Equivalent, [@nat], [{:var, 1}, {:var, 1}]}],
          [{:ctor, :reflexive, [{:var, 1}]}, {:ctor, :reflexive, [{:var, 1}]}]}
       )},
      # two-var frame: a helper context var lets extra_ty carry a STUCK app /
      # projection / builtin-op spine (K2) — replace_branch_vars' app/fst/snd arms.
      {2,
       var_index_extra2(
         {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat},
         {:data, :Equivalent, [@nat], [{:app, {:var, 1}, {:var, 3}}, {:app, {:var, 1}, {:var, 3}}]}
       )},
      {2,
       var_index_extra2(
         {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []},
         {:data, :Equivalent, [@nat],
          [
            {:case, {:var, 1},
             {:lam, Cure.Core.Grade.unrestricted(),
              {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}, @nat},
             [{:mk_pair, 2, {:var, 1}}]},
            {:case, {:var, 1},
             {:lam, Cure.Core.Grade.unrestricted(),
              {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}, @nat},
             [{:mk_pair, 2, {:var, 1}}]}
          ]}
       )},
      {2,
       var_index_extra2(
         {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []},
         {:data, :Equivalent, [@nat],
          [
            {:case, {:var, 1},
             {:lam, Cure.Core.Grade.unrestricted(),
              {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}, @nat},
             [{:mk_pair, 2, {:var, 0}}]},
            {:case, {:var, 1},
             {:lam, Cure.Core.Grade.unrestricted(),
              {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}, @nat},
             [{:mk_pair, 2, {:var, 0}}]}
          ]}
       )},
      {2,
       var_index_extra2(
         {:data, :Int, [], []},
         {:data, :Equivalent, [{:data, :Int, [], []}],
          [
            {:app, {:app, {:global, :int_add}, {:var, 1}}, {:var, 1}},
            {:app, {:app, {:global, :int_add}, {:var, 1}}, {:var, 1}}
          ]}
       )},
      # a STUCK case over a Bool helper var in an index position — the case arm of
      # replace_branch_vars. Inner motive λb:Bool.Nat; both branches yield Z.
      {2, var_index_extra2(stuck_case_helper(), {:data, :Equivalent, [@nat], [stuck_case(), stuck_case()]})},
      # POLYMORPHIC motive: Γ = [n:Nat, x:a, a:Type0]; case n of Z→x | S→x with
      # motive λv:Nat. a — the result type is the Type-parameter VARIABLE a, so
      # check_motive_wf's infer_type_value_sort takes its neutral-var (nvar) clause
      # (a bound-at-a-universe motive result), distinct from the data/Π/Σ/Eq arms.
      {2, tyvar_motive_case()},
      # motive returns Eq Type0 (List Nat) (List Nat) — a propositional equality
      # between PARAMETER-BEARING family TYPES. check_motive_wf's veq clause reifies
      # the endpoints signature-aware, so Quote.split_data_args splits List's param
      # off the (empty) index list — the dependent param/index read-back split.
      {2, eqtype_motive_case()},
      # TWO-index diagonal family Sq — matching forces a ≡ b, the only v1 shape
      # that reaches unify_spine (2-index spine) + bind_index's merge path.
      {3, sq_diag()},
      {2, sq_closed(@z, @z)},
      {2, sq_closed(@z, {:ctor, :S, [@z]})},
      # Type0-indexed family Ty — a closed type index unified against each ctor's
      # rigid type index (rigid_index? data/int/float/Π/Σ, head_key :data,
      # unify_one data-spine / syntactic-equal). Random concrete index + a var index.
      {4, ty_closed()},
      {2, ty_var()},
      # Ty with a Vec (S Z) index that matches NO ctor — unifying against tvec's
      # Vec Z index drives unify_spine to :impossible on a differing element.
      {1, ty_scrutinee({:data, :Vec, [{:ctor, :S, [@z]}], []})},
      # Int/Float-value-indexed families Tg/Tgf — literal indices unified at match
      # time (rigid_index? int_lit/float_lit).
      {2, tg_closed(:int)},
      {2, tg_closed(:float)},
      # Compact Nat literal (K2, spec 2026-07-09): a `case` scrutinee that IS a
      # `{:nat_lit, n}` value (not the S/Z tower) — the reachability lever for
      # `Eval.nat_to_ctor`/`nat_to_ctor_if` (n=0 and n>0 both peel one layer).
      {2, nat_case(0)},
      {2, nat_case(4)},
      # Vec closed at a compact-Nat index instead of the tower — drives the
      # `{:nat_lit,_} <-> {:ctor,_,_}` bridge in `unify_one`, i.e. `nat_lit_ctor/1`
      # (n=0 and n>0 both peel one layer during index unification).
      {2, closed_index({:nat_lit, 0})},
      {2, closed_index({:nat_lit, 4})},
      # Sq diagonal closed at a compact-Nat literal vs a mismatched tower ctor —
      # the merge clash in `bind_index` compares the two rigid result-index terms
      # and calls `rigid_index?` on the (unpeeled) `{:nat_lit, _}` side.
      {1, sq_closed({:nat_lit, 4}, {:ctor, :S, [@z]})}
    ])
  end

  # A `case` directly on a compact Nat literal scrutinee (0-index family Nat
  # itself, not Vec/Sq/Ty): `case {:nat_lit,n} of Z -> Z | S(k) -> k`. Mirrors
  # `tyvar_motive_case`'s single-level motive shape (Nat has no index to
  # separately abstract) and `eqtype_motive_case`'s closed non-var scrutinee.
  # `Kernel.infer` on the `{:nat_lit,n}` scrutinee itself resolves via
  # `nat_type_value`; `Eval.eval`'s `:case` clause peels it via `nat_to_ctor_if`.
  defp nat_case(n) do
    term = {:case, {:nat_lit, n}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [{:Z, 0, @z}, {:S, 1, {:var, 0}}]}
    Gen.return({[], term, @nat})
  end

  @doc """
  Deterministic compact-Nat coverage probes, as full `%Challenge{}`s (one per
  assay so `term/subject_reduction`/`term/normalization` — which force `nf`,
  hence `Eval.eval` — are exercised directly, not left to random `@assays`
  sampling). Public so a coverage test can drive them without going through
  `Gen` sampling machinery. Mirrors the shapes wired into `case_challenge/0`
  above (`nat_case/1`, `closed_index/1` at a nat_lit index, `sq_closed/2` at a
  mismatched nat_lit/ctor pair).
  """
  @spec compact_nat_probes() :: [Challenge.t()]
  def compact_nat_probes do
    specs = [
      {"compact_nat/case_zero",
       {[],
        {:case, {:nat_lit, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [{:Z, 0, @z}, {:S, 1, {:var, 0}}]},
        @nat}, "case on {:nat_lit,0} — Eval.nat_to_ctor(0) / nat_to_ctor_if"},
      {"compact_nat/case_succ",
       {[],
        {:case, {:nat_lit, 4}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [{:Z, 0, @z}, {:S, 1, {:var, 0}}]},
        @nat}, "case on {:nat_lit,4} — Eval.nat_to_ctor(n>0) / nat_to_ctor_if"},
      {"compact_nat/vec_closed_zero",
       {[vec({:nat_lit, 0})], mk_case({:var, 0}, motive(@nat), [{:vnil, 0, @z}, {:vcons, 3, @z}]), @nat},
       "Vec({:nat_lit,0}) closed index — Kernel.nat_lit_ctor(0) bridge"},
      {"compact_nat/vec_closed_succ",
       {[vec({:nat_lit, 4})], mk_case({:var, 0}, motive(@nat), [{:vnil, 0, @z}, {:vcons, 3, @z}]), @nat},
       "Vec({:nat_lit,4}) closed index — Kernel.nat_lit_ctor(n>0) bridge"},
      {"compact_nat/sq_merge_clash",
       {[sq({:nat_lit, 4}, {:ctor, :S, [@z]})], mk_case({:var, 0}, sq_motive(), [{:mksq, 1, @z}]), @nat},
       "Sq({:nat_lit,4}, S(Z)) diagonal merge — Kernel.rigid_index?'s nat_lit clause"}
    ]

    for {id, {ctx, term, type}, note} <- specs,
        assay <- @assays do
      Challenge.new(
        kind: :typed_term,
        assay: assay,
        label: :well_typed,
        payload: %{sig: :v1, ctx: ctx, type: type, term: term},
        note: "#{id} (#{assay}): #{note}"
      )
    end
  end

  # Closed scrutinee x : Ty T for an ARBITRARY closed type index (possibly matching
  # no ctor — all branches then unify T against a differing rigid index).
  defp ty_scrutinee(idx) do
    Gen.bind(numeral(), fn body ->
      term = mk_case({:var, 0}, ty_motive(), replace_first_body(@ty_branches, body))
      Gen.return({[ty(idx)], term, @nat})
    end)
  end

  @tg %{
    int: {:Tg, [{:tg0, 0, @z}, {:tg1, 0, @z}], [{:int_lit, 0}, {:int_lit, 1}, {:int_lit, 5}]},
    float: {:Tgf, [{:tgf0, 0, @z}, {:tgf1, 0, @z}], [{:float_lit, 0.0}, {:float_lit, 1.5}, {:float_lit, 2.5}]}
  }

  # Closed scrutinee x : Tg <lit> (Int/Float-indexed) — matching unifies the closed
  # literal index against each ctor's literal result index.
  defp tg_closed(kind) do
    {fname, branches, indices} = @tg[kind]

    Gen.bind(Gen.member_of(indices), fn idx ->
      Gen.bind(numeral(), fn body ->
        brs = replace_first_body(branches, body)
        term = mk_case({:var, 0}, tg_motive(fname, kind), brs)
        Gen.return({[{:data, fname, [], [idx]}], term, @nat})
      end)
    end)
  end

  defp tg_motive(fname, kind) do
    ity = if kind == :int, do: {:data, :Int, [], []}, else: {:float_type}

    {:lam, Cure.Core.Grade.unrestricted(), ity,
     {:lam, Cure.Core.Grade.unrestricted(), {:data, fname, [], [{:var, 0}]}, @nat}}
  end

  # Closed scrutinee x : Ty T for a random concrete type index T. The matching ctor
  # is trivial/solved; the rest unify T against a differing rigid head (:impossible
  # or :undecided) — the rigid_index?/head_key comparison lever.
  defp ty_closed do
    Gen.bind(Gen.member_of(@ty_indices), fn idx ->
      Gen.bind(numeral(), fn body ->
        term = mk_case({:var, 0}, ty_motive(), replace_first_body(@ty_branches, body))
        Gen.return({[ty(idx)], term, @nat})
      end)
    end)
  end

  # Variable index x : Ty a (a : Type0) — every ctor's rigid type index is bound to a.
  defp ty_var do
    Gen.bind(numeral(), fn body ->
      term = mk_case({:var, 0}, ty_motive(), replace_first_body(@ty_branches, body))
      Gen.return({[ty({:var, 0}), {:type, 0}], term, @nat})
    end)
  end

  defp ty(a), do: {:data, :Ty, [], [a]}
  # λa. λv:Ty a. Nat
  defp ty_motive,
    do: {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:lam, Cure.Core.Grade.unrestricted(), ty({:var, 0}), @nat}}

  # vary the reachable-branch body without disturbing the fixed ctor set
  defp replace_first_body([{c, ar, _} | rest], body), do: [{c, ar, body} | rest]

  # Γ = [ s : Sq a b (idx 0), b : Nat (idx 1), a : Nat (idx 2) ]; matching mksq
  # unifies the diagonal result index against both a and b → forces a ≡ b.
  defp sq_diag do
    Gen.bind(numeral(), fn body ->
      term = mk_case({:var, 0}, sq_motive(), [{:mksq, 1, body}])
      Gen.return({[sq({:var, 1}, {:var, 0}), @nat, @nat], term, @nat})
    end)
  end

  # Closed Sq indices: Sq Z Z (mksq trivial) / Sq Z (S Z) (mksq :impossible).
  defp sq_closed(i, j) do
    Gen.bind(numeral(), fn body ->
      term = mk_case({:var, 0}, sq_motive(), [{:mksq, 1, body}])
      Gen.return({[sq(i, j)], term, @nat})
    end)
  end

  defp sq(i, j), do: {:data, :Sq, [], [i, j]}
  # λi.λj.λv:Sq i j. Nat  (v's frame: i = var 2, j = var 1)
  defp sq_motive,
    do:
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), @nat,
        {:lam, Cure.Core.Grade.unrestricted(), sq({:var, 2}, {:var, 1}), @nat}}}

  # Γ = [ p : extra_ty (idx 0), xs : Vec n (idx 1), n : Nat (idx 2) ] where
  # extra_ty mentions n (var 1 from p's frame). Scrutinee is xs (var 1). When a
  # branch refines n, `specialize_branch_context` rewrites p's type — exercising
  # `replace_branch_vars` over extra_ty's shape.
  defp var_index_extra(extra_ty) do
    Gen.bind(numeral(), fn zbody ->
      Gen.bind(numeral(), fn sbody ->
        term = mk_case({:var, 1}, motive(@nat), [{:vnil, 0, zbody}, {:vcons, 3, sbody}])
        Gen.return({[extra_ty, vec({:var, 0}), @nat], term, @nat})
      end)
    end)
  end

  # Like var_index_extra but with an extra HELPER context var (a function / Σ /
  # Int) so `extra_ty` can carry a value-level subterm that stays STUCK through
  # evaluation — `helper n` (app), `fst/snd helper` (projections), `prim add
  # [helper,helper]` — driving replace_branch_vars' app/fst/snd/prim arms when a
  # branch refines the index. Frame: Γ = [extra_ty, helper_ty, Vec n, n:Nat]; the
  # scrutinee is var 2, the helper var 1, and `n` var 3 inside extra_ty.
  # helper for the case-in-index variant: a Bool-typed helper var, and a stuck
  # `case helper of False -> Z; True -> Z` (helper is var 1 in the two-var frame).
  defp stuck_case_helper, do: {:data, :Bool, [], []}

  defp stuck_case,
    do:
      {:case, {:var, 1}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bool, [], []}, @nat},
       [{:False, 0, @z}, {:True, 0, @z}]}

  # Γ = [n:Nat (idx0), x:a (idx1), a:Type0 (idx2)]; case n of Z→x | S→x with a
  # constant motive λv:Nat. a. Result type is the Type-var a (var 2). Fixed shape.
  defp tyvar_motive_case do
    Gen.return(
      {[@nat, {:var, 0}, {:type, 0}],
       {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 3}},
        [{:Z, 0, {:var, 1}}, {:S, 1, {:var, 2}}]}, {:var, 2}}
    )
  end

  # case Z of Z→reflexive(Nil) | S→reflexive(Nil) with motive λv:Nat.
  # Equivalent (List Nat) Nil Nil. Closed; result type is that Equivalent.
  # (Phase C retarget: the old form equated the TYPE `List Nat` at carrier
  # Type0 via the primitive {:eq} — inexpressible as the inductive Equivalent,
  # whose param lives in Type0. The param-bearing family `List Nat` now rides
  # as Equivalent's PARAM, still driving signature-aware handling of a
  # param-bearing family type through motive-WF and branch-body checks.)
  @list_nat {:data, :List, [{:data, :Nat, [], []}], []}
  @nil_ln {:ctor, :Nil, []}
  defp eqtype_motive_case do
    eqty = {:data, :Equivalent, [@list_nat], [@nil_ln, @nil_ln]}
    refl_ln = {:ctor, :reflexive, [@nil_ln]}
    # claimed type in FLAT params++indices form (reify has no signature to
    # recover the split, so the inferred type reads back flat)
    eqty_flat = {:data, :Equivalent, [@list_nat, @nil_ln, @nil_ln], []}

    Gen.return(
      {[], {:case, @z, {:lam, Cure.Core.Grade.unrestricted(), @nat, eqty}, [{:Z, 0, refl_ln}, {:S, 1, refl_ln}]},
       eqty_flat}
    )
  end

  defp var_index_extra2(helper_ty, extra_ty) do
    Gen.bind(numeral(), fn zbody ->
      Gen.bind(numeral(), fn sbody ->
        term = mk_case({:var, 2}, motive(@nat), [{:vnil, 0, zbody}, {:vcons, 3, sbody}])
        Gen.return({[extra_ty, helper_ty, vec({:var, 0}), @nat], term, @nat})
      end)
    end)
  end

  # Γ = [ xs : Vec n (idx 0), n : Nat (idx 1) ]; case xs of vnil | vcons, with a
  # CONSTANT motive λm.λv. result_ty — both branch bodies inhabit result_ty. The
  # motive body's shape (universe / Int / Float / data) selects the
  # infer_type_value_sort clause exercised.
  defp var_const(result_ty, body_gen) do
    Gen.bind(body_gen, fn zbody ->
      Gen.bind(body_gen, fn sbody ->
        term = mk_case({:var, 0}, motive(result_ty), [{:vnil, 0, zbody}, {:vcons, 3, sbody}])
        Gen.return({[vec({:var, 0}), @nat], term, result_ty})
      end)
    end)
  end

  # Dependent motive λm.λv. Equivalent Nat m m — branch bodies are reflexive at
  # the refined index (vnil : Equivalent Nat Z Z → reflexive Z; vcons :
  # Equivalent Nat (S n) (S n) → reflexive (S n)).
  defp var_index(:eq) do
    eq_ty = fn m -> {:data, :Equivalent, [@nat], [m, m]} end
    # claimed type in FLAT params++indices form (reify reads back flat)
    eq_ty_flat = fn m -> {:data, :Equivalent, [@nat, m, m], []} end

    motive_eq =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), vec({:var, 0}), eq_ty.({:var, 1})}}

    nil_body = {:ctor, :reflexive, [@z]}
    cons_body = {:ctor, :reflexive, [{:ctor, :S, [{:var, 2}]}]}
    term = mk_case({:var, 0}, motive_eq, [{:vnil, 0, nil_body}, {:vcons, 3, cons_body}])
    Gen.return({[vec({:var, 0}), @nat], term, eq_ty_flat.({:var, 1})})
  end

  # Dependent motive λm.λv. Vec m — branch bodies must inhabit Vec at the refined
  # index (vnil : Vec Z; vcons n x xs : Vec (S n)).
  defp var_index(:vec) do
    nil_body = {:ctor, :vnil, []}
    cons_body = {:ctor, :vcons, [{:var, 2}, {:var, 1}, {:var, 0}]}
    term = mk_case({:var, 0}, dep_motive(), [{:vnil, 0, nil_body}, {:vcons, 3, cons_body}])
    # infer normalizes Vec's sole argument into the PARAMS slot (empty indices) —
    # the claimed type must match that reified normal form (see Generators.Term).
    Gen.return({[vec({:var, 0}), @nat], term, {:data, :Vec, [{:var, 1}], []}})
  end

  # D1 neutral-application motive: λm. λv:Vec(m). b(m) — the NEW napp shape
  # (b is a free context variable of type (Nat) -> Type; b(m) reifies to
  # {:app, <b>, <m>} and must sort via the new infer_type_value_sort clause).
  # Closed to Vec(Z) so the vcons branch is :impossible (unify S k ~ Z fails,
  # mirroring closed_index/1) — only vnil needs a real inhabitant, supplied by
  # context witness w : b(Z).
  #
  # ctx (list position = final var index, per rebuild_context's reversed-fold):
  #   0 = xs : Vec(Z)         (scrutinee)
  #   1 = w  : b(Z)           (witness; its own type references b as {:var,0},
  #                             the only var already bound at that point)
  #   2 = b  : (Nat) -> Type
  defp neutral_app_motive_case do
    b_ty = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:type, 0}}
    w_ty = {:app, {:var, 0}, @z}
    # under the motive's 2 own binders (m, v), ambient var k reads as {:var, 2+k}:
    # b is ambient index 2 -> {:var, 4}; m is the motive's own outer binder -> {:var, 1}.
    motive_napp =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), vec({:var, 0}), {:app, {:var, 4}, {:var, 1}}}}

    term = mk_case({:var, 0}, motive_napp, [{:vnil, 0, {:var, 1}}, {:vcons, 3, @z}])
    Gen.return({[vec(@z), w_ty, b_ty], term, {:app, {:var, 2}, @z}})
  end

  # Γ = [ xs : Vec <idx> (idx 0) ] with a closed index → one branch is :impossible.
  # Constant Nat motive; the reachable branch's body is a numeral, the impossible
  # branch's body is unchecked (any well-formed term).
  defp closed_index(idx) do
    Gen.bind(numeral(), fn body ->
      term = mk_case({:var, 0}, motive(@nat), [{:vnil, 0, body}, {:vcons, 3, @z}])
      Gen.return({[vec(idx)], term, @nat})
    end)
  end

  # motive λm. λv:Vec m. <ty>  (constant result type)
  defp motive(ty),
    do: {:lam, Cure.Core.Grade.unrestricted(), @nat, {:lam, Cure.Core.Grade.unrestricted(), vec({:var, 0}), ty}}

  # dependent motive λm. λv:Vec m. Vec m
  defp dep_motive,
    do:
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), vec({:var, 0}), vec({:var, 1})}}

  defp mk_case(scrut, motive, branches), do: {:case, scrut, motive, branches}

  defp numeral do
    Gen.bind(Gen.int(0, 4), fn n ->
      Gen.return(Enum.reduce(1..n//1, @z, fn _, acc -> {:ctor, :S, [acc]} end))
    end)
  end

  defp bd_lit, do: Gen.member_of([{:ctor, :T, []}, {:ctor, :F, []}])

  # A closed type inhabiting Type 0 (for a λm.λv.Type0 motive's branch bodies).
  defp small_type, do: Gen.member_of([@nat, @bd, {:int_type}, {:float_type}])
  defp int_lit, do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:int_lit, n}) end)
  defp float_lit, do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:float_lit, n / 2}) end)
end

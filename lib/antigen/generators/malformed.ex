defmodule Antigen.Generators.Malformed do
  @moduledoc """
  Parametric generator for the NEGATIVE `term/rejection` vertical (assay
  `Antigen.Assays.Malformed`): terms that `Kernel.infer` MUST reject, exercising
  its defensive rejection clauses that no well-typed generator reaches. Each
  challenge is closed (empty local context over the v1 menu) and labelled
  `:ill_typed`; the assay confirms the kernel rejects it.

  Malformation families (each parametric over its variable positions):

    * `{:absurd}` in a reachable position → `:absurd_in_reachable_position`
    * `{:global, <undeclared>}` → `:unknown_global`
    * `{:data, <undeclared>, …}` → `{:unknown_family, _}`
    * `{:ctor, <undeclared>, …}` → `{:unknown_ctor, _}`
    * `case <non-data>` → `:case_scrutinee_not_data` (scrutinee is a literal /
      universe / Π-type / λ, none of which infer to a data value)
    * `<non-function> arg` → `ensure_pi` guard
    * `rewrite <non-Eq proof>` → `ensure_eq` guard
  """
  alias Antigen.{Gen, Challenge}

  @nat {:data, :Nat, [], []}
  @bd {:data, :Bd, [], []}
  @z {:ctor, :Z, []}

  @doc """
  Shape-coverage cells for the manifest gate (`Antigen.CoverManifest`). Each names
  one defensive rejection shape this generator constructs; the gate confirms every
  cell is actually produced by sampling `gen/0`.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for cell <- [
          :absurd_in_reachable_position,
          :unknown_global,
          :unknown_family,
          :unknown_ctor,
          :case_scrutinee_not_data,
          :app_non_function,
          :rewrite_bad_proof,
          :rewrite_premise,
          :universe_ceiling,
          :unknown_op_global,
          :builtin_op_nonnumeric,
          :case_unknown_ctor_branch,
          :case_foreign_ctor_branch,
          :motive_non_type_var,
          :motive_unknown_family,
          :motive_bare_value,
          :motive_napp_reject
        ],
        do: {"term/rejection", cell}
  end

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(malformation(), fn {term, note, cell} ->
      Gen.return(
        Challenge.new(
          kind: :malformed,
          assay: "term/rejection",
          label: :ill_typed,
          payload: %{sig: :v1, ctx: [], term: term},
          note: "malformed (must reject): #{note}",
          cover_tag: cell
        )
      )
    end)
  end

  defp malformation do
    Gen.frequency([
      {1, tagged({:absurd}, "absurd in reachable position", :absurd_in_reachable_position)},
      {2, tagged({:global, :nosuchdef}, "unknown global", :unknown_global)},
      {2, tagged({:data, :NoSuchFamily, [], []}, "unknown family", :unknown_family)},
      {2, ctor_bad()},
      {3, case_non_data()},
      {2, app_non_function()},
      {2, rewrite_bad_proof()},
      {2, rewrite_premise()},
      {1, tagged({:type, 2}, "universe ceiling (Type 2 has no sort)", :universe_ceiling)},
      # an UNREGISTERED op-named global spine → :unknown_global (K2: the
      # {:prim,<unknown op>} seed re-encodes as a global-app error, R5-enumerated)
      {1, tagged({:app, {:global, :nosuchop}, @z}, "unknown builtin-op global", :unknown_op_global)},
      # int_add on non-numeric operands → the app-argument check failure
      # (check-against-{:vint_type} mismatch; was infer_prim's :prim_type)
      {1,
       tagged(
         {:app, {:app, {:global, :int_add}, {:type, 0}}, {:type, 0}},
         "builtin-op on non-numeric operands",
         :builtin_op_nonnumeric
       )},
      # a case covering Nat's ctors PLUS a spurious branch — coverage passes, so
      # check_case_branches reaches the bad branch: an unknown ctor (:unknown_ctor)
      # or a ctor of another family (:foreign_ctor, vnil belongs to Vec).
      {1, tagged(case_extra_branch(:nosuchctor), "case with unknown-ctor branch", :case_unknown_ctor_branch)},
      {1, tagged(case_extra_branch(:vnil), "case with foreign-ctor branch", :case_foreign_ctor_branch)},
      # a case whose MOTIVE result is not a well-formed type → check_motive_wf's
      # :bad_motive via infer_type_value_sort: a bound non-type var (λv.v), an
      # unknown family (λv.NoSuchFamily), or a bare value (λv.Z).
      {1,
       tagged(
         case_bad_motive({:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 0}}),
         "case motive returns a non-type var",
         :motive_non_type_var
       )},
      {1,
       tagged(
         case_bad_motive({:lam, Cure.Core.Grade.unrestricted(), @nat, {:data, :NoSuchFamily, [], []}}),
         "case motive returns an unknown family",
         :motive_unknown_family
       )},
      {1,
       tagged(
         case_bad_motive({:lam, Cure.Core.Grade.unrestricted(), @nat, @z}),
         "case motive returns a bare value",
         :motive_bare_value
       )},
      {1,
       tagged(
         case_bad_motive({:lam, Cure.Core.Grade.unrestricted(), @nat, {:app, {:var, 0}, @z}}),
         "case motive applies a non-function (Nat-typed) head — napp reject path",
         :motive_napp_reject
       )}
    ])
  end

  # `case Z of {Z→Z; S→Z}` with a supplied (ill-formed) motive — the scrutinee and
  # branches are fine; only the motive's result type is not a valid type.
  defp case_bad_motive(motive) do
    {:case, @z, motive, [{:Z, 0, @z}, {:S, 1, @z}]}
  end

  # `case Z of {Z→Z; S→Z; <bad>→Z}` — the full Nat ctor set (coverage passes) plus
  # a spurious final branch the kernel rejects in check_case_branches.
  defp case_extra_branch(bad_ctor) do
    {:case, @z, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [{:Z, 0, @z}, {:S, 1, @z}, {bad_ctor, 0, @z}]}
  end

  # rewrite with a VALID Eq proof but a body that does not inhabit the motive at
  # the proof's endpoint → the `check(body, expected)` failure branch
  # (`:rewrite_premise`), distinct from the ensure_eq guard above.
  defp rewrite_premise do
    Gen.one_of([
      # proof reflexive Nat Z : Equivalent Nat Z Z; motive λx:Nat.Nat ⇒ the
      # transport expects a Nat body; body is a Bd
      Gen.bind(bd_ctor(), fn b ->
        tagged(
          {:app,
           transport({:ctor, :reflexive, [@nat, @z]}, @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, @z), b},
          "transport body ill-typed (Nat motive, Bd body)",
          :rewrite_premise
        )
      end),
      # proof reflexive Bd T : Equivalent Bd T T; motive λx:Bd.Bd ⇒ Bd; body is a Nat
      Gen.bind(numeral(), fn n ->
        tagged(
          {:app,
           transport(
             {:ctor, :reflexive, [@bd, {:ctor, :T, []}]},
             @bd,
             {:lam, Cure.Core.Grade.unrestricted(), @bd, @bd},
             {:ctor, :T, []}
           ), n},
          "transport body ill-typed (Bd motive, Nat body)",
          :rewrite_premise
        )
      end)
    ])
  end

  # J/subst transport for CLOSED ty/motive/l (shifts elided) — mirrors the
  # elaborator's `transport_case/4`; replaced the retired `{:rewrite}` node.
  defp transport(proof, ty, motive, l) do
    scrut_ty = {:data, :Equivalent, [ty], [{:var, 1}, {:var, 0}]}
    arrow = {:pi, Cure.Core.Grade.unrestricted(), {:app, motive, {:var, 2}}, {:app, motive, {:var, 2}}}

    arrow_motive =
      {:lam, Cure.Core.Grade.unrestricted(), ty,
       {:lam, Cure.Core.Grade.unrestricted(), ty, {:lam, Cure.Core.Grade.unrestricted(), scrut_ty, arrow}}}

    {:case, proof, arrow_motive,
     [{:reflexive, 1, {:lam, Cure.Core.Grade.unrestricted(), {:app, motive, l}, {:var, 0}}}]}
  end

  # NOTE: the `{:absurd}` family is exercised by this generator's assay test (which
  # covers `infer`'s `:absurd_in_reachable_position` clause), but NOT by the live
  # `mix antigen cover` campaign: the runner's `well_formed?` gate calls
  # `Cure.Core.Term.term?/1`, which does not recognise `{:absurd}` (a shape `infer`
  # handles but the Term recogniser rejects), so every absurd challenge is discarded
  # before its assay runs. Left in for the unit-test coverage + as documentation of
  # that recogniser gap.

  # {:ctor, <undeclared>, args} with a random (well-formed) argument list.
  defp ctor_bad do
    Gen.bind(arglist(), fn args -> tagged({:ctor, :nosuchctor, args}, "unknown ctor", :unknown_ctor) end)
  end

  # case over a scrutinee that does NOT infer to a data value.
  defp case_non_data do
    Gen.bind(non_data(), fn scrut ->
      tagged(
        {:case, scrut, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, []},
        "case scrutinee not data",
        :case_scrutinee_not_data
      )
    end)
  end

  # apply a non-function to an argument.
  defp app_non_function do
    Gen.bind(non_function(), fn f -> tagged({:app, f, @z}, "apply non-function", :app_non_function) end)
  end

  # transport whose proof does not infer to an Equivalent — the reflexive
  # branch is foreign to the scrutinee's family (:foreign_ctor), the :case
  # analog of the retired ensure_eq guard.
  defp rewrite_bad_proof do
    Gen.bind(non_eq_proof(), fn pr ->
      tagged(
        {:app, transport(pr, @nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, @z), @z},
        "transport proof not an equality",
        :rewrite_bad_proof
      )
    end)
  end

  # --- parametric leaf pools -------------------------------------------------

  # values / types that are NOT data values (so `case` over them is not_data)
  defp non_data do
    Gen.one_of([
      literal(),
      Gen.return({:type, 0}),
      Gen.return({:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}),
      Gen.return({:lam, Cure.Core.Grade.unrestricted(), @nat, @z})
    ])
  end

  # terms that do NOT infer to a Π type (so applying them trips ensure_pi)
  defp non_function do
    Gen.one_of([literal(), Gen.return(@z), Gen.return({:type, 0})])
  end

  # terms that do NOT infer to an Eq type (so rewrite trips ensure_eq)
  defp non_eq_proof, do: Gen.one_of([literal(), Gen.return(@z)])

  defp literal do
    Gen.one_of([
      Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:int_lit, n}) end),
      Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:float_lit, n / 2}) end)
    ])
  end

  # a short list of well-formed argument terms (for the unknown-ctor case)
  defp arglist do
    Gen.frequency([
      {2, Gen.return([])},
      {1, Gen.return([@z])},
      {1, Gen.return([@z, @z])}
    ])
  end

  defp bd_ctor, do: Gen.member_of([{:ctor, :T, []}, {:ctor, :F, []}])

  defp numeral do
    Gen.bind(Gen.int(0, 4), fn n ->
      Gen.return(Enum.reduce(1..n//1, @z, fn _, acc -> {:ctor, :S, [acc]} end))
    end)
  end

  defp tagged(term, note, cell), do: Gen.return({term, note, cell})
end

defmodule Antigen.Generators.Indexed do
  @moduledoc """
  Known-label indexed-family `case` generator (spec 2026-07-01-antigen-indexed-case).
  Each builder hand-constructs a GADT `case` challenge as raw Core whose
  `:well_typed`/`:ill_typed` label is correct by construction; the assay checks
  the kernel accepts iff well-typed. No elaborator, no term generator.
  """
  alias Antigen.{Challenge, Gen}
  alias Cure.Core.{Env, Inductive}

  # -- coverage manifest ------------------------------------------------------
  # One shape-cell per (obligation, label) twin. Every builder routes through
  # `challenge/6`, which stamps `cover_tag: :"#{name}_#{label}"`; `name` is the
  # obligation atom (also the def_name), `label` the well/ill twin. These are the
  # only shapes this generator constructs — no invented cells.
  @shapes [
    {:branch_family, :well_typed},
    {:branch_family, :ill_typed},
    {:coverage_gap, :well_typed},
    {:coverage_unknown_gap, :ill_typed},
    {:refine, :well_typed},
    {:refine, :ill_typed},
    {:motive_wf, :well_typed},
    {:motive_wf, :ill_typed},
    {:motive_dom, :well_typed},
    {:motive_dom, :ill_typed},
    {:data_split, :well_typed},
    {:data_split, :ill_typed},
    {:reify_distinct, :well_typed},
    {:reify_distinct, :ill_typed},
    {:discharge, :well_typed},
    {:discharge, :ill_typed},
    {:inject, :well_typed},
    {:inject, :ill_typed},
    {:delete, :well_typed},
    {:delete, :ill_typed}
  ]

  @doc "Coverage-manifest cells (`Antigen.CoverManifest`) — one per obligation × label twin."
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for {name, label} <- @shapes, do: {"indexed/case", :"#{name}_#{label}"}
  end

  @doc """
  Uniform sampleable generator over the vertical's hand-built `case` challenges
  (this vertical is otherwise curated / seed-test-fed). Used by the coverage-manifest
  gate to confirm every declared cell is actually produced.
  """
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.member_of([
      branch_family(:well_typed),
      branch_family(:ill_typed),
      coverage(:well_typed),
      coverage(:ill_typed),
      refinement(:well_typed),
      refinement(:ill_typed),
      motive_wf(:well_typed),
      motive_wf(:ill_typed),
      motive_indexed_domain(:well_typed),
      motive_indexed_domain(:ill_typed),
      data_split_validation(:well_typed),
      data_split_validation(:ill_typed),
      reify_collapse_distinct(:well_typed),
      reify_collapse_distinct(:ill_typed),
      discharge(:well_typed),
      discharge(:ill_typed),
      injectivity(:well_typed),
      injectivity(:ill_typed),
      deletion(:well_typed),
      deletion(:ill_typed)
    ])
  end

  @dec {:data, :Dec, [], []}
  @wr {:data, :Wr, [], []}
  # SNat(s): an INDEXED family (one Dec index) — used as a Π DOMAIN inside a motive
  # (the convoy encoding of `with` sibling refinement). `s` = the motive/def binder.
  @snat_s {:data, :SNat, [], [{:var, 0}]}

  # -- shared families --------------------------------------------------------
  defp dec_family,
    do: {Inductive.family(:Dec, [], [], 0), [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]}

  defp foo_family, do: {Inductive.family(:Foo, [], [], 0), [Inductive.ctor(:MkFoo, [], [])]}

  @doc "Rebuild the Env: declare every family, then add the def under test."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{families: families, def_name: dn, def_type: dt, def_body: db}}) do
    # Seed the canonical :nat/:int builtins first: the W3 deletion challenge's
    # def types the compact literal `{:int_lit, 3}` (IxN's index is now the Int
    # family, `{:int_lit}` at wrapn's result index), which reads the :int builtin.
    # The families are inert to every Dec/Wr/IW-based indexed probe.
    seed = Antigen.CanonBuiltins.seed(Env.empty())
    env = Enum.reduce(families, seed, fn {fam, ctors}, e -> Inductive.declare(e, fam, ctors) end)
    Env.add_def(env, dn, dt, db)
  end

  # -- 4.1 branch-family discipline ------------------------------------------
  @doc "Branch-family obligation. `:ill_typed` adds a foreign `Foo` branch to a Dec case."
  @spec branch_family(:well_typed | :ill_typed) :: Challenge.t()
  def branch_family(:well_typed) do
    body =
      {:case, {:ctor, :Causal, []}, {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec},
       [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}

    challenge(:well_typed, [dec_family()], :branch_family, @dec, body, "well-typed Dec case, all branches from Dec")
  end

  def branch_family(:ill_typed) do
    body =
      {:case, {:ctor, :Causal, []}, {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec},
       [
         {:Dcoupled, 0, {:ctor, :Causal, []}},
         {:Causal, 0, {:ctor, :Dcoupled, []}},
         {:MkFoo, 0, {:ctor, :Dcoupled, []}}
       ]}

    challenge(
      :ill_typed,
      [dec_family(), foo_family()],
      :branch_family,
      @dec,
      body,
      "ill-typed: extra branch names MkFoo, a constructor of family Foo, not Dec"
    )
  end

  # -- 4.2 coverage exactness -------------------------------------------------
  defp tri_family,
    do:
      {Inductive.family(:Tri, [], [], 0),
       [Inductive.ctor(:A, [], []), Inductive.ctor(:B, [], []), Inductive.ctor(:C, [], [])]}

  @tri {:data, :Tri, [], []}

  @doc "Coverage obligation: known constructors specialize; opaque variables remain exhaustive."
  @spec coverage(:well_typed | :ill_typed) :: Challenge.t()
  def coverage(:well_typed) do
    body =
      {:case, {:ctor, :A, []}, {:lam, Cure.Core.Grade.unrestricted(), @tri, @tri}, [{:A, 0, {:ctor, :A, []}}]}

    challenge(:well_typed, [tri_family()], :coverage_gap, @tri, body, "known A specializes to its A branch")
  end

  def coverage(:ill_typed) do
    def_type = {:pi, Cure.Core.Grade.unrestricted(), @tri, @tri}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @tri,
       {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @tri, @tri},
        [{:A, 0, {:ctor, :A, []}}, {:B, 0, {:ctor, :A, []}}]}}

    challenge(:ill_typed, [tri_family()], :coverage_unknown_gap, def_type, body, "opaque Tri variable omits C")
  end

  # -- 4.3 compound-index refinement (crown jewel) ----------------------------
  defp ix_family,
    do: {Inductive.family(:Ix, [], [{:n, @dec}], 0), [Inductive.ctor(:wrap, [{:p, @dec}], [{:ctor, :Causal, []}])]}

  @doc """
  Compound-index refinement obligation. The `wrap` ctor's result index is the
  GROUND term `Causal` (not a bare var), so `branch_index_subst` drops the
  refinement equation.
  """
  @spec refinement(:well_typed | :ill_typed) :: Challenge.t()
  def refinement(:well_typed) do
    # Refinement-complete but genuinely legal: `h`, bound before the case at the
    # unrefined type `Ix n`, is reused in the `wrap` branch where the required
    # type is `Ix Causal`. Only the dropped ground-index equation (n := Causal)
    # bridges them. A sound, refinement-complete kernel accepts this by refining
    # h's context type; the current kernel drops the equation and is expected to
    # reject (incompleteness, reported not fixed).
    ix_of_0 = {:data, :Ix, [], [{:var, 0}]}
    ix_of_1 = {:data, :Ix, [], [{:var, 1}]}
    ix_of_2 = {:data, :Ix, [], [{:var, 2}]}

    def_type =
      {:pi, Cure.Core.Grade.unrestricted(), @dec,
       {:pi, Cure.Core.Grade.unrestricted(), ix_of_0, {:pi, Cure.Core.Grade.unrestricted(), ix_of_1, ix_of_2}}}

    motive = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:lam, Cure.Core.Grade.unrestricted(), ix_of_0, ix_of_1}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), ix_of_0,
        {:lam, Cure.Core.Grade.unrestricted(), ix_of_1, {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 2}}]}}}}

    challenge(
      :well_typed,
      [dec_family(), ix_family()],
      :refine,
      def_type,
      body,
      "refinement-complete: reusing h : Ix n as Ix Causal in the wrap branch needs n:=Causal"
    )
  end

  def refinement(:ill_typed) do
    # soundness probe independent of the refinement gap: wrong-typed branch body.
    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :Ix, [], [{:var, 0}]}, @dec}}

    body = {:case, {:ctor, :wrap, [{:ctor, :Dcoupled, []}]}, motive, [{:wrap, 1, {:type, 0}}]}

    challenge(
      :ill_typed,
      [dec_family(), ix_family()],
      :refine,
      @dec,
      body,
      "ill-typed: wrap branch body {:type,0} where Dec is expected"
    )
  end

  # -- 4.4 motive well-formedness ---------------------------------------------
  @doc """
  Motive well-formedness obligation. `:ill_typed` over-applies the motive (an extra
  `:lam` layer beyond index_arity+1), so `apply_motive` leaves a residual `{:vlam, Cure.Core.Grade.unrestricted(),...}`
  which `infer_type_value_sort` rejects as {:error, :bad_motive}. (Do NOT under-apply
  — that crashes Eval.apply; see spec §4.4.)
  """
  @spec motive_wf(:well_typed | :ill_typed) :: Challenge.t()
  def motive_wf(:well_typed) do
    body =
      {:case, {:ctor, :Causal, []}, {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec},
       [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}

    challenge(:well_typed, [dec_family()], :motive_wf, @dec, body, "well-formed motive λx:Dec. Dec")
  end

  def motive_wf(:ill_typed) do
    # one lam too many for a 0-index family
    over = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:lam, Cure.Core.Grade.unrestricted(), @dec, @dec}}

    body =
      {:case, {:ctor, :Causal, []}, over, [{:Dcoupled, 0, {:ctor, :Causal, []}}, {:Causal, 0, {:ctor, :Dcoupled, []}}]}

    # def_type is irrelevant to the motive check; use @dec (check fails before it matters).
    challenge(:ill_typed, [dec_family()], :motive_wf, @dec, body, "over-applied motive → :bad_motive")
  end

  # -- 4.4b motive well-formedness: an INDEXED family as a Π DOMAIN -----------
  defp snat_family,
    do: {Inductive.family(:SNat, [], [{:d, @dec}], 0), [Inductive.ctor(:snat0, [], [{:ctor, :Dcoupled, []}])]}

  @doc """
  Convoy-motive well-formedness: the motive body is a Π whose DOMAIN is an indexed
  family `SNat s` (the encoding of `with` sibling refinement). `check_motive_wf`
  used to reify the Π value and re-infer it, but `Quote.reify` collapses
  `{:vdata,name,args}` → `{:data,name,args,[]}` (it has no inductive signature to
  recover the param/index split), so an indexed-family domain re-inferred with
  `:arg_arity` and the motive was wrongly `:bad_motive` — a false negative.

    * `:well_typed` — `λs. Π(SNat s). Dec`. Now accepted (value-recursion classifies
      the `{:vdata,…}` domain by its family's declared level, no lossy round-trip).
    * `:ill_typed` — NEGATIVE CONTROL: `λs. Π(Dcoupled). Dec`, whose Π domain is a
      Dec VALUE (a constructor), NOT a type. The value-recursion must still reject
      it (`:bad_motive`); this proves the fix removes false negatives WITHOUT
      introducing false positives (accepting a non-type domain).
  """
  @spec motive_indexed_domain(:well_typed | :ill_typed) :: Challenge.t()
  def motive_indexed_domain(:well_typed) do
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

    challenge(
      :well_typed,
      [dec_family(), snat_family()],
      :motive_dom,
      def_type,
      body,
      "convoy motive λs. Π(SNat s). Dec — indexed family as Π domain (was false :bad_motive)"
    )
  end

  def motive_indexed_domain(:ill_typed) do
    neg_motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec, {:pi, Cure.Core.Grade.unrestricted(), {:ctor, :Dcoupled, []}, @dec}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:case, {:var, 0}, neg_motive, [{:Dcoupled, 0, {:type, 0}}, {:Causal, 0, {:type, 0}}]}}

    challenge(
      :ill_typed,
      [dec_family(), snat_family()],
      :motive_dom,
      @dec,
      body,
      "negative control: Π domain is a Dec value (Dcoupled), not a type → :bad_motive"
    )
  end

  # -- convoy soundness invariants (indexed with-clause LHS re-match) ----------
  #
  # The elaborator's convoy (indexed `with` LHS re-match, `elaborate_with_rematch`)
  # is a non-TCB fix that LEANS on two kernel properties. These antibodies are the
  # standing guards that they hold — a soundness gate the convoy requires even
  # though it edits no TCB code (`Quote.reify`'s `{:vdata}` split-collapse is
  # incompleteness, repaired only by re-eval / value-directed conv; the principled
  # repair is signature-aware reify, reach-pinned separately).

  @doc """
  SPLIT VALIDATION: the kernel checks a `{:data, name, params, indices}`
  application's slots against the family's param/index telescopes from the
  SIGNATURE (`check_spine`) — it does NOT trust a caller's split. `SNat` has 0
  params + 1 index.

    * `:well_typed` — correct split `{:data,:SNat,[],[Dcoupled]}` as a Π domain: accepted.
    * `:ill_typed`  — an index shoved into the PARAMS slot (`{:data,:SNat,[Dcoupled],[]}`):
      `check_def`'s `infer_sort` must reject it (`:arg_arity`). If the kernel ever
      trusted an (untrusted) caller's split blindly this replays `{:wrongly_accepted, _}`.
  """
  @spec data_split_validation(:well_typed | :ill_typed) :: Challenge.t()
  def data_split_validation(:well_typed) do
    dom = {:data, :SNat, [], [{:ctor, :Dcoupled, []}]}

    challenge(
      :well_typed,
      [dec_family(), snat_family()],
      :data_split,
      {:pi, Cure.Core.Grade.unrestricted(), dom, @dec},
      {:lam, Cure.Core.Grade.unrestricted(), dom, {:ctor, :Dcoupled, []}},
      "correct SNat split (0 params, 1 index) as a Π domain — accepted"
    )
  end

  def data_split_validation(:ill_typed) do
    bad = {:data, :SNat, [{:ctor, :Dcoupled, []}], []}

    challenge(
      :ill_typed,
      [dec_family(), snat_family()],
      :data_split,
      {:pi, Cure.Core.Grade.unrestricted(), bad, @dec},
      {:lam, Cure.Core.Grade.unrestricted(), bad, {:ctor, :Dcoupled, []}},
      "index in the PARAMS slot of a 0-param family — kernel must reject (:arg_arity)"
    )
  end

  @doc """
  REIFY-COLLAPSE INJECTIVITY: `Quote.reify` collapses `{:vdata,name,args}` →
  `{:data,name,args,[]}`, but that is INCOMPLETENESS, not unsoundness — `conv?` is
  value-directed and never equates two DISTINCT indexed types (even of the same
  arg-vector shape). `snat0 : SNat(Dcoupled)`.

    * `:well_typed` — `snat0` against `SNat(Dcoupled)`: accepted.
    * `:ill_typed`  — `snat0` against the DISTINCT (same-shape) `SNat(Causal)`:
      must be rejected. If the collapse ever let `conv?` equate distinct indexed
      types this replays `{:wrongly_accepted, _}`.
  """
  @spec reify_collapse_distinct(:well_typed | :ill_typed) :: Challenge.t()
  def reify_collapse_distinct(:well_typed) do
    challenge(
      :well_typed,
      [dec_family(), snat_family()],
      :reify_distinct,
      {:data, :SNat, [], [{:ctor, :Dcoupled, []}]},
      {:ctor, :snat0, []},
      "snat0 : SNat(Dcoupled) against SNat(Dcoupled) — accepted"
    )
  end

  def reify_collapse_distinct(:ill_typed) do
    challenge(
      :ill_typed,
      [dec_family(), snat_family()],
      :reify_distinct,
      {:data, :SNat, [], [{:ctor, :Causal, []}]},
      {:ctor, :snat0, []},
      "snat0 : SNat(Dcoupled) against distinct SNat(Causal) — must reject"
    )
  end

  # RETIRED (Phase C, primitive-identity retirement) — `reify_eq_indexed_reach`.
  #
  # This was the REACH PIN for the `Quote.reify` `{:vdata}` signature-gap on
  # primitive-Eq ENDPOINTS: a motive body `Eq(Type, SNat(x), SNat(x))` whose
  # `infer_type_value_sort({:veq,…})` clause reified the endpoints and
  # false-rejected `:bad_motive`. The pinned debt DISSOLVED rather than being
  # achieved: Phase C removed the `{:veq}` clause together with the primitive
  # `{:eq}`/`{:refl}` forms, so the code path the pin covered no longer exists.
  # The scenario itself (an equality of TYPES at carrier `Type 0`) is not
  # expressible on the inductive `Equivalent`, whose parameter lives in
  # `Type 0` — matching Idris/Agda, where type-level equations need universe
  # polymorphism Cure does not have. Value-level Equivalent motives (the
  # surviving analog) are exercised by `Generators.DepMatch.var_index(:eq)` and
  # `eqtype_motive_case`. The banked record (`reach_reify_split.sexp`) was
  # deleted in the same commit — its pieces encode grammar that no longer
  # parses; per the reach-pin migration contract a dissolved pin is removed,
  # never edited in place.

  # -- 4.5 impossible-branch discharge (no-confusion) -------------------------
  @doc """
  Impossible-branch discharge obligation. `wrap` builds `Ix Causal`; on an
  `Ix Dcoupled` scrutinee the branch is unreachable and its deliberately
  ill-typed body (`{:type,0}` where `Dec` is expected) must NOT be checked
  (`:well_typed`, discharged). The `:ill_typed` variant makes the SAME branch
  REACHABLE (scrutinee `Ix Causal`), so its body must be checked and rejected —
  the antibody that goes red if discharge ever over-fires on a live branch.
  """
  @spec discharge(:well_typed | :ill_typed) :: Challenge.t()
  def discharge(:well_typed) do
    ix_dcoupled = {:data, :Ix, [], [{:ctor, :Dcoupled, []}]}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :Ix, [], [{:var, 0}]}, @dec}}

    def_type = {:pi, Cure.Core.Grade.unrestricted(), ix_dcoupled, @dec}
    body = {:lam, Cure.Core.Grade.unrestricted(), ix_dcoupled, {:case, {:var, 0}, motive, [{:wrap, 1, {:type, 0}}]}}

    challenge(
      :well_typed,
      [dec_family(), ix_family()],
      :discharge,
      def_type,
      body,
      "impossible wrap branch (scrutinee Ix Dcoupled) discharged, body not checked"
    )
  end

  def discharge(:ill_typed) do
    ix_causal = {:data, :Ix, [], [{:ctor, :Causal, []}]}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :Ix, [], [{:var, 0}]}, @dec}}

    def_type = {:pi, Cure.Core.Grade.unrestricted(), ix_causal, @dec}
    body = {:lam, Cure.Core.Grade.unrestricted(), ix_causal, {:case, {:var, 0}, motive, [{:wrap, 1, {:type, 0}}]}}

    challenge(
      :ill_typed,
      [dec_family(), ix_family()],
      :discharge,
      def_type,
      body,
      "ill-typed: wrap branch REACHABLE (scrutinee Ix Causal), {:type,0} body must be rejected"
    )
  end

  # -- 4.6 constructor injectivity (spine descent) ----------------------------
  # Wr = MkWr(Dec): a unary wrapper, so an index can be constructor-headed WITH an
  # argument. IW(w:Wr) with iw:(p:Dec)->IW(MkWr Causal): the result index
  # MkWr(Causal) unifies with a scrutinee index MkWr(n) ONLY by descending through
  # the shared MkWr head (injectivity → unify_spine) to solve n := Causal. Without
  # injectivity the pair is :undecided and the equation is dropped.
  defp wr_family, do: {Inductive.family(:Wr, [], [], 0), [Inductive.ctor(:MkWr, [{:d, @dec}], [])]}

  defp iw_family,
    do:
      {Inductive.family(:IW, [], [{:w, @wr}], 0),
       [Inductive.ctor(:iw, [{:p, @dec}], [{:ctor, :MkWr, [{:ctor, :Causal, []}]}])]}

  # IW indexed by MkWr(var k).
  defp iw_mk(k), do: {:data, :IW, [], [{:ctor, :MkWr, [{:var, k}]}]}

  @doc """
  Constructor-injectivity obligation. `:well_typed` reuses an outer hypothesis
  `h : IW(MkWr n)` as `IW(MkWr Causal)` inside the `iw` branch — sound only
  because injectivity descends through `MkWr` to solve `n := Causal`. `:ill_typed`
  demands `IW(MkWr Dcoupled)` in the branch, an equation the match never
  entails (injectivity yields only `n := Causal`), so it must be rejected.
  """
  @spec injectivity(:well_typed | :ill_typed) :: Challenge.t()
  def injectivity(:well_typed) do
    def_type =
      {:pi, Cure.Core.Grade.unrestricted(), @dec,
       {:pi, Cure.Core.Grade.unrestricted(), iw_mk(0), {:pi, Cure.Core.Grade.unrestricted(), iw_mk(1), iw_mk(2)}}}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @wr,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :IW, [], [{:var, 0}]}, {:data, :IW, [], [{:var, 1}]}}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), iw_mk(0),
        {:lam, Cure.Core.Grade.unrestricted(), iw_mk(1), {:case, {:var, 0}, motive, [{:iw, 1, {:var, 2}}]}}}}

    challenge(
      :well_typed,
      [dec_family(), wr_family(), iw_family()],
      :inject,
      def_type,
      body,
      "n := Causal solved by descending through MkWr (injectivity); reuse h:IW(MkWr n) as IW(MkWr Causal)"
    )
  end

  def injectivity(:ill_typed) do
    iw_dcoupled = {:data, :IW, [], [{:ctor, :MkWr, [{:ctor, :Dcoupled, []}]}]}

    def_type =
      {:pi, Cure.Core.Grade.unrestricted(), @dec,
       {:pi, Cure.Core.Grade.unrestricted(), iw_mk(0), {:pi, Cure.Core.Grade.unrestricted(), iw_mk(1), iw_dcoupled}}}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @wr,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :IW, [], [{:var, 0}]}, iw_dcoupled}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), iw_mk(0),
        {:lam, Cure.Core.Grade.unrestricted(), iw_mk(1), {:case, {:var, 0}, motive, [{:iw, 1, {:var, 2}}]}}}}

    challenge(
      :ill_typed,
      [dec_family(), wr_family(), iw_family()],
      :inject,
      def_type,
      body,
      "ill-typed: injectivity yields only n:=Causal; body needs IW(MkWr Dcoupled) — must be rejected"
    )
  end

  # -- W3: deletion rule (pre-port banking spec §4 W3) -------------------------
  # IxN is indexed by a raw integer; wrapn's GROUND result index is the literal 3.
  # A scrutinee at `IxN 3` yields the index equation `3 ~ 3`, which no other
  # unifier clause consumes (not a var, not ctor/data-headed) — it is discharged
  # by the DELETION rule (r == s ⇒ consistent, kernel.ex `unify_one`). The branch
  # is therefore REACHABLE with no refinement.
  defp ixn_family,
    do:
      {Inductive.family(:IxN, [], [{:i, {:data, :Int, [], []}}], 0),
       [Inductive.ctor(:wrapn, [{:p, @dec}], [{:int_lit, 3}])]}

  @doc """
  Deletion-rule obligation. `:well_typed`: the reachable-via-deletion branch has a
  well-typed body and must be ACCEPTED — the antibody against deletion degrading
  to `:impossible` (which would discharge a live branch and, on the ill side,
  wrongly accept). `:ill_typed`: the same reachable branch with an ill-typed body
  (`{:type,0}` where `Dec` is expected) must be REJECTED — deletion must never
  skip the body check.
  """
  @spec deletion(:well_typed | :ill_typed) :: Challenge.t()
  def deletion(label) do
    ixn3 = {:data, :IxN, [], [{:int_lit, 3}]}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), {:data, :Int, [], []},
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :IxN, [], [{:var, 0}]}, @dec}}

    def_type = {:pi, Cure.Core.Grade.unrestricted(), ixn3, @dec}

    branch_body =
      case label do
        :well_typed -> {:ctor, :Dcoupled, []}
        :ill_typed -> {:type, 0}
      end

    body = {:lam, Cure.Core.Grade.unrestricted(), ixn3, {:case, {:var, 0}, motive, [{:wrapn, 1, branch_body}]}}

    challenge(
      label,
      [dec_family(), ixn_family()],
      :delete,
      def_type,
      body,
      "deletion rule: index equation 3 ~ 3 is consistent (r==s); branch reachable, body #{label}"
    )
  end

  defp challenge(label, families, name, def_type, def_body, note) do
    Challenge.new(
      kind: :indexed_case,
      assay: "indexed/case",
      label: label,
      payload: %{families: families, def_name: name, def_type: def_type, def_body: def_body},
      note: note,
      cover_tag: :"#{name}_#{label}"
    )
  end
end

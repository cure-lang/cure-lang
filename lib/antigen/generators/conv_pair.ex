defmodule Antigen.Generators.ConvPair do
  @moduledoc """
  Known-label generator for the `conv/decision` vertical (`Antigen.Assays.Conv`):
  pairs of closed-up-to-context Core terms with a correct-by-construction
  convertibility verdict, decided by `Cure.Core.Conv.conv?/5` against a context of
  fresh neutral variables (sig = nil, so globals stay opaque and δ is off).

  `conv?` is type-free (η is the §4.5 λ-vs-neutral trick), so these terms need not
  type-check — they only need to *evaluate* to the value shapes whose comparison
  clauses were otherwise cold: stuck projections/primitives (`conv_neutral?`'s
  `nfst`/`nsnd`/`nprim` + the head-mismatch fallback), η (λ-vs-neutral, λ-vs-λ,
  λ-vs-non-λ), Σ-pairs and `refl` (`conv_struct?`), and `same_value_no_delta?`'s
  recursion through a stuck application's argument (type/int/float/data/ctor/λ).
  """
  alias Antigen.{Gen, Challenge}

  # v0..v2: three free variables, materialised as fresh neutrals by the assay.
  @ctx 3

  @doc """
  Shape-coverage cells for the manifest gate (`Antigen.CoverManifest`). Each names
  one value-shape comparison this generator drives; the gate confirms every cell is
  actually produced by sampling `gen/0`.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for cell <- [
          :fst_distinct,
          :snd_distinct,
          :fst_vs_snd,
          :prim_spine_distinct,
          :eta_neutral_lam,
          :eta_lam_lam,
          :lam_vs_nonlam,
          :mk_pair_refl,
          :reflexive_refl,
          :fst_beta,
          :snd_beta,
          :var_neutral,
          :app_arg_type,
          :app_arg_int_type,
          :app_arg_int,
          :app_arg_float_type,
          :app_arg_float,
          :app_arg_data,
          :app_arg_ctor,
          :app_arg_lam,
          :app_arg_nat,
          :nat_refl,
          :nat_distinct,
          :nat_vs_tower,
          :tower_vs_nat,
          :neutral_head_mismatch
        ],
        do: {"conv/decision", cell}
  end

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(shape(), fn {t1, t2, expect, note, cell} ->
      Gen.return(
        Challenge.new(
          kind: :conv_pair,
          assay: "conv/decision",
          label: if(expect, do: :convertible, else: :distinct),
          payload: %{t1: t1, t2: t2, ctx: @ctx, expect: expect},
          note: note,
          cover_tag: cell
        )
      )
    end)
  end

  defp v(i), do: {:var, i}

  # Σ(Nat, const-Nat) and its single-branch ι-on-case projections (replacing the
  # retired primitive {:fst,_}/{:snd,_}). conv? is type-free, so the closed Sigma
  # motive only supplies the mk_pair branch shape the projection eliminates.
  defp sig,
    do:
      {:data, :Sigma,
       [{:data, :Nat, [], []}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}}],
       []}

  defp pfst(p),
    do: {:case, p, {:lam, Cure.Core.Grade.unrestricted(), sig(), {:data, :Nat, [], []}}, [{:mk_pair, 2, {:var, 1}}]}

  defp psnd(p),
    do: {:case, p, {:lam, Cure.Core.Grade.unrestricted(), sig(), {:data, :Nat, [], []}}, [{:mk_pair, 2, {:var, 0}}]}

  defp shape do
    Gen.frequency([
      # -- stuck-neutral discrimination (conv_neutral?) --
      {2, ret(pfst(v(0)), pfst(v(1)), false, "ι-on-case first component, distinct inner (135)", :fst_distinct)},
      {2, ret(psnd(v(0)), psnd(v(1)), false, "ι-on-case second component, distinct inner (136)", :snd_distinct)},
      {2,
       ret(pfst(v(0)), psnd(v(0)), false, "case first vs second component, branch-body mismatch (150)", :fst_vs_snd)},
      {2,
       ret(
         {:app, {:app, {:global, :int_add}, v(0)}, v(1)},
         {:app, {:app, {:global, :int_add}, v(0)}, v(2)},
         false,
         "builtin-op spine distinct arg (napp congruence, K2 §1.8)",
         :prim_spine_distinct
       )},
      # -- η (conv_struct? RHS-λ + eta_eq?) --
      {2,
       ret(
         v(0),
         {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:app, v(1), v(0)}},
         true,
         "η neutral-vs-λ (70,108)",
         :eta_neutral_lam
       )},
      {2,
       ret(
         {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, v(1)},
         {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, v(1)},
         true,
         "λ-vs-λ η (107)",
         :eta_lam_lam
       )},
      {2,
       ret(
         {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, v(1)},
         {:type, 0},
         false,
         "λ-vs-non-λ (109)",
         :lam_vs_nonlam
       )},
      # -- Σ-pair / refl (conv_struct?) --
      {2,
       ret(
         {:ctor, :mk_pair, [v(0), v(1)]},
         {:ctor, :mk_pair, [v(0), v(1)]},
         true,
         "mk_pair reflexive (83)",
         :mk_pair_refl
       )},
      {2,
       ret(
         {:ctor, :reflexive, [v(0)]},
         {:ctor, :reflexive, [v(0)]},
         true,
         "reflexive-ctor reflexive (102)",
         :reflexive_refl
       )},
      # -- β for projections: fst/snd of an actual pair reduce (Eval vfst/vsnd) --
      {2,
       ret(pfst({:ctor, :mk_pair, [v(0), v(1)]}), v(0), true, "case (mk_pair a b) first → a (ι-on-case)", :fst_beta)},
      {2,
       ret(psnd({:ctor, :mk_pair, [v(0), v(1)]}), v(1), true, "case (mk_pair a b) second → b (ι-on-case)", :snd_beta)},
      # -- an out-of-context de Bruijn var evaluates to a fresh neutral (Eval :var nil arm) --
      {1, ret({:var, 5}, {:var, 5}, true, "out-of-ctx var → neutral (eval)", :var_neutral)},
      # -- same_value_no_delta? over a stuck app's argument --
      {1, app_refl({:type, 0}, "vtype (187)", :app_arg_type)},
      {1, app_refl({:int_type}, "vint_type (188)", :app_arg_int_type)},
      {1, Gen.bind(Gen.int(-9, 9), fn k -> app_refl({:int_lit, k}, "vint (189)", :app_arg_int) end)},
      {1, app_refl({:float_type}, "vfloat_type (190)", :app_arg_float_type)},
      {1, Gen.bind(Gen.int(-9, 9), fn k -> app_refl({:float_lit, k / 2}, "vfloat (191)", :app_arg_float) end)},
      {1, app_refl({:data, :Nat, [], []}, "vdata (193)", :app_arg_data)},
      {1, app_refl({:ctor, :Z, []}, "vctor (196)", :app_arg_ctor)},
      {1,
       app_refl(
         {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:type, 0}},
         "vλ fallback → conv_struct η (199)",
         :app_arg_lam
       )},
      # -- compact-Nat conversion (conv_struct? 85/88/91, same_value_no_delta? 194) --
      # The definitional-equality bridge between a compact `{:nat_lit,n}` and its
      # n-fold S/Z tower, both directions, plus the neutral-spine no-δ fast path on
      # a nat-literal argument. This is the conversion-layer sibling of the audited
      # compact-lit↔tower unifier bridge; previously never exercised by any generator.
      {1, app_refl({:nat_lit, 3}, "vnat no-δ fast path (194)", :app_arg_nat)},
      {2, ret({:nat_lit, 2}, {:nat_lit, 2}, true, "compact-nat reflexive (85)", :nat_refl)},
      {2, ret({:nat_lit, 2}, {:nat_lit, 3}, false, "compact-nat distinct literals (85)", :nat_distinct)},
      {2, ret({:nat_lit, 1}, s_tower(1), true, "compact-lit vs S/Z tower (88)", :nat_vs_tower)},
      {2, ret(s_tower(2), {:nat_lit, 2}, true, "S/Z tower vs compact-lit (91)", :tower_vs_nat)},
      # -- structurally-distinct stuck neutrals (conv_neutral? head-mismatch, 146) --
      {2, ret(v(0), {:app, v(1), {:type, 0}}, false, "nvar vs napp head mismatch (146)", :neutral_head_mismatch)}
    ])
  end

  # The n-fold successor tower over Z: `S (S (… Z))`, the ctor-spelling counterpart
  # of `{:nat_lit, n}`. Evaluates to the `{:vctor, :S, [{:vctor, :Z, []}]}`-shaped
  # value `Eval.nat_to_ctor/1` peels a compact literal into.
  defp s_tower(0), do: {:ctor, :Z, []}
  defp s_tower(n) when n > 0, do: {:ctor, :S, [s_tower(n - 1)]}

  # `v0 arg` compared to itself: same_neutral_no_delta? recurses through the napp
  # spine into same_value_no_delta? on the argument value.
  defp app_refl(arg, note, cell) do
    t = {:app, v(0), arg}
    ret(t, t, true, "app-arg " <> note, cell)
  end

  defp ret(t1, t2, expect, note, cell), do: Gen.return({t1, t2, expect, note, cell})
end

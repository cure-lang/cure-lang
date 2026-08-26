defmodule Antigen.Generators.IndexedDecl do
  @moduledoc """
  Parametric generator for **indexed-family declaration checking** — the
  `Kernel.check_ctor` pipeline (`check_ctor_args` → `check_uniform_params` →
  `check_result_indices`), which validates a constructor against its family's
  parameter/index telescopes at DECLARE time. Distinct from `Generators.DepMatch`,
  which drives index unification at case-MATCH time. No live generator reached this
  path before — the universes `:family` probes were all non-indexed and nullary.

  Emits `:family` universes challenges (assay `"universes"`, oracle = known label)
  over builtin literal index types (Int / Float), so each single-family challenge
  needs no auxiliary declarations. Four shapes:

    * **nullary** `IdxI : (n:T) -> Type0`, ctor `mki : IdxI <lit>` — result-index
      count/type checking (`check_result_indices`: success, wrong-type, wrong-arity).
    * **arg-bearing** ctor `mki : (x:T) -> IdxI <lit>` — a field telescope, so
      `check_ctor_args` infers each field's sort.
    * **parameterized (uniform)** `P : (a:Type0) -> (n:T) -> Type0`, ctor
      `pc : (x:a) -> P a <lit>` with `result_params = [a]` — `check_uniform_params`
      accepts the uniform parameter.
    * **parameterized (non-uniform)** the same but `result_params = [x]` (a
      non-parameter var) — `check_uniform_params` rejects (ill_typed).

  Every known label is correct by construction and cross-checked against the kernel
  in the generator's test.
  """
  alias Antigen.{Gen, Challenge}
  alias Cure.Core.Inductive

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`). This generator shares the
  `"universes"` assay id with `Generators.Universes`, so its cells carry a distinct
  `:idx_` prefix (indexed-declaration shapes) and union with that participant's
  cells in the manifest. One cell per `check_ctor` verdict-branch `shape/1` builds.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for cell <- [
          :idx_nullary_match,
          :idx_nullary_mistype,
          :idx_nullary_arity,
          :idx_argbearing_ok,
          :idx_argbearing_nontype,
          :idx_param_uniform,
          :idx_param_nonuniform,
          :idx_param_arity,
          :idx_dependent_eq
        ],
        do: {"universes", cell}
  end

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of([:int, :float]), fn kind ->
      Gen.bind(shape(kind), fn {fam, label, ctors, note, cell} ->
        Gen.return(
          Challenge.new(
            kind: :family,
            assay: "universes",
            label: label,
            cover_tag: cell,
            payload: %{family: fam, ctors: ctors},
            note: note
          )
        )
      end)
    end)
  end

  defp shape(kind) do
    Gen.frequency([
      {3, nullary(kind)},
      {2, arg_bearing(kind)},
      {2, param(kind, :uniform)},
      {1, param(kind, :non_uniform)},
      {1, param(kind, :arity)},
      {2, dependent_eq()}
    ])
  end

  # MyEqK : (a:Type0) -> (x0:a) -> ... -> (x_{k-1}:a) -> Type0 with a ctor
  # mreflK : (w:a) -> MyEqK a w ... w — the single generalized field w:a written
  # into every result-index position. Each index-telescope TYPE references the
  # parameter (index i has type a = {:var, i}, the param shifted past i preceding
  # indices), so `check_result_indices` must seed do_spine with the parameter
  # value. With a Type param AND the var repeated across ≥2 indices this is the
  # exact shape that tripped the de Bruijn seeding bug (the dp01/dp02 datatype).
  # Correct label :well_typed; cross-checked against the kernel in the gen test.
  defp dependent_eq do
    Gen.bind(Gen.member_of([2, 3]), fn k ->
      indices = for i <- 0..(k - 1), do: {:n, {:var, i}}
      fam = Inductive.family(:MyEqK, [{:a, {:type, 0}}], indices, 0)
      ctor = Inductive.ctor(:mreflK, [{:w, {:var, 0}}], List.duplicate({:var, 0}, k), [:many], [{:var, 1}])

      Gen.return(
        {fam, :well_typed, [ctor], "dependent #{k}-index family, generalized var repeated (Type param)",
         :idx_dependent_eq}
      )
    end)
  end

  # IdxI : (n:T) -> Type0 with a nullary ctor, result-index checking only.
  defp nullary(kind) do
    fam = idxi(kind)

    Gen.frequency([
      {3, ctor_result(fam, :well_typed, :mki, single(lit(kind)), "nullary matching index", :idx_nullary_match)},
      {2,
       ctor_result(
         fam,
         :ill_typed,
         :mkb,
         single(lit(other(kind))),
         "nullary mismatched-type index",
         :idx_nullary_mistype
       )},
      {1, ctor_result(fam, :ill_typed, :mkb, arity_indices(kind), "nullary wrong-arity index", :idx_nullary_arity)}
    ])
  end

  # IdxI : (n:T) -> Type0 with an arg-bearing ctor mki : (x:T) -> IdxI <lit>.
  # The ill twin gives the field a non-type (a literal in type position), so
  # `check_ctor_args`' `infer_sort` rejects it (:not_a_type → the halt branch).
  defp arg_bearing(kind) do
    fam = idxi(kind)

    Gen.frequency([
      {2,
       Gen.bind(lit(kind), fn v ->
         ctor = Inductive.ctor(:mki, [{:x, itype(kind)}], [v])
         Gen.return({fam, :well_typed, [ctor], "arg-bearing ctor (x:#{kind}) -> IdxI", :idx_argbearing_ok})
       end)},
      {1,
       Gen.bind(lit(kind), fn v ->
         # field type is a value, not a type ⇒ infer_sort halts in check_ctor_args
         ctor = Inductive.ctor(:mki, [{:x, lit_of(kind)}], [v])
         Gen.return({fam, :ill_typed, [ctor], "arg-bearing ctor with non-type field", :idx_argbearing_nontype})
       end)}
    ])
  end

  # P : (a:Type0) -> (n:T) -> Type0 with ctor pc : (x:a) -> P a <lit>.
  # uniform: result_params = [a] (var 1 in ctx_full = [a, x]); non_uniform: [x] (var 0).
  defp param(kind, uniformity) do
    fam = Inductive.family(:P, [{:a, {:type, 0}}], [{:n, itype(kind)}], 0)
    # result_params: [a]=uniform (accept); [x]=non-uniform var (reject); []=wrong
    # count (check_uniform_params' arity branch).
    {rparams, label, note, cell} =
      case uniformity do
        :uniform -> {[{:var, 1}], :well_typed, "parameterized uniform (result param = a)", :idx_param_uniform}
        :non_uniform -> {[{:var, 0}], :ill_typed, "parameterized non-uniform (result param = x)", :idx_param_nonuniform}
        :arity -> {[], :ill_typed, "parameterized wrong result-param arity", :idx_param_arity}
      end

    Gen.bind(lit(kind), fn v ->
      ctor = Inductive.ctor(:pc, [{:x, {:var, 0}}], [v], [:many], rparams)
      Gen.return({fam, label, [ctor], note, cell})
    end)
  end

  # A literal VALUE of the given kind (used as a non-type in a field-type position).
  defp lit_of(:int), do: {:int_lit, 0}
  defp lit_of(:float), do: {:float_lit, 0.0}

  defp ctor_result(fam, label, cname, indices_gen, note, cell) do
    Gen.bind(indices_gen, fn is ->
      Gen.return({fam, label, [Inductive.ctor(cname, [], is)], note, cell})
    end)
  end

  defp idxi(kind), do: Inductive.family(:IdxI, [], [{:n, itype(kind)}], 0)

  defp itype(:int), do: {:data, :Int, [], []}
  defp itype(:float), do: {:float_type}

  defp single(lit_gen), do: Gen.bind(lit_gen, fn v -> Gen.return([v]) end)

  # 0 or 2 matching-type indices (both wrong against the single-index telescope)
  defp arity_indices(kind) do
    Gen.frequency([
      {1, Gen.return([])},
      {1, Gen.bind(lit(kind), fn a -> Gen.bind(lit(kind), fn b -> Gen.return([a, b]) end) end)}
    ])
  end

  defp other(:int), do: :float
  defp other(:float), do: :int

  defp lit(:int), do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:int_lit, n}) end)
  defp lit(:float), do: Gen.bind(Gen.int(-9, 9), fn n -> Gen.return({:float_lit, n / 2}) end)
end

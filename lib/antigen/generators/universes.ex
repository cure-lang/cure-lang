defmodule Antigen.Generators.Universes do
  @moduledoc """
  Known-label universe-rule challenges (pre-port banking spec §4 W5): the
  unbounded predicative finite hierarchy (`Cure.Core.Sort`), no
  Type-in-Type, dependent family formation, and the constructor-field rule —
  roadmap #20's rules, previously with zero Antigen coverage (A4).

  Def-shaped probes reuse the `:indexed_case` record shape (families + one def,
  checked by `Kernel.check_def`); family-shaped probes (formation/ctor fields) use the
  `:family` shape (checked by `Kernel.check_family` + `check_ctor`). Labels are
  `:well_typed`/`:ill_typed`, correct by construction (argument in each @doc).
  """
  alias Antigen.{Challenge, Gen}
  alias Cure.Core.{Env, Inductive, Sort}

  @nat {:data, :Nat, [], []}

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`). Family formation has its
  own positive/negative cells, distinct from definition and constructor checks.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for cell <- [
          :type_in_type,
          :finite_successor_pos,
          :finite_successor_neg,
          :cumulativity,
          :stratification,
          :ctor_field_pos,
          :ctor_field_neg,
          :indexed_ctor_pos,
          :indexed_ctor_neg,
          :family_formation_pos,
          :family_formation_neg
        ],
        do: {"universes", cell}
  end

  @doc """
  Uniform sampleable generator over the vertical's named constructors (the universes
  vertical is otherwise curated / seed-test–fed). Used by the coverage-manifest gate
  to confirm every declared cell is actually produced.
  """
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.member_of([
      type_in_type(:ill_typed),
      finite_successor(:well_typed),
      finite_successor(:ill_typed),
      cumulativity(:well_typed),
      stratification(:well_typed),
      ctor_field(:well_typed, 37),
      ctor_field(:ill_typed, 37),
      indexed_ctor(:well_typed),
      indexed_ctor(:ill_typed),
      family_formation(:well_typed),
      family_formation(:ill_typed)
    ])
  end

  defp nat_family,
    do:
      {Inductive.family(:Nat, [], [], Cure.Core.Sort.finite_closed(0)),
       [Inductive.ctor(:Z, [], []), Inductive.ctor(:S, [{:n, @nat}], [])]}

  @doc "Girard guard: `def u : Type 0 = Type 0` must reject — Type 0's least sort is Type 1."
  @spec type_in_type(:ill_typed) :: Challenge.t()
  def type_in_type(:ill_typed) do
    def_challenge(
      :ill_typed,
      [],
      {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}},
      {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}},
      "Type-in-Type: Type 0 : Type 0 must reject (Type 0 : Type 1)",
      :type_in_type
    )
  end

  @doc """
  Finite successor discrimination: `Type k : Type (k+1)` is accepted, but
  `Type k : Type k` is rejected. Every finite annotation has a successor;
  there is no largest finite universe.
  """
  @spec finite_successor(:well_typed | :ill_typed, non_neg_integer()) :: Challenge.t()
  def finite_successor(label, level \\ 37)
      when label in [:well_typed, :ill_typed] and is_integer(level) and level >= 0 do
    annotation = if label == :well_typed, do: level + 1, else: level

    def_challenge(
      label,
      [],
      {:type, Sort.finite_closed(annotation)},
      {:type, Sort.finite_closed(level)},
      "finite successor: Type #{level} checked at Type #{annotation}, #{label}",
      if(label == :well_typed, do: :finite_successor_pos, else: :finite_successor_neg)
    )
  end

  @doc "Cumulativity: `Nat : Type 0` accepted at `Type 1` (`Type 0 <: Type 1`)."
  @spec cumulativity(:well_typed) :: Challenge.t()
  def cumulativity(:well_typed) do
    def_challenge(
      :well_typed,
      [nat_family()],
      {:type, {:finite, %Cure.Core.UniverseLevel{constant: 1, atoms: []}}},
      @nat,
      "cumulativity: Nat (level 0) accepted at Type 1",
      :cumulativity
    )
  end

  @doc "Exact stratification: `def u : Type 1 = Type 0` accepted."
  @spec stratification(:well_typed) :: Challenge.t()
  def stratification(:well_typed) do
    def_challenge(
      :well_typed,
      [],
      {:type, {:finite, %Cure.Core.UniverseLevel{constant: 1, atoms: []}}},
      {:type, {:finite, %Cure.Core.UniverseLevel{constant: 0, atoms: []}}},
      "stratification: Type 0 : Type 1 accepted",
      :stratification
    )
  end

  @doc """
  Two-universe constructor-field rule (`Kernel.check_ctor` → `:universe_level`):
  a field of type `Type k` has sort level k+1, so it fits a level-(k+1)
  family (`:well_typed`) and does NOT fit a level-k family (`:ill_typed`).
  """
  @spec ctor_field(:well_typed | :ill_typed, non_neg_integer()) :: Challenge.t()
  def ctor_field(label, level \\ 0)
      when label in [:well_typed, :ill_typed] and is_integer(level) and level >= 0 do
    family_level = if label == :well_typed, do: level + 1, else: level
    fam = Inductive.family(:Foo, [], [], Sort.finite_closed(family_level))
    ctors = [Inductive.ctor(:MkFoo, [{:x, {:type, Sort.finite_closed(level)}}], [])]

    Challenge.new(
      kind: :family,
      assay: "universes",
      label: label,
      payload: %{family: fam, ctors: ctors},
      note: "predicativity: field x : Type #{level} (sort #{level + 1}) vs family level #{family_level}",
      cover_tag: if(label == :well_typed, do: :ctor_field_pos, else: :ctor_field_neg)
    )
  end

  @doc """
  Indexed-constructor result-index check (`Kernel.check_ctor` → `check_result_indices`).
  `IdxI : (n:Int) -> Type0` is indexed by the builtin Int (so the single-family
  challenge needs no extra declarations). `mki : IdxI 7` is well-formed — its result
  index `7` is checked against the Int telescope through the result-index spine.
  The `:ill_typed` twin `mkb : IdxI 1.5` pins a Float result index against the Int
  telescope, which must reject (`conversion_failure`). This is the only family-shaped
  probe whose constructor carries a result index, so it is the sole driver of the
  `check_result_indices` success path.
  """
  @spec indexed_ctor(:well_typed | :ill_typed) :: Challenge.t()
  def indexed_ctor(label) do
    # Post-2026-07-18 surface flip, `Int` is the inductive family
    # `Int = FromNat(Nat) | NegativeSuccessor(Nat)`; the index type is that family, and
    # the compact result-index literal `7` inhabits it via `int_type_value`. The run
    # env (Antigen.Assays.Universes) seeds the bare `:nat`/`:int` builtins this needs.
    fam = Inductive.family(:IdxI, [], [{:n, {:data, :Int, [], []}}], Cure.Core.Sort.finite_closed(0))

    ctors =
      case label do
        :well_typed -> [Inductive.ctor(:mki, [], [{:int_lit, 7}])]
        :ill_typed -> [Inductive.ctor(:mkb, [], [{:float_lit, 1.5}])]
      end

    Challenge.new(
      kind: :family,
      assay: "universes",
      label: label,
      payload: %{family: fam, ctors: ctors},
      note: "indexed ctor result-index check: IdxI (n:Int), #{label}",
      cover_tag: if(label == :well_typed, do: :indexed_ctor_pos, else: :indexed_ctor_neg)
    )
  end

  @doc """
  Genuine dependent family formation. After parameters `a : Type k, x : a`,
  an index `y : a` is well-formed, but `y : x` is not: the value `x` is not a
  type. Both inputs use canonical sorts and scoped variables, so the negative
  reaches `check_family`'s telescope typing, not a serializer/encoding guard.
  No constructors are present: bypassing `check_family` cannot be masked by
  `check_ctor` independently rechecking the family.
  """
  @spec family_formation(:well_typed | :ill_typed, non_neg_integer()) :: Challenge.t()
  def family_formation(label, level \\ 37)
      when label in [:well_typed, :ill_typed] and is_integer(level) and level >= 0 do
    index = if label == :well_typed, do: 1, else: 0
    sort = Sort.finite_closed(level)
    fam = Inductive.family(:Over, [a: {:type, sort}, x: {:var, 0}], [y: {:var, index}], sort)

    Challenge.new(
      kind: :family,
      assay: "universes",
      label: label,
      payload: %{family: fam, ctors: []},
      note: "dependent family formation at Type #{level}: index y uses #{if index == 1, do: "type a", else: "value x"}",
      cover_tag: if(label == :well_typed, do: :family_formation_pos, else: :family_formation_neg)
    )
  end

  @doc "Rebuild the Env for a def-shaped universes challenge."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{kind: :indexed_case, payload: %{families: families, def_name: dn, def_type: dt, def_body: db}}) do
    env = Enum.reduce(families, Env.empty(), fn {fam, ctors}, e -> Inductive.declare(e, fam, ctors) end)
    Env.add_def(env, dn, dt, db)
  end

  defp def_challenge(label, families, def_type, def_body, note, cell) do
    Challenge.new(
      kind: :indexed_case,
      assay: "universes",
      label: label,
      payload: %{families: families, def_name: :u, def_type: def_type, def_body: def_body},
      note: note,
      cover_tag: cell
    )
  end
end

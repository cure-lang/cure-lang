defmodule Antigen.Generators.Universes do
  @moduledoc """
  Known-label universe-rule challenges (pre-port banking spec §4 W5): the fixed
  cumulative hierarchy `Type 0 : Type 1 : Type 2` (`Cure.Core.Universe`), no
  Type-in-Type, the ceiling, and the two-universe constructor-field rule —
  roadmap #20's rules, previously with zero Antigen coverage (A4).

  Def-shaped probes reuse the `:indexed_case` record shape (families + one def,
  checked by `Kernel.check_def`); family-shaped probes (ctor fields) use the
  `:family` shape (checked by `Kernel.check_family` + `check_ctor`). Labels are
  `:well_typed`/`:ill_typed`, correct by construction (argument in each @doc).
  """
  alias Antigen.{Challenge, Gen}
  alias Cure.Core.{Env, Inductive, Universe}

  @nat {:data, :Nat, [], []}

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`). `:family_ceiling` is the
  family-level ceiling cell — `check_family`'s declared-level range-check, which had
  no coverage because every ceiling probe was def-shaped (`check_def`).
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for cell <- [
          :type_in_type,
          :ceiling_def,
          :cumulativity,
          :stratification,
          :ctor_field_pos,
          :ctor_field_neg,
          :indexed_ctor_pos,
          :indexed_ctor_neg,
          :family_ceiling
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
      ceiling(:ill_typed),
      cumulativity(:well_typed),
      stratification(:well_typed),
      ctor_field(:well_typed),
      ctor_field(:ill_typed),
      indexed_ctor(:well_typed),
      indexed_ctor(:ill_typed),
      family_ceiling(:ill_typed)
    ])
  end

  defp nat_family,
    do: {Inductive.family(:Nat, [], [], 0), [Inductive.ctor(:Z, [], []), Inductive.ctor(:S, [{:n, @nat}], [])]}

  @doc "Girard guard: `def u : Type 0 = Type 0` must be rejected — Type 0 inhabits Type 1 only."
  @spec type_in_type(:ill_typed) :: Challenge.t()
  def type_in_type(:ill_typed) do
    def_challenge(
      :ill_typed,
      [],
      {:type, 0},
      {:type, 0},
      "Type-in-Type: Type 0 : Type 0 must reject (Type 0 : Type 1)",
      :type_in_type
    )
  end

  @doc """
  Ceiling: `def u : Type 2 = Type 1` must be rejected — a def's TYPE must itself
  be well-sorted, and `Type 2` has no successor sort in the fixed 0..2 hierarchy
  (`Universe.succ/1` → `:universe_ceiling`). The ceiling is a classifier of last
  resort, not an annotatable def type.
  """
  @spec ceiling(:ill_typed) :: Challenge.t()
  def ceiling(:ill_typed) do
    def_challenge(
      :ill_typed,
      [],
      {:type, 2},
      {:type, 1},
      "ceiling: Type 2 has no sort — a def cannot be annotated AT Type 2",
      :ceiling_def
    )
  end

  @doc "Cumulativity: `Nat : Type 0` accepted at `Type 1` (`Type 0 <: Type 1`)."
  @spec cumulativity(:well_typed) :: Challenge.t()
  def cumulativity(:well_typed) do
    def_challenge(
      :well_typed,
      [nat_family()],
      {:type, 1},
      @nat,
      "cumulativity: Nat (level 0) accepted at Type 1",
      :cumulativity
    )
  end

  @doc "Exact stratification: `def u : Type 1 = Type 0` accepted."
  @spec stratification(:well_typed) :: Challenge.t()
  def stratification(:well_typed) do
    def_challenge(:well_typed, [], {:type, 1}, {:type, 0}, "stratification: Type 0 : Type 1 accepted", :stratification)
  end

  @doc """
  Two-universe constructor-field rule (`Kernel.check_ctor` → `:universe_level`):
  a field of type `Type 0` has sort level 1, so it fits a level-1 family
  (`:well_typed`) and does NOT fit a level-0 family (`:ill_typed`).
  """
  @spec ctor_field(:well_typed | :ill_typed) :: Challenge.t()
  def ctor_field(label) do
    level = if label == :well_typed, do: 1, else: 0
    fam = Inductive.family(:Foo, [], [], level)
    ctors = [Inductive.ctor(:MkFoo, [{:x, {:type, 0}}], [])]

    Challenge.new(
      kind: :family,
      assay: "universes",
      label: label,
      payload: %{family: fam, ctors: ctors},
      note: "two-universe rule: field x : Type 0 (sort level 1) vs family level #{level}",
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
    fam = Inductive.family(:IdxI, [], [{:n, {:data, :Int, [], []}}], 0)

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
  Family universe ceiling (`Kernel.check_family` → `:universe_ceiling`): a family
  declared AT a level above the fixed predicative ceiling (`Type0 : Type1 : Type2`)
  contradicts the hierarchy the rest of the kernel enforces and must be rejected.
  `check_family` originally validated only the param/index telescopes and never
  range-checked the declared `level`, so an over-ceiling family was admitted — the
  family-level twin of the def-shaped `ceiling/1` probe (which pins `check_def`).
  `Over` is declared at `Universe.ceiling() + 1`. Label `:ill_typed`.
  """
  @spec family_ceiling(:ill_typed) :: Challenge.t()
  def family_ceiling(:ill_typed) do
    fam = Inductive.family(:Over, [], [], Universe.ceiling() + 1)
    ctors = [Inductive.ctor(:MkOver, [], [])]

    Challenge.new(
      kind: :family,
      assay: "universes",
      label: :ill_typed,
      payload: %{family: fam, ctors: ctors},
      note: "family declared at Type #{Universe.ceiling() + 1} (above the ceiling) must reject",
      cover_tag: :family_ceiling
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

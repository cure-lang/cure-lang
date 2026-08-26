defmodule Antigen.CoverManifest do
  @moduledoc """
  Shape-coverage manifest for the Antigen assays (design
  `docs/superpowers/specs/2026-07-10-antigen-coverage-manifest-design.md`).

  Kernel *line* coverage (`Antigen.Cover`) and the plateauing dedup key
  (`Antigen.Coverage`) both went green while four soundness findings were live,
  because the vulnerable clause was executed / the shape was collapsed into an
  existing cell. This manifest tracks something finer: each participating generator
  declares the set of soundness-relevant *shape cells* it is responsible for
  producing (`cover_cells/0 :: [{assay_id, cell}]`), and stamps each challenge with a
  `cover_tag`. The coverage-manifest gate samples every participant and fails when a
  declared cell is never produced — the level at which the four findings would have
  been caught (each was a declared-cell-with-zero-hits waiting to happen).

  A generator is a **participant** iff it declares `cover_cells/0` and exposes a
  sampleable `gen/0`. Cell-completeness is checked only for participants; assay-level
  firing is checked for every registered assay by the gate (`Antigen.Runner.registered_assays/0`).
  """
  alias Antigen.Backend.StreamData, as: B

  alias Antigen.Generators.{
    Positivity,
    Totality,
    BranchUnify,
    Universes,
    Malformed,
    ConvPair,
    CheckMode,
    DeltaReduce,
    BetaSubst,
    ZetaSubst,
    GradeConv,
    EffectInert,
    DotForcing,
    Forcing,
    DecodeProbe,
    TypeFormer,
    IndexedDecl,
    ElabComplete,
    ElabDotForcing,
    ElabErasure,
    ElabGuardLint,
    ElabNatRep,
    ElabLiteralTyping,
    Indexed,
    Rewrite,
    ClosureEnv,
    Conversion,
    ErasureTerm,
    KernelProbe
  }

  # Generator modules under the shape-coverage manifest. Each declares the
  # soundness-relevant shape cells it is responsible for producing; the gate fails
  # if any declared cell is never generated. Free random-term generators
  # (Serialization, Term, DepMatch, Equality, Primitive, Context) are deliberately
  # NOT here — they have no discrete enumerable shape menu and are covered by the
  # health metrics instead; a fake cell over a continuous space is worse than none.
  @participants [
    Positivity,
    Totality,
    BranchUnify,
    Universes,
    Malformed,
    ConvPair,
    CheckMode,
    DeltaReduce,
    BetaSubst,
    ZetaSubst,
    GradeConv,
    EffectInert,
    DotForcing,
    Forcing,
    DecodeProbe,
    TypeFormer,
    IndexedDecl,
    ElabComplete,
    ElabDotForcing,
    ElabErasure,
    ElabGuardLint,
    ElabNatRep,
    ElabLiteralTyping,
    Indexed,
    Rewrite,
    ClosureEnv,
    Conversion,
    ErasureTerm,
    KernelProbe
  ]

  @doc "The generator modules under the shape-coverage manifest."
  @spec participants() :: [module()]
  def participants, do: @participants

  @doc "Every `{assay_id, cell}` point the participants declare they must cover."
  @spec expected() :: MapSet.t({String.t(), atom()})
  def expected do
    @participants |> Enum.flat_map(& &1.cover_cells()) |> MapSet.new()
  end

  @doc """
  Sample each participant's `gen/0` (`draws` draws apiece) and collect the
  `{assay_id, cover_tag}` points actually produced (tagged challenges only).
  """
  @spec hit_points(pos_integer()) :: MapSet.t({String.t(), atom()})
  def hit_points(draws \\ 600) do
    for mod <- @participants,
        c <- B.interp(mod.gen()) |> Enum.take(draws),
        not is_nil(c.cover_tag),
        into: MapSet.new(),
        do: {c.assay, c.cover_tag}
  end

  @doc "Declared points that no draw produced — empty iff the manifest is fully covered."
  @spec missing(pos_integer()) :: MapSet.t({String.t(), atom()})
  def missing(draws \\ 600), do: MapSet.difference(expected(), hit_points(draws))

  @stash_key {__MODULE__, :coverage_summary}

  @type miss :: %{assay: String.t(), cell: atom(), generator: module() | nil}
  @type summary :: %{
          expected: non_neg_integer(),
          produced: non_neg_integer(),
          missing: MapSet.t({String.t(), atom()}),
          missing_detail: [miss()],
          assays: [String.t()]
        }

  @doc """
  Full shape-coverage summary — sampled once, `draws` per participant. As a side
  effect it stashes the result in `persistent_term` so the suite-end report
  (`report/0`, called from `after_suite` in `test/test_helper.exs`) can surface it
  with no extra sampling. The coverage-manifest gate calls this, so a normal
  `mix test` populates the stash exactly once.
  """
  @spec summary(pos_integer()) :: summary()
  def summary(draws \\ 600) do
    expected = expected()
    missing = MapSet.difference(expected, hit_points(draws))

    declarers =
      for mod <- @participants, point <- mod.cover_cells(), into: %{}, do: {point, mod}

    missing_detail =
      missing
      |> Enum.map(fn {assay, cell} = point ->
        %{assay: assay, cell: cell, generator: Map.get(declarers, point)}
      end)
      |> Enum.sort_by(&{&1.assay, to_string(&1.cell)})

    s = %{
      expected: MapSet.size(expected),
      produced: MapSet.size(expected) - MapSet.size(missing),
      missing: missing,
      missing_detail: missing_detail,
      assays: participant_assays()
    }

    :persistent_term.put(@stash_key, s)
    s
  end

  @doc "The summary stashed by the most recent `summary/1` call this run, or nil."
  @spec stashed_summary() :: summary() | nil
  def stashed_summary, do: :persistent_term.get(@stash_key, nil)

  @doc "Distinct assay ids the participants declare cells for."
  @spec participant_assays() :: [String.t()]
  def participant_assays do
    @participants
    |> Enum.flat_map(& &1.cover_cells())
    |> Enum.map(&elem(&1, 0))
    |> Enum.uniq()
    |> Enum.sort()
  end

  @doc """
  Suite-end human report string, or `nil` when the manifest was never evaluated this
  run (gate test filtered out) so the caller can stay silent. Always leads with the
  aggregate `produced/expected` line; when a participant assay has declared cells that
  were never produced, each such assay is listed with its missing cells — this is the
  "incompletely covered assays" surface asked for at suite end.
  """
  @spec report(summary() | nil) :: String.t() | nil
  def report(summary \\ stashed_summary())
  def report(nil), do: nil

  def report(%{missing_detail: detail} = s) do
    header =
      "Antigen shape-coverage: #{s.produced}/#{s.expected} declared cells produced " <>
        "across #{length(s.assays)} manifest assays"

    case detail do
      [] ->
        header <> " ✓"

      _ ->
        affected = detail |> Enum.map(& &1.assay) |> Enum.uniq() |> length()

        lines =
          Enum.map(detail, fn m ->
            "  - #{m.assay} · #{m.cell} — declared by #{short_gen(m.generator)}, never produced"
          end)

        Enum.join(
          [
            header <>
              " — #{length(detail)} shape(s) uncovered in #{affected} assay(s):"
            | lines
          ],
          "\n"
        )
    end
  end

  defp short_gen(nil), do: "?"
  defp short_gen(mod), do: mod |> Module.split() |> List.last()
end

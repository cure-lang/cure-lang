defmodule Antigen.Generators.ElabErasure do
  @moduledoc """
  Elaborator **erasure** vertical — a generative pin on the `{0,ω}` relevance
  check (`Cure.Elab.Relevance`, M8.3).

  Unlike `elab/completeness` (one-sided: every catalog entry must ACCEPT), this
  vertical is **two-sided**. Each base program is parameterised on WHERE an erased
  implicit binder is used, and its label carries the expected verdict:

    * used only in a TYPE/index position → ACCEPT;
    * used only inside an `Eq`/proof position → ACCEPT;
    * RETURNED as the value → REJECT;
    * passed in a PRESENT argument position → REJECT;
    * SCRUTINISED as a `case` discriminant → REJECT.

  The `elab/erasure` assay reports an infection whenever the actual verdict
  differs from the expected one — so it catches both an under-strict check (a
  reject-case that slips through, an unsound erasure) AND an over-strict check (an
  accept-case wrongly rejected, a completeness regression).

  ## Metamorphic layer

  `relevance_injection` takes an ACCEPTING base and injects a single relevant use
  of the erased binder; the verdict MUST flip to reject (relation `:flip`) — proof
  the check is load-bearing, not vacuous. `alpha_rename` and `extra_unused_param`
  are typing/erasure-preserving frame perturbations; the verdict MUST NOT change
  (relation `:same`), applied to both an accepting and a rejecting base.
  """

  alias Antigen.{Challenge, Gen}

  @preamble """
    type Nat = Z | S(Nat)
    type SNat indices (n: Nat)
      szero : SNat(Z)
      ssuc : SNat(n) -> SNat(S(n))
    type NV indices (n: Nat)
      vz : NV(Z)
      vs : SNat(n) -> NV(S(n))
  """

  @doc "Wrap a `fn` body (or bodies) into a self-contained, elaborable module."
  @spec module(String.t()) :: String.t()
  def module(body), do: "mod P\n" <> @preamble <> body <> "end\n"

  # -- Two-sided catalog: {id, cell, expect, note, fn-body} --------------------
  @catalog [
    {"type_position", :type_position, :accept, "erased `n` used only in a type/index position",
     """
       fn f({n: Nat}, v: NV(n)) -> NV(n) = v
     """},
    {"eq_proof_position", :eq_proof_position, :accept, "erased `n` used only inside an Eq/proof term",
     """
       fn f({n: Nat}, v: NV(n)) -> Equivalent(Nat, n, n) = reflexive(n)
     """},
    {"returned", :returned, :reject, "erased `n` returned as the value",
     """
       fn f({n: Nat}, v: NV(n)) -> Nat = n
     """},
    {"present_arg", :present_arg, :reject, "erased `n` passed in a present argument position",
     """
       fn g(m: Nat) -> Nat = m
       fn f({n: Nat}, v: NV(n)) -> Nat = g(n)
     """},
    {"scrutinised", :scrutinised, :reject, "erased `n` scrutinised as a case discriminant",
     """
       fn f({n: Nat}, v: NV(n)) -> Nat =
         match n
           Z() -> Z()
           S(k) -> Z()
     """}
  ]

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`): one per two-sided catalog
  cell, plus the metamorphic transform cells (all under the `elab/erasure` assay).
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    base = for {_id, cell, _e, _n, _b} <- @catalog, do: {"elab/erasure", cell}

    base ++
      [
        {"elab/erasure", :relevance_injection},
        {"elab/erasure", :alpha_rename},
        {"elab/erasure", :extra_unused_param}
      ]
  end

  @doc """
  Sampleable generator over every declared cell (the vertical is otherwise a
  fixed two-sided catalog + metamorphic layer). Used by the coverage-manifest gate.
  """
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.member_of(erasure_challenges() ++ metamorphic_challenges())
  end

  @doc "All two-sided catalog challenges as `%Challenge{}` structs (deterministic)."
  @spec erasure_challenges() :: [Challenge.t()]
  def erasure_challenges do
    Enum.map(@catalog, fn {id, cell, expect, note, body} ->
      Challenge.new(
        kind: :elab_program,
        assay: "elab/erasure",
        label: expect,
        payload: %{id: id, src: module(body), expect: expect},
        note: note,
        cover_tag: cell
      )
    end)
  end

  @doc "The catalog ids paired with their expected verdicts."
  @spec catalog() :: [{String.t(), :accept | :reject}]
  def catalog, do: Enum.map(@catalog, fn {id, _cell, expect, _n, _b} -> {id, expect} end)

  @doc "Look up a catalog entry's full module source by id (for tests/probes)."
  @spec source(String.t()) :: String.t() | nil
  def source(id) do
    case Enum.find(@catalog, fn {i, _, _, _, _} -> i == id end) do
      {_id, _cell, _expect, _note, body} -> module(body)
      nil -> nil
    end
  end

  # -- Metamorphic challenges --------------------------------------------------

  @doc """
  Metamorphic challenges. For every ACCEPTING base:

    * `relevance_injection` (relation `:flip`) — inject a relevant use of the
      erased binder; the verdict must flip accept → reject.
    * `alpha_rename` / `extra_unused_param` (relation `:same`) — frame-preserving
      perturbations; the verdict must not change.

  For every REJECTING base, the two `:same` perturbations are also emitted, so
  invariance is pinned on both sides of the check.
  """
  @spec metamorphic_challenges() :: [Challenge.t()]
  def metamorphic_challenges do
    Enum.flat_map(@catalog, fn {id, _cell, expect, _note, body} ->
      base_src = module(body)

      invariance =
        [{"alpha_rename", alpha_rename(body)}, {"extra_unused_param", prepend_unused_param(body)}]
        |> Enum.filter(fn {_t, b} -> is_binary(b) and b != body end)
        |> Enum.map(fn {transform, vbody} ->
          challenge(id, transform, :same, base_src, module(vbody))
        end)

      injection =
        case {expect, inject_relevant_use(body)} do
          {:accept, injected} when is_binary(injected) and injected != body ->
            [challenge(id, "relevance_injection", :flip, base_src, module(injected))]

          _ ->
            []
        end

      invariance ++ injection
    end)
  end

  defp challenge(id, transform, relation, base_src, variant_src) do
    Challenge.new(
      kind: :elab_program,
      assay: "elab/erasure",
      label: :none,
      payload: %{
        id: id,
        transform: transform,
        relation: relation,
        base_src: base_src,
        variant_src: variant_src
      },
      note: "#{id} #{relation} under #{transform}",
      cover_tag: meta_cell(transform)
    )
  end

  defp meta_cell("relevance_injection"), do: :relevance_injection
  defp meta_cell("alpha_rename"), do: :alpha_rename
  defp meta_cell("extra_unused_param"), do: :extra_unused_param

  # -- Metamorphic transforms --------------------------------------------------

  # Turn an accepting type-position body (`-> NV(n) = v`) into the returning form
  # (`-> Nat = n`): a single relevant use of the erased `n`. Returns nil if the
  # base has no such shape to inject into.
  defp inject_relevant_use(body) do
    if String.contains?(body, "-> NV(n) = v") do
      String.replace(body, "-> NV(n) = v", "-> Nat = n")
    else
      nil
    end
  end

  # Rename the bound value `v` consistently (α-equivalence); never touches the
  # type name `NV` (only standalone `v`).
  defp alpha_rename(body), do: String.replace(body, ~r/\bv\b/, "vv0")

  # Prepend an unused erased implicit to the FIRST probe `fn`, shifting every de
  # Bruijn index by one — a frame perturbation a correct relevance walk absorbs.
  # Leaves a helper `fn g(` (present-arg base) at the head alone by targeting the
  # first `fn \w+({` implicit-list form; falls back to the first `fn \w+(`.
  defp prepend_unused_param(body) do
    cond do
      Regex.match?(~r/fn \w+\(\{/, body) ->
        String.replace(body, ~r/(fn \w+\()\{/, "\\1{z_unused: Nat}, {", global: false)

      Regex.match?(~r/fn \w+\(/, body) ->
        String.replace(body, ~r/(fn \w+\()/, "\\1{z_unused: Nat}, ", global: false)

      true ->
        nil
    end
  end
end

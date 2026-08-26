defmodule Antigen.Generators.ElabComplete do
  @moduledoc """
  Elaborator **completeness** vertical (property-based testing for `Surface →
  Core`, not the kernel).

  Antigen's other verticals hand-build Core terms and probe the KERNEL. This one
  probes the ELABORATOR, whose defects are a different class: the kernel already
  re-checks every term the elaborator emits, so an elaborator bug shows up not as
  an unsound accept but as an unsound **reject** — a genuinely well-typed program
  the elaborator fails to elaborate (a completeness / "reach" gap). Kernel-level
  property testing is blind to this: the kernel is behaving correctly when it
  rejects a mis-framed Core term the elaborator handed it.

  ## Construction-guaranteed well-typed challenges

  Each challenge is a self-contained surface module whose sole probe `fn` body is
  a dependent `match` that is **well-typed by construction**: in every branch the
  dependent match refines the scrutinee to that branch's constructor, so a goal
  of the form `F(idx)` / `Equivalent(F(idx), scrut, scrut)` reduces to a goal the
  branch's canonical inhabitant (`ctor` / `reflexive(ctor)`) provably satisfies. Idris
  accepts every one of these. The expected verdict is therefore ACCEPT; the
  `elab/completeness` assay reports an infection on any REJECT.

  The catalog is parameterised on **where the scrutinee's index (and value)
  appears in the goal**, because that occurrence position is exactly what the
  motive machinery must abstract per-branch. Threading the index into ever deeper
  goal positions maps the blast radius of a motive/refinement gap.

  ## Metamorphic layer

  `variants/1` applies typing-preserving transforms (α-rename, arm reorder,
  unused-binder insertion) to a base program. The `elab/metamorphic` assay
  asserts the accept/reject verdict is invariant under them — a self-contained
  oracle (no Idris needed) that catches de Bruijn / binder-framing bugs.
  """

  alias Antigen.{Challenge, Gen}

  # Two preambles. `:nat_nv` — Nat, its singleton SNat(n), an indexed view NV(n),
  # and the certified toS/view builders. `:slist_f` — SList, append, and the
  # computed-append-index family F (the FRP `par`/`app` crux, generalized).
  @nat_nv """
    type Nat = Z | S(Nat)
    type SNat indices (n: Nat)
      szero : SNat(Z)
      ssuc : SNat(n) -> SNat(S(n))
    type NV indices (n: Nat)
      vz : NV(Z)
      vs : SNat(n) -> NV(S(n))
    fn toS(m: Nat) -> SNat(m) = match m
      Z() -> szero()
      S(j) -> ssuc(toS(j))
    fn view(n: Nat) -> NV(n) = match n
      Z() -> vz()
      S(m) -> vs(toS(m))
  """

  @slist_f """
    type Nat = Z | S(Nat)
    type SList = SNil | SCons(Nat, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(h, t) -> SCons(h, app(t, ys))
    type F indices (xs: SList)
      leaf : F(SNil())
      mk : F(as) -> F(bs) -> F(app(as, bs))
  """

  defp preamble(:nat_nv), do: @nat_nv
  defp preamble(:slist_f), do: @slist_f

  @doc "Wrap a `fn` body into a self-contained, elaborable module."
  @spec module(:nat_nv | :slist_f, String.t()) :: String.t()
  def module(pre, body), do: "mod P\n" <> preamble(pre) <> body <> "end\n"

  # -- The completeness catalog ------------------------------------------------
  #
  # Each entry: {id, cell, preamble, note, fn-body}. Every one is construction-
  # guaranteed well-typed (Idris-accepted). `id` names the goal *shape* so a
  # reported infection reads as a blast-radius coordinate.
  @catalog [
    # (control) goal mentions ONLY the index; plain var scrutinee. build_motive's
    # index generalization + var abstraction already handle this — expected
    # ACCEPT, so it anchors that an infection elsewhere is shape-specific.
    {"idx_only/var/rebuild", :idx_only_var_rebuild, :nat_nv, "goal NV(n), var scrutinee, rebuild constructor",
     """
       fn f({n: Nat}, v: NV(n)) -> NV(n) =
         match v
           vz() -> vz()
           vs(s) -> vs(s)
     """},

    # goal is an Eq whose TYPE argument carries the index AND whose value
    # endpoints are the scrutinee value; var scrutinee; reflexive(ctor) bodies.
    {"eq_value/var/refl_ctor", :eq_value_var_refl_ctor, :nat_nv,
     "goal Equivalent(NV(n), v, v), var scrutinee, reflexive(ctor)",
     """
       fn f({n: Nat}, v: NV(n)) -> Equivalent(NV(n), v, v) =
         match v
           vz() -> reflexive(vz())
           vs(s) -> reflexive(vs(s))
     """},

    # same goal, but branch bodies return `reflexive(v)` (the scrutinee value) rather
    # than rebuilding the constructor — isolates value-occurrence refinement.
    {"eq_value/var/refl_scrut", :eq_value_var_refl_scrut, :nat_nv, "goal Equivalent(NV(n), v, v), reflexive(v)",
     """
       fn f({n: Nat}, v: NV(n)) -> Equivalent(NV(n), v, v) =
         match v
           vz() -> reflexive(v)
           vs(s) -> reflexive(v)
     """},

    # the scrutinee is a COMPUTED view expression, not a variable.
    {"eq_value/computed/refl_ctor", :eq_value_computed_refl_ctor, :nat_nv,
     "goal Equivalent(NV(n), view(n), view(n)), computed scrutinee",
     """
       fn f(n: Nat) -> Equivalent(NV(n), view(n), view(n)) =
         match view(n)
           vz() -> reflexive(vz())
           vs(s) -> reflexive(vs(s))
     """},

    # computed-index family: goal mentions the scrutinee's stuck computed index
    # through a rebuild (the FRP `app`-style crux, generalized). Covered by 3a.
    {"computed_idx/rebuild", :computed_idx_rebuild, :slist_f, "goal F(app(p,q)) rebuild — computed result index",
     """
       fn g({p: SList}, {q: SList}, v: F(app(p, q))) -> F(app(p, q)) =
         match v
           leaf() -> leaf()
           mk(l, r) -> mk(l, r)
     """}
  ]

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`). Each catalog goal-shape cell
  appears under both `elab/completeness` and `elab/soundness` (the latter reuses
  the same challenges via `soundness_challenges/0`); the metamorphic transforms
  are their own cells under `elab/metamorphic`.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    catalog_cells = for {_id, cell, _pre, _note, _body} <- @catalog, do: cell

    for(assay <- ["elab/completeness", "elab/soundness"], c <- catalog_cells, do: {assay, c}) ++
      [
        {"elab/metamorphic", :arm_reorder},
        {"elab/metamorphic", :alpha_rename},
        {"elab/metamorphic", :extra_unused_param}
      ]
  end

  @doc """
  Sampleable generator over every declared cell (the vertical is otherwise a
  fixed catalog + metamorphic layer). Used by the coverage-manifest gate.
  """
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.member_of(completeness_challenges() ++ soundness_challenges() ++ metamorphic_challenges())
  end

  @doc "All completeness challenges as `%Challenge{}` structs (deterministic)."
  @spec completeness_challenges() :: [Challenge.t()]
  def completeness_challenges do
    Enum.map(@catalog, fn {id, cell, pre, note, body} ->
      Challenge.new(
        kind: :elab_program,
        assay: "elab/completeness",
        label: :well_typed,
        payload: %{id: id, src: module(pre, body)},
        note: note,
        cover_tag: cell
      )
    end)
  end

  @spec soundness_challenges() :: [Challenge.t()]
  def soundness_challenges do
    Enum.map(completeness_challenges(), fn c -> %{c | assay: "elab/soundness"} end)
  end

  @doc "The catalog ids (blast-radius coordinates)."
  @spec catalog_ids() :: [String.t()]
  def catalog_ids, do: Enum.map(@catalog, &elem(&1, 0))

  @doc "Look up a catalog entry's full module source by id (for tests/probes)."
  @spec source(String.t()) :: String.t() | nil
  def source(id) do
    case Enum.find(@catalog, fn {i, _, _, _, _} -> i == id end) do
      {_id, _cell, pre, _note, body} -> module(pre, body)
      nil -> nil
    end
  end

  # -- Metamorphic transforms --------------------------------------------------

  @doc """
  Typing-preserving variants of a base `fn` body. Each is a `{transform, body}`
  whose elaboration verdict MUST match the base's. Used by `elab/metamorphic`.
  Returns only transforms that actually changed the source.

  Every transform here is *reliably* typing-preserving in Cure's dependent-match
  surface (verified against Idris): α-rename, arm reorder (a covering dependent
  match is order-independent), and prepending an unused implicit parameter (inert
  in Idris; a deliberate de Bruijn frame shift that a correct elaborator must
  absorb). A transform that wraps the match head in a `let`/block is NOT
  preserving — Cure requires the dependent match to be the body head — so it is
  deliberately excluded to keep the assay from crying wolf on its own rewrite.
  """
  @spec variants(String.t()) :: [{String.t(), String.t()}]
  def variants(body) do
    [
      {"arm_reorder", reorder_arms(body)},
      {"alpha_rename", alpha_rename(body)},
      {"extra_unused_param", prepend_unused_param(body)}
    ]
    |> Enum.filter(fn {_t, b} -> is_binary(b) and b != body end)
  end

  @doc "Metamorphic challenges: each catalog base paired with each of its variants."
  @spec metamorphic_challenges() :: [Challenge.t()]
  def metamorphic_challenges do
    Enum.flat_map(@catalog, fn {id, _cell, pre, _note, body} ->
      base_src = module(pre, body)

      Enum.map(variants(body), fn {transform, vbody} ->
        Challenge.new(
          kind: :elab_program,
          assay: "elab/metamorphic",
          label: :none,
          payload: %{id: id, transform: transform, base_src: base_src, variant_src: module(pre, vbody)},
          note: "#{id} invariant under #{transform}",
          cover_tag: meta_cell(transform)
        )
      end)
    end)
  end

  defp meta_cell("arm_reorder"), do: :arm_reorder
  defp meta_cell("alpha_rename"), do: :alpha_rename
  defp meta_cell("extra_unused_param"), do: :extra_unused_param

  # Swap the two match arms (order-independent for a covering dependent match).
  # An arm line is an INDENTED `pattern -> body`; the `fn … -> RetType =`
  # signature also contains `->` and must be excluded, so we anchor on a line
  # that starts (after indentation) with a constructor pattern `Name(`.
  defp reorder_arms(body) do
    lines = String.split(body, "\n")
    arm? = fn l -> Regex.match?(~r/^\s+[A-Za-z]\w*\(.*->/, l) end
    arm_lines = Enum.filter(lines, arm?)

    case arm_lines do
      [a, b] ->
        Enum.map_join(lines, "\n", fn
          ^a -> b
          ^b -> a
          other -> other
        end)

      _ ->
        nil
    end
  end

  # Rename the bound scrutinee `v`/`s` consistently (α-equivalence). Only touches
  # standalone identifiers, never substrings of type names.
  defp alpha_rename(body) do
    body
    |> String.replace(~r/\bv\b/, "vv0")
    |> String.replace(~r/\bs\b/, "ss0")
  end

  # Prepend an unused implicit parameter to the probe `fn`. Inert in Idris (an
  # extra erased argument nothing depends on), but it shifts every de Bruijn
  # index in the goal and scrutinee by one — a targeted probe that a correct
  # elaborator absorbs the frame shift. Only rewrites the first `fn NAME({`/`fn
  # NAME((` parameter list; leaves helper defs (toS/view/app) untouched.
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

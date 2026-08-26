defmodule Antigen.Generators.ElabDotForcing do
  @moduledoc """
  Source-level dot-forcing vertical (spec 2026-07-08-antigen-elab-dot-forcing):
  `:elab_program` challenges entering at `Cure.Elab.Program.elaborate/1`, so the
  named-implicit check's CALL-SITE WIRING is probed — the class the value-level
  `forcing/dot` oracle is structurally blind to (it calls the check directly and
  can never observe a dispatch path that skips it, as C-a's carried-eq path did
  pre-#12).

  Six two-sided catalog cells (labels correct-by-construction — the generator
  writes both the forced solution and the written dot value):

    * forced axis, {plain, carried} × {right, wrong} — `wrong` cells pin error
      head `:forced_pattern_mismatch`;
    * unforced C-c axis, {bind_erased, bind_relevant} — `bind_relevant` pins
      `:erased_used_relevantly` (the quantity gate, not a named-implicit error).

  Sources are verbatim the #12-landed fixtures (`named_implicit_tail_test.exs`);
  carried cells are the only landed programs reaching
  `elaborate_carried_eq_branch`. Metamorphic layer: `corrupt_dot` /
  `promote_use` are `:flip` relations (the C-a-class causal pin — base held
  fixed, only the checked property mutated); `alpha_rename` /
  `extra_unused_param` are `:same` perturbations. Transforms operate on the
  probe-fn BODY only, never `preamble <> body` (first-match regex safety —
  spec §2.2 structural note).
  """

  alias Antigen.{Challenge, Gen}

  # Carried + forced mixed shape (#12 Task 2): H's first index is ctor-pinned
  # (forced m := j), the second is a stuck function index carried via the
  # sibling `w : G(app(p, q))` (detect_carried_index).
  @carried_preamble """
    type Nat = Z | S(Nat)
    type SList = SNil | SCons(Nat, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(h, t) -> SCons(h, app(t, ys))
    type H indices (n: Nat, xs: SList)
      hmk : H(S(m), app(as, bs))
    type G indices (xs: SList)
      gwrap : G(cs)
  """

  # Vec (plain forced cells) + Pack (unforced C-c cells) — the landed
  # @exist_preamble of #12 Task 4.
  @exist_preamble """
    type Nat = Z | S(Nat)
    type Vec(a: Type) indices (n: Nat)
      vnil : Vec(a, Z)
      vcons : a -> Vec(a, n) -> Vec(a, S(n))
    type Pack(a: Type) indices ()
      pk : Vec(a, m) -> Pack(a)
  """

  defp preamble(:carried), do: @carried_preamble
  defp preamble(:exist), do: @exist_preamble

  @doc "Wrap a probe-`fn` body into a self-contained, elaborable module."
  @spec module(:carried | :exist, String.t()) :: String.t()
  def module(pre, body), do: "mod P\n" <> preamble(pre) <> body <> "end\n"

  # -- Two-sided catalog: {id, cell, expect, expect_error | nil, preamble, note, body}
  @catalog [
    {"forced/carried/right", :forced_carried_right, :accept, nil, :carried,
     "right dot on the carried-eq path (over-rejection guard)",
     """
       fn g({j: Nat}, {p: SList}, {q: SList}, v: H(S(j), app(p, q)), w: G(app(p, q))) -> Nat = match v
         hmk({m = .j}) -> Z()
     """},
    {"forced/carried/wrong", :forced_carried_wrong, :reject, :forced_pattern_mismatch, :carried,
     "wrong dot on the carried-eq path (the C-a cell — pre-#12 this ACCEPTED)",
     """
       fn f({j: Nat}, {p: SList}, {q: SList}, v: H(S(j), app(p, q)), w: G(app(p, q))) -> Nat = match v
         hmk({m = .(S(j))}) -> Z()
     """},
    {"forced/plain/right", :forced_plain_right, :accept, nil, :exist,
     "right dot on the plain dispatch path (landed C-b shape)",
     """
       fn f({a: Type}, {k: Nat}, v: Vec(a, S(k))) -> Vec(a, S(k)) = match v
         vcons({n = .k}, h, t) -> v
     """},
    {"forced/plain/wrong", :forced_plain_wrong, :reject, :forced_pattern_mismatch, :exist,
     "wrong dot on the plain dispatch path",
     """
       fn f({a: Type}, {k: Nat}, v: Vec(a, S(k))) -> Vec(a, S(k)) = match v
         vcons({n = .(S(k))}, h, t) -> v
     """},
    {"unforced/bind_erased", :unforced_bind_erased, :accept, nil, :exist,
     "unforced bare-variable named implicit bound at quantity 0, used only erasedly",
     """
       fn f({a: Type}, p: Pack(a)) -> Nat = match p
         pk({m = mm}, v) -> Z()
     """},
    {"unforced/bind_relevant", :unforced_bind_relevant, :reject, :erased_used_relevantly, :exist,
     "quantity-0 binding used relevantly rejects via Relevance (C-c gate)",
     """
       fn g({a: Type}, p: Pack(a)) -> Nat = match p
         pk({m = mm}, v) -> mm
     """}
  ]

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`): one per two-sided catalog
  cell, plus the metamorphic transform cells (all under the `elab/dot_forcing` assay).
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    base = for {_id, cell, _e, _err, _p, _n, _b} <- @catalog, do: {"elab/dot_forcing", cell}

    base ++
      [
        {"elab/dot_forcing", :alpha_rename},
        {"elab/dot_forcing", :extra_unused_param},
        {"elab/dot_forcing", :corrupt_dot},
        {"elab/dot_forcing", :promote_use}
      ]
  end

  @doc """
  Sampleable generator over every declared cell (the vertical is otherwise a
  fixed two-sided catalog + metamorphic layer). Used by the coverage-manifest gate.
  """
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.member_of(dot_forcing_challenges() ++ metamorphic_challenges())
  end

  @doc "All two-sided catalog challenges as `%Challenge{}` structs (deterministic)."
  @spec dot_forcing_challenges() :: [Challenge.t()]
  def dot_forcing_challenges do
    Enum.map(@catalog, fn {id, cell, expect, err, pre, note, body} ->
      payload = %{id: id, src: module(pre, body), expect: expect}
      payload = if err, do: Map.put(payload, :expect_error, err), else: payload

      Challenge.new(
        kind: :elab_program,
        assay: "elab/dot_forcing",
        label: expect,
        payload: payload,
        note: note,
        cover_tag: cell
      )
    end)
  end

  @doc "The catalog ids paired with their expected verdicts."
  @spec catalog() :: [{String.t(), :accept | :reject}]
  def catalog, do: Enum.map(@catalog, fn {id, _cell, expect, _e, _p, _n, _b} -> {id, expect} end)

  @doc "Look up a catalog entry's full module source by id."
  @spec source(String.t()) :: String.t() | nil
  def source(id) do
    case entry(id) do
      {_id, _cell, _e, _err, pre, _n, body} -> module(pre, body)
      nil -> nil
    end
  end

  @doc "Look up a catalog entry's probe-fn BODY by id (transform input)."
  @spec body(String.t()) :: String.t() | nil
  def body(id) do
    case entry(id) do
      {_id, _cell, _e, _err, _pre, _n, body} -> body
      nil -> nil
    end
  end

  defp entry(id), do: Enum.find(@catalog, fn {i, _, _, _, _, _, _} -> i == id end)

  # -- Metamorphic challenges --------------------------------------------------

  @doc """
  Metamorphic challenges.

    * `corrupt_dot` (`:flip`) — on each forced-axis ACCEPTING base, corrupt only
      the written dot value; the verdict must flip. Holding the program fixed
      and varying only the checked value pins "the check runs and compares" on
      that dispatch path (the carried instance is the C-a detector).
    * `promote_use` (`:flip`) — on the bind_erased base, use the quantity-0
      binding relevantly; must flip (the C-c gate is load-bearing).
    * `alpha_rename` / `extra_unused_param` (`:same`) — typing-preserving frame
      perturbations on EVERY base; the verdict must not change.

  All transforms take the probe-fn BODY only (never `preamble <> body`), so the
  first-match regexes can never collide with the preamble's helper `fn app`.
  """
  @spec metamorphic_challenges() :: [Challenge.t()]
  def metamorphic_challenges do
    Enum.flat_map(@catalog, fn {id, _cell, expect, _err, pre, _note, body} ->
      base_src = module(pre, body)

      invariance =
        [{"alpha_rename", alpha_rename(body)}, {"extra_unused_param", prepend_unused_param(body)}]
        |> Enum.filter(fn {_t, b} -> is_binary(b) and b != body end)
        |> Enum.map(fn {t, vbody} -> challenge(id, t, :same, base_src, module(pre, vbody)) end)

      flips =
        case {id, expect} do
          {_, :accept} ->
            [{"corrupt_dot", corrupt_dot(body)}, {"promote_use", promote_use(body)}]
            |> Enum.filter(fn {_t, b} -> is_binary(b) and b != body end)
            |> Enum.map(fn {t, vbody} -> challenge(id, t, :flip, base_src, module(pre, vbody)) end)

          _ ->
            []
        end

      invariance ++ flips
    end)
  end

  defp challenge(id, transform, relation, base_src, variant_src) do
    Challenge.new(
      kind: :elab_program,
      assay: "elab/dot_forcing",
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

  defp meta_cell("alpha_rename"), do: :alpha_rename
  defp meta_cell("extra_unused_param"), do: :extra_unused_param
  defp meta_cell("corrupt_dot"), do: :corrupt_dot
  defp meta_cell("promote_use"), do: :promote_use

  # -- Metamorphic transforms (probe-fn BODY input only) ------------------------

  # Corrupt the written dot value on a forced right-dot base: the forced
  # solution is `j` (carried, `{m = .j}`) or `k` (plain, `{n = .k}`); wrap it
  # in one more S so it can no longer be convertible with the pinned value.
  # nil on bodies with no right-dot to corrupt (unforced cells).
  defp corrupt_dot(body) do
    cond do
      String.contains?(body, "{m = .j}") -> String.replace(body, "{m = .j}", "{m = .(S(j))}")
      String.contains?(body, "{n = .k}") -> String.replace(body, "{n = .k}", "{n = .(S(k))}")
      true -> nil
    end
  end

  # Use the quantity-0 binding relevantly: bind_erased's arm `pk({m = mm}, v)
  # -> Z()` becomes `-> mm` (the landed bind_relevant fixture's exact body
  # motion). nil on bodies without the bound-and-discarded shape.
  defp promote_use(body) do
    if String.contains?(body, "pk({m = mm}, v) -> Z()") do
      String.replace(body, "pk({m = mm}, v) -> Z()", "pk({m = mm}, v) -> mm")
    else
      nil
    end
  end

  # Rename the bound value `v` consistently (α-equivalence); standalone `v`
  # only, so type names and `vcons`/`vnil` are untouched.
  defp alpha_rename(body), do: String.replace(body, ~r/\bv\b/, "vv0")

  # Prepend an unused erased implicit to the probe `fn` (every catalog body's
  # first fn IS the probe fn and starts with a `{…}` implicit list), shifting
  # every de Bruijn index by one — a frame perturbation a correct elaborator
  # absorbs. Mirrors ElabErasure.prepend_unused_param/1.
  defp prepend_unused_param(body) do
    if Regex.match?(~r/fn \w+\(\{/, body) do
      String.replace(body, ~r/(fn \w+\()\{/, "\\1{z_unused: Nat}, {", global: false)
    else
      nil
    end
  end
end

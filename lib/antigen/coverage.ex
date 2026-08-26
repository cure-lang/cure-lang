defmodule Antigen.Coverage do
  @moduledoc "The coverage key: a plateauing feature vector for dedup + the health gate (spec §7.2, §9)."
  alias Antigen.Challenge

  @elim_flags %{app: :app_present, case: :case_present, fst: :fst_present, snd: :snd_present, rewrite: :rewrite_present}

  @spec key(Challenge.t()) :: {MapSet.t(atom()), atom(), MapSet.t(atom()), Challenge.label()}
  def key(%Challenge{} = c) do
    terms = terms_of(c)
    ctors = terms |> Enum.flat_map(&constructors/1) |> MapSet.new()
    depth = terms |> Enum.map(&depth/1) |> Enum.max(fn -> 0 end)
    flags = flags(c, terms, ctors)
    {ctors, bucket(depth), flags, c.label}
  end

  @spec key_string({MapSet.t(), atom(), MapSet.t(), atom()}) :: String.t()
  def key_string({ctors, bucket, flags, label}) do
    cs = ctors |> Enum.sort() |> Enum.join(",")
    fs = flags |> Enum.sort() |> Enum.join(",")
    "ctors=[#{cs}]|depth=#{bucket}|flags=[#{fs}]|label=#{label}"
  end

  @spec terms_of(Challenge.t()) :: [Cure.Core.Term.t()]
  def terms_of(%Challenge{kind: :stub, payload: %{term: t}}), do: [t]

  def terms_of(%Challenge{kind: :typed_term, payload: %{ctx: ctx, type: type, term: term}}),
    do: [type, term | ctx]

  def terms_of(%Challenge{kind: :malformed, payload: %{ctx: ctx, term: term}}),
    do: [term | ctx]

  def terms_of(%Challenge{kind: :serialize, payload: %{term: term}}), do: [term]
  # decode probes carry a raw string, not a Core term → no terms to well-form-check
  def terms_of(%Challenge{kind: :decode_probe}), do: []
  # elab_program challenges carry raw SURFACE source (a string), not a Core term —
  # same reasoning as decode_probe. Only ever hit when an `:elab_program` generator
  # is wired into `default_gen` (previously none were — every `elab_*` fixed
  # catalog was deliberately kept out of it); latent until `ElabLiteralTyping`.
  def terms_of(%Challenge{kind: :elab_program}), do: []

  def terms_of(%Challenge{kind: :conv_pair, payload: %{t1: t1, t2: t2}}), do: [t1, t2]

  def terms_of(%Challenge{kind: :branch_unify, payload: %{indices: idx}}), do: idx

  # motive-probe branch_unify variant: fully determined by the `shape` tag, no
  # Core terms in the payload at all (see Antigen.Generators.BranchUnify's
  # `@motive_cases` and Antigen.Assays.BranchUnify's `motive_probe_result/1`).
  def terms_of(%Challenge{kind: :branch_unify, payload: %{motive_probe: _}}), do: []

  def terms_of(%Challenge{kind: :dot_forcing, payload: %{indices: idx, written: w}}), do: idx ++ [w]

  # `[]` bypasses the well_formed? gate: a check-mode term may be a {:hole, _}
  # (which Term.term? rejects) and the assay self-validates via Kernel.check.
  def terms_of(%Challenge{kind: :check_mode}), do: []

  # Kernel def-level probes carry only a probe tag; the assay reconstructs the
  # input and calls the kernel directly (check_def/validate_certificate/…), so
  # there is no standalone Core Term to well-form-check — bypass the gate as
  # :check_mode/:decode_probe do (some inputs, e.g. `{:absurd}`/`{:hole,_}`, are
  # deliberately shapes Term.term? rejects).
  def terms_of(%Challenge{kind: :kernel_probe}), do: []

  def terms_of(%Challenge{kind: :delta_reduce, payload: %{term: t, expected: e}}), do: [t, e]

  # opts-rejection probes carry no Core Term at all (a deliberately malformed
  # `opts` keyword list, checked directly against a fixed dummy neutral) → no
  # terms to well-form-check, mirroring :decode_probe/:check_mode above.
  def terms_of(%Challenge{kind: :delta_reduce, label: :opts_reject}), do: []

  def terms_of(%Challenge{kind: :mutant_term, payload: %{ctx: ctx, type: type, term: term}}),
    do: [type, term | ctx]

  def terms_of(%Challenge{kind: :def_group, payload: %{defs: defs}}),
    do: Enum.flat_map(defs, fn d -> [d.type, d.body] end)

  def terms_of(%Challenge{kind: :family, payload: %{family: fam, ctors: ctors}}) do
    fam_terms = Enum.map(fam.params, fn {_n, t} -> t end) ++ Enum.map(fam.indices, fn {_n, t} -> t end)
    ctor_terms = Enum.flat_map(ctors, fn ct -> Enum.map(ct.args, fn {_n, t} -> t end) ++ ct.result_indices end)
    fam_terms ++ ctor_terms
  end

  def terms_of(%Challenge{kind: k, payload: %{defs: defs, t: t, tprime: tp}})
      when k in [:forcing_pair, :stuck_elim],
      do: Enum.flat_map(defs, fn d -> [d.type, d.body] end) ++ [t, tp]

  def terms_of(%Challenge{kind: k, payload: p}) when k in [:indexed_case, :rewrite_eq] do
    fam_terms =
      Enum.flat_map(p.families, fn {fam, ctors} ->
        Enum.map(fam.params, fn {_n, t} -> t end) ++
          Enum.map(fam.indices, fn {_n, t} -> t end) ++
          Enum.flat_map(ctors, fn ct -> Enum.map(ct.args, fn {_n, t} -> t end) ++ ct.result_indices end)
      end)

    fam_terms ++ [p.def_type, p.def_body]
  end

  defp bucket(d) when d <= 2, do: :b0_2
  defp bucket(d) when d <= 5, do: :b3_5
  defp bucket(d) when d <= 9, do: :b6_9
  defp bucket(_), do: :b10p

  defp flags(%Challenge{kind: kind}, terms, ctors) do
    base = for {c, flag} <- @elim_flags, MapSet.member?(ctors, c), into: MapSet.new(), do: flag
    base = if kind in [:def_group, :forcing_pair], do: MapSet.put(base, :has_mutual_group), else: base
    base = if Enum.any?(terms, &has_shadowing?/1), do: MapSet.put(base, :has_shadowing), else: base
    base = MapSet.union(base, former_flags(terms))
    MapSet.put(base, binder_depth_flag(terms))
  end

  # Former-histogram signal (spec §2): a bounded per-class count bucket for each
  # Core former, folded into `flags` so `key/1` stays a 4-tuple. Reuses the
  # existing `fold/3` + `tag/1` (fold only ever passes tuple nodes to its callback).
  # :prim retired (K2): builtin-op spines count under :app.
  @former_classes [:lam, :pi, :app, :case, :ctor, :data, :eq, :rewrite]
  defp former_flags(terms) do
    counts =
      Enum.reduce(terms, %{}, fn t, acc ->
        fold(t, acc, fn node, a ->
          case tag(node) do
            cls when cls in @former_classes -> Map.update(a, cls, 1, &(&1 + 1))
            _ -> a
          end
        end)
      end)

    for cls <- @former_classes, into: MapSet.new() do
      :"former_#{cls}_#{count_bucket(Map.get(counts, cls, 0))}"
    end
  end

  defp count_bucket(0), do: :n0
  defp count_bucket(1), do: :n1
  defp count_bucket(_), do: :nm

  # Binder-depth signal (spec §2): max binder nesting, bucketed (distinct from the
  # overall term-depth bucket already in the tuple).
  defp binder_depth_flag(terms) do
    d = terms |> Enum.map(&binder_depth/1) |> Enum.max(fn -> 0 end)
    :"binder_depth_#{bucket(d)}"
  end

  defp binder_depth({t, _dom, body}) when t in [:lam, :pi, :sigma], do: 1 + binder_depth(body)

  defp binder_depth({:case, s, m, brs}) do
    Enum.max([
      binder_depth(s),
      binder_depth(m)
      | Enum.map(brs, fn {_c, ar, b} -> if(ar > 0, do: 1, else: 0) + binder_depth(b) end)
    ])
  end

  defp binder_depth(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> tl() |> Enum.map(&binder_depth/1) |> Enum.max(fn -> 0 end)

  defp binder_depth(l) when is_list(l), do: l |> Enum.map(&binder_depth/1) |> Enum.max(fn -> 0 end)
  defp binder_depth(_), do: 0

  # `:has_shadowing` (spec §7.2): a coarse approximation — any `:lam`/`:pi`/`:sigma`
  # binder nested underneath another such binder. A single top-level binder does
  # not count; only nesting (e.g. a curried `{:pi, Cure.Core.Grade.unrestricted(), _, {:pi, Cure.Core.Grade.unrestricted(), _, _}}`) does.
  defp has_shadowing?(t), do: nested_binder?(t, false)

  defp nested_binder?(t, inside?) when is_tuple(t) do
    tag = elem(t, 0)
    binder? = tag in [:lam, :pi, :sigma]
    here = binder? and inside?
    children = t |> Tuple.to_list() |> tl()
    here or Enum.any?(children, fn c -> nested_binder?(c, inside? or binder?) end)
  end

  defp nested_binder?(list, inside?) when is_list(list), do: Enum.any?(list, &nested_binder?(&1, inside?))
  defp nested_binder?(_, _), do: false

  # structural helpers over the tagged-tuple AST
  defp constructors(t), do: fold(t, [], fn node, acc -> [tag(node) | acc] end) |> Enum.reject(&is_nil/1)
  defp depth(t), do: fold_depth(t)
  defp tag(t) when is_tuple(t), do: elem(t, 0)
  defp tag(_), do: nil

  defp fold(t, acc, f) when is_tuple(t) do
    acc = f.(t, acc)
    t |> Tuple.to_list() |> Enum.reduce(acc, fn child, a -> fold(child, a, f) end)
  end

  defp fold(list, acc, f) when is_list(list), do: Enum.reduce(list, acc, fn c, a -> fold(c, a, f) end)
  defp fold(_leaf, acc, _f), do: acc

  # A node's depth is 1 + the max depth of its *term-shaped* children (nested
  # tuples/lists); non-term children (the leading tag atom, bare integers/de
  # Bruijn indices, plain atoms) don't count, so a primitive leaf like
  # `{:type, 0}` or `{:var, 0}` has depth 0, not 1 — verified against the
  # Step-1 fixtures: `{:app, {:lam, Cure.Core.Grade.unrestricted(), {:type,0}, {:var,0}}, {:type,0}}` computes
  # to depth 2 (bucket `:b0_2`) and the four-`:app` `deep` fixture computes to
  # depth 3 (bucket `:b3_5`).
  defp fold_depth(t) when is_tuple(t) do
    child_depths =
      t
      |> Tuple.to_list()
      |> Enum.filter(&(is_tuple(&1) or is_list(&1)))
      |> Enum.map(&fold_depth/1)

    case child_depths do
      [] -> 0
      ds -> 1 + Enum.max(ds)
    end
  end

  defp fold_depth(list) when is_list(list), do: Enum.max([0 | Enum.map(list, &fold_depth/1)])
  defp fold_depth(_), do: 0
end

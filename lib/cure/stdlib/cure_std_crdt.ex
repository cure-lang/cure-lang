defmodule :cure_std_crdt do
  @moduledoc """
  Runtime helpers for `Std.CRDT` (v0.27.0).

  Five state-based (CvRDT) implementations. Every `merge/2` function
  is commutative, associative, and idempotent; the laws are exercised
  by `test/cure/stdlib/cure_std_crdt_test.exs`.

  ## Wire shape

  Each CRDT is a map tagged with a `:__struct__` key:

    * `%{__struct__: :g_counter, counts: %{node => n}}`
    * `%{__struct__: :pn_counter, p: g_counter, n: g_counter}`
    * `%{__struct__: :or_set, entries: %{element => MapSet(tag)},
         tombstones: MapSet(tag)}`
    * `%{__struct__: :lww_register, value: term | :empty,
         stamp: integer, node: atom}`
    * `%{__struct__: :mv_register, writes: %{node => {stamp, value}}}`

  The MVRegister retains the latest stamped write per node and
  surfaces cross-node concurrent writes as a list via `mv_values/1`.

  Tags in the ORSet are `{node, tag}` pairs, where `tag` is supplied by
  the caller — as `stamp` is for `lww_set/4` and `mv_write/4`. Every
  function here is pure, so none of them can mint a fresh tag: two calls
  with equal arguments must return equal values. The caller owns the
  contract that a given `node` never reuses a `tag`; break it and an
  `or_remove/2` of one element will tombstone another.
  """

  @k :__struct__

  # --------------------------------------------------------------------------
  # GCounter
  # --------------------------------------------------------------------------

  def g_empty, do: %{@k => :g_counter, counts: %{}}

  def g_increment(%{@k => :g_counter, counts: counts}, node, by)
      when is_atom(node) and is_integer(by) and by >= 0 do
    current = Map.get(counts, node, 0)
    %{@k => :g_counter, counts: Map.put(counts, node, current + by)}
  end

  def g_value(%{@k => :g_counter, counts: counts}) do
    counts |> Map.values() |> Enum.sum()
  end

  def g_merge(%{@k => :g_counter, counts: a}, %{@k => :g_counter, counts: b}) do
    merged =
      Map.merge(a, b, fn _k, va, vb -> max(va, vb) end)

    %{@k => :g_counter, counts: merged}
  end

  # --------------------------------------------------------------------------
  # PNCounter
  # --------------------------------------------------------------------------

  def pn_empty, do: %{@k => :pn_counter, p: g_empty(), n: g_empty()}

  def pn_increment(%{@k => :pn_counter, p: p, n: n}, node, by)
      when is_atom(node) and is_integer(by) and by >= 0 do
    %{@k => :pn_counter, p: g_increment(p, node, by), n: n}
  end

  def pn_decrement(%{@k => :pn_counter, p: p, n: n}, node, by)
      when is_atom(node) and is_integer(by) and by >= 0 do
    %{@k => :pn_counter, p: p, n: g_increment(n, node, by)}
  end

  def pn_value(%{@k => :pn_counter, p: p, n: n}) do
    g_value(p) - g_value(n)
  end

  def pn_merge(%{@k => :pn_counter, p: ap, n: an}, %{@k => :pn_counter, p: bp, n: bn}) do
    %{@k => :pn_counter, p: g_merge(ap, bp), n: g_merge(an, bn)}
  end

  # --------------------------------------------------------------------------
  # ORSet
  # --------------------------------------------------------------------------

  def or_empty do
    %{@k => :or_set, entries: %{}, tombstones: MapSet.new()}
  end

  def or_add(%{@k => :or_set, entries: entries, tombstones: tombs}, node, tag, element)
      when is_atom(node) and is_integer(tag) do
    unique = {node, tag}
    tags_for_elem = Map.get(entries, element, MapSet.new())
    new_tags = MapSet.put(tags_for_elem, unique)
    %{@k => :or_set, entries: Map.put(entries, element, new_tags), tombstones: tombs}
  end

  def or_remove(%{@k => :or_set, entries: entries, tombstones: tombs}, element) do
    case Map.get(entries, element) do
      nil ->
        %{@k => :or_set, entries: entries, tombstones: tombs}

      tags ->
        new_tombs = MapSet.union(tombs, tags)
        %{@k => :or_set, entries: Map.delete(entries, element), tombstones: new_tombs}
    end
  end

  def or_value(%{@k => :or_set, entries: entries}) do
    entries
    |> Map.keys()
    |> Enum.sort()
  end

  def or_merge(
        %{@k => :or_set, entries: ea, tombstones: ta},
        %{@k => :or_set, entries: eb, tombstones: tb}
      ) do
    tombs = MapSet.union(ta, tb)

    all_keys = Map.keys(ea) ++ Map.keys(eb)

    entries =
      all_keys
      |> Enum.uniq()
      |> Enum.reduce(%{}, fn k, acc ->
        union = MapSet.union(Map.get(ea, k, MapSet.new()), Map.get(eb, k, MapSet.new()))
        live = MapSet.difference(union, tombs)

        if MapSet.size(live) == 0 do
          acc
        else
          Map.put(acc, k, live)
        end
      end)

    %{@k => :or_set, entries: entries, tombstones: tombs}
  end

  # --------------------------------------------------------------------------
  # LWWRegister
  # --------------------------------------------------------------------------

  def lww_empty(node) when is_atom(node) do
    %{@k => :lww_register, value: :empty, stamp: 0, node: node}
  end

  def lww_set(%{@k => :lww_register}, value, stamp, node)
      when is_integer(stamp) and is_atom(node) do
    %{@k => :lww_register, value: value, stamp: stamp, node: node}
  end

  # An unset register has no value, so the result is an `Option(t)`. This used
  # to return the bare atom `:empty` under a declared `-> t`: at `t = Int` a
  # caller was promised an integer and handed `:empty`. Dependent-pipeline
  # erasure gives the OTP-compatible shapes `{:some, v}` and `:none`.
  # (The register's own `%{__struct__: :lww_register}` shape is internal and
  # opaque — Cure never matches it — so it stays a struct map.)
  def lww_value(%{@k => :lww_register, value: :empty}), do: :none
  def lww_value(%{@k => :lww_register, value: value}), do: {:some, value}

  def lww_merge(
        %{@k => :lww_register, stamp: sa, node: na} = a,
        %{@k => :lww_register, stamp: sb, node: nb} = b
      ) do
    cond do
      sa > sb -> a
      sa < sb -> b
      true -> if na >= nb, do: a, else: b
    end
  end

  # --------------------------------------------------------------------------
  # MVRegister
  # --------------------------------------------------------------------------

  def mv_empty, do: %{@k => :mv_register, writes: %{}}

  def mv_write(%{@k => :mv_register, writes: writes}, value, stamp, node)
      when is_integer(stamp) and is_atom(node) do
    # Each node keeps only its latest stamped write; older writes from
    # the same node are shadowed.
    case Map.get(writes, node) do
      {existing_stamp, _existing_value} when existing_stamp > stamp ->
        %{@k => :mv_register, writes: writes}

      _ ->
        %{@k => :mv_register, writes: Map.put(writes, node, {stamp, value})}
    end
  end

  def mv_values(%{@k => :mv_register, writes: writes}) do
    writes
    |> Enum.sort_by(fn {node, {stamp, _}} -> {stamp, node} end)
    |> Enum.map(fn {_node, {_stamp, v}} -> v end)
  end

  def mv_merge(%{@k => :mv_register, writes: a}, %{@k => :mv_register, writes: b}) do
    merged =
      Map.merge(a, b, fn _node, {sa, va}, {sb, vb} ->
        cond do
          sa > sb -> {sa, va}
          sa < sb -> {sb, vb}
          va >= vb -> {sa, va}
          true -> {sb, vb}
        end
      end)

    %{@k => :mv_register, writes: merged}
  end
end

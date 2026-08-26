defmodule Cure.MetaAST.ConformanceTripwireTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.MetaAST.Conformance

  @moduledoc false

  # The MetaAST-conformance tripwire over the whole first-party .cure corpus
  # (stdlib + examples + oracle probes + fixtures — every committed source). It is
  # the executable form of the meta-shape contract handed to Metastatic: the shape
  # is whatever these tests prove, and anything falling outside is a change target.
  #
  # Under decision D (2026-07-15 blind-spot design) Metastatic's traversal descends
  # meta values that contain nodes, so a subterm parked in meta is LEGAL — a node is
  # `{atom, keyword_list, _}` in every slot. What must hold instead is that the meta
  # shape is regular enough for that descent to be TOTAL and SOUND. Three invariants
  # (see `Cure.MetaAST.Conformance`), split by their nature:
  #
  #   * INV-C — soundness — is asserted HARD, because the corpus already satisfies
  #     it (measured):
  #       C.1  no guard-matching non-node in any meta value (`meta_nonnodes` empty) —
  #            the walker never descends opaque data as if it were a subterm.
  #       C.2  every node tag reaching a meta position is in the frozen vocabulary —
  #            a new atom in node-position (a new subterm kind, or an opaque payload
  #            wrongly shaped) trips the gate for a human to classify. This frozen
  #            set IS the node-tag half of the contract sent to Metastatic.
  #
  #   * INV-A / INV-B — completeness — are hard invariants. The corpus must be
  #     reachable by a canonical-guard walker; any new structural bucket is a
  #     normalization regression.

  # INV-C.2 — the frozen node-tag vocabulary. Exactly the canonical-node tags that
  # occur inside a meta value across the whole corpus (derived by enumeration, not
  # by hand). Equality is asserted both ways: a NEW tag means an unclassified atom
  # reached node-position in meta (soundness review); a VANISHED tag means the
  # vocabulary — and the contract sent to Metastatic — is stale and must be updated.
  @meta_vocabulary MapSet.new([
                     :as_pattern,
                     :attribute_access,
                     :binary_op,
                     :decorator,
                     :forced_pattern,
                     :function_call,
                     :lambda,
                     :list,
                     :literal,
                     :named_implicit_pat,
                     :param,
                     :pi_type,
                     :pin,
                     :sigma_type,
                     :tuple,
                     :tuple_type,
                     :typed_pattern,
                     :union_type,
                     :variable
                   ])

  # INV-A / INV-B — the shrinking structural allowlist. Each entry is a
  # {kind, tag, key} bucket (key always nil) whose nodes a canonical-guard walker
  # cannot reach. These are normalization targets, not permanent shape.
  @structural_allowlist MapSet.new()

  # Every committed first-party .cure tree. Detection is structural, so widening the
  # corpus only ever adds coverage — it never changes how a node is judged.
  @corpus_globs [
    "lib/std/*.cure",
    # "examples/**/*.cure", # intentionally excluded from 0.34 test runs
    "test/oracle/**/*.cure",
    "test/fixtures/*.cure"
  ]

  # One pass over the corpus, folding every file's analysis together:
  #   tags     — union of meta_node_tags (INV-C.2)
  #   buckets  — union of violation_buckets (INV-A/INV-B)
  #   nonnodes — concatenated meta_nonnodes (INV-C.1)
  #   failed   — files that did not parse (would silently shrink coverage)
  defp corpus do
    @corpus_globs
    |> Enum.flat_map(&Path.wildcard/1)
    |> Enum.uniq()
    |> Enum.reduce(%{tags: MapSet.new(), buckets: MapSet.new(), nonnodes: [], failed: []}, fn file, acc ->
      with {:ok, toks} <- Lexer.tokenize(File.read!(file), emit_events: false),
           {:ok, ast} <- Parser.parse(toks, emit_events: false) do
        %{
          acc
          | tags: MapSet.union(acc.tags, Conformance.meta_node_tags(ast)),
            buckets: MapSet.union(acc.buckets, Conformance.violation_buckets(ast)),
            nonnodes: acc.nonnodes ++ tag_file(Conformance.meta_nonnodes(ast), file)
        }
      else
        _ -> %{acc | failed: [Path.basename(file) | acc.failed]}
      end
    end)
  end

  defp tag_file(nonnodes, file), do: Enum.map(nonnodes, &Map.put(&1, :file, Path.basename(file)))

  setup_all do
    # Parsing and analysing the first-party corpus is the expensive part of this
    # tripwire. The result is immutable and every test examines the same snapshot,
    # so compute it once per module run instead of repeating the full pass five
    # times. A new `mix test` invocation always builds a fresh snapshot.
    {:ok, corpus: corpus()}
  end

  test "every first-party file parses (a parse failure would silently shrink coverage)", %{corpus: corpus} do
    failed = corpus.failed
    assert failed == [], "files failed to parse: #{Enum.join(failed, ", ")}"
  end

  test "INV-C.1: no guard-matching non-node appears in any meta value", %{corpus: corpus} do
    nonnodes = corpus.nonnodes

    assert nonnodes == [], """
    A meta value holds a tuple that Metastatic's descent guard (`{atom, is_list, _}`)
    would enter as a node, but that is not a canonical node (its second element is a
    list but not a keyword list). Descending it would make the walker treat opaque
    data as a subterm — an INV-C soundness break.

    #{Enum.map_join(nonnodes, "\n", fn e -> "  #{e.file}: #{inspect(e.tag)}  #{inspect(e.node)}" end)}

    Fix the producer so this is either a canonical node or opaque data with a
    non-list second element.
    """
  end

  test "INV-C.2: the node-tag vocabulary in meta is exactly the frozen set", %{corpus: corpus} do
    tags = corpus.tags
    new_tags = MapSet.difference(tags, @meta_vocabulary)
    gone_tags = MapSet.difference(@meta_vocabulary, tags)

    assert MapSet.equal?(tags, @meta_vocabulary), """
    The set of canonical-node tags reaching a meta position has drifted from the
    frozen INV-C vocabulary (which is also the node-tag contract sent to Metastatic).

    New in meta (classify — a new subterm kind is fine; an opaque payload wrongly
    shaped as `{atom, keyword_list, _}` is a soundness bug): #{inspect(MapSet.to_list(new_tags))}

    No longer in meta (the vocabulary and the Metastatic contract are stale — update
    both): #{inspect(MapSet.to_list(gone_tags))}
    """
  end

  test "INV-A/INV-B: no structural violation outside the shrinking allowlist", %{corpus: corpus} do
    unexpected = MapSet.difference(corpus.buckets, @structural_allowlist)

    assert MapSet.equal?(unexpected, MapSet.new()), """
    New MetaAST structural violation(s) not in the allowlist:

    #{format(unexpected)}

    A node here is invisible to a canonical-guard walker (its subterms are lost).
    Either bring it to canonical shape (INV-A: 3-tuple node; INV-B: list children)
    or, if this is a deliberate new construct, add its {kind, tag, nil} bucket to
    @structural_allowlist with a note.
    """
  end

  test "INV-A/INV-B: the structural allowlist has no stale entries (forces it to shrink)", %{corpus: corpus} do
    stale = MapSet.difference(@structural_allowlist, corpus.buckets)

    assert MapSet.equal?(stale, MapSet.new()), """
    Allowlisted structural bucket(s) no longer occur in the corpus:

    #{format(stale)}

    These were normalized (or the construct was removed). Delete them from
    @structural_allowlist — it must only ever shrink.
    """
  end

  defp format(set) do
    set
    |> Enum.sort()
    |> Enum.map_join("\n", fn {kind, tag, key} -> "  #{kind}  #{inspect(tag)}  #{inspect(key)}" end)
  end
end

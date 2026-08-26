defmodule Cure.MetaAST.Conformance do
  @moduledoc """
  Structural MetaAST-conformance check for Cure's *surface* AST.

  ## Decision D — meta is a legal home for subterms

  Metastatic's canonical node is `{type, meta, children}`: an atom `type`, a
  keyword-list `meta`, and children in the third slot. Historically its traversal
  (`Metastatic.AST.traverse/4`) recursed ONLY the children slot, so any subterm
  parked in a meta value was invisible to every consumer (RAG, MCP, the migrator).
  Cure keeps its whole signature / type / pattern layer in meta (a `param`'s type
  under `:type`, a `function_def`'s `:params` / `:return_type`, a `match_arm`'s
  `:pattern`), so that layer was dark.

  The resolution (2026-07-15 blind-spot design, **Option D**) is that Metastatic's
  traversal will structurally DESCEND meta values that contain nodes — nodes stay
  in meta; the walker reaches them. This is right because in a dependent language
  types ARE terms: the `n` in `Vec n a` (a meta/type position) and the `n` in the
  body (a child/term position) are the *same* node, and a node's encoding must not
  depend on its slot. A node is `{atom, keyword_list, _}` in EVERY slot.

  For that descent to be **total** (reach every node) and **sound** (never descend
  non-node data), the surface must satisfy three invariants. This module is the
  total-descent DUAL of the walker: it checks each one.

    * **INV-A — canonicity.** Every node, in meta OR children, is the canonical
      3-tuple. A node hidden inside a non-canonical atom-headed tuple is a
      `:bad_shape` violation: the walker cannot recognise it, so its subterms are
      lost (completeness failure). The first-party corpus currently satisfies this
      invariant, including dependent constructor domains and arrow chains.

    * **INV-B — composite children are lists.** A composite node's children slot is
      a LIST of child nodes; only the fixed leaf tags (`:variable`, `:literal`,
      `:comment`) carry a bare scalar there. A bare node in a children slot is a
      `:node_child` violation — the walker's `traverse_children` recurses only an
      `is_list` slot, so the subtree is dropped (completeness failure).
      A bare node in a composite children slot is therefore always a violation;
      the first-party corpus currently satisfies this invariant.

    * **INV-C — meta predicate soundness.** Within every meta value, every
      atom-headed tuple is EITHER a canonical node whose tag is in the known
      meta-node vocabulary, OR opaque leaf data with a NON-list second element (an
      MFA `{:erlang, :length, 1}`, a `{:group_ref, :core, 1}`, a module reference).
      No atom-headed tuple in meta has a list second element unless it is a genuine
      node. This is what makes "descend any guard-matching value in meta" sound —
      the walker never mistakes opaque data for a subterm. Two queries express it:
      `meta_nonnodes/1` (guard-matching non-nodes — must be empty) and
      `meta_node_tags/1` (the node-tag vocabulary — pinned by the corpus tripwire).

  INV-A and INV-B are *completeness* obligations; `violations/1` reports any
  regression and the corpus tripwire drives them to zero. INV-C is a *soundness*
  obligation the corpus already
  satisfies (measured: the danger set is empty) and the tripwire pins as a hard
  invariant. Note a node placed in meta is NOT itself a violation any more — that is
  the whole point of Option D.

  Deliberately NOT built on `Metastatic.AST.conforms?/1`: that predicate gates on a
  fixed `@all_types` registry which omits ~100 of Cure's node atoms (every
  dependent / macro / concurrency former), so it rejects almost the whole surface.
  Conformance here is about SHAPE and PLACEMENT, not type-registry membership.
  """

  # Wide tuples carried as trivia, NOT normalization targets. Comments are leaves
  # under Metastatic's traversal anyway — their payload is never a node — so their
  # non-3-tuple shape hides no subterms and needs no rewrite.
  @trivia_tags [:comment, :doc_comment]

  @type kind :: :bad_shape | :node_child

  @type violation :: %{
          kind: kind(),
          path: [atom()],
          tag: atom(),
          key: atom() | nil,
          arity: non_neg_integer() | nil,
          node: term()
        }

  @typedoc """
  A guard-matching non-node found in a meta value: a tuple Metastatic's descent
  guard (`{atom, is_list(second), _}`) would enter, that is NOT a canonical node
  (its second element is a list but not a keyword list). The corpus contains none;
  any occurrence is an INV-C soundness break.
  """
  @type meta_nonnode :: %{path: [atom()], tag: atom(), node: term()}

  @doc """
  True iff `ast` has no INV-A / INV-B structural violation. This is the completeness
  end-state (walker reaches every node). Real Cure surface currently fails it — that
  is what the corpus tripwire tracks — and INV-C soundness is checked separately via
  `meta_nonnodes/1`.
  """
  @spec conformant?(term()) :: boolean()
  def conformant?(ast), do: violations(ast) == []

  @doc """
  Every INV-A (`:bad_shape`) / INV-B (`:node_child`) violation in `ast`, in
  pre-order (outermost first). A node parked in a meta VALUE is not a violation
  (Option D) — but a non-canonical tuple hiding a node, or a non-list children
  slot, is reported wherever it occurs, meta or children.
  """
  @spec violations(term()) :: [violation()]
  def violations(ast), do: ast |> analyze() |> Map.fetch!(:violations) |> Enum.reverse()

  @doc """
  The distinct `{kind, tag, key}` structural-violation buckets present in `ast`
  (`key` is always `nil` now). This is the granularity the corpus tripwire
  allowlists against — robust to stdlib churn.
  """
  @spec violation_buckets(term()) :: MapSet.t({kind(), atom(), nil})
  def violation_buckets(ast) do
    ast
    |> violations()
    |> Enum.map(fn %{kind: kind, tag: tag, key: key} -> {kind, tag, key} end)
    |> MapSet.new()
  end

  @doc """
  The set of canonical-node tags that appear inside a meta value anywhere in `ast`
  (INV-C vocabulary). Every tag here is a genuine subterm the walker will descend
  when it enters meta; the corpus tripwire pins this set so a new atom reaching
  node-position in meta — a new subterm kind, or an opaque payload wrongly shaped —
  trips the gate for a human to classify.
  """
  @spec meta_node_tags(term()) :: MapSet.t(atom())
  def meta_node_tags(ast), do: ast |> analyze() |> Map.fetch!(:meta_tags)

  @doc """
  Guard-matching non-nodes found in meta values (INV-C soundness). Each is a tuple
  Metastatic's `is_list`-second descent guard would enter but that is not a genuine
  node. The corpus contains none; a non-empty result is a soundness break that would
  make the walker descend opaque data.
  """
  @spec meta_nonnodes(term()) :: [meta_nonnode()]
  def meta_nonnodes(ast), do: ast |> analyze() |> Map.fetch!(:meta_nonnodes) |> Enum.reverse()

  @doc """
  A short human-readable line per structural violation, suitable for a warning or a
  test failure message.
  """
  @spec describe([violation()]) :: String.t()
  def describe([]), do: "no MetaAST-conformance violations"

  def describe(violations) do
    Enum.map_join(violations, "\n", fn
      %{kind: :bad_shape, tag: tag, arity: arity, path: path} ->
        "  * [bad_shape] #{inspect(tag)} (arity #{arity}) at #{path_string(path)}"

      %{kind: :node_child, tag: tag, path: path} ->
        "  * [node_child] #{inspect(tag)} children slot is a bare node, not a list, at #{path_string(path)}"
    end)
  end

  @doc """
  Canonicalizes a surface MetaAST tree so that subterms in meta slots are lifted
  into child wrapper nodes, returning a strictly conformant tree for external AST consumers.
  """
  @spec to_conformant(term()) :: term()
  def to_conformant({tag, meta, children}) when is_atom(tag) and is_list(meta) do
    {lifted_meta_children, clean_meta} = extract_meta_subterms(meta)

    normalized_children =
      cond do
        is_list(children) -> Enum.map(children, &to_conformant/1)
        canonical_node?(children) -> [to_conformant(children)]
        true -> children
      end

    {tag, clean_meta, lifted_meta_children ++ normalized_children}
  end

  def to_conformant(list) when is_list(list), do: Enum.map(list, &to_conformant/1)

  def to_conformant(tuple) when is_tuple(tuple) do
    tuple |> Tuple.to_list() |> Enum.map(&to_conformant/1) |> List.to_tuple()
  end

  def to_conformant(other), do: other

  defp extract_meta_subterms(meta) when is_list(meta) do
    Enum.reduce(meta, {[], []}, fn {key, val}, {children_acc, meta_acc} ->
      if hides_node?(val) do
        wrapper_tag = String.to_atom("#{key}_wrapper")
        wrapper_node = {wrapper_tag, [], [to_conformant(val)]}
        {children_acc ++ [wrapper_node], meta_acc}
      else
        {children_acc, meta_acc ++ [{key, val}]}
      end
    end)
  end

  defp path_string(path), do: Enum.map_join(path, ".", &Atom.to_string/1)

  # ── analysis ──────────────────────────────────────────────────────────────
  #
  # A single pre-order walk collects everything the three invariants need:
  #   :violations    — INV-A/INV-B, in reverse order (see violations/1)
  #   :meta_tags     — INV-C vocabulary (canonical tags reached inside meta)
  #   :meta_nonnodes — INV-C danger set (guard-matching non-nodes in meta)
  #
  # `in_meta?` is threaded through the walk: it becomes true the moment we descend a
  # meta value and STAYS true through any nested node's children (everything under a
  # meta value is reachable only via meta). It governs the two INV-C collectors; the
  # INV-A/INV-B checks fire regardless of slot.

  @empty %{violations: [], meta_tags: MapSet.new(), meta_nonnodes: []}

  @doc false
  @spec analyze(term()) :: %{
          violations: [violation()],
          meta_tags: MapSet.t(atom()),
          meta_nonnodes: [meta_nonnode()]
        }
  def analyze(ast), do: walk(ast, [], false, @empty)

  # An atom-headed tuple — the shape of a node. Outcomes:
  #
  #   * canonical `{tag, keyword_meta, children}` → record the tag if we are in
  #     meta (vocabulary), descend the meta values (INV-C soundness + deeper
  #     violations) and the children slot.
  #   * non-canonical but HIDES a node → INV-A `:bad_shape`; flag and descend.
  #   * non-canonical, hides no node, but is guard-matching (is_list second) while
  #     in meta → an INV-C `meta_nonnode` soundness break; record and descend.
  #   * otherwise opaque leaf data (MFA, module ref) → conformant; do not flag.
  defp walk(node, path, in_meta?, acc)
       when is_tuple(node) and tuple_size(node) >= 1 and is_atom(:erlang.element(1, node)) do
    tag = elem(node, 0)

    cond do
      tag in @trivia_tags ->
        acc

      canonical_node?(node) ->
        acc = if in_meta?, do: add_tag(acc, tag), else: acc
        acc = walk_meta(elem(node, 1), [tag | path], acc)
        walk_children(elem(node, 2), tag, path, in_meta?, acc)

      Enum.any?(non_meta_elements(node), &hides_node?/1) ->
        flag_bad_shape_and_descend(node, tag, path, in_meta?, acc)

      in_meta? and guard_match?(node) ->
        acc = add_meta_nonnode(acc, node, tag, path)
        descend_elements(node, [tag | path], in_meta?, acc)

      true ->
        acc
    end
  end

  # A non-node-shaped tuple (e.g. a `{key_node, value_node}` pair): descend every
  # element, preserving `in_meta?`.
  defp walk(node, path, in_meta?, acc) when is_tuple(node) do
    node |> Tuple.to_list() |> Enum.reduce(acc, fn el, acc -> walk(el, path, in_meta?, acc) end)
  end

  # A keyword list encountered as a value is META structure: descend the VALUE side
  # of each pair (marking in_meta?), never the key. A plain list is children/args:
  # descend each element, preserving in_meta?.
  defp walk(list, path, in_meta?, acc) when is_list(list) do
    if keyword_list?(list) do
      Enum.reduce(list, acc, fn {_k, v}, acc -> walk(v, path, true, acc) end)
    else
      Enum.reduce(list, acc, fn el, acc -> walk(el, path, in_meta?, acc) end)
    end
  end

  # Primitive leaf (integer, atom, string, nil, …): nothing to descend.
  defp walk(_other, _path, _in_meta?, acc), do: acc

  # The meta of a canonical node. Every value is descended with `in_meta?` = true —
  # that is where INV-C's vocabulary and danger checks apply. Keys are never nodes.
  # `path` already includes the parent tag.
  defp walk_meta(meta, path, acc) do
    Enum.reduce(meta, acc, fn {_key, value}, acc -> walk(value, path, true, acc) end)
  end

  # The children slot of a canonical node. It must be a LIST — the only shape
  # `traverse_children` recurses. A leaf node legitimately carries an opaque scalar
  # here (hides nothing). Anything else that hides a node is INV-B `:node_child`;
  # descend it to surface deeper defects without re-flagging the slot term itself.
  # `in_meta?` is preserved (children of a meta-node are still reached via meta).
  defp walk_children(children, tag, path, in_meta?, acc) when is_list(children) do
    Enum.reduce(children, acc, fn el, acc -> walk(el, [tag | path], in_meta?, acc) end)
  end

  defp walk_children(children, tag, path, in_meta?, acc) do
    if hides_node?(children) do
      violation = %{
        kind: :node_child,
        path: Enum.reverse([tag | path]),
        tag: tag,
        key: nil,
        arity: nil,
        node: children
      }

      descend_child(children, [tag | path], in_meta?, add_violation(acc, violation))
    else
      acc
    end
  end

  # Descend a non-list children term already flagged `:node_child`, surfacing nested
  # violations without re-flagging the term.
  defp descend_child(child, path, in_meta?, acc) do
    if is_tuple(child) and tuple_size(child) >= 1 and is_atom(:erlang.element(1, child)) and
         not canonical_node?(child) do
      descend_elements(child, path, in_meta?, acc)
    else
      walk(child, path, in_meta?, acc)
    end
  end

  defp flag_bad_shape_and_descend(node, tag, path, in_meta?, acc) do
    violation = %{
      kind: :bad_shape,
      path: Enum.reverse([tag | path]),
      tag: tag,
      key: nil,
      arity: tuple_size(node),
      node: node
    }

    descend_elements(node, [tag | path], in_meta?, add_violation(acc, violation))
  end

  # Descend every element after the tag. A keyword-list element is treated as a meta
  # slot (walk its VALUES with in_meta? = true, not its keys); every other element is
  # walked with the inherited `in_meta?`. The tuple itself is an already-flagged
  # normalization target, so we only surface violations nested inside.
  defp descend_elements(node, path, in_meta?, acc) do
    node
    |> Tuple.to_list()
    |> tl()
    |> Enum.reduce(acc, fn el, acc ->
      if keyword_list?(el),
        do: Enum.reduce(el, acc, fn {_k, v}, acc -> walk(v, path, true, acc) end),
        else: walk(el, path, in_meta?, acc)
    end)
  end

  defp add_violation(acc, v), do: %{acc | violations: [v | acc.violations]}
  defp add_tag(acc, tag), do: %{acc | meta_tags: MapSet.put(acc.meta_tags, tag)}

  defp add_meta_nonnode(acc, node, tag, path) do
    entry = %{path: Enum.reverse([tag | path]), tag: tag, node: node}
    %{acc | meta_nonnodes: [entry | acc.meta_nonnodes]}
  end

  # A canonical MetaAST node: 3-tuple, atom tag, keyword-list meta. Exactly the shape
  # Metastatic descends into (with its guard tightened from `is_list` to keyword —
  # see guard_match?/1 for the looser shape the walker actually tests).
  defp canonical_node?(node) do
    is_tuple(node) and tuple_size(node) == 3 and is_atom(elem(node, 0)) and
      is_list(elem(node, 1)) and Keyword.keyword?(elem(node, 1))
  end

  # Metastatic's ACTUAL descent guard: a 3-tuple with an atom tag and an `is_list`
  # second element — NOT necessarily a keyword list. A tuple that is guard_match? but
  # not canonical_node? (list-but-not-keyword second) is what the walker would enter
  # as a node yet is not one: the INV-C danger shape.
  defp guard_match?(node) do
    is_tuple(node) and tuple_size(node) == 3 and is_atom(elem(node, 0)) and is_list(elem(node, 1))
  end

  # Does `term` contain a canonical node anywhere traversal would need to reach? This
  # separates a malformed NODE (hides real structure — the defect we flag) from
  # opaque leaf DATA that merely happens to be an atom-headed tuple (an MFA, a
  # decorator argument): the latter holds only primitives and hides nothing.
  defp hides_node?(term) when is_tuple(term) do
    cond do
      canonical_node?(term) -> true
      tuple_size(term) >= 1 and is_atom(elem(term, 0)) -> Enum.any?(non_meta_elements(term), &hides_node?/1)
      true -> term |> Tuple.to_list() |> Enum.any?(&hides_node?/1)
    end
  end

  defp hides_node?(term) when is_list(term), do: Enum.any?(term, &hides_node?/1)
  defp hides_node?(_term), do: false

  # A node's elements after the tag, with any meta (keyword-list) slot removed.
  defp non_meta_elements(node) do
    node |> Tuple.to_list() |> tl() |> Enum.reject(&keyword_list?/1)
  end

  # A non-empty keyword list — the shape of a meta slot. `[]` is excluded so an empty
  # children list is still walked as children, not skipped as meta.
  defp keyword_list?(term), do: is_list(term) and term != [] and Keyword.keyword?(term)
end

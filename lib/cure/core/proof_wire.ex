defmodule Cure.Core.ProofWire do
  @moduledoc """
  Render Core terms as the serialised wire format formalised in
  `proof/Core/Wire.agda`.

  This is a REPRESENTATION bridge, not a certificate, an admission gate or a
  proof: it renders data the formal side can decode, and nothing here is
  proved about Elixir. The Agda development carries the codec and its
  round-trip (`Core.Wire.decode-encode`); this module is the producer side.

  ## Grammar (mirrored exactly from `Core/Wire.agda`)

      instruction  characters        meaning
      i-atom k     '1'…'1' ';'       a natural `k`, in unary
      i-open       '('               open a child list
      i-close      ')'               close the current child list

  A term first reflects to the `Code` tree of `Core.SyntaxEquality`
  (`code/1`, tags below), then each code interns its name and becomes a node
  `[tag, name-index, number, children…]`, which renders as above.

  ## Names are interned

  The wire never carries a name's characters: a character-faithful `String`
  round-trip is not provable in the formal development (the standard library
  offers only injectivity, and the missing direction is a postulate it
  refuses to use). The caller supplies a NAME TABLE and the wire carries an
  INDEX into it. The empty name `""` of the non-name code nodes must be in
  the table, and `intern/2` returns `{:error, {:unknown_name, name}}` for a
  name the table lacks — exactly as the formal encoder is partial.

  ## Tag table (from `Core.SyntaxEquality.encode`)

  | tag | node | tag | node |
  |----|----|----|----|
  | 0 | `type` | 11 / 12 | `int_lit` positive / negative-successor |
  | 1 | `var` | 13 | `nat_lit` |
  | 2 | `pi` | 14 | `bounded_lit` |
  | 3 | `lam` | 15 | `float_type` |
  | 4 | `let` | 16 | `float_lit` |
  | 5 | `app` | 17 | `binary_type` |
  | 6 | `data` | 18 | `atom_type` |
  | 7 | `ctor` | 19 | `atom_lit` |
  | 8 | `case` | 20 | effect nodes and development leaves |
  | 9 | `global` | | `number` `0` type, `1` pure, `2` bind, `3` hole, `4` absurd |
  | 10 | `int_type` | 100 | a plain child list (data params/indices, case branches) |

  Grades render as `erased` 0, `linear` 1, `affine` 2, `unrestricted` 3. A
  case branch renders as tag `0` with the constructor's name index as its
  name and its arity as its number, exactly as the formal encoder does.

  ## Scope

  Rendering is TOTAL over the Core taxonomy and PARTIAL over names, matching
  the formal encoder. Nothing here decides typing, admission or coverage.
  In particular `{:float_lit}` has no payload on the wire, mirroring the
  formal syntax; and no byte-for-byte claim is made about any fixture until
  the generated Agda fixture is regenerated and checked.
  """

  @type table :: [atom() | String.t()]
  @type error :: {:unknown_name, term()} | {:malformed_term, term()}

  @doc """
  Render a Core term to wire characters, interning names against `table`.

  Returns `{:ok, characters}`, or `{:error, {:unknown_name, name}}` when a
  name is absent from the table, or `{:error, {:malformed_term, term}}`.
  """
  @spec encode_term(Cure.Core.Term.t(), table()) :: {:ok, String.t()} | {:error, error()}
  def encode_term(term, table) when is_list(table) do
    with {:ok, code} <- code(term),
         {:ok, interned} <- intern(code, table) do
      {:ok, render(interned)}
    end
  end

  @doc "The interned index of `name` in `table`, or `:error` when absent."
  @spec index_of(atom() | String.t(), table()) :: {:ok, non_neg_integer()} | :error
  def index_of(name, table) do
    case Enum.find_index(table, &same_name?(&1, name)) do
      nil -> :error
      index -> {:ok, index}
    end
  end

  @doc """
  Reflect a Core term to the `Code` tree of `Core.SyntaxEquality`.

  The tree carries names as strings; `intern/2` replaces them with indices.
  """
  @spec code(Cure.Core.Term.t()) :: {:ok, tuple()} | {:error, error()}
  def code(term)

  def code({:type, level}) when is_integer(level) and level >= 0, do: {:ok, node(0, "", level, [])}
  def code({:var, k}) when is_integer(k) and k >= 0, do: {:ok, node(1, "", k, [])}

  def code({:pi, grade, dom, cod}) do
    with {:ok, d} <- code(dom), {:ok, c} <- code(cod) do
      {:ok, node(2, "", grade_number(grade), [d, c])}
    end
  end

  def code({:lam, grade, dom, body}) do
    with {:ok, d} <- code(dom), {:ok, b} <- code(body) do
      {:ok, node(3, "", grade_number(grade), [d, b])}
    end
  end

  def code({:let, grade, ty, value, body}) do
    with {:ok, t} <- code(ty),
         {:ok, v} <- code(value),
         {:ok, b} <- code(body) do
      {:ok, node(4, "", grade_number(grade), [t, v, b])}
    end
  end

  def code({:app, fun, arg}) do
    with {:ok, f} <- code(fun), {:ok, a} <- code(arg) do
      {:ok, node(5, "", 0, [f, a])}
    end
  end

  def code({:data, name, params, indices}) do
    with {:ok, ps} <- codes(params), {:ok, is} <- codes(indices) do
      {:ok, node(6, name_of(name), 0, [node(100, "", 0, ps), node(100, "", 0, is)])}
    end
  end

  def code({:ctor, name, args}) do
    with {:ok, as} <- codes(args) do
      {:ok, node(7, name_of(name), 0, as)}
    end
  end

  def code({:case, scrutinee, motive, branches}) do
    with {:ok, s} <- code(scrutinee),
         {:ok, m} <- code(motive),
         {:ok, bs} <- branch_codes(branches) do
      {:ok, node(8, "", 0, [s, m, node(100, "", 0, bs)])}
    end
  end

  def code({:global, name}), do: {:ok, node(9, name_of(name), 0, [])}
  def code({:int_type}), do: {:ok, node(10, "", 0, [])}

  def code({:int_lit, value}) when is_integer(value) and value >= 0,
    do: {:ok, node(11, "", value, [])}

  def code({:int_lit, value}) when is_integer(value),
    do: {:ok, node(12, "", -value - 1, [])}

  def code({:nat_lit, k}) when is_integer(k) and k >= 0, do: {:ok, node(13, "", k, [])}
  def code({:bounded_lit, k}) when is_integer(k) and k >= 0, do: {:ok, node(14, "", k, [])}
  def code({:float_type}), do: {:ok, node(15, "", 0, [])}
  def code({:float_lit}), do: {:ok, node(16, "", 0, [])}
  def code({:binary_type}), do: {:ok, node(17, "", 0, [])}
  def code({:atom_type}), do: {:ok, node(18, "", 0, [])}
  def code({:atom_lit, name}), do: {:ok, node(19, name_of(name), 0, [])}

  def code({:effect_type, inner}) do
    with {:ok, i} <- code(inner), do: {:ok, node(20, "", 0, [i])}
  end

  def code({:effect_pure, inner}) do
    with {:ok, i} <- code(inner), do: {:ok, node(20, "", 1, [i])}
  end

  def code({:effect_bind, effect, continuation}) do
    with {:ok, e} <- code(effect), {:ok, k} <- code(continuation) do
      {:ok, node(20, "", 2, [e, k])}
    end
  end

  def code({:hole, name}), do: {:ok, node(20, name_of(name), 3, [])}
  def code({:absurd}), do: {:ok, node(20, "", 4, [])}
  def code(other), do: {:error, {:malformed_term, other}}

  defp codes(terms) when is_list(terms), do: codes_loop(terms, [])
  defp codes(other), do: {:error, {:malformed_term, other}}

  defp codes_loop([], acc), do: {:ok, Enum.reverse(acc)}

  defp codes_loop([term | rest], acc) do
    case code(term) do
      {:ok, code} -> codes_loop(rest, [code | acc])
      error -> error
    end
  end

  defp branch_codes(branches) when is_list(branches), do: branch_loop(branches, [])
  defp branch_codes(other), do: {:error, {:malformed_term, other}}

  defp branch_loop([], acc), do: {:ok, Enum.reverse(acc)}

  defp branch_loop([{name, arity, body} | rest], acc) when is_integer(arity) and arity >= 0 do
    case code(body) do
      {:ok, b} -> branch_loop(rest, [node(0, name_of(name), arity, [b]) | acc])
      error -> error
    end
  end

  defp branch_loop([other | _rest], _acc), do: {:error, {:malformed_term, other}}

  @doc """
  Replace every name in a `Code` tree with its index in `table`.

  Returns `{:error, {:unknown_name, name}}` for the first name the table
  lacks, mirroring the formal encoder's partiality.
  """
  @spec intern(tuple(), table()) :: {:ok, tuple()} | {:error, error()}
  def intern({:node, tag, name, number, kids}, table) do
    with {:ok, index} <- interned_index(name, table),
         {:ok, interned_kids} <- intern_all(kids, table) do
      {:ok, {:node, tag, index, number, interned_kids}}
    end
  end

  defp interned_index(name, table) do
    case index_of(name, table) do
      {:ok, index} -> {:ok, index}
      :error -> {:error, {:unknown_name, name}}
    end
  end

  defp intern_all(kids, table) do
    Enum.reduce_while(kids, {:ok, []}, fn kid, {:ok, acc} ->
      case intern(kid, table) do
        {:ok, interned} -> {:cont, {:ok, [interned | acc]}}
        error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, reversed} -> {:ok, Enum.reverse(reversed)}
      error -> error
    end
  end

  @doc "Render an interned code node to wire characters."
  @spec render(tuple()) :: String.t()
  def render({:node, _tag, _index, _number, _kids} = code), do: render_node(code)

  defp render_node({:node, tag, index, number, kids}) do
    "(" <> atom(tag) <> atom(index) <> atom(number) <> Enum.map_join(kids, &render_node/1) <> ")"
  end

  # A unary natural terminated by ';'.
  defp atom(k) when is_integer(k) and k >= 0, do: String.duplicate("1", k) <> ";"

  defp node(tag, name, number, kids), do: {:node, tag, name, number, kids}

  # An atom and its string form are the same wire identity, matching the
  # formal side's first-match string keys.
  defp same_name?(left, right), do: name_of(left) == name_of(right)

  defp name_of(name) when is_atom(name), do: Atom.to_string(name)
  defp name_of(name) when is_binary(name), do: name
  defp name_of(other), do: other

  defp grade_number(:erased), do: 0
  defp grade_number(:linear), do: 1
  defp grade_number(:affine), do: 2
  defp grade_number(:unrestricted), do: 3
end

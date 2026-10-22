defmodule Cure.Core.ProofWire do
  @moduledoc """
  Render Core terms as the serialised wire format formalised in
  `proof/Core/Wire.agda`.

  This is a REPRESENTATION bridge, not a certificate, an admission gate or a
  proof: it renders data the formal side can decode, and nothing here is
  proved about Elixir. The Agda development carries the codec and its
  round-trip (`Core.Wire.decode-encode`) and validates canonical reflected
  term codes before accepting them; this module is the producer side.

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
  INDEX into it. Include the empty name `""` whenever a term has non-name
  code nodes. `intern/2` returns `{:error, {:unknown_name, name}}` for a
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

  This is a PARTIAL representation bridge, not typing, admission or coverage.
  Tuple shapes, universe bounds, grades, symbol representations and name tables
  are checked. Symbolic names may be atoms or valid UTF-8 strings.

  Actual `{:float_lit, value}` payloads cannot be represented by the current
  payload-free formal Float node: they are explicitly unsupported, never
  silently erased. The malformed placeholder `{:float_lit}` is rejected too.
  Tag 16 remains part of the FORMAL codec, not this producer's supported slice.
  No universal producer/decoder correspondence is established by concrete vectors.
  """
  alias Cure.Core.{Grade, Universe}
  @ceiling Universe.ceiling()

  @type table :: [atom() | String.t()]
  @type error ::
          {:unknown_name, term()}
          | {:malformed_term, term()}
          | {:malformed_table, term()}
          | {:malformed_code, term()}
          | {:unsupported_term, term()}

  @doc """
  Render a Core term to wire characters, interning names against `table`.

  Returns `{:ok, characters}`, or `{:error, {:unknown_name, name}}` when a
  name is absent from the table. Invalid shapes/tables return structured
  `:malformed_term`/`:malformed_table` errors; actual Float payloads return
  `:unsupported_term` until a payload-faithful formal representation exists.
  """
  @spec encode_term(term(), table()) :: {:ok, String.t()} | {:error, error()}
  def encode_term(term, table) do
    if valid_table?(table) do
      with {:ok, code} <- code(term),
           {:ok, interned} <- intern_code(code, table) do
        {:ok, render(interned)}
      end
    else
      {:error, {:malformed_table, table}}
    end
  end

  @doc "The interned index of `name` in `table`, or `:error` when absent."
  @spec index_of(atom() | String.t(), table()) :: {:ok, non_neg_integer()} | :error
  def index_of(name, table) do
    if valid_name?(name) and valid_table?(table), do: find_index(name, table), else: :error
  end

  defp find_index(name, table) do
    case Enum.find_index(table, &same_name?(&1, name)) do
      nil -> :error
      index -> {:ok, index}
    end
  end

  @doc """
  Reflect a Core term to the `Code` tree of `Core.SyntaxEquality`.

  The tree carries names as strings; `intern/2` replaces them with indices.
  """
  @spec code(term()) :: {:ok, tuple()} | {:error, error()}
  def code(term)

  def code({:type, level}) when is_integer(level) and level >= 0 and level <= @ceiling,
    do: {:ok, node(0, "", level, [])}

  def code({:var, k}) when is_integer(k) and k >= 0, do: {:ok, node(1, "", k, [])}

  def code({:pi, grade, dom, cod} = term) do
    with {:ok, number} <- grade_number(grade), {:ok, d} <- code(dom), {:ok, c} <- code(cod) do
      {:ok, node(2, "", number, [d, c])}
    else
      :error -> {:error, {:malformed_term, term}}
      {:error, _} = error -> error
    end
  end

  def code({:lam, grade, dom, body} = term) do
    with {:ok, number} <- grade_number(grade), {:ok, d} <- code(dom), {:ok, b} <- code(body) do
      {:ok, node(3, "", number, [d, b])}
    else
      :error -> {:error, {:malformed_term, term}}
      {:error, _} = error -> error
    end
  end

  def code({:let, grade, ty, value, body} = term) do
    with {:ok, number} <- grade_number(grade),
         {:ok, t} <- code(ty),
         {:ok, v} <- code(value),
         {:ok, b} <- code(body) do
      {:ok, node(4, "", number, [t, v, b])}
    else
      :error -> {:error, {:malformed_term, term}}
      {:error, _} = error -> error
    end
  end

  def code({:app, fun, arg}) do
    with {:ok, f} <- code(fun), {:ok, a} <- code(arg) do
      {:ok, node(5, "", 0, [f, a])}
    end
  end

  def code({:data, name, params, indices} = term) do
    with {:ok, ps} <- codes(params), {:ok, is} <- codes(indices) do
      named(6, name, 0, [node(100, "", 0, ps), node(100, "", 0, is)], term)
    end
  end

  def code({:ctor, name, args} = term) do
    with {:ok, as} <- codes(args) do
      named(7, name, 0, as, term)
    end
  end

  def code({:case, scrutinee, motive, branches}) do
    with {:ok, s} <- code(scrutinee),
         {:ok, m} <- code(motive),
         {:ok, bs} <- branch_codes(branches) do
      {:ok, node(8, "", 0, [s, m, node(100, "", 0, bs)])}
    end
  end

  def code({:global, name} = term), do: named(9, name, 0, [], term)
  def code({:int_type}), do: {:ok, node(10, "", 0, [])}

  def code({:int_lit, value}) when is_integer(value) and value >= 0,
    do: {:ok, node(11, "", value, [])}

  def code({:int_lit, value}) when is_integer(value),
    do: {:ok, node(12, "", -value - 1, [])}

  def code({:nat_lit, k}) when is_integer(k) and k >= 0, do: {:ok, node(13, "", k, [])}
  def code({:bounded_lit, k}) when is_integer(k) and k >= 0, do: {:ok, node(14, "", k, [])}
  def code({:float_type}), do: {:ok, node(15, "", 0, [])}
  def code({:float_lit, value} = term) when is_float(value), do: {:error, {:unsupported_term, term}}
  def code({:binary_type}), do: {:ok, node(17, "", 0, [])}
  def code({:atom_type}), do: {:ok, node(18, "", 0, [])}
  def code({:atom_lit, name} = term), do: named(19, name, 0, [], term)

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

  def code({:hole, name} = term), do: named(20, name, 3, [], term)
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

  defp codes_loop(other, _acc), do: {:error, {:malformed_term, other}}

  defp branch_codes(branches) when is_list(branches), do: branch_loop(branches, [])
  defp branch_codes(other), do: {:error, {:malformed_term, other}}

  defp branch_loop([], acc), do: {:ok, Enum.reverse(acc)}

  defp branch_loop([{name, arity, body} = branch | rest], acc) when is_integer(arity) and arity >= 0 do
    with {:ok, b} <- code(body), {:ok, reflected} <- named(0, name, arity, [b], branch) do
      branch_loop(rest, [reflected | acc])
    else
      error -> error
    end
  end

  defp branch_loop([other | _rest], _acc), do: {:error, {:malformed_term, other}}
  defp branch_loop(other, _acc), do: {:error, {:malformed_term, other}}

  @doc """
  Replace every name in a `Code` tree with its index in `table`.

  Returns `{:error, {:unknown_name, name}}` for the first name the table
  lacks, mirroring the formal encoder's partiality.
  """
  @spec intern(tuple(), table()) :: {:ok, tuple()} | {:error, error()}
  def intern(code, table) do
    if valid_table?(table), do: intern_code(code, table), else: {:error, {:malformed_table, table}}
  end

  defp intern_code({:node, tag, name, number, kids} = code, table)
       when is_integer(tag) and tag >= 0 and is_integer(number) and number >= 0 do
    if valid_name?(name) do
      with {:ok, index} <- interned_index(name, table),
           {:ok, interned_kids} <- intern_all(kids, table) do
        {:ok, {:node, tag, index, number, interned_kids}}
      end
    else
      {:error, {:malformed_code, code}}
    end
  end

  defp intern_code(other, _table), do: {:error, {:malformed_code, other}}

  defp interned_index(name, table) do
    case find_index(name, table) do
      {:ok, index} -> {:ok, index}
      :error -> {:error, {:unknown_name, name}}
    end
  end

  defp intern_all([], _table), do: {:ok, []}

  defp intern_all([kid | rest], table) do
    with {:ok, interned} <- intern_code(kid, table),
         {:ok, tail} <- intern_all(rest, table) do
      {:ok, [interned | tail]}
    else
      error -> error
    end
  end

  defp intern_all(other, _table), do: {:error, {:malformed_code, other}}

  @doc "Render a validated interned code node to wire characters."
  @spec render(tuple()) :: String.t()
  def render({:node, _tag, _index, _number, _kids} = code), do: render_node(code)

  defp render_node({:node, tag, index, number, kids}) do
    "(" <> atom(tag) <> atom(index) <> atom(number) <> Enum.map_join(kids, &render_node/1) <> ")"
  end

  # A unary natural terminated by ';'.
  defp atom(k) when is_integer(k) and k >= 0, do: String.duplicate("1", k) <> ";"

  defp node(tag, name, number, kids), do: {:node, tag, name, number, kids}

  defp named(tag, name, number, kids, term) do
    if valid_name?(name),
      do: {:ok, node(tag, name_of(name), number, kids)},
      else: {:error, {:malformed_term, term}}
  end

  defp valid_name?(name) when is_atom(name), do: true
  defp valid_name?(name) when is_binary(name), do: String.valid?(name)
  defp valid_name?(_name), do: false
  defp valid_table?([]), do: true
  defp valid_table?([name | rest]), do: valid_name?(name) and valid_table?(rest)
  defp valid_table?(_table), do: false

  # An atom and its string form are the same wire identity, matching the
  # formal side's first-match string keys.
  defp same_name?(left, right), do: name_of(left) == name_of(right)

  defp name_of(name) when is_atom(name), do: Atom.to_string(name)
  defp name_of(name) when is_binary(name), do: name

  defp grade_number(grade) do
    cond do
      grade == Grade.zero() -> {:ok, 0}
      grade == Grade.one() -> {:ok, 1}
      grade == Grade.affine() -> {:ok, 2}
      grade == Grade.unrestricted() -> {:ok, 3}
      true -> :error
    end
  end
end

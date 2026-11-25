defmodule Cure.Core.Serialize do
  @moduledoc """
  Serialize `Cure.Core` terms to a stable, host-independent S-expression form and
  back (design spec §9, commitment C2).

  The point of C2 is *independent re-validation*: a kernel written in another
  language can parse this format, rebuild the Core term, and re-run
  `check`/`infer` on it. The grammar is therefore deliberately small and explicit
  — every term is `(tag …)`, de Bruijn indices are integers,
  names are symbols, hole labels are quoted strings, and `case` branches are
  `(branch <ctor> <arity> <body>)`.

      encode({:app, {:app, {:global, :int_add}, {:int_lit, 3}}, {:int_lit, 5}})
      #=> "(cure-core 2 (app (app (global int_add) (int 3)) (int 5)))"
  """

  alias Cure.Core.{Term, UniverseCodec}

  @version UniverseCodec.version()
  @max_bytes UniverseCodec.max_bytes()
  @max_nodes UniverseCodec.max_nodes()
  @max_depth UniverseCodec.max_depth()
  @max_digits UniverseCodec.max_digits()

  @doc """
  Encode current syntax in a versioned whole-term frame.

  This representation is not typing evidence. Independent contextual kernel
  admission remains necessary before a decoded artifact is trusted.
  """
  @spec encode(Cure.Core.Term.t()) :: binary()
  def encode(term) do
    if Term.term?(term),
      do: IO.iodata_to_binary(["(cure-core ", Integer.to_string(@version), " ", enc(term), ")"]),
      else: raise(ArgumentError, "ill-formed Core term")
  end

  @doc false
  def encode_node(term), do: term |> enc() |> IO.iodata_to_binary()

  defp enc({:level_type}), do: "(level-type)"
  defp enc({:level_value, level}), do: ["(level-value ", enc_level(level), ")"]
  defp enc({:type, sort}), do: ["(type ", enc_sort(sort), ")"]
  defp enc({:var, k}), do: ["(var ", Integer.to_string(k), ")"]
  defp enc({:global, name}), do: ["(global ", sym(name), ")"]
  # Binders carry a QTT grade, encoded as a leading symbol — the same convention
  # `:ctor`/`:global` use for their names. `Grade` owns the carrier; nothing here
  # pattern-matches a grade.
  defp enc({:pi, g, d, c}), do: ["(pi ", sym(g), " ", enc(d), " ", enc(c), ")"]
  defp enc({:lam, g, d, b}), do: ["(lam ", sym(g), " ", enc(d), " ", enc(b), ")"]

  defp enc({:let, g, t, v, b}),
    do: ["(let ", sym(g), " ", enc(t), " ", enc(v), " ", enc(b), ")"]

  defp enc({:app, f, a}), do: node("app", [f, a])
  defp enc({:hole, name}), do: ["(hole ", str(name), ")"]
  defp enc({:absurd}), do: "(absurd)"
  # NOTE(int-facade): `enc`/`build_node("int-type", ...)` below stay so
  # (de)serialization round-trips a pre-flip saved `{:int_type}` term, even
  # though fresh elaboration never produces one anymore (spec 2026-07-18 §3a).
  defp enc({:int_type}), do: "(int-type)"
  defp enc({:float_type}), do: "(float-type)"
  defp enc({:binary_type}), do: "(binary-type)"
  defp enc({:atom_type}), do: "(atom-type)"
  defp enc({:atom_lit, a}), do: ["(atom ", sym(a), ")"]
  # Inert effect nodes: preserve shape; children encode recursively. `k` is an
  # ordinary term (a `{:lam, …}`), so no special binder handling.
  defp enc({:effect_type, t}), do: node("effect-type", [t])
  defp enc({:effect_pure, a}), do: node("effect-pure", [a])
  defp enc({:effect_bind, e, k}), do: node("effect-bind", [e, k])
  defp enc({:int_lit, n}), do: ["(int ", Integer.to_string(n), ")"]
  defp enc({:nat_lit, n}), do: ["(nat ", Integer.to_string(n), ")"]
  defp enc({:bounded_lit, n}), do: ["(bounded ", Integer.to_string(n), ")"]
  defp enc({:float_lit, f}), do: ["(float ", Float.to_string(f), ")"]
  defp enc({:ctor, name, args}), do: ["(ctor ", sym(name), args_iodata(args), ")"]

  defp enc({:data, name, params, indices}),
    do: ["(data ", sym(name), " ", seq(params), " ", seq(indices), ")"]

  defp enc({:case, scrut, motive, branches}) do
    ["(case ", enc(scrut), " ", enc(motive), branches_iodata(branches), ")"]
  end

  defp enc_sort({:finite, level}), do: ["(finite ", enc_level(level), ")"]
  defp enc_sort({:omega, n}), do: ["(omega ", Integer.to_string(n), ")"]

  defp enc_level(level) do
    {:level_nf, constant, atoms} = UniverseCodec.public_nf(level)

    [
      "(level-nf ",
      Integer.to_string(constant),
      Enum.map(atoms, fn {atom, offset} ->
        [" (atom ", enc(atom), " ", Integer.to_string(offset), ")"]
      end),
      ")"
    ]
  end

  defp node(tag, children),
    do: ["(", tag, Enum.map(children, fn c -> [" ", enc(c)] end), ")"]

  defp args_iodata(args), do: Enum.map(args, fn a -> [" ", enc(a)] end)
  defp seq(terms), do: ["(", Enum.map_intersperse(terms, " ", &enc/1), ")"]

  defp branches_iodata(branches) do
    Enum.map(branches, fn {ctor, arity, body} ->
      [" (branch ", sym(ctor), " ", Integer.to_string(arity), " ", enc(body), ")"]
    end)
  end

  # An Elixir atom is an arbitrary byte sequence, not an identifier: `:"has space"` is a
  # perfectly ordinary global name. Emitting one as a bareword produces something the
  # tokenizer splits into several tokens, so `decode(encode(t))` would not return `t`. A name
  # the tokenizer cannot read back as a single symbol is quoted instead, and the symbol
  # positions of `decode/1` accept a quoted string wherever they accept a bareword.
  defp sym(atom) do
    s = Atom.to_string(atom)
    if bareword?(s), do: s, else: str(s)
  end

  defp bareword?(""), do: false

  defp bareword?(s) do
    not String.contains?(s, [" ", "\t", "\n", "\r", "(", ")", "\"", "\\"]) and
      not number_like?(s)
  end

  # `classify/1` turns "5" or "1.0" into an `{:int, _}`/`{:float, _}` token, never a symbol.
  defp number_like?(s),
    do: match?({_, ""}, Integer.parse(s)) or match?({_, ""}, Float.parse(s))

  # Backslash first, or escaping the quote would re-escape its own escape character.
  defp str(s) do
    escaped = s |> String.replace("\\", "\\\\") |> String.replace("\"", "\\\"")
    [?", escaped, ?"]
  end

  # -- decoding ---------------------------------------------------------------

  @doc "Decode a canonical S-expression string back into a Core term."
  @spec decode(binary()) :: {:ok, Cure.Core.Term.t()} | {:error, term()}
  # The bytes are untrusted: this is the entry point an independent checker feeds an on-disk
  # artifact into. Rebuilding a *tuple* is not enough — every shape invariant `Term.term?/1`
  # states must hold, or the kernel is handed a term its own grammar rejects. `{:type, -1}`
  # would type-check as `Type(-1) : Type(0)`; `{:var, -1}` would resolve, via `Enum.at/2`'s
  # count-from-the-end semantics, to a binding it does not name; a negative `nat`/`bounded`
  # literal or a negative branch arity would crash `infer/2` with `FunctionClauseError`
  # against clauses guarded `n >= 0` with no fallback. Checking the finished term against
  # `Term.term?/1` — one linear pass — closes all of those at once and cannot drift from the
  # grammar it is validating against.
  def decode(string), do: decode_input(string, :current)

  @doc """
  Import an unframed historical fixed-ceiling S-expression explicitly.

  Only historical levels 0..2 are translated. The result is current syntax,
  not a revived certificate; contextual checking and fresh certification are
  required. Current decoding never falls back to this function.
  """
  def decode_legacy(string), do: decode_input(string, :legacy)

  defp decode_input(string, mode) when is_binary(string) and byte_size(string) <= @max_bytes do
    with :ok <- input_budget(string),
         {:ok, tokens} <- tokenize(string, []),
         {:ok, sexp, []} <- parse(tokens),
         {:ok, sexp} <- unframe(sexp, mode),
         {:ok, sexp} <- import_legacy(sexp, mode),
         {:ok, term} <- build(sexp),
         :ok <- well_formed(term) do
      {:ok, term}
    else
      {:ok, _sexp, _rest} -> {:error, :trailing_tokens}
      {:error, _} = err -> err
    end
  rescue
    ArgumentError -> {:error, :malformed}
  end

  defp decode_input(_, _), do: {:error, :core_input_budget_exceeded}

  defp unframe({:sexp, [{:atom, "cure-core"}, {:int, @version}, term]}, :current), do: {:ok, term}
  defp unframe(_sexp, :current), do: {:error, :incompatible_core_format}
  defp unframe(sexp, :legacy), do: {:ok, sexp}

  defp import_legacy(sexp, :current), do: {:ok, sexp}

  defp import_legacy({:sexp, [{:atom, "type"}, {:int, n}]}, :legacy) when n in 0..2 do
    {:ok, {:sexp, [{:atom, "type"}, {:sexp, [{:atom, "finite"}, {:sexp, [{:atom, "level-nf"}, {:int, n}]}]}]}}
  end

  defp import_legacy({:sexp, [{:atom, tag} | _]}, :legacy)
       when tag in [
              "type",
              "level-type",
              "level-value",
              "finite",
              "omega",
              "level-nf",
              "cure-core"
            ],
       do: {:error, :invalid_legacy_universe_encoding}

  defp import_legacy({:sexp, entries}, :legacy) do
    Enum.reduce_while(entries, {:ok, []}, fn entry, {:ok, acc} ->
      case import_legacy(entry, :legacy) do
        {:ok, imported} -> {:cont, {:ok, [imported | acc]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, reversed} -> {:ok, {:sexp, Enum.reverse(reversed)}}
      error -> error
    end
  end

  defp import_legacy(token, :legacy), do: {:ok, token}

  # A byte-size cap alone does not bound recursive parser stack depth.
  # Count syntax before allocating the token/AST lists; quoted data is inert.
  defp input_budget(string), do: scan_budget(string, 0, 0, false, false, 0)

  defp scan_budget(_rest, depth, nodes, _quoted, _escaped, digits)
       when depth > @max_depth or nodes > @max_nodes or digits > @max_digits,
       do: {:error, :core_input_budget_exceeded}

  defp scan_budget(<<>>, _depth, _nodes, _quoted, _escaped, _digits), do: :ok

  defp scan_budget(<<_byte, rest::binary>>, depth, nodes, true, true, _digits),
    do: scan_budget(rest, depth, nodes, true, false, 0)

  defp scan_budget(<<?\\, rest::binary>>, depth, nodes, true, false, _digits),
    do: scan_budget(rest, depth, nodes, true, true, 0)

  defp scan_budget(<<?", rest::binary>>, depth, nodes, quoted, false, _digits),
    do: scan_budget(rest, depth, nodes + 1, not quoted, false, 0)

  defp scan_budget(<<_byte, rest::binary>>, depth, nodes, true, false, _digits),
    do: scan_budget(rest, depth, nodes, true, false, 0)

  defp scan_budget(<<?(, rest::binary>>, depth, nodes, false, false, _digits),
    do: scan_budget(rest, depth + 1, nodes + 1, false, false, 0)

  defp scan_budget(<<?), rest::binary>>, depth, nodes, false, false, _digits),
    do: scan_budget(rest, depth - 1, nodes + 1, false, false, 0)

  defp scan_budget(<<byte, rest::binary>>, depth, nodes, false, false, digits)
       when byte in ?0..?9,
       do: scan_budget(rest, depth, nodes + 1, false, false, digits + 1)

  defp scan_budget(<<_byte, rest::binary>>, depth, nodes, false, false, _digits),
    do: scan_budget(rest, depth, nodes + 1, false, false, 0)

  defp well_formed(term) do
    if Cure.Core.Term.term?(term), do: :ok, else: {:error, {:ill_formed_term, term}}
  end

  # tokenizer → [:lparen | :rparen | {:atom, s} | {:int, n} | {:float, f} | {:str, s}]
  defp tokenize(<<>>, acc), do: {:ok, Enum.reverse(acc)}
  defp tokenize(<<c, rest::binary>>, acc) when c in [?\s, ?\t, ?\n, ?\r], do: tokenize(rest, acc)
  defp tokenize(<<?(, rest::binary>>, acc), do: tokenize(rest, [:lparen | acc])
  defp tokenize(<<?), rest::binary>>, acc), do: tokenize(rest, [:rparen | acc])

  defp tokenize(<<?", rest::binary>>, acc) do
    case take_string(rest, []) do
      {:ok, s, rest2} -> tokenize(rest2, [{:str, s} | acc])
      :error -> {:error, :unterminated_string}
    end
  end

  defp tokenize(bin, acc) do
    {word, rest} = take_atom(bin, [])
    tokenize(rest, [classify(word) | acc])
  end

  defp take_string(<<?\\, ?\\, rest::binary>>, acc), do: take_string(rest, [?\\ | acc])
  defp take_string(<<?\\, ?", rest::binary>>, acc), do: take_string(rest, [?" | acc])
  defp take_string(<<?", rest::binary>>, acc), do: {:ok, finish(acc), rest}
  defp take_string(<<>>, _acc), do: :error
  defp take_string(<<c, rest::binary>>, acc), do: take_string(rest, [c | acc])

  defp take_atom(<<c, _::binary>> = bin, acc) when c in [?\s, ?\t, ?\n, ?\r, ?(, ?)],
    do: {finish(acc), bin}

  defp take_atom(<<>>, acc), do: {finish(acc), <<>>}
  defp take_atom(<<c, rest::binary>>, acc), do: take_atom(rest, [c | acc])

  # `acc` accumulates raw BYTES, so it must be reassembled as bytes. `to_string/1` on a list of
  # integers reads them as codepoints and would re-encode each byte of a multi-byte character
  # separately, mangling any non-ASCII name on the way back in.
  defp finish(acc), do: acc |> Enum.reverse() |> :erlang.list_to_binary()

  defp classify(word) do
    case Integer.parse(word) do
      {n, ""} ->
        {:int, n}

      _ ->
        case Float.parse(word) do
          {f, ""} -> {:float, f}
          _ -> {:atom, word}
        end
    end
  end

  # parser: token list → nested s-expr ({:sexp, [..]} | {:atom,_} | {:int,_} | ...)
  defp parse([:lparen | rest]), do: parse_list(rest, [])
  defp parse([{_, _} = leaf | rest]), do: {:ok, leaf, rest}
  defp parse([]), do: {:error, :unexpected_eof}
  defp parse([:rparen | _]), do: {:error, :unexpected_rparen}

  defp parse_list([:rparen | rest], acc), do: {:ok, {:sexp, Enum.reverse(acc)}, rest}
  defp parse_list([], _acc), do: {:error, :unterminated_list}

  defp parse_list(tokens, acc) do
    with {:ok, item, rest} <- parse(tokens), do: parse_list(rest, [item | acc])
  end

  # build: s-expr → Core term.
  #
  # Every Core term is `(tag …)`. A bare token — `5`, `foo` — is never one, and `enc/1` never
  # emits one in a child position: literals are always wrapped, as `(int 5)`. `build_node`'s
  # own clauses match the raw tokens they need directly, so nothing here needs a leaf
  # pass-through; having one only let a raw Elixir scalar sit where a subterm belongs.
  defp build({:sexp, [{:atom, head} | args]}), do: build_node(head, args)
  defp build(_), do: {:error, :malformed}

  defp build_node("level-type", []), do: {:ok, {:level_type}}

  defp build_node("level-value", [wire]) do
    with {:ok, level} <- build_level(wire), do: {:ok, {:level_value, level}}
  end

  defp build_node("type", [wire]) do
    with {:ok, sort} <- build_sort(wire), do: {:ok, {:type, sort}}
  end

  defp build_node("var", [{:int, k}]), do: {:ok, {:var, k}}

  defp build_node("global", [n]) do
    with {:ok, a} <- sym_atom(n), do: {:ok, {:global, a}}
  end

  defp build_node("int-type", []), do: {:ok, {:int_type}}
  defp build_node("float-type", []), do: {:ok, {:float_type}}
  defp build_node("binary-type", []), do: {:ok, {:binary_type}}
  defp build_node("atom-type", []), do: {:ok, {:atom_type}}

  defp build_node("atom", [n]) do
    with {:ok, at} <- sym_atom(n), do: {:ok, {:atom_lit, at}}
  end

  defp build_node("int", [{:int, n}]), do: {:ok, {:int_lit, n}}
  defp build_node("nat", [{:int, n}]), do: {:ok, {:nat_lit, n}}
  defp build_node("bounded", [{:int, n}]), do: {:ok, {:bounded_lit, n}}
  defp build_node("float", [{:float, f}]), do: {:ok, {:float_lit, f}}
  defp build_node("hole", [{:str, s}]), do: {:ok, {:hole, s}}
  defp build_node("absurd", []), do: {:ok, {:absurd}}

  defp build_node("pi", [g, d, c]), do: graded2(:pi, g, d, c)
  defp build_node("lam", [g, d, b]), do: graded2(:lam, g, d, b)
  defp build_node("let", [g, t, v, b]), do: graded3(:let, g, t, v, b)
  defp build_node("app", [f, a]), do: binary(:app, f, a)

  defp build_node("ctor", [name | args]) do
    with {:ok, a} <- sym_atom(name), {:ok, cargs} <- build_all(args), do: {:ok, {:ctor, a, cargs}}
  end

  defp build_node("data", [name, {:sexp, ps}, {:sexp, is}]) do
    with {:ok, a} <- sym_atom(name),
         {:ok, cps} <- build_all(ps),
         {:ok, cis} <- build_all(is),
         do: {:ok, {:data, a, cps, cis}}
  end

  defp build_node("case", [scrut, motive | branches]) do
    with {:ok, cs} <- build(scrut),
         {:ok, cm} <- build(motive),
         {:ok, cbs} <- build_branches(branches) do
      {:ok, {:case, cs, cm, cbs}}
    end
  end

  defp build_node("effect-type", [t]),
    do: with({:ok, ct} <- build(t), do: {:ok, {:effect_type, ct}})

  defp build_node("effect-pure", [a]),
    do: with({:ok, ca} <- build(a), do: {:ok, {:effect_pure, ca}})

  defp build_node("effect-bind", [e, k]), do: binary(:effect_bind, e, k)

  defp build_node(_tag, _args), do: {:error, :unknown_node}

  defp build_sort({:sexp, [{:atom, "finite"}, wire]}) do
    with {:ok, level} <- build_level(wire), do: {:ok, {:finite, level}}
  end

  defp build_sort({:sexp, [{:atom, "omega"}, {:int, index}]}) do
    with :ok <- UniverseCodec.natural(index), do: {:ok, {:omega, index}}
  end

  defp build_sort(_), do: {:error, {:noncanonical_level_encoding, :invalid_sort}}

  defp build_level({:sexp, [{:atom, "level-nf"}, {:int, constant} | entries]}) do
    with :ok <- UniverseCodec.natural(constant),
         :ok <- UniverseCodec.bounded(entries, UniverseCodec.max_atoms()),
         {:ok, atoms} <- build_atoms(entries, []),
         {:ok, level} <- UniverseCodec.internal_nf({:level_nf, constant, atoms}) do
      {:ok, level}
    end
  end

  defp build_level(_), do: {:error, {:noncanonical_level_encoding, :invalid_level_nf}}
  defp build_atoms([], acc), do: {:ok, Enum.reverse(acc)}

  defp build_atoms([{:sexp, [{:atom, "atom"}, wire, {:int, offset}]} | rest], acc) do
    with :ok <- UniverseCodec.natural(offset),
         {:ok, term} <- build(wire),
         do: build_atoms(rest, [{term, offset} | acc])
  end

  defp build_atoms(_, _), do: {:error, {:noncanonical_level_encoding, :invalid_atom_entry}}

  # Decode a grade symbol through the same bounded-interning path names use, then
  # verify it against the carrier. An unknown symbol fails the decode cleanly.
  defp decode_grade(tok) do
    with {:ok, g} <- sym_atom(tok) do
      if Cure.Core.Grade.grade?(g), do: {:ok, g}, else: {:error, {:bad_grade, g}}
    end
  end

  defp graded2(tag, g, a, b) do
    with {:ok, gg} <- decode_grade(g),
         {:ok, ta} <- build(a),
         {:ok, tb} <- build(b),
         do: {:ok, {tag, gg, ta, tb}}
  end

  defp graded3(tag, g, a, b, c) do
    with {:ok, gg} <- decode_grade(g),
         {:ok, ta} <- build(a),
         {:ok, tb} <- build(b),
         {:ok, tc} <- build(c),
         do: {:ok, {tag, gg, ta, tb, tc}}
  end

  defp binary(tag, a, b) do
    with {:ok, ta} <- build(a), {:ok, tb} <- build(b), do: {:ok, {tag, ta, tb}}
  end

  defp build_all(items) do
    Enum.reduce_while(items, {:ok, []}, fn item, {:ok, acc} ->
      case build(item) do
        {:ok, t} -> {:cont, {:ok, [t | acc]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> reverse_result()
  end

  defp build_branches(branches) do
    Enum.reduce_while(branches, {:ok, []}, fn
      {:sexp, [{:atom, "branch"}, ctor, {:int, arity}, body]}, {:ok, acc} ->
        with {:ok, a} <- sym_atom(ctor), {:ok, b} <- build(body) do
          {:cont, {:ok, [{a, arity, b} | acc]}}
        else
          {:error, _} = err -> {:halt, err}
        end

      _other, _acc ->
        {:halt, {:error, :malformed_branch}}
    end)
    |> reverse_result()
  end

  defp reverse_result({:ok, reversed}), do: {:ok, Enum.reverse(reversed)}
  defp reverse_result(error), do: error

  # A symbol reads as a bareword, or as a quoted string when its name is not one (see `sym/1`).
  defp sym_atom({:atom, s}), do: intern(s)
  defp sym_atom({:str, s}), do: intern(s)
  defp sym_atom(_other), do: {:error, :malformed_symbol}

  # Bounded symbol interning (K12 / spec §D): decode names into EXISTING atoms
  # only. Untrusted C2 input cannot then exhaust the atom table — an unknown
  # symbol fails the decode cleanly (`:unknown_symbol`) instead of minting a new
  # permanent atom. Every symbol in a real program is already interned by the
  # compiler, so valid terms still round-trip.
  defp intern(s) do
    {:ok, String.to_existing_atom(s)}
  rescue
    ArgumentError -> {:error, {:unknown_symbol, s}}
  end
end

defmodule Cure.Core.Term do
  @moduledoc """
  Explicit, fully-annotated Core terms for the trusted dependent-type kernel.

  Terms are plain tagged tuples using de Bruijn indices for bound variables.
  This is the soundness-critical representation described in the design spec
  §4.1; it deliberately carries no implicits, holes, or erasure annotations
  (those live only in the surface/elaborator) — a checked Core term is fully
  explicit and fully relevant.

  Node taxonomy (de Bruijn):

    * `{:type, sort}`                       universe, `sort` a `Cure.Core.Sort.t()`
    * `{:level_type}`                        the primitive `UniverseLevel` type
    * `{:level_value, level}`                a canonical level value
    * `{:var, k}`                            bound variable, de Bruijn index `k >= 0`
    * `{:pi, g, dom, cod}`                   dependent function type (binds in `cod`)
    * `{:lam, g, dom, body}`                 lambda (binds in `body`)
    * `{:let, g, ty, val, body}`             let-binding (binds in `body`);
                                             ζ-transparent: the variable is
                                             definitionally `val`. Idris
                                             `Binder.Let`, Lean `Expr.letE`.
    * `{:app, f, a}`                         application
    * `{:data, name, params, indices}`       family applied to params + indices
    * `{:ctor, name, args}`                  data constructor application
    * `{:case, scrut, motive, branches}`     dependent eliminator;
                                             `branches :: [{ctor_name, arity, body}]`
    * `{:global, name}`                      reference to a global def
    * `{:int_type}` / `{:int_lit, n}`        integer type / literal
    * `{:float_type}` / `{:float_lit, f}`    float type / literal
    * `{:binary_type}`                       BEAM binary base type (Int-tier)
    * `{:atom_type}` / `{:atom_lit, a}`      BEAM atom base type / literal (`a`
                                             an atom); the atom is its own
                                             canonical value (Int-tier prim)
    * `{:nat_lit, n}`                        compact Nat literal (`n >= 0`),
                                             definitionally equal to the n-fold
                                             `S`-tower over `Z` (Lean kernel Nat /
                                             Agda BUILTIN NATURAL — a compact
                                             literal form for `Nat` values, not a
                                             separate primitive type)
    * `{:effect_type, t}`                    `Effect(T)` — the inert effect type
                                             former (Lean `IO`, Idris `PrimIO`)
    * `{:effect_pure, a}`                    `pure(a)` — trivial computation
    * `{:effect_bind, e, k}`                 `bind(e, k)` — sequencing; `k` is an
                                             ordinary function term, so the node
                                             itself binds NOTHING. All three are
                                             uninterpreted: zero reduction rules,
                                             not even the monad laws (design
                                             `2026-07-09-effect-type-former-design.md`
                                             §3.2).
    (Bool and Nat are real inductive families, not primitive term forms.)
  """

  # Single source of truth for the universe representation is `Cure.Core.Sort`;
  # this module only validates against it.
  alias Cure.Core.{Grade, Sort, UniverseLevel}

  @typedoc "A `:case` branch: constructor name, its arity, and the branch body."
  @type branch :: {atom(), non_neg_integer(), t()}

  @typedoc """
  A Core term — the node taxonomy above, as a closed union.

  This is deliberately NOT `tuple()`. Written loosely, Dialyzer and Elixir's
  set-theoretic checker are blind to binder shape: a wrong-arity `{:pi, dom}`
  or a pattern that can never match sails straight through. Written precisely,
  both catch it statically, which is the only cheap net over a taxonomy that is
  reshaped from time to time (the QTT grade reshape being the current one).
  """
  @type t ::
          {:type, Sort.t()}
          | {:level_type}
          | {:level_value, UniverseLevel.t()}
          | {:var, non_neg_integer()}
          | {:pi, Grade.t(), t(), t()}
          | {:lam, Grade.t(), t(), t()}
          | {:let, Grade.t(), t(), t(), t()}
          | {:app, t(), t()}
          | {:data, atom(), [t()], [t()]}
          | {:ctor, atom(), [t()]}
          | {:case, t(), t(), [branch()]}
          | {:global, atom()}
          | {:int_type}
          | {:int_lit, integer()}
          | {:nat_lit, non_neg_integer()}
          | {:bounded_lit, non_neg_integer()}
          | {:float_type}
          | {:float_lit, float()}
          | {:binary_type}
          | {:atom_type}
          | {:atom_lit, atom()}
          | {:effect_type, t()}
          | {:effect_pure, t()}
          | {:effect_bind, t(), t()}
          | {:hole, atom() | String.t()}
          | {:absurd}

  @doc """
  True when `term` is a structurally well-formed Core term.

  This is a shape check only — it validates node arities, the sort index, and
  non-negative de Bruijn indices, recursively. It does not type-check; that is
  the kernel's job.

  A **legacy integer level** (`{:type, 0}`) is NOT a term: the migration to
  `Cure.Core.Sort` is complete at this boundary, and §17.3 requires the final
  validator to refuse integer-level Core so stale walkers or generators cannot
  silently survive. Old artifacts are converted by the compatibility decoder in
  `Cure.Core.Serialize`, never admitted here.
  """
  @spec term?(term()) :: boolean()
  def term?({:type, sort}), do: Sort.validate(sort, nil) == :ok

  # The primitive `UniverseLevel` type and its canonical values. A level value
  # is a LEAF here for shape purposes, but every traversal below descends into
  # its atoms (§7.2) — reading it as inert would permit scope escape.
  def term?({:level_type}), do: true
  def term?({:level_value, level}), do: UniverseLevel.validate(level, nil) == :ok
  def term?({:var, k}), do: is_integer(k) and k >= 0
  # Binders carry a QTT grade in their FIRST field (Idris `Core/TT/Binder.idr`).
  # A stale 3-tuple binder is NOT a term — Elixir would otherwise let it fall
  # through a catch-all and behave silently wrong, so this is the net.
  def term?({:pi, g, dom, cod}), do: Grade.grade?(g) and term?(dom) and term?(cod)
  def term?({:lam, g, dom, body}), do: Grade.grade?(g) and term?(dom) and term?(body)

  def term?({:let, g, ty, val, body}),
    do: Grade.grade?(g) and term?(ty) and term?(val) and term?(body)

  def term?({:app, f, a}), do: term?(f) and term?(a)

  def term?({:data, name, params, indices}),
    do: is_atom(name) and terms?(params) and terms?(indices)

  def term?({:ctor, name, args}), do: is_atom(name) and terms?(args)

  def term?({:case, scrut, motive, branches}),
    do: term?(scrut) and term?(motive) and branches?(branches)

  def term?({:global, name}), do: is_atom(name)

  # NOTE(int-facade): the primitive `{:int_type}` node is retired from the surface
  # (spec 2026-07-18 §3a(i) — `Int` is the inductive `FromNat`/`NegativeSuccessor`
  # family) but this and the `shift`/`subst`/`to_external`/`from_external` clauses
  # below are kept as an internal facade: `from_external` must still deserialize
  # pre-flip saved terms (certificates, quasiquote captures) that spell the old
  # node. No surface elaboration path can produce a fresh `{:int_type}` anymore.
  def term?({:int_type}), do: true
  def term?({:int_lit, n}), do: is_integer(n)
  def term?({:nat_lit, n}), do: is_integer(n) and n >= 0
  def term?({:bounded_lit, n}), do: is_integer(n) and n >= 0
  def term?({:float_type}), do: true
  def term?({:float_lit, f}), do: is_float(f)
  def term?({:binary_type}), do: true
  def term?({:atom_type}), do: true
  def term?({:atom_lit, a}), do: is_atom(a)

  # Inert effect nodes. None binds a variable, so `term?` is a plain arity +
  # recursive shape check; a stale 2-tuple `bind`/1-tuple `type` falls through
  # to the catch-all and is (correctly) not a term.
  def term?({:effect_type, t}), do: term?(t)
  def term?({:effect_pure, a}), do: term?(a)
  def term?({:effect_bind, e, k}), do: term?(e) and term?(k)

  # A hole is a live Core node — `Kernel.check/3` accepts one at any type, and a definition
  # mid-development legitimately contains them (only the release/emit boundary rejects
  # them). It carries no de Bruijn variables, so it is an inert leaf everywhere below.
  def term?({:hole, name}), do: is_binary(name)

  # Likewise `{:absurd}`: `Kernel.check/3` admits it against any type once the context is
  # inconsistent, `Serialize` encodes and decodes it, and `Validator` has a clause for it.
  def term?({:absurd}), do: true

  def term?(_), do: false

  @doc """
  Atom terms in a recognized universe wrapper, with no additional binder.

  This is also usable by conservative audits of malformed wrappers: known
  level payloads expose their term entries even when their offsets or
  canonicality are invalid. It is not a validator or a generic AST walker.
  """
  @spec level_atoms(term()) :: [term()]
  def level_atoms({:type, {:finite, level}}), do: level_payload_atoms(level)
  def level_atoms({:level_value, level}), do: level_payload_atoms(level)
  def level_atoms({:type, _}), do: []
  def level_atoms({:level_type}), do: []

  @doc false
  def level_payload_atoms(%UniverseLevel{atoms: atoms}), do: raw_atom_terms(atoms)
  def level_payload_atoms({:level_nf, _constant, atoms}), do: raw_atom_terms(atoms)
  def level_payload_atoms(_), do: []

  defp raw_atom_terms(atoms) when is_list(atoms) do
    Enum.flat_map(atoms, fn
      {term, _offset} -> [term]
      _malformed_entry -> []
    end)
  end

  defp raw_atom_terms(_), do: []

  # -- de Bruijn shift / substitution -----------------------------------------
  #
  # Binder convention: `:pi`/`:lam` introduce exactly one binder in
  # their codomain/body. A `:case` branch `{ctor, arity, body}` binds `arity`
  # variables in `body`. Motives (`:case`/`:rewrite`) are represented as
  # lambda-chains, so their binders are the ordinary `:lam` nodes inside them
  # and need no special counting here (confirmed by the M4 case-eliminator).

  @doc "Lift every free de Bruijn variable (index ≥ `cutoff`) by `amount`."
  @spec shift(t(), integer(), non_neg_integer()) :: t()
  def shift(term, amount, cutoff \\ 0)

  def shift({:var, k}, amount, cutoff) when k >= cutoff, do: {:var, k + amount}
  def shift({:var, _} = v, _amount, _cutoff), do: v
  # A sort index is NOT an inert leaf: a finite sort's level atoms may contain
  # de Bruijn variables, and §7.2 names shift as a traversal that must descend
  # into them (treating a level as a leaf would permit scope escape).
  def shift({:type, sort}, amount, cutoff), do: {:type, Sort.shift(sort, amount, cutoff)}
  def shift({:level_type} = t, _amount, _cutoff), do: t

  def shift({:level_value, level}, amount, cutoff),
    do: {:level_value, UniverseLevel.shift(level, amount, cutoff)}

  def shift({:global, _} = t, _amount, _cutoff), do: t

  # Literals / type constants bind nothing and contain no variables: identity.
  def shift({:int_type} = t, _amount, _cutoff), do: t
  def shift({:int_lit, _} = t, _amount, _cutoff), do: t
  def shift({:nat_lit, _} = t, _amount, _cutoff), do: t
  def shift({:bounded_lit, _} = t, _amount, _cutoff), do: t
  def shift({:float_type} = t, _amount, _cutoff), do: t
  def shift({:float_lit, _} = t, _amount, _cutoff), do: t
  def shift({:binary_type} = t, _amount, _cutoff), do: t
  def shift({:atom_type} = t, _amount, _cutoff), do: t
  def shift({:atom_lit, _} = t, _amount, _cutoff), do: t
  def shift({:hole, _} = t, _amount, _cutoff), do: t
  def shift({:absurd} = t, _amount, _cutoff), do: t
  def shift({:pi, g, dom, cod}, a, c), do: {:pi, g, shift(dom, a, c), shift(cod, a, c + 1)}
  def shift({:lam, g, dom, body}, a, c), do: {:lam, g, shift(dom, a, c), shift(body, a, c + 1)}
  # `ty` and `val` live OUTSIDE the binder; only `body` is one deeper.
  def shift({:let, g, ty, val, body}, a, c),
    do: {:let, g, shift(ty, a, c), shift(val, a, c), shift(body, a, c + 1)}

  def shift({:app, f, x}, a, c), do: {:app, shift(f, a, c), shift(x, a, c)}

  def shift({:data, n, ps, is}, a, c),
    do: {:data, n, Enum.map(ps, &shift(&1, a, c)), Enum.map(is, &shift(&1, a, c))}

  def shift({:ctor, n, args}, a, c), do: {:ctor, n, Enum.map(args, &shift(&1, a, c))}

  def shift({:case, s, m, brs}, a, c),
    do: {:case, shift(s, a, c), shift(m, a, c), Enum.map(brs, fn {cn, ar, b} -> {cn, ar, shift(b, a, c + ar)} end)}

  # Effect nodes bind nothing: recurse into every child at the SAME cutoff.
  def shift({:effect_type, t}, a, c), do: {:effect_type, shift(t, a, c)}
  def shift({:effect_pure, x}, a, c), do: {:effect_pure, shift(x, a, c)}
  def shift({:effect_bind, e, k}, a, c), do: {:effect_bind, shift(e, a, c), shift(k, a, c)}

  @doc """
  Is `term` closed (no free de Bruijn variables)?

  A closed term has no variable index that escapes its own binders. Only a
  genuine free `{:var, k}` counts as open — non-variable leaves (`{:hole, _}`,
  globals, types, literals) are closed. The binder structure mirrors `shift/3`
  exactly (the trusted source of truth): `:lam`/`:pi` bind one variable
  in their body/codomain, and each `:case` branch binds `arity`; every other form
  is traversed at the same depth. Kept in lockstep with `shift/3` — if a new
  binding form is added there, add it here.
  """
  @spec closed?(t()) :: boolean()
  def closed?(term), do: not has_free_var?(term, 0)

  defp has_free_var?({:var, k}, depth), do: k >= depth

  # A finite sort's level atoms may carry free variables, so closure must look
  # inside them (§7.2). The catch-all tuple walk below would NOT do this
  # correctly: a level normal form is a struct, and `Tuple.to_list/1` on a
  # struct yields its fields, not its atoms. Explicit clauses are the fix.
  defp has_free_var?({:type, sort}, depth),
    do: Enum.any?(Sort.free_vars(sort), &(&1 >= depth))

  defp has_free_var?({:level_type}, _depth), do: false

  defp has_free_var?({:level_value, level}, depth),
    do: Enum.any?(UniverseLevel.free_vars(level), &(&1 >= depth))

  defp has_free_var?({:lam, _g, d, b}, depth),
    do: has_free_var?(d, depth) or has_free_var?(b, depth + 1)

  defp has_free_var?({:let, _g, t, v, b}, depth),
    do: has_free_var?(t, depth) or has_free_var?(v, depth) or has_free_var?(b, depth + 1)

  defp has_free_var?({:pi, _g, d, c}, depth),
    do: has_free_var?(d, depth) or has_free_var?(c, depth + 1)

  defp has_free_var?({:case, s, m, brs}, depth) do
    has_free_var?(s, depth) or has_free_var?(m, depth) or
      Enum.any?(brs, fn {_c, ar, b} -> has_free_var?(b, depth + ar) end)
  end

  # Non-binding forms: recurse into every sub-term at the same depth. Covers
  # :app/:ctor/:data/:eq/:refl/:rewrite/:prim and anything else.
  defp has_free_var?(t, depth) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.any?(&has_free_var?(&1, depth))

  defp has_free_var?(l, depth) when is_list(l), do: Enum.any?(l, &has_free_var?(&1, depth))
  defp has_free_var?(_leaf, _depth), do: false

  @doc """
  Substitute the de Bruijn index `j` with `replacement` everywhere it occurs.

  Descends under binders, incrementing the target index and shifting the
  replacement so its free variables are not captured. This is a targeted
  substitution (it replaces index `j`; it does not renumber the others).
  """
  @spec subst(t(), non_neg_integer(), t()) :: t()
  def subst({:var, j}, j, replacement), do: replacement
  def subst({:var, _} = term, _j, _replacement), do: term

  # A sort index is not inert: substitute inside a finite sort's level atoms
  # (§7.2). The replacement is shifted under the sort's own binders by
  # `UniverseLevel.subst/3`.
  def subst({:type, sort}, j, r), do: {:type, Sort.subst(sort, j, r)}
  def subst({:level_type} = t, _j, _r), do: t
  def subst({:level_value, level}, j, r), do: {:level_value, UniverseLevel.subst(level, j, r)}
  def subst({:global, _} = t, _j, _r), do: t

  # Literals / type constants bind nothing and contain no variables: identity.
  def subst({:int_type} = t, _j, _r), do: t
  def subst({:int_lit, _} = t, _j, _r), do: t
  def subst({:nat_lit, _} = t, _j, _r), do: t
  def subst({:bounded_lit, _} = t, _j, _r), do: t
  def subst({:float_type} = t, _j, _r), do: t
  def subst({:float_lit, _} = t, _j, _r), do: t
  def subst({:binary_type} = t, _j, _r), do: t
  def subst({:atom_type} = t, _j, _r), do: t
  def subst({:atom_lit, _} = t, _j, _r), do: t
  def subst({:hole, _} = t, _j, _r), do: t
  def subst({:absurd} = t, _j, _r), do: t

  def subst({:pi, g, dom, cod}, j, r),
    do: {:pi, g, subst(dom, j, r), subst(cod, j + 1, shift(r, 1, 0))}

  def subst({:lam, g, dom, body}, j, r),
    do: {:lam, g, subst(dom, j, r), subst(body, j + 1, shift(r, 1, 0))}

  def subst({:let, g, ty, val, body}, j, r),
    do: {:let, g, subst(ty, j, r), subst(val, j, r), subst(body, j + 1, shift(r, 1, 0))}

  def subst({:app, f, x}, j, r), do: {:app, subst(f, j, r), subst(x, j, r)}

  def subst({:data, n, ps, is}, j, r),
    do: {:data, n, Enum.map(ps, &subst(&1, j, r)), Enum.map(is, &subst(&1, j, r))}

  def subst({:ctor, n, args}, j, r), do: {:ctor, n, Enum.map(args, &subst(&1, j, r))}

  def subst({:case, s, m, brs}, j, r),
    do:
      {:case, subst(s, j, r), subst(m, j, r),
       Enum.map(brs, fn {cn, ar, b} -> {cn, ar, subst(b, j + ar, shift(r, ar, 0))} end)}

  # Effect nodes bind nothing: substitute index `j` in every child, no shift.
  def subst({:effect_type, t}, j, r), do: {:effect_type, subst(t, j, r)}
  def subst({:effect_pure, x}, j, r), do: {:effect_pure, subst(x, j, r)}
  def subst({:effect_bind, e, k}, j, r), do: {:effect_bind, subst(e, j, r), subst(k, j, r)}

  # -- serialization (commitment C2) ------------------------------------------
  #
  # A language-agnostic, JSON-able encoding (maps / lists / strings / ints) so
  # an independent checker can re-validate the same Core terms. No PIDs, refs,
  # or closures appear in Core terms, so the encoding is total and reversible.

  # -- universe representation (§7.1, §15) ------------------------------------
  #
  # A sort index encodes as `{"tag" => "finite", "level" => <level>}` or
  # `{"tag" => "omega", "index" => n}`. A level normal form encodes as its
  # constant plus its atoms, each `{"term" => <core>, "offset" => k}`.
  #
  # The universe representation is versioned (§15): `sort` carries a sort index;
  # `level_type` / `level_value` are the primitive `UniverseLevel` forms.

  @doc "Encode structurally valid Core syntax in a current versioned external frame."
  @spec to_external(t()) :: map()
  def to_external(term) do
    if term?(term),
      do: Cure.Core.UniverseCodec.frame(to_external_node(term)),
      else: raise(ArgumentError, "ill-formed Core term")
  end

  @doc false
  @spec to_external_node(t()) :: map()
  def to_external_node({:type, sort}),
    do: %{"node" => "type", "sort" => Cure.Core.UniverseCodec.encode_sort(sort, &to_external_node/1)}

  def to_external_node({:level_type}), do: %{"node" => "level_type"}

  def to_external_node({:level_value, level}),
    do: %{"node" => "level_value", "level" => Cure.Core.UniverseCodec.encode_level(level, &to_external_node/1)}

  def to_external_node({:var, k}), do: %{"node" => "var", "index" => k}

  def to_external_node({:pi, g, d, c}),
    do: %{"node" => "pi", "grade" => grade_ext(g), "dom" => to_external_node(d), "cod" => to_external_node(c)}

  def to_external_node({:lam, g, d, b}),
    do: %{"node" => "lam", "grade" => grade_ext(g), "dom" => to_external_node(d), "body" => to_external_node(b)}

  def to_external_node({:let, g, t, v, b}),
    do: %{
      "node" => "let",
      "grade" => grade_ext(g),
      "type" => to_external_node(t),
      "value" => to_external_node(v),
      "body" => to_external_node(b)
    }

  def to_external_node({:app, f, a}),
    do: %{"node" => "app", "fun" => to_external_node(f), "arg" => to_external_node(a)}

  def to_external_node({:data, n, ps, is}),
    do: %{
      "node" => "data",
      "name" => Atom.to_string(n),
      "params" => Enum.map(ps, &to_external_node/1),
      "indices" => Enum.map(is, &to_external_node/1)
    }

  def to_external_node({:ctor, n, args}),
    do: %{"node" => "ctor", "name" => Atom.to_string(n), "args" => Enum.map(args, &to_external_node/1)}

  def to_external_node({:case, s, m, brs}),
    do: %{
      "node" => "case",
      "scrut" => to_external_node(s),
      "motive" => to_external_node(m),
      "branches" =>
        Enum.map(brs, fn {cn, ar, b} ->
          %{"ctor" => Atom.to_string(cn), "arity" => ar, "body" => to_external_node(b)}
        end)
    }

  def to_external_node({:global, n}), do: %{"node" => "global", "name" => Atom.to_string(n)}

  def to_external_node({:int_type}), do: %{"node" => "int_type"}
  def to_external_node({:int_lit, n}), do: %{"node" => "int_lit", "value" => n}
  def to_external_node({:nat_lit, n}), do: %{"node" => "nat_lit", "value" => n}
  def to_external_node({:bounded_lit, n}), do: %{"node" => "bounded_lit", "value" => n}
  def to_external_node({:float_type}), do: %{"node" => "float_type"}
  def to_external_node({:float_lit, f}), do: %{"node" => "float_lit", "value" => f}
  def to_external_node({:binary_type}), do: %{"node" => "binary_type"}
  def to_external_node({:atom_type}), do: %{"node" => "atom_type"}
  def to_external_node({:atom_lit, a}), do: %{"node" => "atom_lit", "value" => Atom.to_string(a)}

  def to_external_node({:effect_type, t}), do: %{"node" => "effect_type", "arg" => to_external_node(t)}
  def to_external_node({:effect_pure, a}), do: %{"node" => "effect_pure", "arg" => to_external_node(a)}

  def to_external_node({:effect_bind, e, k}),
    do: %{"node" => "effect_bind", "effect" => to_external_node(e), "cont" => to_external_node(k)}

  def to_external_node({:absurd}), do: %{"node" => "absurd"}

  def to_external_node({:hole, name}), do: %{"node" => "hole", "name" => name}

  @doc false
  def sort_external_decode(map),
    do: Cure.Core.UniverseCodec.decode_sort(map, &from_external_node/1)

  @doc false
  def level_external_decode(map),
    do: Cure.Core.UniverseCodec.decode_level(map, &from_external_node/1)

  @doc """
  Decode a JSON-able map produced by `to_external/1` back into a Core term.

  The map is an external trust boundary. The fully reconstructed value is
  checked against `term?/1`; malformed encodings raise instead of leaking a
  tuple that the Core grammar itself rejects.
  """
  @spec from_external(map()) :: t()
  def from_external(external) do
    case Cure.Core.UniverseCodec.unframe(external) do
      {:ok, node} -> from_external_node(node)
      {:error, _} -> raise ArgumentError, "incompatible external Core format"
    end
  end

  @doc false
  def from_external_node(external) do
    with :ok <- Cure.Core.UniverseCodec.budget(external),
         term <- decode_external(external),
         true <- term?(term) do
      term
    else
      _ -> raise ArgumentError, "ill-formed external Core term"
    end
  rescue
    FunctionClauseError -> raise ArgumentError, "ill-formed external Core node"
    Protocol.UndefinedError -> raise ArgumentError, "ill-formed external Core collection"
  end

  @doc "Import historical external syntax explicitly; no certification survives this translation."
  def from_legacy_external(external) do
    case Cure.Core.UniverseCodec.budget(external) do
      :ok -> external |> import_legacy_external() |> from_external_node()
      {:error, _} -> raise ArgumentError, "historical Core input budget exceeded"
    end
  end

  defp import_legacy_external(%{"node" => "type", "level" => n} = node)
       when map_size(node) == 2 and n in 0..2,
       do: to_external_node({:type, Sort.finite_closed(n)})

  defp import_legacy_external(%{"node" => tag})
       when tag in ["type", "sort", "level_type", "level_value"],
       do: raise(ArgumentError, "invalid historical universe encoding")

  defp import_legacy_external(map) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, import_legacy_external(value)} end)

  defp import_legacy_external(list) when is_list(list), do: Enum.map(list, &import_legacy_external/1)
  defp import_legacy_external(value), do: value

  @external_node_keys %{
    "type" => ~w(node sort),
    "level_type" => ~w(node),
    "level_value" => ~w(node level),
    "var" => ~w(node index),
    "pi" => ~w(node grade dom cod),
    "lam" => ~w(node grade dom body),
    "let" => ~w(node grade type value body),
    "app" => ~w(node fun arg),
    "data" => ~w(node name params indices),
    "ctor" => ~w(node name args),
    "case" => ~w(node scrut motive branches),
    "global" => ~w(node name),
    "int_type" => ~w(node),
    "int_lit" => ~w(node value),
    "nat_lit" => ~w(node value),
    "bounded_lit" => ~w(node value),
    "float_type" => ~w(node),
    "float_lit" => ~w(node value),
    "binary_type" => ~w(node),
    "atom_type" => ~w(node),
    "atom_lit" => ~w(node value),
    "effect_type" => ~w(node arg),
    "effect_pure" => ~w(node arg),
    "effect_bind" => ~w(node effect cont),
    "hole" => ~w(node name),
    "absurd" => ~w(node)
  }

  defp decode_external(%{"node" => tag} = external) do
    case Map.fetch(@external_node_keys, tag) do
      {:ok, keys} ->
        if Enum.sort(Map.keys(external)) == Enum.sort(keys),
          do: decode_external_node(external),
          else: raise(ArgumentError, "unexpected external Core node fields")

      :error ->
        raise ArgumentError, "unknown external Core node"
    end
  end

  defp decode_external(_), do: raise(ArgumentError, "invalid external Core node")

  # Current representation (§15).
  defp decode_external_node(%{"node" => "type", "sort" => sort}) do
    case sort_external_decode(sort) do
      {:ok, decoded} -> {:type, decoded}
      {:error, reason} -> raise ArgumentError, "malformed sort index: #{inspect(reason)}"
    end
  end

  defp decode_external_node(%{"node" => "level_type"}), do: {:level_type}

  defp decode_external_node(%{"node" => "level_value", "level" => level}) do
    case level_external_decode(level) do
      {:ok, decoded} -> {:level_value, decoded}
      {:error, reason} -> raise ArgumentError, "malformed level value: #{inspect(reason)}"
    end
  end

  defp decode_external_node(%{"node" => "var", "index" => k}), do: {:var, k}

  defp decode_external_node(%{"node" => "pi", "grade" => g, "dom" => d, "cod" => c}),
    do: {:pi, grade_int(g), decode_external(d), decode_external(c)}

  defp decode_external_node(%{"node" => "lam", "grade" => g, "dom" => d, "body" => b}),
    do: {:lam, grade_int(g), decode_external(d), decode_external(b)}

  defp decode_external_node(%{"node" => "let", "grade" => g, "type" => t, "value" => v, "body" => b}),
    do: {:let, grade_int(g), decode_external(t), decode_external(v), decode_external(b)}

  defp decode_external_node(%{"node" => "app", "fun" => f, "arg" => a}),
    do: {:app, decode_external(f), decode_external(a)}

  defp decode_external_node(%{"node" => "data", "name" => n, "params" => ps, "indices" => is}),
    do: {:data, sym_atom(n), Enum.map(ps, &decode_external/1), Enum.map(is, &decode_external/1)}

  defp decode_external_node(%{"node" => "ctor", "name" => n, "args" => args}),
    do: {:ctor, sym_atom(n), Enum.map(args, &decode_external/1)}

  defp decode_external_node(%{"node" => "case", "scrut" => s, "motive" => m, "branches" => brs}),
    do: {:case, decode_external(s), decode_external(m), Enum.map(brs, &decode_external_branch/1)}

  defp decode_external_node(%{"node" => "global", "name" => n}), do: {:global, sym_atom(n)}

  defp decode_external_node(%{"node" => "int_type"}), do: {:int_type}
  defp decode_external_node(%{"node" => "int_lit", "value" => n}), do: {:int_lit, n}
  defp decode_external_node(%{"node" => "nat_lit", "value" => n}), do: {:nat_lit, n}
  defp decode_external_node(%{"node" => "bounded_lit", "value" => n}), do: {:bounded_lit, n}
  defp decode_external_node(%{"node" => "float_type"}), do: {:float_type}
  defp decode_external_node(%{"node" => "float_lit", "value" => f}), do: {:float_lit, f}
  defp decode_external_node(%{"node" => "binary_type"}), do: {:binary_type}
  defp decode_external_node(%{"node" => "atom_type"}), do: {:atom_type}
  # An atom literal's value is user data (`:ok`, `:tick`, ...), but it is still
  # decoded through the same bounded-interning path as every other symbol:
  # a real term's atom literal was minted when its source was parsed, so it is
  # already interned and `sym_atom/1` decodes it. Using `String.to_atom/1` here
  # was the one atom-minting path in this module that could exhaust the atom
  # table from untrusted `from_external` input (K12 §D).
  defp decode_external_node(%{"node" => "atom_lit", "value" => a}), do: {:atom_lit, sym_atom(a)}

  defp decode_external_node(%{"node" => "effect_type", "arg" => t}), do: {:effect_type, decode_external(t)}
  defp decode_external_node(%{"node" => "effect_pure", "arg" => a}), do: {:effect_pure, decode_external(a)}

  defp decode_external_node(%{"node" => "effect_bind", "effect" => e, "cont" => k}),
    do: {:effect_bind, decode_external(e), decode_external(k)}

  defp decode_external_node(%{"node" => "hole", "name" => name}) when is_binary(name), do: {:hole, name}

  defp decode_external_node(%{"node" => "absurd"}), do: {:absurd}

  defp decode_external_branch(%{"ctor" => name, "arity" => arity, "body" => body} = branch)
       when map_size(branch) == 3 do
    {sym_atom(name), arity, decode_external(body)}
  end

  defp decode_external_branch(_), do: raise(ArgumentError, "invalid external Core branch")

  # -- helpers ----------------------------------------------------------------

  # Bounded symbol interning (K12 / spec §D): decode names into EXISTING atoms
  # only, so untrusted JSON `from_external` input cannot exhaust the atom table
  # (it never shrinks). An unknown symbol raises here — consistent with this
  # function's already-partial contract (a malformed map hits no clause and
  # raises too) — rather than minting a permanent atom. Every symbol in a real
  # term is already interned by the compiler, so valid terms still decode.
  defp sym_atom(n), do: String.to_existing_atom(n)

  defp terms?(list) when is_list(list), do: Enum.all?(list, &term?/1)
  defp terms?(_), do: false

  defp branches?(list) when is_list(list), do: Enum.all?(list, &branch?/1)
  defp branches?(_), do: false

  defp branch?({ctor_name, arity, body})
       when is_atom(ctor_name) and is_integer(arity) and arity >= 0,
       do: term?(body)

  defp branch?(_), do: false

  # Grades cross the external boundary as their own names; `Grade` owns the
  # carrier, so nothing here pattern-matches one.
  defp grade_ext(g), do: Atom.to_string(g)

  defp grade_int(s) when is_binary(s) do
    g = String.to_existing_atom(s)
    if Grade.grade?(g), do: g, else: raise(ArgumentError, "not a grade: #{s}")
  end
end

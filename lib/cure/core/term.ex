defmodule Cure.Core.Term do
  @moduledoc """
  Explicit, fully-annotated Core terms for the trusted dependent-type kernel.

  Terms are plain tagged tuples using de Bruijn indices for bound variables.
  This is the soundness-critical representation described in the design spec
  §4.1; it deliberately carries no implicits, holes, or erasure annotations
  (those live only in the surface/elaborator) — a checked Core term is fully
  explicit and fully relevant.

  Node taxonomy (de Bruijn):

    * `{:type, level}`                       universe, `level` in 0..2
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

  # Single source of truth for the universe ceiling is `Cure.Core.Universe`; this
  # module only mirrors the value into its compile-time shape-check guards.
  alias Cure.Core.Grade

  @ceiling Cure.Core.Universe.ceiling()

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
          {:type, non_neg_integer()}
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

  @doc "Highest universe level (inclusive). The fixed hierarchy is `Type 0 : Type 1 : Type 2`."
  @spec ceiling() :: non_neg_integer()
  def ceiling, do: Cure.Core.Universe.ceiling()

  @doc """
  True when `term` is a structurally well-formed Core term.

  This is a shape check only — it validates node arities, the universe-level
  bound (`0..#{@ceiling}`), and non-negative de Bruijn indices, recursively.
  It does not type-check; that is the kernel's job.
  """
  @spec term?(term()) :: boolean()
  def term?({:type, level}), do: is_integer(level) and level >= 0 and level <= @ceiling
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
  def shift({:type, _} = t, _amount, _cutoff), do: t
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
  def subst({:var, k}, j, r) when k == j, do: r
  def subst({:var, _} = v, _j, _r), do: v
  def subst({:type, _} = t, _j, _r), do: t
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

  @doc "Encode a Core term as a JSON-able map."
  @spec to_external(t()) :: map()
  def to_external({:type, l}), do: %{"node" => "type", "level" => l}
  def to_external({:var, k}), do: %{"node" => "var", "index" => k}

  def to_external({:pi, g, d, c}),
    do: %{"node" => "pi", "grade" => grade_ext(g), "dom" => to_external(d), "cod" => to_external(c)}

  def to_external({:lam, g, d, b}),
    do: %{"node" => "lam", "grade" => grade_ext(g), "dom" => to_external(d), "body" => to_external(b)}

  def to_external({:let, g, t, v, b}),
    do: %{
      "node" => "let",
      "grade" => grade_ext(g),
      "type" => to_external(t),
      "value" => to_external(v),
      "body" => to_external(b)
    }

  def to_external({:app, f, a}),
    do: %{"node" => "app", "fun" => to_external(f), "arg" => to_external(a)}

  def to_external({:data, n, ps, is}),
    do: %{
      "node" => "data",
      "name" => Atom.to_string(n),
      "params" => Enum.map(ps, &to_external/1),
      "indices" => Enum.map(is, &to_external/1)
    }

  def to_external({:ctor, n, args}),
    do: %{"node" => "ctor", "name" => Atom.to_string(n), "args" => Enum.map(args, &to_external/1)}

  def to_external({:case, s, m, brs}),
    do: %{
      "node" => "case",
      "scrut" => to_external(s),
      "motive" => to_external(m),
      "branches" =>
        Enum.map(brs, fn {cn, ar, b} ->
          %{"ctor" => Atom.to_string(cn), "arity" => ar, "body" => to_external(b)}
        end)
    }

  def to_external({:global, n}), do: %{"node" => "global", "name" => Atom.to_string(n)}

  def to_external({:int_type}), do: %{"node" => "int_type"}
  def to_external({:int_lit, n}), do: %{"node" => "int_lit", "value" => n}
  def to_external({:nat_lit, n}), do: %{"node" => "nat_lit", "value" => n}
  def to_external({:bounded_lit, n}), do: %{"node" => "bounded_lit", "value" => n}
  def to_external({:float_type}), do: %{"node" => "float_type"}
  def to_external({:float_lit, f}), do: %{"node" => "float_lit", "value" => f}
  def to_external({:binary_type}), do: %{"node" => "binary_type"}
  def to_external({:atom_type}), do: %{"node" => "atom_type"}
  def to_external({:atom_lit, a}), do: %{"node" => "atom_lit", "value" => Atom.to_string(a)}

  def to_external({:effect_type, t}), do: %{"node" => "effect_type", "arg" => to_external(t)}
  def to_external({:effect_pure, a}), do: %{"node" => "effect_pure", "arg" => to_external(a)}

  def to_external({:effect_bind, e, k}),
    do: %{"node" => "effect_bind", "effect" => to_external(e), "cont" => to_external(k)}

  def to_external({:hole, name}), do: %{"node" => "hole", "name" => name}

  @doc """
  Decode a JSON-able map produced by `to_external/1` back into a Core term.

  The map is an external trust boundary. The fully reconstructed value is
  checked against `term?/1`; malformed encodings raise instead of leaking a
  tuple that the Core grammar itself rejects.
  """
  @spec from_external(map()) :: t()
  def from_external(external) when is_map(external) do
    term = decode_external(external)

    if term?(term) do
      term
    else
      raise ArgumentError, "ill-formed external Core term: #{inspect(term)}"
    end
  end

  defp decode_external(%{"node" => "type", "level" => l}), do: {:type, l}
  defp decode_external(%{"node" => "var", "index" => k}), do: {:var, k}

  defp decode_external(%{"node" => "pi", "grade" => g, "dom" => d, "cod" => c}),
    do: {:pi, grade_int(g), decode_external(d), decode_external(c)}

  defp decode_external(%{"node" => "lam", "grade" => g, "dom" => d, "body" => b}),
    do: {:lam, grade_int(g), decode_external(d), decode_external(b)}

  defp decode_external(%{"node" => "let", "grade" => g, "type" => t, "value" => v, "body" => b}),
    do: {:let, grade_int(g), decode_external(t), decode_external(v), decode_external(b)}

  defp decode_external(%{"node" => "app", "fun" => f, "arg" => a}),
    do: {:app, decode_external(f), decode_external(a)}

  defp decode_external(%{"node" => "data", "name" => n, "params" => ps, "indices" => is}),
    do: {:data, sym_atom(n), Enum.map(ps, &decode_external/1), Enum.map(is, &decode_external/1)}

  defp decode_external(%{"node" => "ctor", "name" => n, "args" => args}),
    do: {:ctor, sym_atom(n), Enum.map(args, &decode_external/1)}

  defp decode_external(%{"node" => "case", "scrut" => s, "motive" => m, "branches" => brs}),
    do:
      {:case, decode_external(s), decode_external(m),
       Enum.map(brs, fn %{"ctor" => cn, "arity" => ar, "body" => b} ->
         {sym_atom(cn), ar, decode_external(b)}
       end)}

  defp decode_external(%{"node" => "global", "name" => n}), do: {:global, sym_atom(n)}

  defp decode_external(%{"node" => "int_type"}), do: {:int_type}
  defp decode_external(%{"node" => "int_lit", "value" => n}), do: {:int_lit, n}
  defp decode_external(%{"node" => "nat_lit", "value" => n}), do: {:nat_lit, n}
  defp decode_external(%{"node" => "bounded_lit", "value" => n}), do: {:bounded_lit, n}
  defp decode_external(%{"node" => "float_type"}), do: {:float_type}
  defp decode_external(%{"node" => "float_lit", "value" => f}), do: {:float_lit, f}
  defp decode_external(%{"node" => "binary_type"}), do: {:binary_type}
  defp decode_external(%{"node" => "atom_type"}), do: {:atom_type}
  defp decode_external(%{"node" => "atom_lit", "value" => a}), do: {:atom_lit, String.to_atom(a)}

  defp decode_external(%{"node" => "effect_type", "arg" => t}), do: {:effect_type, decode_external(t)}
  defp decode_external(%{"node" => "effect_pure", "arg" => a}), do: {:effect_pure, decode_external(a)}

  defp decode_external(%{"node" => "effect_bind", "effect" => e, "cont" => k}),
    do: {:effect_bind, decode_external(e), decode_external(k)}

  defp decode_external(%{"node" => "hole", "name" => name}) when is_binary(name), do: {:hole, name}

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

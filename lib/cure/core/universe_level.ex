defmodule Cure.Core.UniverseLevel do
  @moduledoc """
  Canonical universe levels: the maximum-plus normal form of Agda's
  `Agda.Syntax.Internal.Level'` (`Max Integer [PlusLevel]`).

  **Authority:** `docs/superpowers/specs/types/2026-07-20-agda-style-universe-polymorphism-design.md`
  §6. Structural canonicalization is distinct from contextual atom typing and
  certified conversion. Constructing a level is never evidence of admission.

  ## Representation

  A level is a *maximum of atoms plus offsets, floored by a constant*:

      L ::= max(c, a₁ + k₁, …, aₙ + kₙ)

  where `c` and each `kᵢ` are non-negative integers, and each `aᵢ` is a quoted
  neutral Core term checked at `UniverseLevel`. The canonical form is a struct:

      %UniverseLevel{constant: c, atoms: [{atom_term, offset}]}

  Canonicalization (§6.2) guarantees, for every value this module returns:

    1. no atom appears twice;
    2. for an equal atom only the greatest offset is retained;
    3. atoms are sorted deterministically (see "Atom ordering" below);
    4. `constant` is `0` when some atom offset already guarantees at least `c`;
    5. `max(0)` — `constant: 0, atoms: []` — is the unique zero normal form;
    6. offsets and the constant are non-negative.

  **No caller may assemble an unchecked normal form by concatenating atom
  lists** (§6.3). Every constructor here returns canonical form; `validate/2`
  re-checks a value that crossed an untrusted boundary.

  ## Atom ordering

  Core atoms are ordered by the portable unframed term bytes owned by the
  versioned `Cure.Core.UniverseCodec`. Private semantic NbE atoms never cross
  this boundary; they are quoted to Core at the actual binder depth first.

  ## What is deliberately absent

  Per §4 ("Cure does not initially adopt"), there is no `Prop`, no cubical
  interval universe, no size universe, no `--type-in-type` escape hatch, no
  user-defined level rewrite rules, no runtime reflection over levels, and no
  eliminator exposing a natural-number representation. A level is
  compile-time-only; §13 requires it to erase.
  """

  alias Cure.Core.Grade

  @enforce_keys [:constant, :atoms]
  defstruct constant: 0, atoms: []

  @typedoc """
  A canonical level: a `max`-of-atoms-plus-offsets floored by a constant.

  `atoms` is a list of `{atom_term, offset}` with `offset >= 0`, sorted by
  `atom_order_key/1`, free of duplicate atoms.
  """
  @type t :: %__MODULE__{
          constant: non_neg_integer(),
          atoms: [{Cure.Core.Term.t(), non_neg_integer()}]
        }

  @type context :: Cure.Core.Context.t() | nil

  # ---------------------------------------------------------------------------
  # Construction (§6.3)
  # ---------------------------------------------------------------------------

  @doc """
  The unique zero normal form: `max(0)` with no atoms.
  """
  @spec zero() :: t()
  def zero, do: %__MODULE__{constant: 0, atoms: []}

  @doc """
  A closed level `n` — a bare constant, never expanded into `n` successor nodes.

  §5.2: "Closed numeric spellings use `TypeN` and are stored as a constant in the
  level normal form, never expanded into `N` successor nodes." So `closed(37)`
  is one struct, not a 37-deep tower, which is what makes `Type37 : Type38`
  cheap (§19.2).
  """
  @spec closed(non_neg_integer()) :: t()
  def closed(n) when is_integer(n) and n >= 0, do: %__MODULE__{constant: n, atoms: []}

  def closed(n) do
    raise ArgumentError, "a closed universe level must be a non-negative integer, got: #{inspect(n)}"
  end

  @doc "Map Core atom terms without introducing a binder, then restore canonical form."
  @spec map(t(), (Cure.Core.Term.t() -> Cure.Core.Term.t())) :: t()
  def map(%__MODULE__{} = level, transform) do
    normalize(%__MODULE__{
      constant: level.constant,
      atoms: Enum.map(level.atoms, fn {term, offset} -> {transform.(term), offset} end)
    })
  end

  @doc """
  A single atom: a neutral Core term checked at `UniverseLevel`, at offset zero.

  The term is *not* validated here — checking that it inhabits `UniverseLevel`
  is the kernel's job (§6.3 `validate/2`, §7.3 "every atom is scope-correct").
  A forged atom can therefore be constructed by untrusted code, which is
  exactly why `validate/2` exists and why the kernel must call it at the
  boundary.
  """
  @spec atom(Cure.Core.Term.t()) :: t()
  def atom(term), do: normalize(%__MODULE__{constant: 0, atoms: [{term, 0}]})

  @doc """
  Successor. Distributes over `max` (§3.2): `succ(max(c, a+k, …))` is
  `max(c+1, a+(k+1), …)`.
  """
  @spec succ(t()) :: t()
  def succ(%__MODULE__{constant: c, atoms: atoms}) do
    normalize(%__MODULE__{
      constant: c + 1,
      atoms: Enum.map(atoms, fn {term, offset} -> {term, offset + 1} end)
    })
  end

  @doc """
  Least upper bound. Canonical: commutative, associative, idempotent, and
  `max(a, zero) == a` (§19.1).
  """
  @spec max(t(), t()) :: t()
  def max(%__MODULE__{} = left, %__MODULE__{} = right) do
    normalize(%__MODULE__{
      constant: Kernel.max(left.constant, right.constant),
      atoms: left.atoms ++ right.atoms
    })
  end

  @doc """
  Canonicalize a raw level.

  This is the single normalizer (§6.2 steps 1–4). Every constructor above routes
  through it, so no caller can assemble a non-canonical form.
  """
  @spec normalize(t()) :: t()
  def normalize(%__MODULE__{constant: c, atoms: atoms}) when is_integer(c) and c >= 0 and is_list(atoms) do
    {c, atoms} =
      Enum.reduce(atoms, {c, []}, fn entry, acc ->
        {term, offset} = check_atom!(entry)
        flatten_atom(term, offset, acc)
      end)

    merged =
      atoms
      # Step 2: merge equal atoms, retaining the greatest offset.
      |> Enum.reduce(%{}, fn {term, offset}, acc ->
        Map.update(acc, term, offset, &Kernel.max(&1, offset))
      end)
      # Step 3: deterministic order.
      |> Enum.sort_by(fn {term, _offset} -> atom_order_key(term) end)
      |> Enum.map(fn {term, offset} -> {term, offset} end)

    # Step 4: a constant already subsumed by an atom offset is dropped. Every
    # atom contributes at least its offset, so the effective floor is
    # `max(c, max_offset)`, and storing the larger of the two in `constant`
    # would be redundant. We keep the constant only when it strictly exceeds
    # every atom offset.
    effective_constant = if merged == [], do: c, else: max_constant(c, merged)

    %__MODULE__{constant: effective_constant, atoms: merged}
  end

  def normalize(other) do
    raise ArgumentError, "not a universe level: #{inspect(other)}"
  end

  defp flatten_atom({:level_value, %__MODULE__{} = inner}, offset, {constant, atoms}) do
    inner = normalize(inner)

    {Kernel.max(constant, inner.constant + offset),
     Enum.map(inner.atoms, fn {term, inner_offset} -> {term, inner_offset + offset} end) ++ atoms}
  end

  defp flatten_atom(term, offset, {constant, atoms}), do: {constant, [{term, offset} | atoms]}

  # The constant survives only if it exceeds EVERY atom offset; otherwise the
  # atoms already guarantee at least that much and the constant is redundant.
  defp max_constant(c, merged) do
    if Enum.all?(merged, fn {_term, offset} -> offset < c end), do: c, else: 0
  end

  defp check_atom!({term, offset}) when is_integer(offset) and offset >= 0, do: {term, offset}

  defp check_atom!(other) do
    raise ArgumentError,
          "a level atom must be {term, offset} with a non-negative integer offset, got: #{inspect(other)}"
  end

  # ---------------------------------------------------------------------------
  # Equality and ordering (§6.4, §6.5)
  # ---------------------------------------------------------------------------

  @doc """
  Equality of canonical normal forms.

  §6.4 requires atoms to be compared by ordinary Core definitional equality, not
  Elixir term equality. That comparison needs conversion, which needs the
  signature — so this function takes a `context` (a `%Cure.Core.Context{}`, or
  `nil` for a context-free comparison).

  **U1 scope:** with `nil` the comparison is structural. With a context it still
  is structural, because atom *conversion* is U2/U3 work — `Conv.conv_values?/4`
  does not yet know about levels. The signature is threaded now so the call
  sites do not change when that lands.
  """
  @spec equal?(t(), t(), context()) :: boolean()
  def equal?(%__MODULE__{} = left, %__MODULE__{} = right, _context) do
    left = normalize(left)
    right = normalize(right)
    left.constant == right.constant and atoms_equal?(left.atoms, right.atoms)
  end

  defp atoms_equal?(left, right) when length(left) != length(right), do: false

  defp atoms_equal?(left, right) do
    Enum.zip(left, right)
    |> Enum.all?(fn {{lt, lo}, {rt, ro}} -> lo == ro and atom_equal?(lt, rt) end)
  end

  # Structural atom equality. U2 replaces this with conversion at
  # `UniverseLevel` (§6.4); the seam is here and nowhere else.
  defp atom_equal?(left, right), do: left == right

  @doc """
  Cumulative inclusion: `a <= b` iff `max(a, b) == b` (§6.5).

  The component test is used directly rather than building the join, because it
  is the same decision without the allocation:

    * the constant of `a` must be dominated by `b`;
    * every `x + k` of `a` must have the same atom `x` in `b` at an offset
      `j >= k`;
    * unrelated atoms do not dominate each other.
  """
  @spec leq?(t(), t(), context()) :: boolean()
  def leq?(%__MODULE__{} = left, %__MODULE__{} = right, context) do
    left = normalize(left)
    right = normalize(right)

    constant_dominated?(left, right) and atoms_dominated?(left.atoms, right.atoms, context)
  end

  # `a`'s constant must be reachable from `b`: either `b`'s constant covers it,
  # or some atom of `b` has an offset that does.
  defp constant_dominated?(%{constant: c}, %{constant: bc, atoms: batoms}) do
    c <= bc or Enum.any?(batoms, fn {_term, offset} -> c <= offset end)
  end

  defp atoms_dominated?(left_atoms, right_atoms, _context) do
    Enum.all?(left_atoms, fn {lterm, loffset} ->
      Enum.any?(right_atoms, fn {rterm, roffset} ->
        loffset <= roffset and atom_equal?(lterm, rterm)
      end)
    end)
  end

  # ---------------------------------------------------------------------------
  # Substitution and shifting (§6.3, §7.2)
  # ---------------------------------------------------------------------------

  @doc """
  Shift every free de Bruijn variable inside every atom by `amount`, above
  `cutoff`.

  §7.2 lists shift as one of the traversals that **must** descend into level
  atoms; treating a level as an inert leaf "would permit scope escape and is a
  soundness bug".
  """
  @spec shift(t(), integer(), non_neg_integer()) :: t()
  def shift(%__MODULE__{} = level, amount, cutoff \\ 0) do
    normalize(%__MODULE__{
      constant: level.constant,
      atoms: Enum.map(level.atoms, fn {term, offset} -> {Cure.Core.Term.shift(term, amount, cutoff), offset} end)
    })
  end

  @doc """
  Substitute de Bruijn index `index` with `replacement` inside every atom.

  Like `shift/3`, this must descend into atoms (§7.2). The replacement is a Core
  term; offsets are untouched.
  """
  @spec subst(t(), non_neg_integer(), Cure.Core.Term.t()) :: t()
  def subst(%__MODULE__{} = level, index, replacement) do
    normalize(%__MODULE__{
      constant: level.constant,
      atoms: Enum.map(level.atoms, fn {term, offset} -> {Cure.Core.Term.subst(term, index, replacement), offset} end)
    })
  end

  @doc """
  Every free de Bruijn variable occurring in any atom, as a sorted unique list.

  Used by scope checks. A level with no atoms has no free variables.
  """
  @spec free_vars(t()) :: [non_neg_integer()]
  def free_vars(%__MODULE__{atoms: atoms}) do
    atoms
    |> Enum.flat_map(fn {term, _offset} -> term_free_vars(term, 0) end)
    |> Enum.uniq()
    |> Enum.sort()
  end

  # Mirror of `Term.has_free_var?/2`'s binder accounting, but collecting instead
  # of testing. Kept in lockstep with `Term.shift/3`.
  defp term_free_vars({:var, k}, depth), do: if(k >= depth, do: [k - depth], else: [])

  defp term_free_vars({:lam, _g, dom, body}, depth),
    do: term_free_vars(dom, depth) ++ term_free_vars(body, depth + 1)

  defp term_free_vars({:pi, _g, dom, cod}, depth),
    do: term_free_vars(dom, depth) ++ term_free_vars(cod, depth + 1)

  defp term_free_vars({:let, _g, ty, val, body}, depth),
    do:
      term_free_vars(ty, depth) ++
        term_free_vars(val, depth) ++ term_free_vars(body, depth + 1)

  defp term_free_vars({:case, scrut, motive, branches}, depth) do
    term_free_vars(scrut, depth) ++
      term_free_vars(motive, depth) ++
      Enum.flat_map(branches, fn {_ctor, arity, body} -> term_free_vars(body, depth + arity) end)
  end

  defp term_free_vars(%__MODULE__{atoms: atoms}, depth),
    do: Enum.flat_map(atoms, fn {term, _offset} -> term_free_vars(term, depth) end)

  defp term_free_vars(term, depth) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.flat_map(&term_free_vars(&1, depth))

  defp term_free_vars(list, depth) when is_list(list),
    do: Enum.flat_map(list, &term_free_vars(&1, depth))

  defp term_free_vars(_leaf, _depth), do: []

  # ---------------------------------------------------------------------------
  # Validation (§6.3, §15)
  # ---------------------------------------------------------------------------

  @doc """
  Is `value` a well-formed *canonical* level?

  Rejects, per §15's untrusted-decoding list: negative constants or offsets,
  duplicate or unsorted atoms, a nonzero constant subsumed by an atom offset,
  and any shape that is not a `%UniverseLevel{}`.

  This is a **structural** check. Scope-correctness of atoms and their
  inhabitation of `UniverseLevel` are the kernel's obligation (§7.3) and need a
  context; `validate/2` accepts one and, when given, re-checks each atom is a
  Core term. It does not type-check them — that is `Kernel.infer/2`.
  """
  @spec validate(term(), context()) :: :ok | {:error, term()}
  def validate(%__MODULE__{constant: c, atoms: atoms}, context) do
    cond do
      not (is_integer(c) and c >= 0) ->
        {:error, {:noncanonical_level_encoding, {:negative_or_noninteger_constant, c}}}

      not is_list(atoms) ->
        {:error, {:noncanonical_level_encoding, {:atoms_not_a_list, atoms}}}

      true ->
        with :ok <- validate_atoms(atoms, context),
             :ok <- validate_canonical(%__MODULE__{constant: c, atoms: atoms}) do
          :ok
        end
    end
  end

  def validate(other, _context),
    do: {:error, {:noncanonical_level_encoding, {:not_a_universe_level, other}}}

  defp validate_atoms(atoms, context) do
    Enum.reduce_while(atoms, :ok, fn
      {term, offset}, :ok when is_integer(offset) and offset >= 0 ->
        if atom_term?(term, context),
          do: {:cont, :ok},
          else: {:halt, {:error, {:noncanonical_level_encoding, {:bad_atom_term, term}}}}

      other, :ok ->
        {:halt, {:error, {:noncanonical_level_encoding, {:bad_atom, other}}}}
    end)
  end

  defp atom_term?(term, context) when is_tuple(term),
    do:
      neutral_term?(term) and Cure.Core.Term.term?(term) and not hidden_hole?(term) and
        atom_typed?(term, context)

  defp atom_term?(_term, _context), do: false

  defp atom_typed?(_term, nil), do: true

  defp atom_typed?(term, context) do
    case Cure.Core.Kernel.infer(context, term) do
      {:ok, type} ->
        Cure.Core.Normalise.whnf_value(type, Cure.Core.Context.signature(context)) == {:vlevel_type}

      {:error, _} ->
        false
    end
  end

  defp neutral_term?({:var, _}), do: true
  defp neutral_term?({:global, _}), do: true
  defp neutral_term?({:app, head, _}), do: neutral_term?(head)
  defp neutral_term?({:case, scrutinee, _, _}), do: neutral_term?(scrutinee)
  defp neutral_term?(_), do: false

  defp hidden_hole?({:hole, _}), do: true
  defp hidden_hole?({:meta, _}), do: true

  defp hidden_hole?(%__MODULE__{atoms: atoms}),
    do: Enum.any?(atoms, fn {term, _offset} -> hidden_hole?(term) end)

  defp hidden_hole?(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.any?(&hidden_hole?/1)

  defp hidden_hole?(terms) when is_list(terms), do: Enum.any?(terms, &hidden_hole?/1)
  defp hidden_hole?(_), do: false

  # A canonical form must be a fixed point of `normalize/1`. That single check
  # covers duplicate atoms, unsorted atoms and a subsumed constant at once,
  # without restating each rule — and it cannot drift from the normalizer.
  defp validate_canonical(%__MODULE__{} = level) do
    if normalize(level) == level,
      do: :ok,
      else: {:error, {:noncanonical_level_encoding, {:not_normalized, level}}}
  end

  # ---------------------------------------------------------------------------
  # Display (§6.3 "printing", §16)
  # ---------------------------------------------------------------------------

  @doc """
  Render a level in source notation: `universe_zero`, `universe_succ(...)`,
  `universe_max(...)`, or a closed numeral.

  §16 asks diagnostics to "show both source notation and normalized form when
  that distinction explains the failure". `to_string/1` is the source-notation
  side; `inspect/1` (the struct) is the normalized side.
  """
  @spec to_string(t(), [String.t()]) :: String.t()
  def to_string(level, names \\ [])

  def to_string(%__MODULE__{constant: 0, atoms: []}, _names), do: "universe_zero"

  def to_string(%__MODULE__{constant: c, atoms: []}, _names), do: render_integer(c)

  def to_string(%__MODULE__{constant: c, atoms: atoms}, names) do
    # Each atom renders as `atom` at offset 0, or as the `offset`-fold successor
    # of the atom. The constant is a SEPARATE operand only when it is not
    # already implied by an atom — canonical form guarantees that (a nonzero
    # constant exceeds every atom offset), so it is safe to emit it first.
    parts =
      Enum.map(Enum.take(atoms, 16), fn {term, offset} -> render_atom(term, offset, names) end)

    constant_part = if c > 0, do: [render_integer(c)], else: []
    suffix = if length(atoms) > 16, do: ["…"], else: []
    Enum.reduce(constant_part ++ parts ++ suffix, fn part, acc -> "universe_max(#{acc}, #{part})" end)
  end

  # An atom at offset `n` is `n`-fold `universe_succ` of the atom. Rendering it
  # as `universe_max(atom, n)` would be WRONG — that is `max(atom, n)`, a level
  # floored by the numeral `n`, not `atom + n`. Successor is the operation the
  # offset actually denotes (§3.2: `succ(a + k) = a + (k+1)`).
  defp render_atom(term, 0, names), do: render_term(term, names)

  defp render_atom(term, offset, names) when is_integer(offset) and offset > 0 and offset <= 16 do
    Enum.reduce(1..offset, render_term(term, names), fn _step, acc ->
      "universe_succ(#{acc})"
    end)
  end

  defp render_atom(term, offset, names), do: "#{render_term(term, names)} + #{render_integer(offset)}"

  defp render_integer(integer) do
    if :erlang.external_size(integer) <= 128,
      do: Integer.to_string(integer),
      else: "<large level>"
  end

  defp render_term(term, names) do
    if :erlang.external_size(term) <= 2048,
      do: term |> Cure.Core.Printer.print(names) |> String.slice(0, 512),
      else: "<level atom>"
  end

  # ---------------------------------------------------------------------------
  # Atom ordering seam
  # ---------------------------------------------------------------------------

  @doc """
  The deterministic ordering key for a level atom.

  §6.2 requires canonical serialized term order, not host ETF order.
  """
  @spec atom_order_key(Cure.Core.Term.t()) :: binary()
  def atom_order_key(term), do: Cure.Core.UniverseCodec.atom_order_key(term)

  # ---------------------------------------------------------------------------
  # Erasure (§13)
  # ---------------------------------------------------------------------------

  @doc """
  The grade every `UniverseLevel` binder is forced to.

  §13: "Every binder whose domain is `UniverseLevel` is forced to grade zero. An
  explicit attempt to mark one present is rejected." Exposed here so the
  elaborator and the relevance checker share one source of truth rather than
  each spelling `:erased`.
  """
  @spec binder_grade() :: Grade.t()
  def binder_grade, do: :erased
end

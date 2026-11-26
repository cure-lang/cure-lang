defmodule Cure.Core.Sort do
  @moduledoc """
  Sort indices: the replacement for integer universe levels in Core.

  **Authority:** `docs/superpowers/specs/types/2026-07-20-agda-style-universe-polymorphism-design.md`
  §7.1 and §8. This module is **phase U2** of that spec's §18 sequence.

  ## Representation (§7.1)

      sort_index ::= {:finite, level_nf}
                   | {:omega, non_neg_integer()}

  `{:finite, level}` is a finite universe `Type(level)`; `level` is a
  `Cure.Core.UniverseLevel` canonical normal form. `{:omega, n}` is the
  user-facing `TypeLimit(n)` — the sort of types whose finite level is unbounded
  because it depends rigidly on a quantified `UniverseLevel` (§12).

  `omega` is retained as the internal tag and mathematical name; `TypeLimit` is
  the surface spelling.

  ## Sorting rules (§8)

  The rules implemented here are the primitive ones plus the join/`piSort`
  classification. They are **pure functions on sort indices**; the kernel calls
  them, and the kernel is still the only thing that decides a judgment.

  Write `U(u)` for `{:finite, u}` and `Limit(n)` for `{:omega, n}`.

  ### 8.1 Primitive rules

      UniverseLevel : Type(universe_zero)
      universe_zero : UniverseLevel
      universe_succ(u) : UniverseLevel     when u : UniverseLevel
      universe_max(u, v) : UniverseLevel   when u, v : UniverseLevel

  ### 8.2 Universe rules

      Type(u) : Type(universe_succ(u))
      TypeLimit(n) : TypeLimit(n + 1)

  There is deliberately **no** derivation of `Type(u) : Type(u)` or
  `TypeLimit(n) : TypeLimit(n)`. `successor/1` is therefore total on both forms
  and never returns the input.

  ### 8.3 Join of non-dependent sorts

      join(U(a), U(b))   = U(universe_max(a, b))
      join(U(_), Limit(n)) = Limit(n)
      join(Limit(n), U(_)) = Limit(n)
      join(Limit(m), Limit(n)) = Limit(max(m, n))

  ### 8.5 Cumulativity

      U(a)     <= U(b)     iff a <= b
      U(a)     <= Limit(n) always
      Limit(m) <= Limit(n) iff m <= n
      Limit(_) <= U(_)     never

  Cumulativity is identity-only: it inserts no runtime coercion and has no
  reduction rule (§8.5). `Kernel.check` records success only by running
  `leq?/2`; the elaborator cannot assert it.

  ### 8.4 Rigidly level-dependent `Pi`

  `pi_sort/3` decides the sort of `Pi(x:A).B`. When the codomain sort does not
  mention the binder, the result is `join(dom_sort, cod_sort)`. When it does —
  `x` occurs rigidly in the finite level of the codomain sort — no finite sort
  is a uniform upper bound, so the result is `Limit(0)`, or `Limit(n)` if the
  domain already has sort `Limit(n)`.

  Because checked Core has no level metavariables (§7.3), the kernel sees either
  a rigid occurrence or none; the "blocked under an unsolved meta" case is an
  elaborator concern and is not representable here.
  """

  alias Cure.Core.UniverseLevel

  @typedoc """
  A sort index: a finite universe at a canonical level, or `TypeLimit(n)`.
  """
  @type t :: {:finite, UniverseLevel.t()} | {:omega, non_neg_integer()}

  @type context :: UniverseLevel.context()

  @doc "Map atom terms without introducing a binder; limit indices contain no terms."
  @spec map(t(), (Cure.Core.Term.t() -> Cure.Core.Term.t())) :: t()
  def map({:finite, level}, transform), do: {:finite, UniverseLevel.map(level, transform)}
  def map({:omega, _} = sort, _transform), do: sort

  # ---------------------------------------------------------------------------
  # Construction
  # ---------------------------------------------------------------------------

  @doc "The smallest finite sort, `Type(universe_zero)`."
  @spec finite_zero() :: t()
  def finite_zero, do: {:finite, UniverseLevel.zero()}

  @doc "A finite sort at a closed level `n`."
  @spec finite_closed(non_neg_integer()) :: t()
  def finite_closed(n), do: {:finite, UniverseLevel.closed(n)}

  @doc "A finite sort at an arbitrary canonical level."
  @spec finite(UniverseLevel.t()) :: t()
  def finite(%UniverseLevel{} = level), do: {:finite, UniverseLevel.normalize(level)}

  @doc "`TypeLimit(n)` — the `n`-th limit sort."
  @spec omega(non_neg_integer()) :: t()
  def omega(n) when is_integer(n) and n >= 0, do: {:omega, n}

  def omega(n) do
    raise ArgumentError, "a TypeLimit index must be a non-negative integer, got: #{inspect(n)}"
  end

  # ---------------------------------------------------------------------------
  # §8.1 / §8.2 — universe formation
  # ---------------------------------------------------------------------------

  @doc """
  The sort of a sort: `Type(u) : Type(succ u)` and `TypeLimit(n) : TypeLimit(n+1)`.

  §8.2 states there is deliberately no derivation of `Type(u) : Type(u)` or
  `TypeLimit(n) : TypeLimit(n)`, so this is strictly increasing on both forms.
  """
  @spec successor(t()) :: t()
  def successor({:finite, level}), do: {:finite, UniverseLevel.succ(level)}
  def successor({:omega, n}), do: {:omega, n + 1}

  # ---------------------------------------------------------------------------
  # §8.3 — join of non-dependent sorts
  # ---------------------------------------------------------------------------

  @doc """
  The join of two sorts, used for a **non-dependent** `Pi`.

  `join(U(a), U(b)) = U(max a b)`; any limit operand dominates, and two limits
  join by their index maximum.
  """
  @spec join(t(), t()) :: t()
  def join({:finite, a}, {:finite, b}), do: {:finite, UniverseLevel.max(a, b)}
  def join({:finite, _}, {:omega, n}), do: {:omega, n}
  def join({:omega, n}, {:finite, _}), do: {:omega, n}
  def join({:omega, m}, {:omega, n}), do: {:omega, Kernel.max(m, n)}

  # ---------------------------------------------------------------------------
  # §8.4 — dependent Pi sorting
  # ---------------------------------------------------------------------------

  @doc """
  The sort of `Pi(x:A).B`.

  `cod_mentions_binder?` must be `true` exactly when `x` occurs **rigidly** in
  the finite level of the codomain sort (§8.4). The kernel computes it by
  inspecting the codomain sort's level atoms; this function only applies the
  rule.

  * codomain sort does not mention the binder → `join(dom_sort, cod_sort)`
  * codomain sort mentions it rigidly and the domain is finite → `Limit(0)`
  * codomain sort mentions it rigidly and the domain is `Limit(n)` → `Limit(n)`
  """
  @spec pi_sort(t(), t(), boolean()) :: t()
  def pi_sort(dom_sort, cod_sort, false), do: join(dom_sort, cod_sort)

  def pi_sort({:omega, n}, _cod_sort, true), do: {:omega, n}
  def pi_sort({:finite, _}, _cod_sort, true), do: {:omega, 0}

  # ---------------------------------------------------------------------------
  # §8.5 — cumulativity
  # ---------------------------------------------------------------------------

  @doc """
  Sort inclusion, §8.5.

      U(a)     <= U(b)     iff a <= b
      U(a)     <= Limit(n) always
      Limit(m) <= Limit(n) iff m <= n
      Limit(_) <= U(_)     never
  """
  @spec leq?(t(), t(), context()) :: boolean()
  def leq?({:finite, a}, {:finite, b}, context), do: UniverseLevel.leq?(a, b, context)
  def leq?({:finite, _}, {:omega, _n}, _context), do: true
  def leq?({:omega, m}, {:omega, n}, _context), do: m <= n
  def leq?({:omega, _}, {:finite, _}, _context), do: false

  @doc """
  Sort **equality** — structural, with no cumulativity.

  §9: "`Conv` compares `vtype` values using sort-index equality, not
  cumulativity. Cumulativity belongs to checking/subsumption; definitional
  equality does not identify `Type(a)` with a strictly larger `Type(b)`."
  """
  @spec equal?(t(), t(), context()) :: boolean()
  def equal?({:finite, a}, {:finite, b}, context), do: UniverseLevel.equal?(a, b, context)
  def equal?({:omega, m}, {:omega, n}, _context), do: m == n
  def equal?(_left, _right, _context), do: false

  # ---------------------------------------------------------------------------
  # Traversal (§7.2)
  # ---------------------------------------------------------------------------

  @doc """
  Shift the level atoms inside a finite sort. A limit sort has no atoms.

  §7.2 lists shift as a traversal that must descend into level atoms; treating
  a sort as an inert leaf would permit scope escape.
  """
  @spec shift(t(), integer(), non_neg_integer()) :: t()
  def shift({:finite, level}, amount, cutoff),
    do: {:finite, UniverseLevel.shift(level, amount, cutoff)}

  def shift({:omega, _} = sort, _amount, _cutoff), do: sort

  @doc "Substitute inside a finite sort's level atoms."
  @spec subst(t(), non_neg_integer(), Cure.Core.Term.t()) :: t()
  def subst({:finite, level}, index, replacement),
    do: {:finite, UniverseLevel.subst(level, index, replacement)}

  def subst({:omega, _} = sort, _index, _replacement), do: sort

  @doc "Free de Bruijn variables occurring in a sort's level atoms."
  @spec free_vars(t()) :: [non_neg_integer()]
  def free_vars({:finite, level}), do: UniverseLevel.free_vars(level)
  def free_vars({:omega, _}), do: []

  # ---------------------------------------------------------------------------
  # §15 — validation
  # ---------------------------------------------------------------------------

  @doc """
  Is `value` a well-formed sort index?

  Rejects unknown tags, negative limit indices, and any finite level that
  `UniverseLevel.validate/2` rejects. A **legacy integer level** is rejected
  here: §17.3 says the final validator refuses integer-level Core so stale
  walkers or generators cannot silently survive the migration. Old artifacts
  are handled by the compatibility decoder in `Cure.Core.Serialize`, not here.
  """
  @spec validate(term(), context()) :: :ok | {:error, term()}
  def validate({:finite, %UniverseLevel{} = level}, context),
    do: UniverseLevel.validate(level, context)

  def validate({:omega, n}, _context) when is_integer(n) and n >= 0, do: :ok

  def validate({:omega, n}, _context),
    do: {:error, {:invalid_sort, {:negative_or_noninteger_limit_index, n}}}

  def validate(other, _context), do: {:error, {:invalid_sort, other}}

  # ---------------------------------------------------------------------------
  # Display (§16)
  # ---------------------------------------------------------------------------

  @doc """
  Render a sort in source notation: `Type`, `TypeN`, or `TypeLimitN`.

  A finite sort whose level is a bare constant `n` renders as `Type` for `n == 0`
  and `TypeN` otherwise, matching the surface spellings in §5.2. A level with
  atoms renders as `Type(<level>)`.
  """
  @spec to_string(t()) :: String.t()
  def to_string({:finite, %UniverseLevel{constant: 0, atoms: []}}), do: "Type"
  def to_string({:finite, %UniverseLevel{constant: n, atoms: []}}), do: "Type#{n}"
  def to_string({:finite, level}), do: "Type(#{UniverseLevel.to_string(level)})"
  def to_string({:omega, 0}), do: "TypeLimit"
  def to_string({:omega, n}), do: "TypeLimit#{n}"
end

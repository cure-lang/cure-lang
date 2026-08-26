defmodule Cure.Core.Grade do
  @moduledoc """
  The quantity carrier for Quantitative Type Theory (Atkey), and the single
  place any grade is interpreted.

  Idris abstracts its quantity behind `Algebra.Semiring` (`|+|`, `|*|`,
  `plusNeutral`, `timesNeutral`) plus `Algebra.Preorder`, and instantiates it at
  the three-element `ZeroOneOmega` (`src/Algebra/ZeroOneOmega.idr`). Cure keeps
  the same interface and instantiates a **four**-element carrier:

    * `:erased`       — `0`, used zero times; erased at runtime.
    * `:linear`       — `1`, used exactly once.
    * `:affine`       — `≤1`, used at most once; **may be dropped**.
    * `:unrestricted` — `ω`, used freely. The default.

  ## Why four, and why now

  The expensive part of quantities is the **binder reshape** (`{:pi, dom, cod}` →
  `{:pi, grade, dom, cod}`) and teaching `Conv` to compare grades — Idris's
  `convBinders` compares `multiplicity`, so `(1 x : A) -> B` is a *different type*
  from `(x : A) -> B` (`src/Core/Normalise/Convert.idr:328`). That cost is
  identical whether the carrier has three elements or four, and it is paid once.
  Affine is then one row in `admits?/2`.

  Nothing outside this module may pattern-match a grade. Downstream passes go
  through `add/2`, `mul/2`, `admits?/2`, `leq/2` and the predicates, so extending
  the carrier again touches this file, `Serialize`, and the surface — not the
  hundreds of binder sites.

  ## The two operations

  `add/2` sums **usages**: if a variable is used once in one subterm and once in
  another, it was used `1 + 1 = ω` times (over-linear, so unrestricted).

  `mul/2` **scales** a usage context: entering a subterm that is itself used with
  grade `q` multiplies every usage inside it by `q`. `0` annihilates (nothing
  inside an erased position is used at runtime); `1` is the identity.

  ## The usage rule

  Idris checks only linearity, and does it by equality
  (`LinearCheck.idr:274-276`):

      checkUsageOK used r = when (isLinear r && used /= 1) (throw (LinearUsed …))

  `admits?/2` is that rule generalised over the carrier, which is exactly where
  affinity enters: `:affine` admits `0` or `1`.

  ## The preorder

  `leq/2` is *subusaging*: `leq(a, b)` means a value used with grade `a` is
  acceptable where grade `b` was declared. `:unrestricted` is the top. `:linear`
  and `:erased` both fit where `:affine` is demanded; the converse fails, because
  an affine value may be dropped and a linear one may not.

  The carrier is finite, so every law in `Cure.Core.GradeTest` is checked
  exhaustively — those are proofs, not samples.
  """

  @type t :: :erased | :linear | :affine | :unrestricted

  @all [:erased, :linear, :affine, :unrestricted]

  @doc "True when `g` is a grade."
  @spec grade?(term()) :: boolean()
  def grade?(g), do: g in @all

  @doc "The unrestricted grade, `ω`. The default for every unannotated binder."
  @spec unrestricted() :: t()
  def unrestricted, do: :unrestricted

  @doc "The affine grade, `≤1` — used at most once, and may be dropped."
  @spec affine() :: t()
  def affine, do: :affine

  @doc "Every grade, for exhaustive checks."
  @spec all() :: [t()]
  def all, do: @all

  @doc "The additive neutral, `0` (Idris `plusNeutral` / `erased`)."
  @spec zero() :: t()
  def zero, do: :erased

  @doc "The multiplicative neutral, `1` (Idris `timesNeutral` / `linear`)."
  @spec one() :: t()
  def one, do: :linear

  # -- additive monoid: summing usages ----------------------------------------

  @doc """
  Sum two usages. `1 + 1` is `ω`, not `2`: the carrier records *how a binder may
  be used*, and "twice" is already outside every restricted grade.
  """
  @spec add(t(), t()) :: t()
  def add(:erased, b), do: b
  def add(a, :erased), do: a
  def add(:unrestricted, _), do: :unrestricted
  def add(_, :unrestricted), do: :unrestricted
  # Both operands are now `:linear` or `:affine`, so the total may reach 2.
  def add(a, b) when a in [:linear, :affine] and b in [:linear, :affine], do: :unrestricted

  # -- multiplicative monoid: scaling a context -------------------------------

  @doc """
  Scale a usage by a grade. `0` annihilates — nothing inside an erased position
  is used at runtime — and `1` is the identity.

  `affine * affine == affine` is what keeps affinity stable under nesting: an
  at-most-once use of an at-most-once thing is still at-most-once.
  """
  @spec mul(t(), t()) :: t()
  def mul(:erased, _), do: :erased
  def mul(_, :erased), do: :erased
  def mul(:linear, b), do: b
  def mul(a, :linear), do: a
  def mul(:affine, :affine), do: :affine
  def mul(:unrestricted, _), do: :unrestricted
  def mul(_, :unrestricted), do: :unrestricted

  # -- the usage rule ---------------------------------------------------------

  @doc """
  Does `declared` admit exactly `used` occurrences?

  This is the generalisation of Idris's `checkUsageOK` (`LinearCheck.idr:274`),
  and the one place affinity differs from linearity.
  """
  @spec admits?(t(), non_neg_integer()) :: boolean()
  def admits?(:erased, used), do: used == 0
  def admits?(:linear, used), do: used == 1
  def admits?(:affine, used), do: used <= 1
  def admits?(:unrestricted, used) when is_integer(used) and used >= 0, do: true

  # -- preorder: subusaging ---------------------------------------------------

  @doc """
  `leq(a, b)` — a value used with grade `a` is acceptable where `b` was declared.

  Reflexive and transitive, with `:unrestricted` as the top. Note the two
  asymmetries that carry the meaning: `:erased` does not fit where `:linear` is
  demanded (a linear value must actually be used), and `:affine` does not fit
  where `:linear` is demanded (an affine value may be dropped).
  """
  @spec leq(t(), t()) :: boolean()
  def leq(a, a) when a in @all, do: true
  def leq(_, :unrestricted), do: true
  def leq(:erased, :affine), do: true
  def leq(:linear, :affine), do: true
  def leq(a, b) when a in @all and b in @all, do: false

  # -- predicates -------------------------------------------------------------

  @doc "Erasable: no runtime value exists. The `{0, …}` half of erasure."
  @spec erased?(t()) :: boolean()
  def erased?(:erased), do: true
  def erased?(g) when g in @all, do: false

  @doc "The dual of `erased?/1`: a runtime value must exist."
  @spec present?(t()) :: boolean()
  def present?(g), do: not erased?(g)

  @doc """
  True when a usage check must actually count occurrences for this grade.
  `:unrestricted` is the only grade that imposes no obligation.
  """
  @spec restricted?(t()) :: boolean()
  def restricted?(:unrestricted), do: false
  def restricted?(g) when g in @all, do: true
end

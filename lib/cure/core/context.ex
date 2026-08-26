defmodule Cure.Core.Context do
  @moduledoc """
  The kernel's typing context: a telescope of variable **types** (as semantic
  values) for bidirectional `infer`/`check` (design spec §5).

  Variables are de Bruijn-indexed — index 0 is the most-recently-bound, at the
  head. `env/1` produces the matching NbE evaluation environment, mapping each
  bound variable to a fresh neutral at its de Bruijn *level* (the most-recent
  variable, index 0, gets the highest level), so types and bodies can be
  evaluated and read back consistently under the context.
  """

  alias Cure.Core.{Env, Value}

  defstruct types: [], grades: [], env: [], length: 0, signature: nil

  @type t :: %__MODULE__{
          types: [Value.t()],
          grades: [Cure.Core.Grade.t()],
          env: [Value.t()],
          length: non_neg_integer(),
          signature: Env.t() | nil
        }

  @doc "The empty context, carrying an empty global signature."
  @spec empty() :: t()
  def empty, do: %__MODULE__{signature: Env.empty()}

  @doc "The empty context carrying the given global signature (families, defs)."
  @spec empty(Env.t()) :: t()
  def empty(%Env{} = signature), do: %__MODULE__{signature: signature}

  @doc "The global signature (families, constructors, defs) for this context."
  @spec signature(t()) :: Env.t() | nil
  def signature(%__MODULE__{signature: s}), do: s

  @doc """
  Extend the context with one more variable of the given type value.

  The variable is *opaque*: it evaluates to a fresh neutral at its own de Bruijn
  level, exactly as `neutral_env/1` would have produced. This is the binder used
  by `:pi`, `:lam` and `:case` branches.
  """
  @spec extend(t(), Value.t(), Cure.Core.Grade.t()) :: t()
  def extend(%__MODULE__{} = ctx, type_value, grade \\ Cure.Core.Grade.unrestricted()),
    do: %{
      ctx
      | types: [type_value | ctx.types],
        grades: [grade | ctx.grades],
        env: [{:vneutral, {:nvar, ctx.length}} | ctx.env],
        length: ctx.length + 1
    }

  @doc """
  Extend the context with a variable that is *definitionally equal to a value* —
  a `let`-declaration.

  This is the one thing an opaque binder cannot express, and the reason Core has
  a `:let` former at all: the variable occurs once in the term (sharing) yet
  evaluates to its value (ζ-transparency). Mirrors Idris's `Env` of `Binder`s,
  whose `Let` carries its value (`Core/TT/Binder.idr:93-98`) and unfolds on
  lookup (`Core/Normalise/Eval.idr:242-244`), and Lean's value-carrying
  `LocalDecl.ldecl` (`src/Lean/LocalContext.lean:86`).

  `type_value` types the variable; `value` is what it evaluates to. Because the
  variable is never neutral, no inferred type can mention it — which is why the
  NbE formulation needs no re-abstraction step (contrast Lean's fvar-based
  `infer_let`, `src/kernel/type_checker.cpp`, which ends in `mk_pi(fvars, r)`).
  """
  @spec extend_def(t(), Value.t(), Value.t()) :: t()
  def extend_def(%__MODULE__{} = ctx, type_value, value),
    do: %{
      ctx
      | types: [type_value | ctx.types],
        grades: [Cure.Core.Grade.unrestricted() | ctx.grades],
        env: [value | ctx.env],
        length: ctx.length + 1
    }

  @doc "The type value of the variable at de Bruijn index `k` (0 = most recent)."
  @spec lookup(t(), non_neg_integer()) :: Value.t() | nil
  # A negative index is as out-of-range as one past the end, and must fail the same way.
  # `Enum.at/2` counts from the end for a negative index, so `lookup(ctx, -1)` used to return
  # the OLDEST binding's type — and `Kernel.infer/2` then reported `{:var, -1}` as well-typed
  # at a binding it does not name. `Term.term?/1` has always rejected `{:var, -1}`.
  def lookup(%__MODULE__{}, k) when not is_integer(k) or k < 0, do: nil
  def lookup(%__MODULE__{types: ts}, k), do: Enum.at(ts, k)

  @doc "The declared grade of the variable at de Bruijn index `k`."
  @spec grade(t(), non_neg_integer()) :: Cure.Core.Grade.t() | nil
  def grade(%__MODULE__{}, k) when not is_integer(k) or k < 0, do: nil
  def grade(%__MODULE__{grades: grades}, k), do: Enum.at(grades, k)

  @doc "Number of variables in scope."
  @spec length(t()) :: non_neg_integer()
  def length(%__MODULE__{length: n}), do: n

  @doc """
  The NbE environment for this context, indexed by de Bruijn index.

  Each `extend/2` contributes a fresh neutral at its own level; each
  `extend_def/3` contributes the bound value. For a context built only from
  `extend/2` this is exactly `neutral_env(length(ctx))` — the property the rest
  of the kernel relied on when the environment was derived rather than stored.
  """
  @spec env(t()) :: [Value.t()]
  def env(%__MODULE__{env: env}), do: env

  @doc """
  A neutral NbE environment of `n` fresh variables — index 0 bound to level
  `n-1`, down to level 0. The identity environment a readback re-evaluates
  against (`Normalise`'s `id_env`); shared so the "fresh neutral per de Bruijn
  level" frame lives in one place.
  """
  @spec neutral_env(non_neg_integer()) :: [Value.t()]
  def neutral_env(0), do: []
  def neutral_env(n), do: for(level <- (n - 1)..0//-1, do: {:vneutral, {:nvar, level}})
end

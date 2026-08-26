defmodule Cure.Core.Eval do
  @moduledoc """
  Normalization-by-evaluation: evaluate a `Cure.Core.Term` into a
  `Cure.Core.Value` under an environment (design spec §4.5).

  The environment is a `[value]` indexed by de Bruijn index — `var 0` is the
  most-recently-bound variable, at the head of the list. Binders evaluate to
  closures that capture the current environment; β/ι reduction happens eagerly
  via `apply/2` and the projection helpers.

  δ-unfolding of `:global` heads is **gated**: until a global is certified total
  (milestone M7), it evaluates to an opaque neutral `{:nglobal, name}`. `:case`
  (ι on constructors) is added in M4 and `:eq`/`:refl`/`:rewrite` in M6; this
  module covers the Π/λ/Σ/projection fragment.
  """

  # We define a local `apply/2`; keep it from clashing with Kernel.apply/2.
  import Kernel, except: [apply: 2]

  @builtin_ctor_aliases %{
    Z: :"Std.Nat#Z",
    S: :"Std.Nat#S",
    FromNat: :"Std.Int#FromNat",
    NegativeSuccessor: :"Std.Int#NegativeSuccessor",
    First: :"Std.Bounded#First",
    Next: :"Std.Bounded#Next"
  }

  @doc "Evaluate `term` under `env` (a `[value]` indexed by de Bruijn index)."
  @spec eval(Cure.Core.Term.t(), [Cure.Core.Value.t()]) :: Cure.Core.Value.t()
  def eval({:type, level}, _env), do: {:vtype, level}

  # An index past the end of `env` is a RIGID FREE VARIABLE: Core admits open terms, and the
  # neutral it becomes is what `Conv.conv?/5` compares when both sides share the environment.
  # (Caveat worth knowing: `{:nvar, l}` is a de Bruijn LEVEL, and this arm reuses the index as
  # one. That is only coherent while the value is never read back — `Quote.reify/2` would turn
  # it into the negative index `depth - k - 1`. Callers that reify must supply
  # `Context.env/1`, which binds every index in scope.)
  #
  # A NEGATIVE index is not a free variable, it is not a well-formed term at all — `term?/1`
  # rejects `{:var, -1}` — and `Enum.at/2` counts from the end, so it used to return the
  # OLDEST binding's value. Silently evaluating to the wrong binder is the one answer that
  # cannot be right.
  def eval({:var, k}, env) when is_integer(k) and k >= 0 do
    case Enum.at(env, k) do
      nil -> {:vneutral, {:nvar, k}}
      v -> v
    end
  end

  def eval({:var, k}, _env), do: raise("eval: negative de Bruijn index #{inspect(k)}")

  def eval({:pi, g, dom, cod}, env), do: {:vpi, g, eval(dom, env), {:closure, env, cod}}
  def eval({:lam, g, dom, body}, env), do: {:vlam, g, eval(dom, env), {:closure, env, body}}

  # ζ (zeta): a `let` is NOT a value former. Its value is pushed into the
  # environment and the body evaluated under it, so the bound variable evaluates
  # to `val` rather than to a neutral. Faithful to Idris's
  # `Core/Normalise/Eval.idr:124-130`, which does
  # `eval env (mkClosure … val :: locs) scope stk`.
  #
  # Consequence, and the reason `Value`/`Conv`/`Quote` need no clause: a `let`
  # can never survive evaluation, so no normal form ever contains one. The
  # SHARING the node buys lives in the term (and in `Emit`); the TRANSPARENCY
  # lives here. `ty` is not evaluated — it is a typing annotation, already
  # checked by the kernel, and evaluating it would be wasted work.
  # ζ. The grade is a typing annotation; evaluation never consults it.
  def eval({:let, _g, _ty, val, body}, env), do: eval(body, [eval(val, env) | env])
  def eval({:app, f, a}, env), do: apply(eval(f, env), eval(a, env))

  def eval({:data, name, params, indices}, env),
    do: {:vdata, name, Enum.map(params ++ indices, &eval(&1, env))}

  def eval({:ctor, name, args}, env) do
    values = Enum.map(args, &eval(&1, env))

    case {name, values} do
      {first, [_erased_bound]} when first in [:First, :"Std.Bounded#First"] ->
        {:vbounded, 0}

      {next, [_erased_bound, {:vbounded, predecessor}]} when next in [:Next, :"Std.Bounded#Next"] ->
        {:vbounded, predecessor + 1}

      _ ->
        {:vctor, name, values}
    end
  end

  # Primitive Int/Float literals. Arithmetic is builtin-op GLOBALS (K2, spec
  # 2026-07-09): Eval leaves every global neutral; the certified-δ engine
  # (Normalise) folds saturated literal spines via `fold/2` below.
  # NOTE(int-facade): `{:int_type}` no longer arises from surface elaboration
  # (spec 2026-07-18 §3a) but this clause stays so `Eval` remains total on any
  # legacy/deserialized term that still carries the retired primitive node.
  def eval({:int_type}, _env), do: {:vint_type}
  def eval({:int_lit, n}, _env), do: {:vint, n}

  # Compact Nat literal: a machine integer standing for the n-fold `S`-tower over
  # `Z` (Lean kernel Nat / Agda BUILTIN NATURAL). It never materializes the tower;
  # `nat_to_ctor/1` peels one layer on demand at each ι-site.
  def eval({:nat_lit, n}, _env), do: {:vnat, n}
  # Compact `Bounded` literal: a machine integer `k` standing for the k-fold
  # `Next`-tower over `First` (Lean `Fin n` — a compact `Nat` plus a `< n` witness
  # the kernel re-checks). It never materializes the tower; `bounded_to_ctor/1`
  # peels one layer on demand at each ι-site, exactly like `nat_to_ctor/1`.
  def eval({:bounded_lit, n}, _env), do: {:vbounded, n}
  def eval({:float_type}, _env), do: {:vfloat_type}
  def eval({:binary_type}, _env), do: {:vbinary_type}
  def eval({:float_lit, f}, _env), do: {:vfloat, f}

  # BEAM atom base type + literal. An atom is its own canonical value (like an
  # int literal): Eval maps the type node and literal node straight to values.
  def eval({:atom_type}, _env), do: {:vatom_type}
  def eval({:atom_lit, a}, _env), do: {:vatom, a}

  # Opaque until the global is certified total (M7 gates δ here).
  def eval({:global, name}, _env), do: {:vneutral, {:nglobal, name}}

  # A hole is a STUCK computation — an assumable term the elaborator has not yet
  # filled — so it evaluates to a neutral keyed by its unique id (first-class
  # holes, Slice 1). Application of this neutral accumulates a spine via
  # `apply/2` below, so a hole in argument position (`f(?h)`) no longer crashes
  # the evaluator. `id` is a globally-distinct string; two DIFFERENT holes stay
  # non-convertible (`Conv.conv_neutral?` compares ids), which is what keeps a
  # hole from standing definitionally for another.
  def eval({:hole, id}, _env), do: {:vneutral, {:nhole, id}}

  # Inert effect nodes: map each to its value form and evaluate SUBTERMS only —
  # never the effect structure. In particular `bind` evaluates `e` and `k` and
  # wraps them; it does NOT `apply` `k` to anything, so `bind(pure(a), k)` never
  # reduces to `k(a)` (zero monad laws, design §3.2). `k` evaluates to whatever
  # ordinary function value it is (typically a `{:vlam, …}`).
  def eval({:effect_type, t}, env), do: {:veffect_type, eval(t, env)}
  def eval({:effect_pure, a}, env), do: {:veffect_pure, eval(a, env)}
  def eval({:effect_bind, e, k}, env), do: {:veffect_bind, eval(e, env), eval(k, env)}

  # `rewrite e at (x.M) in t` is erased at runtime to `t` (the proof and motive
  # are computationally irrelevant — `rewrite e _ t ⇝ t`, §4.6).

  def eval({:case, scrut, motive, branches}, env) do
    # A compact Nat scrutinee peels ONE layer to `Z`/`S(pred)` and reuses the
    # ctor ι-rule (the tail stays compact, so eliminating a depth-n literal is n
    # steps, never an n-node heap tower); every other value passes through.
    case int_to_ctor_if(nat_to_ctor_if(eval(scrut, env))) do
      {:vctor, cname, args} ->
        case Enum.find(branches, fn {c, _ar, _b} -> constructor_name_matches?(c, cname) end) do
          {_cname, arity, body} ->
            reduce_branch_body(body, env, args, arity)

          nil ->
            raise "ι: no branch for constructor #{inspect(cname)} " <>
                    "(coverage violation / ill-typed case reached eval)"
        end

      # A compact Bounded scrutinee peels ONE layer to `First`/`Next(pred)` and
      # reuses the ι-rule above — the exact analogue of the `{:vnat, _}` arm. The
      # peel is declaration-arity (`[m]` / `[m, pred]`), so the erased index binds
      # its dead de Bruijn slot exactly as a genuine `First`/`Next` value would.
      {:vbounded, _} = b ->
        {:vctor, cname, args} = bounded_to_ctor(b)

        # Same nil-guard as the `:vctor` arm above. Without it a `case` missing the
        # peeled constructor died with an opaque `MatchError` on `nil` instead of
        # naming the coverage violation. Both arms must fail the same, legible way:
        # reaching here at all means an ill-typed term slipped past `check_coverage`.
        case Enum.find(branches, fn {c, _ar, _b} -> constructor_name_matches?(c, cname) end) do
          {_cname, arity, body} ->
            fields = drop_leading_params(args, arity)
            eval(body, Enum.reverse(fields) ++ env)

          nil ->
            raise "ι: no branch for constructor #{inspect(cname)} " <>
                    "(coverage violation / ill-typed case reached eval)"
        end

      {:vneutral, neutral} ->
        motive_closure = {:closure, env, motive}
        branch_closures = Enum.map(branches, fn {c, ar, b} -> {c, ar, {:closure, env, b}} end)
        {:vneutral, {:ncase, neutral, motive_closure, branch_closures}}

      other ->
        raise "ι: non-data scrutinee #{inspect(other)} reached eval (ill-typed case)"
    end
  end

  @doc """
  Apply a function value to an argument value, performing β-reduction.

  A `:vlam` reduces by evaluating its body in the captured environment extended
  with the argument; a neutral function accumulates the argument on its spine.
  """
  @spec apply(Cure.Core.Value.t(), Cure.Core.Value.t()) :: Cure.Core.Value.t()
  def apply({:vlam, _g, _dom, {:closure, env, body}}, varg), do: eval(body, [varg | env])
  def apply({:vneutral, n}, varg), do: {:vneutral, {:napp, n, varg}}

  # Applying an argument to a non-function value is ill-typed (an over-applied
  # constructor or a term that should have been rejected upstream). Raise a
  # descriptive error instead of a cryptic FunctionClauseError.
  def apply(nonfun, _varg),
    do: raise("Eval.apply: #{inspect(nonfun)} is not a function (over-application / ill-typed term)")

  @doc """
  Apply `value` to each of `args` left-to-right — the spine re-application shared
  by motive elimination (`Kernel.apply_motive`) and stuck-eliminator δ-reduction
  (`Normalise`'s `reapply`). β/ι fire per step for a `:vlam`; a neutral head just
  accumulates its arguments.
  """
  @spec apply_spine(Cure.Core.Value.t(), [Cure.Core.Value.t()]) :: Cure.Core.Value.t()
  def apply_spine(value, args), do: Enum.reduce(args, value, fn arg, acc -> apply(acc, arg) end)

  @doc """
  Evaluate a `case`-branch body under its constructor's `arity` fresh binders.
  The fields occupy the innermost de Bruijn slots (last field = index 0), each a
  fresh neutral at level `depth + i`. This is the single owner of the
  branch-opening frame shared by `Conv`, `Quote`, and `Normalise`; callers
  continue at depth `depth + arity`.
  """
  @spec open_branch([Cure.Core.Value.t()], Cure.Core.Term.t(), non_neg_integer(), non_neg_integer()) ::
          Cure.Core.Value.t()
  def open_branch(env, body, arity, depth) do
    fresh = for i <- 0..(arity - 1)//1, do: {:vneutral, {:nvar, depth + i}}
    eval(body, Enum.reverse(fresh) ++ env)
  end

  @doc """
  Instantiate a closure (e.g. a Π/Σ codomain family) at a value: evaluate the
  closure body in its captured environment extended with `value` at index 0.
  """
  @spec apply_closure({:closure, [Cure.Core.Value.t()], Cure.Core.Term.t()}, Cure.Core.Value.t()) ::
          Cure.Core.Value.t()
  def apply_closure({:closure, env, body}, value), do: eval(body, [value | env])

  # The shared ι field-binding contract: bind a constructor's FIELDS (the last
  # `arity` of `cargs`, after dropping any K6 params-on-spine via
  # `drop_leading_params`) as the innermost de Bruijn variables — the last field
  # is index 0, so the body's environment is `reverse(fields) ++ base_env`. This
  # is the SINGLE owner of that invariant, which `eval`'s `:case` and both of
  # `Normalise`'s `ncase` ι-arms must agree on; keeping it here stops the three
  # sites from drifting. Public (`@doc false`) for the Normalise call-sites.
  @doc false
  def reduce_branch_body(body, base_env, cargs, arity) do
    fields = drop_leading_params(cargs, arity)
    missing = max(0, arity - length(fields))

    # Indexed constructors erase implicit index witnesses from their value
    # spine, while the checked branch body retains those grade-zero binders in
    # its de Bruijn frame. Relevance proves that these missing binders cannot be
    # used computationally; their dead slots must still be present so later
    # fields and outer variables retain their checked indices. Emission mirrors
    # this contract with erased names in its lowering context.
    erased_slots =
      for position <- 0..(missing - 1)//1,
          do: {:vneutral, {:nhole, "$erased_case_slot_#{arity}_#{position}"}}

    fields = erased_slots ++ fields
    eval(body, Enum.reverse(fields) ++ base_env)
  end

  # -- fields-only ι ----------------------------------------------------------

  # Fields-only canonicalization: a K6 params-on-spine ctor value carries its
  # family params ahead of its fields; the ι-rule binds ONLY the fields (the
  # branch's `arity`). length(args) == arity is the canonical zero-cost path.
  # Public (`@doc false`) so `Cure.Core.Normalise`'s two ι sites call the SAME
  # function (Step 1.3) — a single audited algorithm, not a duplicated twin.
  @doc false
  def drop_leading_params(args, arity) when length(args) > arity,
    do: Enum.drop(args, length(args) - arity)

  def drop_leading_params(args, _arity), do: args

  # -- compact Nat peeling ----------------------------------------------------

  # Peel one layer of a compact Nat literal into its `Z`/`S` constructor value,
  # leaving the predecessor COMPACT (`{:vnat, n-1}`). This is the single audited
  # literal→constructor mapping (Lean's `toCtorIfLit` / Agda's `matchLitSuc`);
  # every ι-site (`eval`'s `:case`, `Normalise`'s two `ncase` arms) routes a
  # `{:vnat, _}` scrutinee through it so the peel logic exists exactly once.
  # Public (`@doc false`) for the Normalise call-sites — same pattern as
  # `drop_leading_params/2`.
  @doc false
  def nat_to_ctor({:vnat, 0}), do: {:vctor, :Z, []}
  def nat_to_ctor({:vnat, n}) when is_integer(n) and n > 0, do: {:vctor, :S, [{:vnat, n - 1}]}

  # Peel iff the value is a compact Nat; otherwise pass through unchanged. Lets a
  # whnf-forced scrutinee be normalised to constructor form before the shared
  # `{:vctor, cname, cargs}` ι-logic without a separate branch.
  @doc false
  def nat_to_ctor_if({:vnat, _} = nat), do: nat_to_ctor(nat)
  def nat_to_ctor_if(value), do: value

  # -- compact Int peeling ----------------------------------------------------

  # Map a compact Int literal to its FromNat/NegativeSuccessor constructor value.
  # Unlike nat_to_ctor (which peels ONE S layer, leaving a compact predecessor),
  # this is SINGLE-STEP: Int has exactly two outermost constructors, each with a
  # single compact-Nat field. This is the one audited literal→constructor mapping
  # for Int (Lean's Int.ofNat/negSucc, @[extern]-backed). SOUND only because BEAM
  # integers are arbitrary-precision (see Std.Int module doc): the inductive ℤ is
  # unbounded and native bignums never wrap.
  #   FromNat(n)           = n            (n ≥ 0)
  #   NegativeSuccessor(n) = -(n + 1)     (-1, -2, …)
  @doc false
  def int_to_ctor({:vint, n}) when is_integer(n) and n >= 0, do: {:vctor, :FromNat, [{:vnat, n}]}
  def int_to_ctor({:vint, n}) when is_integer(n) and n < 0, do: {:vctor, :NegativeSuccessor, [{:vnat, -n - 1}]}

  @doc false
  def int_to_ctor_if({:vint, _} = int), do: int_to_ctor(int)
  def int_to_ctor_if(value), do: value

  # Compact literal peeling uses the builtin constructor basename (`:S`,
  # `:FromNat`, `:Next`), while source-elaborated branches carry canonical
  # owner-qualified identities. They denote the same constructor.
  @doc false
  def constructor_name_matches?(left, right) do
    left == right or builtin_constructor_alias?(left, right) or builtin_constructor_alias?(right, left)
  end

  defp builtin_constructor_alias?(bare, qualified) do
    Map.get(@builtin_ctor_aliases, bare) == qualified
  end

  # -- compact Bounded peeling ------------------------------------------------

  # Peel one layer of a compact `Bounded` literal into its `First`/`Next`
  # constructor value, leaving the predecessor COMPACT (`{:vbounded, k-1}`). The
  # analogue of `nat_to_ctor/1` (`First`≙`Z`, `Next`≙`S`), but — unlike Nat —
  # `Bounded` is INDEXED: each ctor carries an erased implicit index `{m : Nat}`
  # ahead of its explicit fields (declaration order `[m, pred]`), so the peeled
  # value is declaration-arity, matching both a genuine surface-written value
  # (`eval` maps every ctor arg, §`eval({:ctor,…})`) and the branch arity the
  # elaborator emits (First: 1, Next: 2). The erased index is computationally
  # irrelevant; we fill it with its true value (`First`: m = 0; `Next` over
  # `{:vbounded, k}`: m = k, since `Next : Bounded(m) -> Bounded(S(m))`).
  @doc false
  def bounded_to_ctor({:vbounded, 0}), do: {:vctor, :First, [{:vnat, 0}]}

  def bounded_to_ctor({:vbounded, k}) when is_integer(k) and k > 0,
    do: {:vctor, :Next, [{:vnat, k}, {:vbounded, k - 1}]}

  @doc false
  def bounded_to_ctor_if({:vbounded, _} = b), do: bounded_to_ctor(b)
  def bounded_to_ctor_if(value), do: value

  # -- projection ι -----------------------------------------------------------

  # The audited δ fold table. Public (`@doc false`) so `Cure.Core.Normalise`'s
  # builtin-op compute hook folds through the SAME table (K2, spec 2026-07-09).
  # Returns `{:ok, value} | :stuck`; §G.1 rule 1 = div/rem by literal zero stays
  # `:stuck` (the spine stays neutral, never crashes).
  @doc false
  def fold(:add, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, a + b}}
  def fold(:sub, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, a - b}}
  def fold(:mul, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, a * b}}
  def fold(:div, [{:vint, _}, {:vint, 0}]), do: :stuck
  def fold(:div, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, div(a, b)}}
  def fold(:rem, [{:vint, _}, {:vint, 0}]), do: :stuck
  def fold(:rem, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, rem(a, b)}}

  # Int-only bitwise (BEAM `band`/`bor`/`bxor`/`bsl`/`bsr`/`bnot` BIFs). Shifts
  # are total on arbitrary-precision ints (negative shift shifts the other way),
  # so no `:stuck` guard is needed.
  def fold(:band, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, Bitwise.band(a, b)}}
  def fold(:bor, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, Bitwise.bor(a, b)}}
  def fold(:bxor, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, Bitwise.bxor(a, b)}}
  def fold(:bsl, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, Bitwise.bsl(a, b)}}
  def fold(:bsr, [{:vint, a}, {:vint, b}]), do: {:ok, {:vint, Bitwise.bsr(a, b)}}

  def fold(:add, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, {:vfloat, a + b}}
  def fold(:sub, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, {:vfloat, a - b}}
  def fold(:mul, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, {:vfloat, a * b}}
  # Float division has its own op key `:fdiv` (see `Builtins.@float_binops`): the
  # BEAM instruction is `/`, not the integer `div` that `:div` folds to. Sharing the
  # key made `Emit` lower `x / y` on floats to `erlang:div/2` (badarith at runtime)
  # while THIS fold happily returned the correct quotient — the normaliser and the
  # emitter disagreeing about the same term. Keep the two keys distinct.
  def fold(:fdiv, [{:vfloat, a}, {:vfloat, b}]) when b != 0.0, do: {:ok, {:vfloat, a / b}}

  # Bool-producing folds now yield the `True`/`False` **constructor values** of the
  # canonical Bool inductive (the True/False ctor values). `:True`/`:False` are
  # hardcoded here (fold has no `sig` on its path — a deliberate plumbing decision;
  # the Task-10 antibody enforces agreement with Builtins.@schemas / seed/1).
  def fold(:eq, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a == b)}
  def fold(:eq, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a == b)}
  def fold(:eq, [{:vatom, a}, {:vatom, b}]), do: {:ok, vbool(a == b)}
  def fold(:eq, [{:vbounded, a}, {:vbounded, b}]), do: {:ok, vbool(a == b)}
  def fold(:ne, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a != b)}
  def fold(:ne, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a != b)}
  def fold(:ne, [{:vatom, a}, {:vatom, b}]), do: {:ok, vbool(a != b)}
  def fold(:ne, [{:vbounded, a}, {:vbounded, b}]), do: {:ok, vbool(a != b)}
  def fold(:lt, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a < b)}
  def fold(:lt, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a < b)}
  def fold(:le, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a <= b)}
  def fold(:le, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a <= b)}
  def fold(:gt, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a > b)}
  def fold(:gt, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a > b)}
  def fold(:ge, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a >= b)}
  def fold(:ge, [{:vfloat, a}, {:vfloat, b}]), do: {:ok, vbool(a >= b)}

  def fold(:neg, [{:vint, a}]), do: {:ok, {:vint, -a}}
  def fold(:neg, [{:vfloat, a}]), do: {:ok, {:vfloat, -a}}

  def fold(:bnot, [{:vint, a}]), do: {:ok, {:vint, Bitwise.bnot(a)}}

  # The Boolean connectives (`and`/`or`/`not`) and Bool-operand equality are
  # Std.Bool `case`-defs, never entries in this table. The catch-all is §G.1
  # rule 1's backstop: any op/argument pair with no clause above (zero divisor,
  # non-literal value, Bool ctor operand) is `:stuck` — the builtin-op spine
  # stays neutral, never unsound (K2, spec 2026-07-09).
  def fold(_op, _args), do: :stuck

  defp vbool(true), do: {:vctor, :"Std.Bool#True", []}
  defp vbool(false), do: {:vctor, :"Std.Bool#False", []}
end

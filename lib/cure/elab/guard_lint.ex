defmodule Cure.Elab.GuardLint do
  @moduledoc """
  Untrusted Z3 guard-coverage lint (spec 2026-07-08-guard-coverage-lint).

  Two queries over ELABORATED guard Core terms (always with their typing
  `Context`, because the fragment is Int-only and must see operand types):

    * `prove_exhaustive/2` — is the disjunction of the guards valid? `:proven`
      lets `guard_chain` accept a final guarded arm as the catch-all (its test
      elided; the kernel re-checks the emitted term as always — §2.3a). Every
      failure mode (refuted / unknown / timeout / untranslatable / Z3 absent)
      is `:not_proven`, leaving behavior byte-identical to pre-lint.
    * `shadowed?/3` — is a guard implied by the disjunction of the guards
      before it (its arm dead)? Only ever produces a warning.

  Translation fragment (§2.2, K2): saturated builtin-op comparison SPINES over
  Int-typed operands (vars checked against the Context, `{:int_lit, _}`,
  linear `add/sub/mul` spines), plus literal `True`/`False`. Anything else falls back to an uninterpreted
  Bool constant interned BY TERM — identical untranslatable guards share a
  constant (so shadow detection catches a literal repeat), distinct ones do
  not, and an uninterpreted constant can never make a disjunction valid, so
  exhaustiveness can never lean on one (K13: untranslatable ⇒ not proven).

  Z3 is OUT of the TCB: nothing here influences a kernel judgement (locked
  SMT trust-boundary decision). Warnings ride a process-dictionary list reset
  by `Cure.Elab.Program.elaborate/1` (§2.5) — not an `Env` field.
  """

  alias Cure.Core.{Context, Env}
  alias Cure.SMT.Process, as: Z3

  @warnings_key :cure_guard_lint_warnings
  @timeout 3_000

  # -- Warnings channel (§2.5) -------------------------------------------------

  def reset_warnings, do: Process.put(@warnings_key, [])

  def record_warning(w), do: Process.put(@warnings_key, [w | Process.get(@warnings_key, [])])

  def warnings, do: Process.get(@warnings_key, []) |> Enum.reverse()

  # -- Lint queries -------------------------------------------------------------

  @spec prove_exhaustive([tuple()], Context.t()) :: :proven | :not_proven
  def prove_exhaustive([], _ctx), do: :not_proven

  def prove_exhaustive(guards, ctx) do
    {forms, st} = render_guards(guards, ctx)

    case check_sat("(assert (not " <> disj(forms) <> "))", st) do
      :unsat -> :proven
      _ -> :not_proven
    end
  end

  @spec shadowed?(tuple(), [tuple()], Context.t()) :: boolean()
  def shadowed?(_guard, [], _ctx), do: false

  def shadowed?(guard, prior, ctx) do
    {[g | ps], st} = render_guards([guard | prior], ctx)

    case check_sat("(assert (and " <> g <> " (not " <> disj(ps) <> ")))", st) do
      :unsat -> true
      _ -> false
    end
  end

  # -- Rendering (§2.2) ----------------------------------------------------------

  defp disj([f]), do: f
  defp disj(fs), do: "(or " <> Enum.join(fs, " ") <> ")"

  defp render_guards(guards, ctx) do
    Enum.map_reduce(guards, %{ints: MapSet.new(), atoms: %{}}, fn g, st ->
      case bool_form(g, ctx, st) do
        {:ok, s, st1} ->
          {s, st1}

        :error ->
          case Map.fetch(st.atoms, g) do
            {:ok, name} ->
              {name, st}

            :error ->
              name = "u" <> Integer.to_string(map_size(st.atoms))
              {name, %{st | atoms: Map.put(st.atoms, g, name)}}
          end
      end
    end)
  end

  @cmp %{lt: "<", le: "<=", gt: ">", ge: ">=", eq: "=", ne: "distinct"}

  # Builtin-op global spine (K2, spec 2026-07-09 §1.6): registry-keyed via the
  # def record — a user def named int_add carries no marker and falls to the
  # sound uninterpreted fallback. `Env.builtin_op/2` returns the SAME op key
  # for int_* and float_* twins; int_form's operand-type gate ({:vint_type}
  # via Context.lookup) is what keeps float ops out — a float_* spine's
  # operands fail it → :error → uninterpreted fallback. A1: struct_eq/
  # struct_ne markers are NOT in @cmp, so structural-equality spines ALWAYS
  # fall to the uninterpreted fallback (never-over-prove).
  defp bool_form({:app, {:app, {:global, g}, a}, b}, ctx, st) do
    case Env.builtin_op(Context.signature(ctx), g) do
      op when is_map_key(@cmp, op) ->
        with {:ok, sa, st} <- int_form(a, ctx, st),
             {:ok, sb, st} <- int_form(b, ctx, st) do
          {:ok, "(" <> Map.fetch!(@cmp, op) <> " " <> sa <> " " <> sb <> ")", st}
        else
          _ -> :error
        end

      _ ->
        :error
    end
  end

  defp bool_form({:ctor, :True, []}, _ctx, st), do: {:ok, "true", st}
  defp bool_form({:ctor, :False, []}, _ctx, st), do: {:ok, "false", st}
  defp bool_form(_other, _ctx, _st), do: :error

  defp int_form({:int_lit, n}, _ctx, st), do: {:ok, int_lit(n), st}

  defp int_form({:var, i}, ctx, st) do
    if int_typed?(Context.lookup(ctx, i), Context.signature(ctx)),
      do: {:ok, var_name(i), %{st | ints: MapSet.put(st.ints, i)}},
      else: :error
  end

  # Builtin-op global spine twins of the prim arithmetic clauses (K2 §1.6).
  # Same linearity rule: `mul` needs a literal multiplicand. Registry-keyed;
  # int-only via the operand-type gate (float operands fail int_form's var/lit
  # clauses → :error → the sound uninterpreted fallback).
  defp int_form({:app, {:app, {:global, g}, a}, b}, ctx, st) do
    case Env.builtin_op(Context.signature(ctx), g) do
      :mul ->
        if match?({:int_lit, _}, a) or match?({:int_lit, _}, b),
          do: arith("*", a, b, ctx, st),
          else: :error

      :add ->
        arith("+", a, b, ctx, st)

      :sub ->
        arith("-", a, b, ctx, st)

      _ ->
        :error
    end
  end

  defp int_form(_other, _ctx, _st), do: :error

  # NOTE(int-facade): An `Int`-typed operand. Post-2026-07-18 surface flip, `Int`
  # is the nullary inductive family `{:vdata, int_fid, []}` (the primitive
  # `{:vint_type}` node is retired for value terms); the facade value is still
  # tolerated so a legacy `{:vint_type}`-typed operand (serialization
  # round-trips, old envs) keeps rendering. Any other family (e.g. `Nat`,
  # `Float`) is NOT int → uninterpreted fallback, exactly as the float gate did
  # before.
  defp int_typed?({:vint_type}, _sig), do: true
  defp int_typed?({:vdata, fid, []}, sig), do: fid == Cure.Core.Inductive.builtin(sig, :int)
  defp int_typed?(_ty, _sig), do: false

  defp arith(sym, a, b, ctx, st) do
    with {:ok, sa, st} <- int_form(a, ctx, st),
         {:ok, sb, st} <- int_form(b, ctx, st) do
      {:ok, "(" <> sym <> " " <> sa <> " " <> sb <> ")", st}
    else
      _ -> :error
    end
  end

  defp int_lit(n) when n < 0, do: "(- " <> Integer.to_string(-n) <> ")"
  defp int_lit(n), do: Integer.to_string(n)

  defp var_name(i), do: "v" <> Integer.to_string(i)

  # -- Z3 execution (§2.4: reuse Cure.SMT.Process ONLY) --------------------------

  defp check_sat(assertion, st) do
    decls =
      Enum.map(Enum.sort(MapSet.to_list(st.ints)), &("(declare-const " <> var_name(&1) <> " Int)")) ++
        Enum.map(Enum.sort(Map.values(st.atoms)), &("(declare-const " <> &1 <> " Bool)"))

    query = Enum.join(decls ++ [assertion, "(check-sat)"], "\n")

    if Z3.z3_available?() do
      run_isolated(fn -> Z3.start_link(timeout: @timeout) end, query)
    else
      :unknown
    end
  end

  # `Cure.SMT.Process.start_link` LINKS the solver GenServer to US (the
  # elaborator/test process). A Z3 binary crash/kill is captured as an ordinary
  # `:exit_status` port message inside `Process`'s own `handle_call` and replied
  # as `{:error, _}` — no crash. But a genuine bug INSIDE the `Process` GenServer
  # (an unhandled message, an exception in its own receive loop) terminates that
  # linked process abnormally, and the resulting EXIT SIGNAL is not something any
  # `try/catch` in our code can intercept — with `trap_exit` at its default
  # `false`, an unhandled linked EXIT kills the receiving process outright,
  # bypassing ordinary exception handling entirely (this is a real per-`Cure.SMT.Process`
  # gap that any direct caller of the Z3 GenServer would share and would
  # typically not guard against either — but this lint sits on every
  # `Program.elaborate/1` call, where spec §3 make "must never crash an
  # elaboration" an absolute, so we harden it unconditionally rather than
  # merely matching an ordinary caller). Toggling `trap_exit` for
  # the duration of the query turns any such crash into an ordinary `{:EXIT, pid,
  # reason}` message we explicitly drain and fold into `:unknown`, instead of
  # letting it kill the caller. Residual, accepted trade-off: for the query's
  # brief window (≤ `@timeout`), an UNRELATED linked process crashing also
  # arrives as a mailbox message instead of killing us; we only drain the one
  # tagged with our own `pid`, so an unrelated `{:EXIT, _, _}` is left queued as
  # ordinary (harmless, since this call runs in an ordinary synchronous
  # process, not a `handle_info` loop expecting none) rather than propagating —
  # acceptable given the alternative (Z3 crashing the elaborator) is strictly
  # worse and the window is short.
  defp run_isolated(start_fun, query) do
    prior = Process.flag(:trap_exit, true)

    try do
      case start_fun.() do
        {:ok, pid} ->
          try do
            case Z3.query(pid, query) do
              {:unsat, _} -> :unsat
              {:sat, _} -> :sat
              _ -> :unknown
            end
          catch
            # A dead port / call timeout / trapped linked crash degrades
            # conservatively (§2.3, §3).
            _, _ -> :unknown
          after
            try do
              Z3.stop(pid)
            catch
              _, _ -> :ok
            end

            # Drain the EXIT message `stop/1` (a normal GenServer.stop) or a
            # crash may have queued, so it never leaks into the caller's own
            # mailbox once trap_exit is restored below.
            receive do
              {:EXIT, ^pid, _} -> :ok
            after
              0 -> :ok
            end
          end

        _ ->
          :unknown
      end
    after
      Process.flag(:trap_exit, prior)
    end
  end
end

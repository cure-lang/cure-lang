defmodule Cure.Dev.Trace do
  @compile {:no_warn_undefined, [:cover, :dbg]}
  @moduledoc """
  Runtime tracing helpers for elaboration/kernel debugging — no source edits,
  no leftover state.

  Two recurring debugging questions, two helpers. Each sets up instrumentation,
  runs a thunk, tears everything down, and returns the observations alongside
  the thunk's own result. Because setup/teardown is scoped to the thunk, there
  is never any `File.write!` breadcrumb to add or a print to rip back out.

    * `lines/3` — "which of these lines actually executed?" (via OTP `:cover`).
      Answers e.g. "which of the two `:missing_branch` sites fired for this
      probe?" — read the hit counts.

    * `calls/4` — "this function fired; with what arguments, returning what?"
      (via OTP `:dbg`). Answers e.g. "was `branch_unify` even called with a
      Vector dname, and what scrutinee index did it see?" — read the events.

    * `nf_probe/2` + `stuck_reducible/2` — "was this term the decision saw in
      normal form, or stuck-but-reducible?" (via the kernel normalizer). Answers
      the whole class of "a coverage/conversion/unify decision consumed an
      un-normalized term" bugs: a `check_coverage` that won't discharge a branch
      because the scrutinee index arrived as `plus(S(k), m)` instead of its
      normal form `S(plus(k, m))`. Feed it the `ctx` and the value from the same
      traced `calls/4` event.

  Intended for one-shot probe scripts (`mix run some_probe.exs`), where the VM
  exits when the probe finishes. `lines/3` leaves its target modules
  cover-instrumented for the remainder of the VM session (a fresh `mix run`
  starts clean); do not interleave it with timing-sensitive work in a long-lived
  iex session.

  This module lives outside the trusted core (`lib/cure/core/**`) and never
  participates in elaboration — it only observes.
  """

  @typedoc "One traced call: the argument list and, when it returned, the value."
  @type event :: %{args: [term()], return: term() | :no_return}

  # -- Line coverage ----------------------------------------------------------

  @doc """
  Run `thunk` with `mods` instrumented under `:cover`, returning
  `{thunk_result, hits}` where `hits` is a sorted list of `{module, line,
  weight}` for every line that executed at least once. `weight` is the number of
  covered expressions on that line (≥ 1 when the line ran); it is a "did it run
  and roughly how much" signal, not a precise call count.

  Uses `:cover`'s `:coverage` analysis, which reports whether each *executable
  line* ran — including lines that only build data (e.g. a bare `{:error, ...}`
  tuple). `:calls` analysis is deliberately NOT used: it counts function-call
  invocations per line, so a pure-data line reads as zero even when reached,
  which would produce false negatives for exactly the "did this error site fire?"
  question this helper exists to answer.

  Options:

    * `:lines` — restrict the reported hits to these line numbers (a bare list
      applies to every module; a `%{Module => [lines]}` map filters per module).
      Lines you ask about that never fired are simply absent from `hits`, so the
      presence/absence of a `{mod, line, _}` tuple is itself the answer.

  ## Example

      {_, hits} =
        Cure.Dev.Trace.lines(
          [Cure.Elab.Elaborator],
          fn -> Cure.Elab.Program.elaborate(src) end,
          lines: [2874, 3427]
        )
      # hits == [{Cure.Elab.Elaborator, 3427, 1}]  => the 3427 site fired, 2874 did not
  """
  @spec lines(module() | [module()], (-> result), keyword()) :: {result, [{module(), pos_integer(), pos_integer()}]}
        when result: term()
  def lines(mods, thunk, opts \\ []) when is_function(thunk, 0) do
    mods = List.wrap(mods)
    _ = :cover.start()

    Enum.each(mods, fn m ->
      _ = :cover.compile_beam(m)
    end)

    result = thunk.()

    hits =
      for m <- mods,
          {line, weight} <- analyse_lines(m),
          weight > 0,
          keep_line?(opts[:lines], m, line),
          do: {m, line, weight}

    {result, Enum.sort(hits)}
  end

  defp analyse_lines(mod) do
    case :cover.analyse(mod, :coverage, :line) do
      {:ok, entries} -> for {{^mod, line}, {cov, _not}} <- entries, line > 0, do: {line, cov}
      _ -> []
    end
  end

  defp keep_line?(nil, _mod, _line), do: true
  defp keep_line?(list, _mod, line) when is_list(list), do: line in list

  defp keep_line?(map, mod, line) when is_map(map) do
    case Map.fetch(map, mod) do
      {:ok, lines} -> line in lines
      :error -> true
    end
  end

  # -- Call tracing -----------------------------------------------------------

  @doc """
  Run `thunk` with every call to `mod.fun` traced, returning `{thunk_result,
  events}` where `events` is the ordered list of `%{args:, return:}` maps (one
  per invocation, oldest first).

  Options:

    * `:arity` — trace only this arity (default: all arities).
    * `:where` — predicate over the raw argument list. Calls for which it
      returns false are discarded before formatting or copying their arguments
      into the collector. This is important when a hot function receives large
      contexts and only one indexed family or declaration is relevant.
    * `:match_spec` — an Erlang trace match specification passed directly to
      `:dbg.tpl/4`. Prefer this over `:where` for very hot functions: rejected
      calls never leave the VM tracing engine and therefore cannot overload the
      collector. The default matches every argument list and records returns.
    * `:on_event` — callback invoked as soon as a matching call returns. This is
      useful when the observed thunk terminates the VM on failure and therefore
      cannot return the accumulated event list.
    * `:on_call` — callback invoked as soon as a matching call begins, with the
      formatted argument list. Use this when the call itself never returns
      because compilation exits on the diagnostic being investigated.
    * `:collect` — retain closed events for the returned list (default: true).
      Set false with `:on_event` on extremely hot functions to stream events
      without allowing the collector process to grow without bound.
    * `:format` — a 1-arg function applied to each captured argument and return
      value before storing, e.g. `&Cure.Core.Quote.reify(&1, 0)` to make kernel
      values readable. Default: identity.

  ## Example

      {_, events} =
        Cure.Dev.Trace.calls(Cure.Core.Kernel, :branch_unify,
          fn -> Cure.Elab.Program.elaborate(src) end)
      # events == [%{args: [ctx, dname, cname, ...], return: {:solved, _}}, ...]
      # (empty list => the function was never called during the probe)
  """
  @spec calls(module(), atom(), (-> result), keyword()) :: {result, [event()]} when result: term()
  def calls(mod, fun, thunk, opts \\ []) when is_function(thunk, 0) do
    arity = Keyword.get(opts, :arity, :_)
    fmt = Keyword.get(opts, :format, & &1)
    where = Keyword.get(opts, :where, fn _args -> true end)
    match_spec = Keyword.get(opts, :match_spec, [{:_, [], [{:return_trace}]}])
    on_call = Keyword.get(opts, :on_call, fn _args -> :ok end)
    on_event = Keyword.get(opts, :on_event, fn _event -> :ok end)
    collect? = Keyword.get(opts, :collect, true)

    {:ok, collector} = Agent.start_link(fn -> %{calls: [], by_pid: %{}} end)

    handler = fn msg, acc ->
      handle_trace(collector, fmt, where, on_call, on_event, collect?, msg)
      acc
    end

    _ = :dbg.stop()
    {:ok, _} = :dbg.tracer(:process, {handler, :ok})
    # Canonical compilation elaborates modules in workers created after the
    # probe starts. `:sos` makes those children inherit call tracing; without it
    # a probe around the compiler can silently report no events even though the
    # target function ran in a newly spawned task.
    _ = :dbg.p(:all, [:c, :sos])
    # Match spec `[{:_, [], [{:return_trace}]}]`: match any args, emit return too.
    _ = :dbg.tpl(mod, fun, arity, match_spec)

    result =
      try do
        thunk.()
      after
        _ = :dbg.stop()
      end

    events =
      Agent.get(collector, fn %{calls: c, by_pid: pending} ->
        # Closed calls (oldest first) followed by any that never returned
        # (e.g. the probe raised mid-call) — those keep `return: :no_return`.
        Enum.reverse(c) ++ (pending |> Map.values() |> List.flatten() |> Enum.reverse())
      end)

    Agent.stop(collector)
    {result, events}
  end

  # A `:call` opens a pending event for that pid; the matching `:return_from`
  # closes it. Interleaving across pids is handled by keying pending calls on pid.
  defp handle_trace(collector, fmt, where, on_call, _on_event, _collect?, {:trace, pid, :call, {_m, _f, args}}) do
    args = List.wrap(args)

    Agent.update(collector, fn state ->
      event =
        if where.(args) do
          formatted = Enum.map(args, fmt)
          on_call.(formatted)
          %{args: formatted, return: :no_return}
        else
          :discard
        end

      %{state | by_pid: Map.update(state.by_pid, pid, [event], &[event | &1])}
    end)
  end

  defp handle_trace(collector, fmt, _where, _on_call, on_event, collect?, {:trace, pid, :return_from, _mfa, retval}) do
    Agent.update(collector, fn state ->
      case Map.get(state.by_pid, pid, []) do
        [:discard | rest] ->
          %{state | by_pid: Map.put(state.by_pid, pid, rest)}

        [pending | rest] ->
          closed = %{pending | return: fmt.(retval)}
          on_event.(closed)
          calls = if collect?, do: [closed | state.calls], else: state.calls
          %{state | calls: calls, by_pid: Map.put(state.by_pid, pid, rest)}

        [] ->
          state
      end
    end)
  end

  defp handle_trace(collector, _fmt, _where, _on_call, _on_event, _collect?, {:trace, _pid, _other, _}),
    do: collector |> ignore()

  defp handle_trace(collector, _fmt, _where, _on_call, _on_event, _collect?, _), do: collector |> ignore()

  defp ignore(_), do: :ok

  # -- Normal-form lens -------------------------------------------------------

  @typedoc """
  A normal-form report for one term/value:
    * `:reified`  — the term as a decision would see it (a value is reified first)
    * `:nf`       — its normal form, or `:fuel_exhausted`
    * `:reduces?` — `true` when `nf` differs from `reified`; i.e. the input was
      stuck-but-reducible. A `true` here on a term that a coverage/conversion/
      unify decision *consumed* is the fingerprint of a "decided on an
      un-normalized term" bug.
  """
  @type nf_report :: %{reified: term(), nf: term() | :fuel_exhausted, reduces?: boolean()}

  @doc """
  Report whether `value_or_term` (as seen in `ctx`) is in normal form or is
  stuck-but-reducible.

  Pass the `ctx` and the value straight from a `calls/4` event — e.g. the
  `scrut_indices` entry from a traced `Kernel.check_coverage` call. Kernel
  *values* (tagged `:vneutral`, `:vctor`, `:vdata`, …) are reified before
  normalizing; pass `as: :term` if you already hold a Core term.

  The tool's own correctness is two-sided: an index that a decision rejected
  should report `reduces?: true`, while the same family's already-normal index
  at a sibling call site reports `reduces?: false`.
  """
  @spec nf_probe(term(), term(), keyword()) :: nf_report()
  def nf_probe(ctx, value_or_term, opts \\ []) do
    depth = Cure.Core.Context.length(ctx)
    sig = Cure.Core.Context.signature(ctx)

    reified =
      case Keyword.get(opts, :as, :value) do
        :term -> value_or_term
        :value -> Cure.Core.Quote.reify(value_or_term, depth, sig)
      end

    nf = Cure.Core.Normalise.nf(ctx, reified)

    %{reified: reified, nf: nf, reduces?: nf != :fuel_exhausted and nf != reified}
  end

  @doc """
  Filter `values` (each interpreted in `ctx`) to those that are
  stuck-but-reducible, returning `{value, nf_report}` pairs. A non-empty result
  for terms a decision consumed pinpoints the un-normalized inputs.
  """
  @spec stuck_reducible(term(), [term()], keyword()) :: [{term(), nf_report()}]
  def stuck_reducible(ctx, values, opts \\ []) do
    for v <- values, r = nf_probe(ctx, v, opts), r.reduces?, do: {v, r}
  end
end

# Example programs are maintained separately from the 0.34 compiler suite.
# Tests tagged `:examples` are opt-in via `mix test --include examples`.
ExUnit.configure(exclude: [examples: true])

# Sweep once, load exactly the verified generation, then make that resident
# generation sticky for the duration of the suite. The manifest is the sole
# completeness authority; test startup does not rescan source declarations or
# infer freshness from filenames.
(fn ->
   output_dir =
     Application.get_env(:cure, :stdlib_beam_dir) ||
       Cure.Stdlib.Paths.build_beam_dir(:test, System.pid())

   Application.put_env(:cure, :stdlib_beam_dir, output_dir)

   artifact_root =
     case Application.get_env(:cure, :stdlib_compiled_in_vm) do
       ^output_dir ->
         IO.puts("test_helper: using stdlib generation verified by compile alias")
         {:ok, _set} = Cure.Compiler.Artifacts.open_verified_set(output_dir, verification: :full)
         output_dir

       _other ->
         IO.puts("test_helper: sweeping Cure stdlib artifacts")

         {:ok, result} =
           Cure.Stdlib.Packages.compile(
             Path.wildcard("lib/std/*.cure"),
             output_dir,
             compile_opts: [emit_events: false]
           )

         result.artifact_root
     end

   :ok = Cure.Compiler.Artifacts.load_verified_set(artifact_root)
   {:ok, artifact_set} = Cure.Compiler.Artifacts.open_verified_set(artifact_root)

   loaded =
     artifact_set.modules
     |> Map.values()
     |> Enum.flat_map(&Map.fetch!(&1, :artifacts))
     |> Enum.map(fn artifact ->
       module = String.to_atom(artifact.module)
       {:file, _} = :code.is_loaded(module)
       true = :code.stick_mod(module)
       module
     end)
     |> MapSet.new()

   if MapSet.size(loaded) == 0 do
     raise "test_helper: verified stdlib artifact manifest is empty"
   end

   IO.puts("test_helper: stuck #{MapSet.size(loaded)} canonical stdlib modules")
 end).()

# A tail-friendly failure formatter.
#
# ExUnit prints each failure inline, in the moment it happens — buried among
# thousands of progress dots, compile warnings, and Antigen breadcrumbs. On a
# ~25-minute suite piped through `tail`, the "Result: N failed" summary survives
# but the actual failure blocks scroll away, so `tail` of the log shows THAT
# something failed but never WHAT. This formatter captures every failure's fully
# formatted block (assertion, diff, stacktrace — exactly what the CLI prints) and
# the `after_suite` hook below re-prints them as the final lines of output. A
# `tail` of a piped run then always ends with precisely what failed and why.
:ets.new(:cure_failure_tail, [:named_table, :public, :ordered_set])

defmodule Cure.FailureTailFormatter do
  @moduledoc false
  use GenServer

  @impl true
  def init(opts), do: {:ok, %{width: Keyword.get(opts, :width, 80)}}

  @impl true
  def handle_cast({:test_finished, %ExUnit.Test{state: {:failed, failures}} = test}, state) do
    counter = :ets.info(:cure_failure_tail, :size) + 1
    text = ExUnit.Formatter.format_test_failure(test, failures, counter, state.width, &plain/2)
    :ets.insert(:cure_failure_tail, {counter, text})
    {:noreply, state}
  end

  # setup_all / module-level failures arrive here, not as individual tests.
  def handle_cast({:module_finished, %ExUnit.TestModule{state: {:failed, failures}} = mod}, state) do
    counter = :ets.info(:cure_failure_tail, :size) + 1
    text = ExUnit.Formatter.format_test_all_failure(mod, failures, counter, state.width, &plain/2)
    :ets.insert(:cure_failure_tail, {counter, text})
    {:noreply, state}
  end

  def handle_cast(_event, state), do: {:noreply, state}

  # This text lands in a piped log, not a TTY — emit it without ANSI coloring.
  defp plain(_kind, content), do: content
end

# A quiet CLI progress formatter — replaces `ExUnit.CLIFormatter`.
#
# The stock formatter prints one green `.` per passing test. On a ~4600-test
# run that is thousands of dots streaming past, burying compile warnings and
# Antigen breadcrumbs and forcing a `tail` just to find the summary. This
# formatter drops the per-test dots entirely. Instead:
#
#   * On an interactive terminal it shows a SINGLE in-place counter
#     (`1234 tests, 0 failures`) that rewrites its own line — live feedback
#     without the scroll.
#   * When output is piped (CI, `| tail`) it stays silent during the run, so
#     the log is just the end-of-run summary followed by the re-printed failure
#     blocks from `Cure.FailureTailFormatter`.
#   * At suite end it prints the standard `Finished in …` / `N tests, M failures`
#     / `Randomized with seed …` block, byte-compatible with what tooling that
#     scrapes ExUnit output (CI, the harness "Result:" line) expects.
#
# Set `CURE_TEST_DOTS=1` to fall back to the stock dot formatter — e.g. when you
# want `--trace`, which only `ExUnit.CLIFormatter` honours.
defmodule Cure.SummaryFormatter do
  @moduledoc false
  use GenServer

  @impl true
  def init(_opts) do
    {:ok, %{seed: nil, tests: 0, failures: 0, excluded: 0, skipped: 0, invalid: 0}}
  end

  @impl true
  def handle_cast({:suite_started, opts}, state) do
    print_filters(opts)
    {:noreply, %{state | seed: opts[:seed]}}
  end

  def handle_cast({:test_finished, %ExUnit.Test{state: test_state}}, state) do
    state = tally(state, test_state)
    progress(state)
    {:noreply, state}
  end

  def handle_cast({:suite_finished, times_us}, state) do
    print_summary(state, times_us)
    {:noreply, state}
  end

  def handle_cast(_event, state), do: {:noreply, state}

  # Excluded tests are filtered out before running: reported separately and NOT
  # part of the "N tests" total, mirroring ExUnit's own accounting. Failed,
  # skipped and invalid tests all count toward the total.
  defp tally(state, {:excluded, _}), do: %{state | excluded: state.excluded + 1}

  defp tally(state, {:failed, _}),
    do: %{state | tests: state.tests + 1, failures: state.failures + 1}

  defp tally(state, {:skipped, _}),
    do: %{state | tests: state.tests + 1, skipped: state.skipped + 1}

  defp tally(state, {:invalid, _}),
    do: %{state | tests: state.tests + 1, invalid: state.invalid + 1}

  defp tally(state, _passed), do: %{state | tests: state.tests + 1}

  # In-place counter — only on an interactive terminal. When output is piped
  # (`IO.ANSI.enabled?/0` is false) stay silent so the log holds only the
  # summary and the re-printed failures.
  defp progress(state) do
    if IO.ANSI.enabled?() do
      # Trailing space so anything a test writes to stdout lands separated from
      # the counter rather than butted up against "failures".
      IO.write([?\r, IO.ANSI.clear_line(), "#{state.tests} tests, #{state.failures} failures "])
    end
  end

  defp print_filters(opts) do
    for type <- [:exclude, :include], (filters = opts[type] || []) != [] do
      IO.puts(ExUnit.Formatter.format_filters(filters, type))
    end
  end

  defp print_summary(state, times_us) do
    # Erase the in-place counter before the summary lands on its own line.
    if IO.ANSI.enabled?(), do: IO.write([?\r, IO.ANSI.clear_line()])

    summary =
      [pluralize(state.tests, "test"), pluralize(state.failures, "failure")]
      |> maybe_add(state.invalid, "invalid")
      |> maybe_add(state.skipped, "skipped")
      |> maybe_add(state.excluded, "excluded")
      |> Enum.join(", ")

    IO.puts("\n" <> ExUnit.Formatter.format_times(times_us))
    IO.puts(colorize(summary, state))
    if state.seed, do: IO.puts("\nRandomized with seed #{state.seed}")
  end

  defp maybe_add(parts, 0, _label), do: parts
  defp maybe_add(parts, n, label), do: parts ++ ["#{n} #{label}"]

  # ExUnit's own pluralization: "1 test" but "0 tests"/"3 tests".
  defp pluralize(1, "test"), do: "1 test"
  defp pluralize(n, "test"), do: "#{n} tests"
  defp pluralize(1, "failure"), do: "1 failure"
  defp pluralize(n, "failure"), do: "#{n} failures"

  # Green when clean, red on failures/invalid, yellow when only skipped/excluded.
  # `IO.ANSI.format/1` strips the codes automatically when ANSI is disabled.
  defp colorize(text, state) do
    color =
      cond do
        state.failures > 0 or state.invalid > 0 -> :red
        state.skipped > 0 or state.excluded > 0 -> :yellow
        true -> :green
      end

    IO.ANSI.format([color, text]) |> IO.iodata_to_binary()
  end
end

# `:slow` marks tests that compile the whole 81-module stdlib to assert something
# narrower than a full stdlib compile. They are excluded from the default run
# because they cost ~43s of a ~156s suite, which is a tax on every local edit.
#
# They are NOT redundant, so they still run everywhere it matters: CI passes
# `--include slow` (see `.github/workflows/ci.yml`). Run them locally with
# `mix test --include slow`. Tag a test `:slow` only when it is genuinely
# stdlib-scale — not merely to quiet a test that has become slow by accident.
# `Cure.SummaryFormatter` replaces the stock dot formatter to kill the stream of
# per-test green dots (see its @moduledoc). `CURE_TEST_DOTS=1` restores
# `ExUnit.CLIFormatter` for the cases that need it (notably `--trace`).
progress_formatter =
  if System.get_env("CURE_TEST_DOTS") in ["1", "true"],
    do: ExUnit.CLIFormatter,
    else: Cure.SummaryFormatter

ExUnit.start(
  exclude: [:slow],
  formatters: [progress_formatter, Cure.FailureTailFormatter]
)

# Antigen deliberately injects "immune response" violations (test scaffolding
# exercising the detection machinery). Rather than flood stdout with one calm
# breadcrumb per occurrence — which buries a genuine `ANTIGEN INFECTION` — the
# Runner tallies them; report the total once, after the suite.
ExUnit.after_suite(fn _result ->
  case Antigen.Report.immune_response_count() do
    0 -> :ok
    n -> IO.puts("\n#{n} immune responses successfully triggered (expected, deliberately injected).")
  end

  # Shape-coverage summary: any manifest assay whose declared cells were not all
  # produced this run is surfaced here (see Antigen.CoverManifest.report/0). Silent
  # when the coverage-manifest gate did not run this invocation (nothing stashed).
  case Antigen.CoverManifest.report() do
    nil -> :ok
    line -> IO.puts("\n" <> line)
  end

  # Last of all: re-print every failure block, so a `tail` of the piped run
  # ends with exactly what failed and why (see Cure.FailureTailFormatter above).
  case :ets.tab2list(:cure_failure_tail) do
    [] ->
      :ok

    entries ->
      bar = String.duplicate("=", 72)
      IO.puts("\n" <> bar)
      IO.puts("FAILURES (#{length(entries)}) — re-printed below so a tail of the log catches them:")
      IO.puts(bar)

      entries
      |> Enum.sort_by(&elem(&1, 0))
      |> Enum.each(fn {_counter, text} -> IO.puts(text) end)
  end
end)

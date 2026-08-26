defmodule Mix.Tasks.Cure.Rewrite do
  @shortdoc "Rewrite legacy `if`/`elif` constructs to `pickup`"

  @moduledoc """
  > #### Deprecated {: .warning}
  >
  > This single-rule task predates the general migration facility. Prefer
  > `cure migrate`, which runs the whole rule registry (including this
  > if/elif→pickup rule), refuses to touch a dirty or untracked tree, and
  > reprints canonically. `mix cure.rewrite` is retained only as a
  > focused, git-guard-free way to apply the one pickup rule, and now
  > delegates to the same `Cure.Migrate` engine.

  AST-driven rewriter that migrates the legacy `if`/`elif` construct
  to the v1.0.0 branching primitive `pickup` defined in
  `docs/PICKUP.md`. The rewrite is purely syntactic: every
  `{:conditional, _, _}` chain whose terminal `else` branch is
  populated is replaced with the equivalent `{:pickup, _, _}` block;
  conditionals that lack an `else` branch are left untouched so the
  rewritten program stays total (PICKUP §5.2).

  ## Modes

  By default, files are rewritten in place. Use `--check` to print
  which files would change without touching the disk (CI-friendly,
  exits non-zero when any file has pending rewrites). Use `--print`
  to dump the rewritten source to stdout.

  ## Usage

      mix cure.rewrite path/to/file.cure
      mix cure.rewrite priv/std/list.cure examples/factorial.cure
      mix cure.rewrite --check priv/std/*.cure
      mix cure.rewrite --print path/to/file.cure

  When no paths are given, the task scans `lib/std/**/*.cure` and
  `examples/**/*.cure` -- the canonical Cure source corpus. Built
  copies under `priv/std/` are deliberately skipped: they are
  regenerated from `lib/std/` on every compile.

  ## Companion specs

    * `docs/PICKUP.md` §17 -- migration guidance.
    * `docs/MATCH.md` §10 -- companion construct.

  ## Output

  The rewritten source is rendered with `Cure.Compiler.Printer`,
  whose canonical block form for `pickup` and `match` follows the
  formatter rules in PICKUP §8 and MATCH §9. Round-trip is
  preserved up to position metadata.

  ## Caveats

  Cure's layout-sensitive parser disables `:indent`/`:dedent`
  emission inside parenthesised contexts, so a multi-line `pickup`
  or `match` block cannot live inside a function-call argument
  list. The rewriter does not currently detect that context, so a
  conditional embedded as a call argument may be rewritten into a
  block that fails to re-parse. Run `--check` first; when in doubt,
  rewrite a single file at a time and recompile.
  """

  use Mix.Task

  alias Cure.Diagnostic.Sink

  alias Cure.Compiler.{Lexer, Parser, Printer}

  @impl Mix.Task
  def run(args) do
    Application.ensure_all_started(:cure)

    {opts, paths, invalid} =
      OptionParser.parse(args,
        strict: [check: :boolean, print: :boolean, write: :boolean],
        aliases: [c: :check, p: :print, w: :write]
      )

    if invalid != [] do
      usage_error("Invalid options for mix cure.rewrite: #{inspect(invalid)}")
    end

    files = expand_paths(paths)

    if files == [] do
      Mix.Shell.IO.info("No `.cure` files found to rewrite.")
    else
      initial_stats = %{rewritten: 0, unchanged: 0, errored: 0, previewed: 0}

      stats =
        Enum.reduce(files, initial_stats, fn file, acc ->
          process_file(file, opts, acc)
        end)

      summary(stats, opts)
    end
  end

  # ── Path Expansion ─────────────────────────────────────────────────────

  defp expand_paths([]) do
    (Path.wildcard("lib/std/**/*.cure") ++ Path.wildcard("examples/**/*.cure"))
    |> Enum.reject(&build_artifact?/1)
  end

  defp expand_paths(paths) do
    Enum.flat_map(paths, fn path ->
      cond do
        File.dir?(path) -> Path.wildcard(Path.join(path, "**/*.cure"))
        String.contains?(path, "*") -> Path.wildcard(path)
        true -> [path]
      end
    end)
    |> Enum.reject(&build_artifact?/1)
  end

  # Files inside `_build/`, `deps/`, or other vendored snapshots are
  # build artefacts that get regenerated on every compile; rewriting
  # them would be a no-op at best and would race with `mix compile` at
  # worst. The exclusion list mirrors the standard Elixir convention.
  defp build_artifact?(path) do
    parts = Path.split(path)
    Enum.any?(parts, &(&1 in ["_build", "deps", "node_modules", ".elixir_ls"]))
  end

  # ── File Processing ────────────────────────────────────────────────────

  defp process_file(file, opts, stats) do
    case File.read(file) do
      {:ok, source} ->
        rewrite_one(file, source, opts, stats)

      {:error, reason} ->
        Mix.shell().error(render_host_diagnostic({:file_read_error, file, reason}, file))
        Map.update!(stats, :errored, &(&1 + 1))
    end
  end

  defp rewrite_one(file, source, opts, stats) do
    with {:ok, tokens} <- Lexer.tokenize(source, file: file, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, file: file, emit_events: false) do
      new_ast = rewrite(ast)

      cond do
        new_ast == ast ->
          if Keyword.get(opts, :verbose, false), do: Mix.Shell.IO.info("  unchanged: #{file}")
          Map.update!(stats, :unchanged, &(&1 + 1))

        Keyword.get(opts, :check, false) ->
          Mix.Shell.IO.info("  would rewrite: #{file}")
          Map.update!(stats, :rewritten, &(&1 + 1))

        Keyword.get(opts, :print, false) ->
          Mix.Shell.IO.info("# --- #{file} ---")
          Mix.Shell.IO.info(render(new_ast))
          Map.update!(stats, :previewed, &(&1 + 1))

        true ->
          rendered = render(new_ast)
          File.write!(file, rendered)
          Mix.Shell.IO.info("  rewrote: #{file}")
          Map.update!(stats, :rewritten, &(&1 + 1))
      end
    else
      {:error, reason} ->
        Mix.shell().error(render_host_diagnostic(reason, file, source))

        Map.update!(stats, :errored, &(&1 + 1))
    end
  end

  defp render(ast) do
    rendered = Printer.quoted_to_string(ast)
    if String.ends_with?(rendered, "\n"), do: rendered, else: rendered <> "\n"
  end

  defp render_host_diagnostic(reason, file, source \\ nil) do
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, file, source)

    Sink.new(format: :plain, color: :auto, width: 80, registry: registry)
    |> Sink.render(diagnostic)
  end

  defp usage_error(message) do
    diagnostic = Cure.Diagnostic.Operational.usage(message)

    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
    |> Mix.shell().error()

    exit({:shutdown, 1})
  end

  defp summary(%{rewritten: r, unchanged: u, errored: e, previewed: p}, opts) do
    cond do
      Keyword.get(opts, :check, false) ->
        Mix.Shell.IO.info("\n#{r} file(s) need rewriting, #{u} clean, #{e} errored.")
        if r > 0, do: exit({:shutdown, 1})

      Keyword.get(opts, :print, false) ->
        Mix.Shell.IO.info("\n#{p} file(s) previewed, #{u} unchanged, #{e} errored.")

      true ->
        Mix.Shell.IO.info("\n#{r} file(s) rewritten, #{u} unchanged, #{e} errored.")
    end
  end

  # ── AST Rewrite ────────────────────────────────────────────────────────
  #
  # The if/elif→pickup transform now lives in the shared migration registry
  # (`Cure.Migrate.Rules.IfElifToPickup`), so this task and `cure migrate`
  # rewrite through exactly the same, verify-by-reparse-equivalence code
  # path. `rewrite/1` is a thin adapter that runs that one rule over `ast`.

  @doc """
  Rewrite every migratable `{:conditional, _, _}` subtree of `ast` into a
  `{:pickup, _, _}` block, by running the shared `IfElifToPickup` migration
  rule. Conditionals without a real `else` branch, or whose rewrite would not
  re-parse to the same shape (e.g. a conditional embedded in a call-argument
  list), are left untouched by that rule so the program stays parseable.

  Delegates to `Cure.Migrate.run/2`; the warnings it returns are discarded
  here because this task's own reporting (`--check`/`--print`/summary) is
  file-oriented, not warning-oriented.
  """
  @spec rewrite(term()) :: term()
  def rewrite(ast) do
    {new_ast, _warnings} =
      Cure.Migrate.run(ast,
        file: "cure.rewrite",
        rules: [Cure.Migrate.Rules.IfElifToPickup.rule()]
      )

    new_ast
  end
end

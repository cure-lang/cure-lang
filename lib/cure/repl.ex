defmodule Cure.REPL do
  @moduledoc """
  Interactive REPL for Cure.

  A readline-grade read-eval-print loop:

  * Arrow keys move the cursor (left/right) and step through history
    (up/down), `Ctrl+R` opens incremental reverse-i-search, and Emacs
    shortcuts (`Ctrl+A`, `Ctrl+E`, `Ctrl+W`, `Ctrl+K`, ...) plus a
    minimal Vi mode (`:mode vi`) are supported.
  * Input is syntax-highlighted live via `Makeup.Lexers.CureLexer` +
    `Marcli.Formatter`.
  * Meta-commands are prefixed with `:`. See `:help`.
  * Multi-line input is detected automatically: a line ending with
    a continuation token (`do`, `->`, `=`, `|`, `then`, `else`,
    `,`, `(`), an unbalanced bracket, an open block-opener
    (`match`, `pickup`, `case`, `try`, `fn`, ...), or a buffer that
    parses with an EOF-rooted error keeps the prompt in
    continuation mode. Press `Alt+Enter` (or `Shift+Enter` /
    `Ctrl+Enter` on terminals that send CSI-u modifier sequences)
    to force-continue regardless of the heuristic, and submit the
    accumulated buffer with a blank line or `;;`.
  * When stdin is not a tty (CI, pipes, etc.) the REPL falls back to
    the legacy `IO.gets` loop, so automation continues to work.

  ## History
  Persisted to `~/.cure_history` (configurable). Entries are deduped
  against the immediately preceding line and capped at 10,000.

  ## Configuration

  * `:history_path` -- override the history file. Pass `nil` to disable
    persistence entirely (useful when the REPL is embedded in an
    ephemeral host such as the Yeesh browser terminal).
  * `:raw` -- force raw mode on or off.
  * `:theme` -- one of `:dark`, `:light`, `:mono`; defaults to `:dark`
    and automatically drops to `:mono` when `NO_COLOR` is set or stdout
    is not a tty.
  * `:mode` -- initial editing mode (`:emacs` or `:vi`).
  * `:error_device` -- IO device used for diagnostic output. Defaults
    to `:stderr`; set to `:stdio` when the REPL is hosted behind a
    custom group leader (e.g. `Yeesh.IOServer`) so compiler errors
    reach the embedder.
  """

  alias Cure.Compiler.Printer
  alias Cure.Diagnostic.{Sink, Operational}
  alias Cure.REPL.{Config, Docs, History, LineEditor, Markdown, Render, Search, Session, Snap, Terminal, Theme}
  alias Cure.Stdlib.Preload

  defstruct n: 1,
            loaded: [],
            uses: [],
            defs: [],
            holes: [],
            editor: nil,
            history: nil,
            history_path: nil,
            input_buffer: [],
            theme: nil,
            mode: :emacs,
            color: true,
            error_device: :stderr,
            stdlib_kind: :none,
            running: true

  @type t :: %__MODULE__{}

  @doc "Start the REPL."
  @spec start(keyword()) :: :ok
  def start(opts \\ []) do
    history_path =
      if Keyword.has_key?(opts, :history_path) do
        Keyword.get(opts, :history_path)
      else
        default_history_path()
      end

    theme = resolve_theme(opts)
    mode = resolve_mode(opts)
    error_device = resolve_error_device(opts)

    # Two independent knobs read from `.cure.repl.toml` (or caller opts):
    #
    #   * `:preload` -- which stdlib BEAMs to load into the VM.
    #     Defaults to `:all` so every Std.* module is callable out of
    #     the box. Override via `[stdlib] preload` in `.cure.repl.toml`
    #     or the `:preload` option passed to `Cure.REPL.start/1`.
    #
    #   * `:stdlib` -- which stdlib modules to auto-import (injected as
    #     `use Std.X` in every REPL expression). Defaults to `:none`
    #     (explicit-over-implicit). Override via `[stdlib] imports` in
    #     `.cure.repl.toml` or the `:stdlib` option passed to
    #     `Cure.REPL.start/1`.
    config = Config.load()
    preload_kind = Keyword.get(opts, :preload, config.preload)
    stdlib_kind = Keyword.get(opts, :stdlib, config.imports)

    # Load the compiled Cure stdlib BEAMs into the VM. By default this
    # loads all of them (preload_kind: :all), making Std.* callable from
    # any expression. The helper is a no-op when the bundled BEAMs and
    # sources are both absent (e.g. a partial escript build).
    #
    # A project's `[compiler] stdlib_path` in Cure.toml (falling back to
    # `$CURE_LIB`) is threaded through as `:stdlib_ebin`, mirroring the CLI
    # (`cure compile` / `cure run`). Without this, loading a file that
    # `use`s a stdlib module raised `:missing_stdlib_module` whenever the
    # path was configured in Cure.toml but not also exported as `$CURE_LIB`.
    _ = Preload.preload(__stdlib_preload_opts__(examples: false, kind: preload_kind))

    # If any requested stdlib module is still not loaded after the
    # preload, surface a diagnostic so the user understands why a
    # `Std.X.y` call is about to raise `:undef`. Silent failures here
    # used to be the primary symptom of the production REPL being
    # shipped without `priv/ebin/`.
    missing_preloads = missing_stdlib_modules(preload_kind)

    state = %__MODULE__{
      history: History.load(history_path),
      history_path: history_path,
      editor: LineEditor.new(mode: mode),
      theme: theme,
      mode: mode,
      color: theme.name != :mono,
      error_device: error_device,
      stdlib_kind: stdlib_kind,
      uses: Docs.default_uses(stdlib_kind)
    }

    cond do
      Keyword.get(opts, :raw, :auto) == false ->
        banner(state)
        maybe_preload_warning(state, missing_preloads)
        legacy_loop(state)

      Terminal.tty?() ->
        with_quieted_logger(fn ->
          case Terminal.enter_raw() do
            {:ok, saved} ->
              try do
                banner(state)
                maybe_preload_warning(state, missing_preloads)
                raw_loop(state)
              after
                Terminal.restore(saved)
              end

              :ok

            {:error, reason} ->
              banner(state)
              maybe_preload_warning(state, missing_preloads)
              raw_mode_warning(state, reason)
              legacy_loop(state)
          end
        end)

      true ->
        banner(state)
        maybe_preload_warning(state, missing_preloads)
        legacy_loop(state)
    end
  end

  # Return the list of stdlib modules that were requested by the
  # preload kind but are not currently loadable. Empty list means the
  # user will not run into `:undef` for a qualified stdlib call in
  # this session.
  defp missing_stdlib_modules(:none), do: []

  defp missing_stdlib_modules(kind) do
    Enum.reject(Preload.stdlib_modules(kind), fn module ->
      match?({:file, _}, :code.is_loaded(module))
    end)
  end

  @doc false
  # Build the option list for `Cure.Stdlib.Preload.preload/1`, injecting
  # `:stdlib_ebin` from the project's `[compiler] stdlib_path` (Cure.toml)
  # or, failing that, `$CURE_LIB`. When neither is configured the option is
  # omitted so `Cure.Stdlib.Paths` falls back to its default candidate
  # chain (bundled `priv/ebin`, `$CURE_HOME`, legacy `_build/cure/ebin`).
  #
  # `project_dir` defaults to the current working directory -- where the
  # REPL is launched and where its Cure.toml lives. Exposed for tests.
  @spec __stdlib_preload_opts__(keyword(), String.t()) :: keyword()
  def __stdlib_preload_opts__(base_opts, project_dir \\ ".") do
    case resolve_stdlib_ebin(project_dir) do
      path when is_binary(path) and path != "" ->
        Keyword.put(base_opts, :stdlib_ebin, path)

      _ ->
        base_opts
    end
  end

  # The configured stdlib BEAM directory: the project's
  # `[compiler] stdlib_path`, else `$CURE_LIB`, else `nil`.
  # `Cure.Project.stdlib_path/1` already applies the `$CURE_LIB` fallback;
  # we apply it again for the no-Cure.toml case so a bare `$CURE_LIB`
  # still pins the directory.
  defp resolve_stdlib_ebin(project_dir) do
    case Cure.Project.load(project_dir) do
      {:ok, project} -> Cure.Project.stdlib_path(project)
      _ -> Cure.Stdlib.Paths.cure_lib()
    end
  end

  defp maybe_preload_warning(_state, []), do: :ok

  defp maybe_preload_warning(state, [_ | _] = missing) do
    count = length(missing)

    sample =
      missing
      |> Enum.take(3)
      |> Enum.map_join(", ", &Atom.to_string/1)

    suffix = if count > 3, do: ", ...", else: ""

    render_info(
      state,
      "(stdlib preload degraded: #{count} module(s) missing -- #{sample}#{suffix}; " <>
        "qualified calls will raise :undef. Check that priv/ebin/ is present in the release.)"
    )
  end

  # Logger output interleaves badly with our raw-mode redraws: a stray
  # `[warning] ...` line from another app (MDEx NIF load, telemetry, etc.)
  # can overwrite the prompt. We raise the primary_config level to `:error`
  # for the duration of the REPL session, and restore it on exit.
  defp with_quieted_logger(fun) do
    prev = Logger.level()

    try do
      _ = Logger.configure(level: :error)
      fun.()
    after
      _ = Logger.configure(level: prev)
    end
  end

  defp raw_mode_warning(state, _reason) do
    render_info(
      state,
      "(raw-mode unavailable; arrows and Ctrl+R will not work -- " <>
        "falling back to line-mode input)"
    )
  end

  # ==========================================================================
  # Raw-mode key loop
  # ==========================================================================

  defp raw_loop(state) do
    prompt = prompt_for(state)
    Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
    raw_loop(state, prompt)
  end

  defp raw_loop(%__MODULE__{running: false} = state, _prompt), do: save_and_bye(state)

  defp raw_loop(state, prompt) do
    key = Terminal.read_key()

    cond do
      key == :eof ->
        Render.newline()
        save_and_bye(state)

      key == {:ctrl, ?L} ->
        Render.clear_screen()
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      key == {:ctrl, ?R} ->
        state = run_search(state, prompt)
        raw_loop(state, prompt_for(state))

      key == :up ->
        state = history_prev(state)
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      key == :down ->
        state = history_next(state)
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      key == :tab ->
        state = handle_tab(state)
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      true ->
        handle_editor_key(state, key, prompt)
    end
  end

  defp handle_editor_key(state, key, prompt) do
    case LineEditor.handle(state.editor, key) do
      {:cont, ed} ->
        state = %{state | editor: ed}
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      {:signal, :submit, ed} ->
        state = %{state | editor: ed}
        Render.newline()
        state = submit(state, ed.buffer)
        if state.running, do: raw_loop(state), else: save_and_bye(state)

      {:signal, :newline, ed} ->
        # Alt+Enter / Shift+Enter / Ctrl+Enter: explicitly extend the
        # current submission with one more line, regardless of whether
        # the parser would consider it complete. Bypasses the
        # incomplete-detection heuristics so the user can compose a
        # multi-line block even when each individual line happens to
        # parse on its own.
        state = %{state | editor: ed}
        Render.newline()
        state = force_continue(state, ed.buffer)
        raw_loop(state)

      {:signal, :abort, ed} ->
        Render.newline()
        render_info(state, "(aborted)")
        state = %{state | editor: ed, input_buffer: []}
        raw_loop(state)

      {:signal, :cancel, ed} ->
        state = %{state | editor: ed}
        Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
        raw_loop(state, prompt)

      {:signal, :eof, _ed} ->
        Render.newline()
        save_and_bye(state)
    end
  end

  # -- History navigation ---------------------------------------------------

  defp history_prev(state) do
    draft = state.editor.buffer

    case History.prev(state.history, draft) do
      {:ok, entry, history} ->
        %{state | history: history, editor: set_buffer_flat(state.editor, entry)}

      :at_top ->
        state
    end
  end

  defp history_next(state) do
    case History.next(state.history) do
      {:ok, entry, history} ->
        %{state | history: history, editor: set_buffer_flat(state.editor, entry)}

      :at_bottom ->
        state
    end
  end

  # -- Tab completion --------------------------------------------------------

  defp handle_tab(state) do
    ed = state.editor

    case Cure.REPL.Completer.complete(ed.buffer, ed.cursor) do
      :none ->
        state

      {:unique, text} ->
        %{state | editor: LineEditor.set_buffer(ed, text)}

      {:partial, common, candidates} ->
        Render.newline()
        render_info(state, "  " <> Enum.join(candidates, "   "))
        new_text = apply_common(ed.buffer, ed.cursor, common)
        %{state | editor: LineEditor.set_buffer(ed, new_text)}
    end
  end

  defp apply_common(buffer, cursor, common) do
    left = String.slice(buffer, 0, cursor)
    # `String.slice/2` with an explicit step (introduced in OTP/Elixir
    # that this project targets) always returns a `String.t()`; the
    # historical `|| ""` fallback is unreachable and upsets Dialyzer.
    right = String.slice(buffer, cursor..-1//1)

    new_left =
      case Regex.run(~r/^(.*?)([\w:.\/~-]*)$/u, left, capture: :all_but_first) do
        [prefix, _token] -> prefix <> common
        _ -> left <> common
      end

    new_left <> right
  end

  # -- Ctrl+R search loop ----------------------------------------------------

  defp run_search(state, prompt) do
    original = state.editor.buffer
    s = Search.new(original)
    search_loop(state, s, prompt)
  end

  defp search_loop(state, s, prompt) do
    Render.redraw(state.editor, state.n, state.theme, prompt: prompt)
    cursor_col = Render.ansi_length(prompt) + state.editor.cursor
    Render.draw_search_status(Search.status(s, state.theme), state.theme, cursor_col)

    case Terminal.read_key() do
      :eof ->
        Render.clear_helpers(cursor_col)
        %{state | editor: set_buffer_flat(state.editor, s.original)}

      key ->
        case Search.handle(s, key, state.history) do
          {:continue, s2} ->
            ed2 = set_buffer_flat(state.editor, s2.match || s2.needle)
            search_loop(%{state | editor: ed2}, s2, prompt)

          {:accept, text} ->
            Render.clear_helpers(cursor_col)
            %{state | editor: set_buffer_flat(state.editor, text)}

          {:accept_and_key, text, key} ->
            Render.clear_helpers(cursor_col)
            ed = set_buffer_flat(state.editor, text)

            case LineEditor.handle(ed, key) do
              {:cont, ed2} -> %{state | editor: ed2}
              _ -> %{state | editor: ed}
            end

          {:cancel, text} ->
            Render.clear_helpers(cursor_col)
            %{state | editor: set_buffer_flat(state.editor, text)}
        end
    end
  end

  # The editor is single-line by construction, so any `\n` present in a
  # history entry (multi-line submission, joined with `\n` by
  # `dispatch_buffer/1`) would desync the logical and visible cursor
  # positions when rendered. We replace each newline with a visible U+23CE
  # RETURN SYMBOL so the buffer stays on one row; the user can recover the
  # original multi-line layout by re-submitting with `;;` or editing it
  # via `:edit`.
  defp set_buffer_flat(%LineEditor{} = ed, text) when is_binary(text) do
    LineEditor.set_buffer(ed, flatten_newlines(text))
  end

  defp flatten_newlines(text) when is_binary(text) do
    text
    |> String.replace("\r\n", "\n")
    |> String.replace("\n", " \u23ce ")
  end

  # -- Submission -----------------------------------------------------------

  defp submit(state, line) do
    state = %{state | editor: LineEditor.new(mode: state.mode)}

    cond do
      line == "" and state.input_buffer == [] ->
        state

      line == ";;" ->
        dispatch_buffer(state)

      line == "" and indentation_block_open?(state.input_buffer) ->
        %{state | input_buffer: state.input_buffer ++ [""]}

      line == "" ->
        dispatch_buffer(state)

      state.input_buffer == [] and starts_with_colon?(line) ->
        state
        |> Map.put(:history, History.append(state.history, line))
        |> handle_meta(line)

      # Bare `use Std.X` was previously routed to `evaluate/2`, where
      # it compiled as the body of a synthetic `fn main() -> Any = use
      # Std.X`. The parser treats `use` as an import directive, not an
      # expression, so the function body collapsed to the literal
      # `:undefined` atom and the REPL printed the confusing `=>
      # :undefined`. The meta-command path (`:use Std.X`) already does
      # the right thing -- install the module into `state.uses`,
      # validate it against the stdlib bundle, and surface a
      # friendly "imported Std.X" message -- so we sugar the bare form
      # to it here. Multi-item forms (`use Std.{List, Map}`) also go
      # through so the user gets a sensible error rather than the
      # `:undefined` rabbit hole.
      state.input_buffer == [] and bare_use?(line) ->
        state
        |> Map.put(:history, History.append(state.history, line))
        |> handle_meta(":" <> line)

      true ->
        new_state = %{state | input_buffer: state.input_buffer ++ [line]}
        joined = Enum.join(new_state.input_buffer, "\n")

        if indented_continuation?(state.input_buffer, line) or incomplete?(line, joined) do
          new_state
        else
          dispatch_buffer(new_state)
        end
    end
  end

  # Force-continuation path: invoked from the raw loop when the user
  # presses Alt+Enter / Shift+Enter / Ctrl+Enter. Always appends the
  # current line to `input_buffer` without consulting the
  # incomplete-detection heuristics; the `;;` / blank-line conventions
  # remain the way to actually dispatch.
  defp force_continue(state, line) do
    state = %{state | editor: LineEditor.new(mode: state.mode)}

    cond do
      # Pressing Alt+Enter on an empty fresh prompt is a no-op rather
      # than starting an unsolicited continuation prompt -- the user
      # almost certainly meant to insert a literal blank line in the
      # middle of an *existing* buffer.
      line == "" and state.input_buffer == [] ->
        state

      true ->
        %{state | input_buffer: state.input_buffer ++ [line]}
    end
  end

  # `use <Ident>(.<Ident>)*` optionally followed by `.{...}` or just
  # `.{...}` for the multi-item form. Greedy enough to catch the
  # everyday imports a REPL user would type, strict enough to leave
  # genuine expressions like `useful_thing(x)` alone.
  #
  # Only called from `submit/2`, which guarantees a binary input, so no
  # catch-all clause is necessary. Dialyzer flags the previous
  # `defp bare_use?(_), do: false` fallback as dead code (E4011 /
  # `pattern_match_cov`) because the binary guard on the first clause
  # already covers the full type of `line`.
  defp bare_use?(line) when is_binary(line) do
    Regex.match?(~r/^\s*use\s+[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*(?:\s*\.\s*\{[^}]*\})?\s*$/u, line)
  end

  defp dispatch_buffer(%__MODULE__{input_buffer: []} = state), do: state

  defp dispatch_buffer(%__MODULE__{input_buffer: buf} = state) do
    src = buf |> Enum.join("\n") |> String.trim()

    if src == "" do
      %{state | input_buffer: []}
    else
      state
      |> Map.put(:history, History.append(state.history, src))
      |> Map.put(:input_buffer, [])
      |> handle_submission(src)
      |> Map.update!(:n, &(&1 + 1))
    end
  end

  # Route a trimmed submission to the definition accumulator or the
  # expression evaluator based on the parser's classification of its
  # top-level nodes. A failure to install definitions (compile error,
  # type error, ...) leaves `state.defs` untouched so the user can fix
  # the source and retry without losing previously-installed bindings.
  defp handle_submission(state, src) do
    case Session.classify(src) do
      {:definitions, entries} -> add_definitions(state, entries)
      :expression -> evaluate(state, src)
    end
  end

  defp add_definitions(state, entries) do
    {candidate_defs, annotated} = Session.merge(state.defs, entries)

    case Session.hole_goals(candidate_defs) do
      {:ok, [_ | _] = holes} ->
        Enum.each(annotated, fn
          {:new, entry} -> render_info(state, "defined #{entry.label} (with holes)")
          {:redefined, entry} -> render_info(state, "redefined #{entry.label} (with holes)")
        end)

        %{state | defs: candidate_defs, holes: holes}

      {:ok, []} ->
        compile_definitions(state, candidate_defs, annotated)

      {:error, reason} ->
        render_reason_error(state, reason)
        state
    end
  end

  defp compile_definitions(state, candidate_defs, annotated) do
    case Session.compile(candidate_defs) do
      {:ok, _module} ->
        Enum.each(annotated, fn
          {:new, entry} -> render_info(state, "defined #{entry.label}")
          {:redefined, entry} -> render_info(state, "redefined #{entry.label}")
        end)

        %{state | defs: candidate_defs, holes: []}

      :empty ->
        %{state | defs: candidate_defs}

      {:error, reason} ->
        render_reason_error(state, reason)
        state
    end
  end

  # Expression submissions are compiled by synthesising a temporary
  # `fn main() -> Any = ...` wrapper. Single-line expressions work fine
  # inline (`= 1 + 1`), but a multi-line submission coming from `:edit`
  # must be indented as the *body* of the function:
  #
  #   fn main() -> Any =
  #     let a = 1
  #     let b = a + 1
  #     b
  #
  # If we instead splice the raw text after `= ` on the same line, the
  # parser sees only the first expression as the function body and the
  # trailing lines as top-level siblings, which is why the REPL printed
  # the result of the first expression only.
  defp indent_body(src) when is_binary(src) do
    src
    |> String.split("\n")
    |> Enum.map_join("\n", fn
      "" -> "    "
      line -> "    " <> line
    end)
  end

  # ==========================================================================
  # Legacy line-mode fallback
  # ==========================================================================

  defp legacy_loop(%__MODULE__{running: false} = state), do: save_and_bye(state)

  defp legacy_loop(state) do
    prompt = if state.input_buffer == [], do: "cure(#{state.n})> ", else: "       ... "

    case IO.gets(prompt) do
      :eof -> save_and_bye(state)
      {:error, _} -> save_and_bye(state)
      raw -> raw |> to_string() |> String.trim_trailing() |> legacy_process_line(state)
    end
  end

  defp legacy_process_line(line, state) do
    state = submit(state, line)
    if state.running, do: legacy_loop(state), else: save_and_bye(state)
  end

  # ==========================================================================
  # Evaluation
  # ==========================================================================

  defp evaluate(state, src) do
    mod_name = "Repl.M#{state.n}"
    uses = state.uses |> Enum.map(&"  use #{&1}\n") |> Enum.join()

    # Session definitions are INLINED as local functions of the eval module rather
    # than reached via `use Repl.Session`. The dependent pipeline (sole compiler
    # post-#18) resolves `use` only against on-disk `Std.*` sources; a
    # runtime-generated user module like `Repl.Session` has no source to elaborate
    # and its function TYPES are not recoverable from the loaded BEAM, so a
    # cross-module call would fail as `:unknown_global`. Inlining keeps every
    # session binding a locally-resolved name.
    defs = inline_session_defs(state)

    source = """
    mod #{mod_name}
    #{uses}#{defs}  fn main() =
    #{indent_body(src)}
    """

    file = "repl/#{mod_name}.cure"

    case Cure.Compiler.compile_and_load(source, file: file, emit_events: false) do
      {:ok, module} ->
        try do
          result = module.main()
          render_value(state, result)
        catch
          kind, reason ->
            render_reason_error(state, Cure.Diagnostic.Operational.command_failure("repl", {kind, reason}))
        end

        state

      {:error, reason} ->
        render_reason_diagnostic(state, reason, file, source)
        state
    end
  end

  # The session definitions, rendered as indented local functions to splice into
  # the eval module ahead of `main/0` (see `evaluate/2` for why they are inlined
  # rather than imported). Empty when no definitions are in play.
  defp inline_session_defs(%__MODULE__{defs: []}), do: ""

  defp inline_session_defs(%__MODULE__{defs: defs}) do
    defs
    |> Enum.map_join("\n\n", fn %{source: src} -> indent_body(src) end)
    |> Kernel.<>("\n")
  end

  # ==========================================================================
  # Meta-commands
  # ==========================================================================

  defp handle_meta(state, ":quit"), do: bye(state)
  defp handle_meta(state, ":q"), do: bye(state)
  defp handle_meta(state, ":exit"), do: bye(state)
  defp handle_meta(state, ":help"), do: print_help(state)
  defp handle_meta(state, ":h"), do: print_help(state)

  defp handle_meta(state, ":clear") do
    Render.clear_screen()
    state
  end

  defp handle_meta(state, ":env") do
    defaults = MapSet.new(Docs.default_uses(state.stdlib_kind))
    {stdlib, user} = Enum.split_with(state.uses, &MapSet.member?(defaults, &1))

    cond do
      stdlib == [] and user == [] ->
        render_info(state, "(no imports)")

      true ->
        if stdlib != [] do
          render_info(
            state,
            "stdlib imports (#{length(stdlib)}): " <> Enum.join(Enum.sort(stdlib), ", ")
          )
        end

        if user != [] do
          render_info(state, "user imports:")
          Enum.each(user, &render_info(state, "  use " <> &1))
        end
    end

    state
  end

  defp handle_meta(state, ":reset") do
    Session.clear()
    render_info(state, "REPL state reset.")

    %{
      state
      | n: 1,
        loaded: [],
        uses: Docs.default_uses(state.stdlib_kind),
        defs: [],
        holes: [],
        input_buffer: []
    }
  end

  defp handle_meta(state, ":defs") do
    case state.defs do
      [] ->
        render_info(state, "(no definitions)")

      defs ->
        render_info(state, "session definitions (#{length(defs)}):")
        Enum.each(defs, fn entry -> render_info(state, "  #{entry.label}") end)
    end

    state
  end

  defp handle_meta(state, ":holes") do
    case state.holes do
      [] ->
        render_info(state, "(no holes recorded)")

      holes ->
        Enum.each(holes, fn %{function: label, goal: goal, context: context} ->
          rendered_context =
            case context do
              [] -> ""
              values -> " (context: " <> Enum.map_join(values, ", ", &Cure.Core.Printer.print/1) <> ")"
            end

          render_info(state, "#{label} : #{Cure.Core.Printer.print(goal)}#{rendered_context}")
        end)
    end

    state
  end

  defp handle_meta(state, ":reload") do
    render_info(state, "Reloading #{length(state.loaded)} file(s)")

    Enum.each(state.loaded, fn path ->
      case File.read(path) do
        {:ok, src} ->
          case Cure.Compiler.compile_and_load(src, file: path, emit_events: false) do
            {:ok, mod} -> render_info(state, "  #{path} -> #{mod}")
            {:error, reason} -> render_reason_diagnostic(state, reason, path, src)
          end

        {:error, reason} ->
          render_reason_error(state, Cure.Diagnostic.Operational.file_read(path, reason))
      end
    end)

    state
  end

  defp handle_meta(state, ":history"), do: cmd_history(state, 20)

  defp handle_meta(state, ":history " <> rest) do
    case Integer.parse(String.trim(rest)) do
      {n, _} when n > 0 -> cmd_history(state, n)
      _ -> cmd_history(state, 20)
    end
  end

  defp handle_meta(state, ":search " <> needle), do: cmd_search(state, String.trim(needle))
  defp handle_meta(state, ":snap save"), do: cmd_snap_save(state, "cure.snap")
  defp handle_meta(state, ":snap save " <> path), do: cmd_snap_save(state, String.trim(path))
  defp handle_meta(state, ":snap load " <> path), do: cmd_snap_load(state, String.trim(path))
  defp handle_meta(state, ":snap list"), do: cmd_snap_list(state, ".")
  defp handle_meta(state, ":snap list " <> dir), do: cmd_snap_list(state, String.trim(dir))
  defp handle_meta(state, ":snap"), do: cmd_snap_help(state)
  defp handle_meta(state, ":save " <> path), do: cmd_save(state, String.trim(path))
  defp handle_meta(state, ":edit"), do: cmd_edit(state)
  defp handle_meta(state, ":edit " <> _), do: cmd_edit(state)
  defp handle_meta(state, ":time " <> expr), do: cmd_time(state, expr)
  defp handle_meta(state, ":bench " <> rest), do: cmd_bench(state, rest)
  defp handle_meta(state, ":ast " <> expr), do: cmd_ast(state, expr)
  defp handle_meta(state, ":theme " <> name), do: cmd_theme(state, String.trim(name))
  defp handle_meta(state, ":mode " <> m), do: cmd_mode(state, String.trim(m))
  defp handle_meta(state, ":color " <> v), do: cmd_color(state, String.trim(v))

  defp handle_meta(state, ":john"), do: cmd_john(state)
  defp handle_meta(state, ":john " <> _), do: cmd_john(state)

  defp handle_meta(state, ":t " <> expr), do: cmd_type(state, expr)
  defp handle_meta(state, ":type " <> expr), do: cmd_type(state, expr)
  defp handle_meta(state, ":printdef " <> name), do: cmd_printdef(state, String.trim(name))
  defp handle_meta(state, ":total " <> name), do: cmd_total(state, String.trim(name))
  defp handle_meta(state, ":browse " <> name), do: cmd_browse(state, String.trim(name))
  defp handle_meta(state, ":apropos " <> query), do: cmd_apropos(state, String.trim(query))
  defp handle_meta(state, ":effects " <> expr), do: cmd_effects(state, expr)
  defp handle_meta(state, ":imports"), do: handle_meta(state, ":env")
  defp handle_meta(state, ":stdlib"), do: cmd_stdlib(state)
  defp handle_meta(state, ":doc " <> name), do: cmd_doc(state, name)
  defp handle_meta(state, ":load " <> path), do: cmd_load(state, String.trim(path))
  defp handle_meta(state, ":use " <> mod), do: cmd_use(state, String.trim(mod))
  defp handle_meta(state, ":fmt " <> expr), do: cmd_fmt(state, expr)
  defp handle_meta(state, ":let " <> rest), do: cmd_let(state, rest)
  defp handle_meta(state, ":let"), do: cmd_let(state, "")

  defp handle_meta(state, other) do
    known_commands = ~w(
      :t :type :printdef :total :browse :apropos :doc :effects :load :use :fmt :let :ast :time :bench
      :theme :mode :color :history :search :save :edit :holes :john
      :defs :reset :reload :help :imports :stdlib :quit :exit :snap
    )

    bare = String.split(String.trim(other), " ") |> hd()

    suffix =
      case Cure.Compiler.Errors.suggest(bare, known_commands) do
        nil -> ""
        suggestion -> " Did you mean '#{suggestion}'?"
      end

    render_operational_error(state, "unknown command: #{other}.#{suffix} Try :help.", :usage)
    state
  end

  defp cmd_doc(state, name) do
    Docs.render(name, state)
    state
  end

  defp cmd_browse(state, name) do
    Docs.render(name, state)
    state
  end

  defp cmd_apropos(state, query) do
    Docs.apropos(query, state)
    state
  end

  defp cmd_printdef(state, name) do
    matches =
      Enum.filter(state.defs, fn entry ->
        entry_name = entry.key |> elem(1) |> to_string()
        entry_name == name or entry.label == name
      end)

    case matches do
      [] -> render_info(state, "(no session definition `#{name}`)")
      entries -> Enum.each(entries, fn entry -> Render.write_line(entry.source) end)
    end

    state
  end

  defp cmd_total(state, name) do
    entry =
      Enum.find(state.defs, fn entry ->
        entry.kind == :fn and (to_string(elem(entry.key, 1)) == name or entry.label == name)
      end)

    case entry do
      nil ->
        render_info(state, "(no session function `#{name}`)")

      _ ->
        source = session_inspection_source(state, "Totality#{state.n}")

        case Cure.Elab.Program.elaborate(source) do
          {:ok, env} ->
            key = Cure.Core.Env.resolve_key(env, env.defs, String.to_atom(name))
            verdict = if Cure.Core.Env.total?(env, key), do: "total", else: "not total"
            render_info(state, "#{entry.label} is #{verdict}")

          {:error, reason} ->
            render_reason_error(state, reason)
        end
    end

    state
  end

  defp cmd_type(state, expr) do
    case infer_expression_type(state, expr) do
      {:ok, type} -> render_info(state, String.trim(expr) <> " : " <> Cure.Core.Printer.print(type))
      {:error, reason} -> render_reason_error(state, reason)
    end

    state
  end

  defp cmd_effects(state, expr) do
    case infer_expression_type(state, expr) do
      {:ok, {:effect_type, _payload}} -> render_info(state, String.trim(expr) <> " : effectful")
      {:ok, _type} -> render_info(state, String.trim(expr) <> " : pure")
      {:error, reason} -> render_reason_error(state, reason)
    end

    state
  end

  defp infer_expression_type(state, expr) do
    probe = "repl_probe_#{state.n}"
    source = session_inspection_source(state, "Inspect#{state.n}", "fn #{probe}() =\n#{indent_body(String.trim(expr))}")

    with {:ok, env} <- Cure.Elab.Program.elaborate(source),
         %{type: type} <- Cure.Core.Env.get_def(env, String.to_atom(probe)) do
      {:ok, type}
    else
      nil -> {:error, {:unknown_global, String.to_atom(probe)}}
      {:error, _reason} = error -> error
    end
  end

  defp session_inspection_source(state, suffix, extra \\ "") do
    uses = state.uses |> Enum.map(&"  use #{&1}\n") |> Enum.join()
    defs = inline_session_defs(state)
    tail = if extra == "", do: "", else: "  " <> extra <> "\n"
    "mod Repl.#{suffix}\n#{uses}#{defs}#{tail}"
  end

  defp cmd_stdlib(state) do
    modules = stdlib_module_names() |> Enum.sort()
    render_info(state, "stdlib modules (#{length(modules)}):")
    Enum.each(modules, &render_info(state, "  " <> &1))
    state
  end

  defp cmd_load(state, path) do
    case File.read(path) do
      {:ok, src} ->
        case Cure.Compiler.compile_and_load(src, file: path, emit_events: false) do
          {:ok, mod} ->
            render_info(state, "loaded #{path} -> #{mod}")
            %{state | loaded: Enum.uniq([path | state.loaded])}

          {:error, reason} ->
            render_reason_error(state, reason)
            state
        end

      {:error, reason} ->
        render_reason_error(state, Cure.Diagnostic.Operational.file_read(path, reason))
        state
    end
  end

  defp cmd_use(state, mod) do
    mod = strip_cure_prefix(mod)

    if mod in state.uses do
      render_info(state, "(already imported: #{mod})")
      state
    else
      # If the module is unknown to the stdlib, warn and suggest the closest.
      known = stdlib_module_names()

      state =
        if known != [] and mod not in known do
          suffix =
            case Cure.Compiler.Errors.suggest(mod, known) do
              nil -> ""
              suggestion -> " Did you mean '#{suggestion}'?"
            end

          render_operational_error(
            state,
            "no stdlib module '#{mod}'.#{suffix} Type :stdlib to list known modules.",
            :usage
          )

          state
        else
          state
        end

      render_info(state, "imported #{mod}")
      %{state | uses: state.uses ++ [mod]}
    end
  end

  # Known stdlib module names, derived from the `lib/std/*.cure` source
  # filenames (e.g. `non_empty.cure` -> `Std.NonEmpty`). Replaces the classic
  # `Cure.Types.Stdlib.all/0` signature bundle, removed with the rip-out (#18).
  defp stdlib_module_names do
    case File.ls(Cure.Stdlib.Paths.source_dir()) do
      {:ok, files} ->
        files
        |> Enum.filter(&String.ends_with?(&1, ".cure"))
        |> Enum.map(fn f -> "Std." <> Macro.camelize(Path.rootname(f)) end)

      _ ->
        []
    end
  end

  defp strip_cure_prefix("Cure." <> rest), do: rest
  defp strip_cure_prefix(other), do: other

  defp cmd_fmt(state, expr) do
    case Cure.quote(expr) do
      {:ok, ast} -> render_info(state, Printer.quoted_to_string(ast))
      {:error, reason} -> render_reason_error(state, reason)
    end

    state
  end

  defp cmd_history(state, n) do
    state.history
    |> History.tail(n)
    |> Enum.with_index(1)
    |> Enum.each(fn {entry, idx} ->
      Render.write_line(
        state.theme.dim <>
          String.pad_leading(Integer.to_string(idx), 4) <>
          state.theme.reset <>
          "  " <>
          Cure.REPL.Highlight.highlight(entry)
      )
    end)

    state
  end

  defp cmd_search(state, ""), do: state

  defp cmd_search(state, needle) do
    hits = History.grep(state.history, needle)

    case hits do
      [] ->
        render_info(state, "(no matches for #{inspect(needle)})")

      _ ->
        Enum.each(hits, &Render.write_line(Cure.REPL.Highlight.highlight(&1)))
    end

    state
  end

  defp cmd_snap_save(state, path) do
    case Snap.save(state, path) do
      :ok ->
        render_info(state, "session saved to #{path}")

      {:error, {:file_write_error, p, reason}} ->
        render_reason_error(state, {:file_write_error, p, reason})
    end

    state
  end

  defp cmd_snap_load(state, path) do
    case Snap.load(path) do
      {:ok, snap_map} ->
        state = Snap.apply_snap(state, snap_map)
        defs_count = length(state.defs)
        render_info(state, "loaded snap from #{path} (#{defs_count} definition(s) merged)")
        state

      {:error, :E069} ->
        render_reason_error(state, Cure.Diagnostic.Operational.snap_schema_incompatible(path))
        state

      {:error, :corrupt} ->
        render_reason_error(state, Cure.Diagnostic.Operational.file_read(path, :corrupt))
        state

      {:error, {:file_read_error, p, reason}} ->
        render_reason_error(state, {:file_read_error, p, reason})
        state
    end
  end

  defp cmd_snap_list(state, dir) do
    files = Snap.list(dir)

    if files == [] do
      render_info(state, "(no .cure-snap files in #{dir})")
    else
      render_info(state, "snap files in #{dir} (#{length(files)}):")
      Enum.each(files, fn f -> render_info(state, "  #{f}") end)
    end

    state
  end

  defp cmd_snap_help(state) do
    render_info(state, "snap subcommands: save [path]  load <path>  list [dir]")
    state
  end

  defp cmd_save(state, ""), do: state

  defp cmd_save(state, path) do
    content = state.history |> History.entries() |> Enum.join("\n")

    case File.write(path, content) do
      :ok -> render_info(state, "saved session to #{path}")
      {:error, reason} -> render_reason_error(state, Cure.Diagnostic.Operational.file_write(path, reason))
    end

    state
  end

  # `:edit` hands the terminal over to `$EDITOR` so the user can compose a
  # multi-line submission with their usual editor. Three subtleties must be
  # handled for this to work under the raw-mode REPL:
  #
  #   1. The REPL still owns `/dev/tty` read/write file descriptors and has
  #      the terminal in raw mode. A curses-based editor (vim, nvim, nano,
  #      lvim, ...) cannot paint its screen against a tty that BEAM is also
  #      holding. `Terminal.with_cooked_io/1` closes our fds and restores
  #      stty around the editor invocation, then re-enters raw mode on the
  #      way out.
  #
  #   2. Children spawned by BEAM have no controlling tty (see
  #      `Cure.REPL.Terminal`'s moduledoc). `</dev/tty` in the child fails
  #      with ENXIO, so we redirect the child's stdio to the *pts path*
  #      (`/dev/pts/N`) that we already resolved on startup. Opening that
  #      node does not require a ctty.
  #
  #   3. After the editor exits, the previous implementation left the
  #      editor's contents stranded in `state.input_buffer` and never
  #      dispatched them, so the prompt silently turned into a continuation
  #      (`...`). We now route the content through `dispatch_buffer/1` so
  #      it is evaluated immediately, matching the user's mental model of
  #      "finish editing, submit".
  defp cmd_edit(state) do
    editor = System.get_env("VISUAL") || System.get_env("EDITOR") || "vi"
    tmp = Path.join(System.tmp_dir!(), "cure-repl-#{System.unique_integer([:positive])}.cure")
    initial = Enum.join(state.input_buffer, "\n")
    File.write!(tmp, initial)

    exit_code = Terminal.with_cooked_io(fn -> spawn_editor(editor, tmp) end)

    new_content =
      case File.read(tmp) do
        {:ok, content} -> content
        _ -> ""
      end

    _ = File.rm(tmp)

    cond do
      exit_code != 0 ->
        render_operational_error(state, "editor exited with status #{exit_code}; buffer discarded")
        %{state | input_buffer: []}

      String.trim(new_content) == "" ->
        render_info(state, "(editor produced an empty buffer; nothing submitted)")
        %{state | input_buffer: []}

      true ->
        lines = String.split(new_content, "\n")
        dispatch_buffer(%{state | input_buffer: lines})
    end
  end

  defp spawn_editor(editor, tmp) do
    tmp_q = shell_escape(tmp)

    command =
      case Terminal.resolve_tty_path() do
        nil ->
          "#{editor} #{tmp_q}"

        path ->
          path_q = shell_escape(path)
          "#{editor} #{tmp_q} <#{path_q} >#{path_q} 2>#{path_q}"
      end

    case System.shell(command) do
      {_out, code} -> code
    end
  end

  defp shell_escape(s) when is_binary(s) do
    "'" <> String.replace(s, "'", "'\\''") <> "'"
  end

  # `:let name = expr` pins the value of `expr` as a zero-arg session
  # function, so the user can reuse it across subsequent prompts.
  #
  # Cure's `let` is expression-scoped -- a bare `let a = 1` on one prompt
  # is thrown away by the time the next prompt runs, because every
  # submission compiles as its own throwaway module. The only kind of
  # binding that *does* persist across prompts is a top-level `fn`, so
  # `:let` desugars to `fn name() -> Any = <expr>` and threads it through
  # the same `Session.merge/2` + `Session.compile/1` pipeline that powers
  # explicit `fn` declarations. The binding is then called back as
  # `name()` from follow-up expressions, and is visible to `:defs`,
  # `:reset`, `:t`, and `:effects`.
  #
  # The return type is deliberately `Any`: a concrete type would prevent
  # redefinition with a value of a different shape (`:let a = 1` then
  # `:let a = "hi"`), which is exactly the ergonomic we want `:let` to
  # preserve. Users who want the inferred type see it in the status line
  # we print on success, and can always run `:t name()` afterwards.
  defp cmd_let(state, raw) do
    case parse_let_binding(raw) do
      {:ok, name, expr_src} ->
        install_let_binding(state, name, expr_src)

      {:error, msg} ->
        render_operational_error(state, msg, :usage)
        state
    end
  end

  defp parse_let_binding(raw) do
    trimmed = String.trim(raw)

    case String.split(trimmed, "=", parts: 2) do
      [lhs, rhs] ->
        name = String.trim(lhs)
        expr = String.trim(rhs)

        cond do
          name == "" or expr == "" ->
            {:error, "usage: :let name = expr"}

          not valid_binding_ident?(name) ->
            {:error, "invalid binding name `#{name}`; use a lowercase identifier (letters, digits, '_')"}

          true ->
            {:ok, name, expr}
        end

      _ ->
        {:error, "usage: :let name = expr"}
    end
  end

  defp valid_binding_ident?(name) when is_binary(name) do
    Regex.match?(~r/^[a-z_][A-Za-z0-9_]*$/, name)
  end

  defp install_let_binding(state, name, expr_src) do
    # Annotation-free: the parser accepts `fn f() = expr` and the elaborator
    # infers the codomain from the body. (The old `-> Any` leaned on the classic
    # checker's top type, which the dependent pipeline — sole compiler post-#18 —
    # has no such type for, so it no longer compiles.)
    source = "fn #{name}() = #{expr_src}"

    entry = %{
      key: {:fn, name, 0, :public},
      kind: :fn,
      label: "#{name}/0",
      source: source
    }

    {candidate_defs, annotated} = Session.merge(state.defs, [entry])

    case Session.compile(candidate_defs) do
      {:ok, _module} ->
        Enum.each(annotated, fn
          {:new, _} -> render_info(state, "pinned #{name}/0")
          {:redefined, _} -> render_info(state, "redefined #{name}/0")
        end)

        %{state | defs: candidate_defs}

      :empty ->
        %{state | defs: candidate_defs}

      {:error, reason} ->
        render_reason_error(state, reason)
        state
    end
  end

  defp cmd_time(state, expr) do
    expr = String.trim(expr)
    t0 = System.monotonic_time(:microsecond)
    state = evaluate(state, expr)
    t1 = System.monotonic_time(:microsecond)
    render_info(state, "elapsed: #{format_microseconds(t1 - t0)}")
    state
  end

  defp cmd_bench(state, rest) do
    case Regex.run(~r/^(.*?)\s+(\d+)$/, String.trim(rest), capture: :all_but_first) do
      [expr, n_str] -> bench_run(state, expr, String.to_integer(n_str))
      _ -> bench_run(state, String.trim(rest), 1_000)
    end
  end

  defp bench_run(state, "", _n), do: state

  defp bench_run(state, expr, n) do
    source = """
    mod Repl.Bench#{state.n}
      fn main() = #{expr}
    """

    case Cure.Compiler.compile_and_load(source, emit_events: false) do
      {:ok, module} ->
        times =
          for _ <- 1..n do
            t0 = System.monotonic_time(:microsecond)
            _ = module.main()
            System.monotonic_time(:microsecond) - t0
          end

        sorted = Enum.sort(times)
        min = List.first(sorted)
        max = List.last(sorted)
        avg = div(Enum.sum(sorted), n)
        p95 = Enum.at(sorted, trunc(n * 0.95))

        render_info(
          state,
          "n=#{n}  min=#{format_microseconds(min)}  avg=#{format_microseconds(avg)}  p95=#{format_microseconds(p95)}  max=#{format_microseconds(max)}"
        )

      {:error, reason} ->
        render_reason_error(state, reason)
    end

    state
  end

  defp cmd_ast(state, expr) do
    case Cure.quote(expr) do
      {:ok, ast} ->
        pretty = inspect(ast, pretty: true, limit: :infinity)
        Render.write_line(pretty)

      {:error, reason} ->
        render_reason_error(state, reason)
    end

    state
  end

  defp cmd_theme(state, name) when name in ["dark", "light", "mono"] do
    theme = Theme.for_name(name)
    render_info(%{state | theme: theme}, "theme: #{name}")
    %{state | theme: theme, color: theme.name != :mono}
  end

  defp cmd_theme(state, other) do
    render_operational_error(state, "unknown theme `#{other}` (expected: dark, light, mono)", :usage)
    state
  end

  defp cmd_mode(state, name) when name in ["emacs", "vi"] do
    mode = if name == "vi", do: :vi_insert, else: :emacs
    render_info(state, "mode: #{name}")
    %{state | mode: mode, editor: %{state.editor | mode: mode}}
  end

  defp cmd_mode(state, other) do
    render_operational_error(state, "unknown mode `#{other}` (expected: emacs, vi)", :usage)
    state
  end

  defp cmd_color(state, "on") do
    theme = Theme.for_name(:dark)
    state = %{state | theme: theme, color: true}
    render_info(state, "colour: on")
    state
  end

  defp cmd_color(state, "off") do
    theme = Theme.for_name(:mono)
    state = %{state | theme: theme, color: false}
    Render.write_line("colour: off")
    state
  end

  defp cmd_color(state, other) do
    render_operational_error(state, "expected :color on|off, got `#{other}`", :usage)
    state
  end

  defp print_help(state) do
    md = help_markdown()

    # We deliberately do NOT pipe through `Marcli.render/2` here: Marcli
    # depends on MDEx, whose Rust NIF cannot be loaded from inside an
    # escript archive (the dynamic loader sees a path that doesn't exist
    # on disk and emits `[warning] The on_load function ... returned
    # {:error, {:load_failed, ...}}`). `Cure.REPL.Markdown.render/2`
    # covers the subset of Markdown our `:help` uses and is pure Elixir.
    Render.write_line(Markdown.render(md, state.theme))
    state
  end

  # `:john` -- the everything-and-the-kitchen-sink diagnostic. Hands the
  # real work to `Cure.John.run/1`, which already knows how to fall back
  # from Marcli to the pure-Elixir Markdown renderer when MDEx is not
  # loadable (escript, CI without the NIF, etc.). We pass the REPL's
  # theme through so the fallback path matches the surrounding session
  # and there is no jarring theme switch for users running `:john`.
  defp cmd_john(state) do
    Cure.John.run(theme: state.theme, ansi: state.color)
    state
  end

  defp help_markdown do
    """
    # Cure REPL

    ## Meta-commands

    - `:t` / `:type expr` - show the inferred type of `expr`
    - `:printdef name` - print a definition entered in this session
    - `:total name` - report whether a session function is totality-certified
    - `:browse Mod` - browse a module's public API
    - `:apropos term` - search module, function, type, and protocol names
    - `:doc name` - show the docstring of `name`
    - `:effects expr` - show the inferred effects of `expr`
    - `:load path` - compile a `.cure` file and bring its bindings in
    - `:reload` - reload all previously loaded files
    - `:use Mod` - bring a module's exports into scope
    - `:holes` - list holes from the last evaluated expression
    - `:env` - list every binding currently in scope
    - `:defs` - list top-level definitions (`fn`, `type`, `rec`, ...) entered this session
    - `:reset` - forget all bindings, fresh session
    - `:fmt expr` - pretty-print `expr`
    - `:let name = expr` - pin `expr` as a zero-arg session fn `name/0`
      so it survives across prompts (call as `name()`)
    - `:history [n]` - print the last `n` (default 20) entries
    - `:search term` - non-interactive history grep
    - `:save path` - write the session transcript to `path`
    - `:snap save [path]` - freeze the REPL session to a `.cure-snap` file
      (default: `cure.snap` in the current directory)
    - `:snap load <path>` - restore a session from a `.cure-snap` file
    - `:snap list [dir]` - list `.cure-snap` files in `dir` (default: `.`)
    - `:edit` - open $EDITOR on the current input buffer
    - `:time expr` - evaluate and report elapsed time
    - `:bench expr [n]` - run `expr` `n` times (default 1000), report stats
    - `:ast expr` - dump parsed AST
    - `:theme dark|light|mono` - switch colour theme
    - `:mode emacs|vi` - switch editing mode
    - `:color on|off` - toggle colour output
    - `:clear` - clear the screen
    - `:john` - print everything about Cure, the VM, and the project
    - `:help` / `:h` - show this help
    - `:quit` / `:q` / `:exit` - leave the REPL

    ## Key bindings (emacs mode)

    - `Left` / `Right` - move cursor
    - `Ctrl+A` / `Home` - beginning of line
    - `Ctrl+E` / `End` - end of line
    - `Alt+B` / `Alt+F` / `Ctrl+Left` / `Ctrl+Right` - word-wise movement
    - `Up` / `Down` - history navigation
    - `Ctrl+R` - incremental reverse history search
    - `Ctrl+K` / `Ctrl+U` - kill to end / start
    - `Ctrl+W` - kill previous word
    - `Ctrl+Y` - yank
    - `Ctrl+T` - transpose chars
    - `Ctrl+L` - clear screen
    - `Ctrl+D` - EOF on empty line, delete char otherwise
    - `Ctrl+C` - abort current input
    - `Tab` - completion for meta-commands, paths, modules, keywords
    - `Enter` - submit (or auto-continue if the input looks incomplete)
    - `Alt+Enter` (also `Shift+Enter` / `Ctrl+Enter` on supporting
      terminals) - force a continuation line even if the current
      buffer parses as complete
    - `;;` on its own line - force submit a multi-line buffer

    ## Top-level declarations
    Submitting `fn name(...) = ...`, `type Name = ...`, `rec Name ...`,
    `interface Name ...`, `implementation Interface for Type ...`, or
    `proof Name ...`
    installs the declaration into the REPL's synthesised
    `Repl.Session` module. Subsequent expressions can call/use those
    names unqualified. Redefining a declaration with the same name &
    arity replaces the previous entry in place.

    ## Vi mode
    Press `Esc` to toggle between insert and normal mode. In normal mode:
    `h/j/k/l`, `w`/`b`/`e`, `0`/`^`/`$`, `i`/`a`/`I`/`A`, `x`, `D`, `C`,
    `u` (undo), `Ctrl+R` (redo).
    """
  end

  # ==========================================================================
  # Rendering helpers
  # ==========================================================================

  defp prompt_for(state) do
    case state.input_buffer do
      [] -> Render.prompt(state.n, state.theme, state.mode)
      _ -> Render.continuation(state.n, state.theme)
    end
  end

  defp banner(state) do
    if state.color do
      Render.write_line(
        state.theme.info <>
          "Cure REPL v#{Cure.version()}" <>
          state.theme.reset <>
          state.theme.dim <>
          "  (type :help for commands, :quit to exit)" <>
          state.theme.reset
      )
    else
      Render.write_line("Cure REPL v#{Cure.version()} (type :help for commands, :quit to exit)")
    end
  end

  defp render_value(state, value) do
    arrow = state.theme.result_arrow <> "=> " <> state.theme.reset
    body = inspect(value, pretty: true, limit: :infinity, syntax_colors: syntax_colors(state))
    Render.write_line(arrow <> body)
  end

  defp syntax_colors(%__MODULE__{color: true}) do
    [
      atom: :cyan,
      binary: :green,
      boolean: :magenta,
      nil: :magenta,
      number: :yellow,
      string: :green
    ]
  end

  defp syntax_colors(_), do: []

  defp render_info(state, msg) do
    if state.color do
      Render.write_line(state.theme.info <> msg <> state.theme.reset)
    else
      Render.write_line(msg)
    end
  end

  defp render_operational_error(state, message, kind \\ :command) do
    reason =
      case kind do
        :usage -> {:usage_error, message}
        :command -> {:command_failed, "repl", message}
      end

    render_reason_diagnostic(state, reason)
  end

  defp render_reason_error(state, reason), do: render_reason_diagnostic(state, reason)

  defp render_reason_diagnostic(state, reason, file \\ "repl.cure", source \\ "") do
    reason = if is_binary(reason), do: Operational.command_failure("repl", reason), else: reason
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, file, source)

    Sink.new(
      format: :terminal,
      registry: registry,
      output_device: state.error_device,
      color: if(state.color, do: :always, else: :never),
      width: 80
    )
    |> Sink.emit(diagnostic)
    |> Sink.flush()

    state
  end

  # ==========================================================================
  # Helpers
  # ==========================================================================

  defp starts_with_colon?(<<":", _::binary>>), do: true
  defp starts_with_colon?(_), do: false

  defp classify_input(line) do
    trimmed = String.trim_trailing(line)

    cond do
      String.ends_with?(trimmed, "do") -> :continue
      String.ends_with?(trimmed, "->") -> :continue
      String.ends_with?(trimmed, "=") -> :continue
      String.ends_with?(trimmed, "|") -> :continue
      String.ends_with?(trimmed, "then") -> :continue
      String.ends_with?(trimmed, "else") -> :continue
      String.ends_with?(trimmed, ",") -> :continue
      String.ends_with?(trimmed, "(") -> :continue
      String.ends_with?(trimmed, "=>") -> :continue
      proof_continuation_cue?(trimmed) -> :continue
      lone_opening_keyword?(trimmed) -> :continue
      true -> :complete
    end
  end

  # Single-token block-opening keywords with no operand on the same
  # line. Typing `match` / `pickup` / `try` / `fn` / `case` / `cond` /
  # `do` and pressing Enter clearly signals an unfinished expression.
  @opening_keywords ~w(match pickup if case cond try fn do let mod rec type interface implementation proto impl proof actor fsm)

  @proof_continuation_keywords ~w(induction have because rewrite simplify)

  defp proof_continuation_cue?(line) do
    words = String.split(String.trim(line), ~r/\s+/, trim: true)
    words == ["proof", "chain"] or List.first(words) in @proof_continuation_keywords
  end

  defp lone_opening_keyword?(line) do
    case String.split(String.trim(line), ~r/\s+/, trim: true) do
      [single] -> single in @opening_keywords
      _ -> false
    end
  end

  @doc false
  def __classify_input__(line), do: classify_input(line)

  defp balanced?(src) do
    {p, b, c} =
      src
      |> String.graphemes()
      |> Enum.reduce({0, 0, 0}, fn g, {p, b, c} ->
        case g do
          "(" -> {p + 1, b, c}
          ")" -> {p - 1, b, c}
          "[" -> {p, b + 1, c}
          "]" -> {p, b - 1, c}
          "{" -> {p, b, c + 1}
          "}" -> {p, b, c - 1}
          _ -> {p, b, c}
        end
      end)

    p <= 0 and b <= 0 and c <= 0
  end

  # ==========================================================================
  # Multiline auto-detection
  # ==========================================================================
  #
  # Decide whether the user's accumulated submission still needs more
  # input. The answer is yes when ANY of these signals fire:
  #
  #   1. The just-typed line ends with a continuation token (`do`, `->`,
  #      `=`, `|`, `then`, `else`, `,`, `(`) or is a lone block-opener
  #      (`match`, `pickup`, `fn`, ...). This is the cheap fast path.
  #   2. Brackets are unbalanced.
  #   3. The full joined buffer fails to parse and at least one parser
  #      error is rooted at the synthetic EOF / dedent token, meaning
  #      "we ran out of input mid-construct".
  #   4. The buffer parses but yields a top-level shape that the parser
  #      treats as a syntactic stub: a `match scrutinee` with no arms,
  #      a `try` body with no rescue/catch, and so on.
  #
  # A `;;` / blank line still always submits, since the user's explicit
  # signal trumps the heuristic.
  defp incomplete?(line, joined) do
    classify_input(line) == :continue or
      not balanced?(joined) or
      parse_indicates_continuation?(joined) or
      ast_is_open_block?(joined)
  end

  # Once a block header has opened a buffer, lines deeper than its authored
  # indentation belong to that submission even if the parser could accept the
  # prefix as a smaller complete program. `;;` (or a later dedented line) ends
  # the block explicitly.
  defp indented_continuation?([], _line), do: false

  defp indented_continuation?(buffer, line) do
    first = Enum.find(buffer, &(String.trim(&1) != "")) || ""
    String.trim(line) != "" and leading_width(line) > leading_width(first)
  end

  defp indentation_block_open?([]), do: false

  defp indentation_block_open?(buffer) do
    nonblank = Enum.reject(buffer, &(String.trim(&1) == ""))

    case nonblank do
      [] -> false
      [first | rest] -> Enum.any?(rest, &(leading_width(&1) > leading_width(first)))
    end
  end

  defp leading_width(line) do
    line
    |> String.to_charlist()
    |> Enum.reduce_while(0, fn
      ?\s, count -> {:cont, count + 1}
      ?\t, count -> {:cont, count + 2}
      _char, count -> {:halt, count}
    end)
  end

  defp parse_indicates_continuation?(src) do
    case Cure.quote(src, file: "repl") do
      {:ok, _ast} ->
        false

      {:error, errors} when is_list(errors) ->
        Enum.any?(errors, &error_at_eof?/1)

      _ ->
        false
    end
  end

  # Errors of the shape `{:expected, _, :got, :eof, ...}` /
  # `{:unexpected_token, :eof, ...}` (and the dedent/newline variants
  # the lexer emits at the synthetic end of input) are the parser's
  # way of saying "more tokens would have satisfied this rule".
  defp error_at_eof?({:expected, _expected, :got, got, _line, _col, %Cure.Diagnostic.Span{}})
       when got in [:eof, :dedent, :newline],
       do: true

  defp error_at_eof?({:unexpected_token, %{token_type: type}})
       when type in [:eof, :dedent, :newline],
       do: true

  defp error_at_eof?(_), do: false

  # The parser is permissive: `match scrutinee` on its own elaborates
  # to `{:pattern_match, _, [scrutinee]}` (only one child, no arms),
  # which is almost always not what the user wanted -- they were
  # halfway through composing the match expression. Treat such open
  # AST shapes as a continuation cue.
  defp ast_is_open_block?(src) do
    case Cure.quote(src, file: "repl") do
      {:ok, ast} -> open_ast?(ast)
      _ -> false
    end
  end

  defp open_ast?({:block, _meta, nodes}) when is_list(nodes) do
    case List.last(nodes) do
      nil -> false
      last -> open_ast?(last)
    end
  end

  # `match scrutinee` without arms.
  defp open_ast?({:pattern_match, _meta, [_scrutinee]}), do: true

  # Open constructs can be nested under a function/proof/container node. The
  # old top-level-only check saw `match x` but missed `fn f() = match x`, which
  # made the REPL submit a definition before its first indented arm arrived.
  defp open_ast?(tuple) when is_tuple(tuple) do
    tuple |> Tuple.to_list() |> Enum.any?(&open_ast?/1)
  end

  defp open_ast?(list) when is_list(list), do: Enum.any?(list, &open_ast?/1)

  defp open_ast?(_), do: false

  defp resolve_theme(opts) do
    case Keyword.get(opts, :theme, :auto) do
      :auto -> if Theme.disabled?(), do: Theme.for_name(:mono), else: Theme.default()
      name -> Theme.for_name(name)
    end
  end

  defp resolve_mode(opts) do
    case Keyword.get(opts, :mode) do
      :vi -> :vi_insert
      :vi_insert -> :vi_insert
      :emacs -> :emacs
      nil -> if System.get_env("CURE_REPL_MODE") == "vi", do: :vi_insert, else: :emacs
      _ -> :emacs
    end
  end

  defp resolve_error_device(opts) do
    case Keyword.get(opts, :error_device, :stderr) do
      :stderr -> :stderr
      :stdio -> :stdio
      :standard_error -> :stderr
      :standard_io -> :stdio
      other when is_atom(other) or is_pid(other) -> other
      _ -> :stderr
    end
  end

  defp default_history_path do
    case System.user_home() do
      nil -> ".cure_history"
      home -> Path.join(home, ".cure_history")
    end
  end

  defp save_and_bye(%__MODULE__{} = state) do
    _ = History.persist(state.history)
    Render.write_line("")
    render_info(state, "Bye.")
    :ok
  end

  defp save_and_bye(_), do: :ok

  # Mark the REPL as done; the outer loop is responsible for `save_and_bye/1`
  # so we don't print the farewell twice.
  defp bye(state), do: %{state | running: false}

  @doc false
  def __render_reason_error__(%__MODULE__{} = state, reason, file \\ "repl.cure", source \\ "") do
    render_reason_diagnostic(state, reason, file, source)
  end

  @doc false
  def __new_state__(opts \\ []) do
    theme = Theme.for_name(Keyword.get(opts, :theme, :mono))

    %__MODULE__{
      theme: theme,
      color: theme.name != :mono,
      error_device: Keyword.get(opts, :error_device, :stderr),
      uses: Keyword.get(opts, :uses, []),
      history: History.load(nil),
      editor: LineEditor.new(mode: :emacs)
    }
  end

  @doc false
  # Test hook: feed a single submission through the same pipeline the
  # raw/legacy loops use, without touching the terminal. Returns the
  # updated state so tests can assert on `:defs`, `:n`, etc.
  def __submit__(%__MODULE__{} = state, line) when is_binary(line) do
    submit(state, line)
  end

  @doc false
  # Test hook for the explicit force-continuation path used by
  # Alt+Enter / Shift+Enter / Ctrl+Enter in the raw loop.
  def __continue__(%__MODULE__{} = state, line) when is_binary(line) do
    force_continue(state, line)
  end

  @doc false
  def __incomplete__?(line, joined) when is_binary(line) and is_binary(joined) do
    incomplete?(line, joined)
  end

  defp format_microseconds(us) when us < 1_000, do: "#{us} us"

  defp format_microseconds(us) when us < 1_000_000,
    do: :io_lib.format("~.2f ms", [us / 1_000]) |> IO.iodata_to_binary()

  defp format_microseconds(us),
    do: :io_lib.format("~.2f s", [us / 1_000_000]) |> IO.iodata_to_binary()
end

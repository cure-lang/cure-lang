defmodule Cure.John do
  @moduledoc """
  A panoramic, single-shot diagnostic for the Cure toolchain, the BEAM
  virtual machine it is riding on, and the project currently under the
  cursor.

  Named in tribute to **John Carbajal**, who had an uncanny knack for
  spotting the one line in a fifty-page report that actually mattered.
  When in doubt, `john` prints everything and lets the operator play
  John for a minute.

  ## What it shows

    * **Cure** -- version, escript entry point, loaded stdlib modules,
      pipeline event bus status, protocol registry size.
    * **BEAM / OTP** -- Elixir and OTP versions, ERTS version, scheduler
      topology, process / atom / port counts and their limits, memory
      breakdown, reductions, uptime, wordsize.
    * **System** -- operating system family + version, architecture,
      hostname, user, home, current directory, relevant environment
      variables (`LANG`, `TERM`, `PATH` summary).
    * **Tooling** -- Elixir / OTP / Cure versions again (easy to spot),
      Z3 availability, `git` presence, top-level dependency versions.
    * **Project** -- when `Cure.toml` is present in the current
      directory: name, version, dependency table, documentation config,
      source paths, lockfile freshness summary.
    * **Runtime** -- a `Cure.Observe.Top` snapshot (supervisors,
      actors, FSMs) if the Cure application is running.
    * **Doctor** -- the severity counters from `Cure.Doctor.run/1`
      (does not reprint the full findings; run `cure doctor` for
      that).
    * **Recent logs** -- tails of `.cure/logs/*.log`,
      `_build/cure/logs/*`, and a note on `erl_crash.dump` when
      present.

  The rendered output is CommonMark Markdown, piped through
  `Marcli.render/2` when the runtime can actually load it (plain Mix
  task, REPL running under `iex`, etc.). Inside the `cure` escript --
  where Marcli's MDEx NIF cannot be loaded -- we fall back to the
  built-in `Cure.REPL.Markdown` renderer, which knows a smaller dialect
  but is pure Elixir.

  ## Public API

    * `collect/1` -- gather every section as a structured map. Handy
      for tests and programmatic consumers.
    * `render/2` -- turn a collected snapshot into a Markdown string.
    * `run/1` -- convenience: `collect/1` + `render/2` + write to IO.
  """

  alias Cure.REPL.{Markdown, Theme}

  @type snapshot :: %{
          at: DateTime.t(),
          cure: map(),
          vm: map(),
          system: map(),
          tooling: map(),
          project: map() | nil,
          runtime: map() | nil,
          doctor: map(),
          logs: [map()]
        }

  @doc """
  Collect every diagnostic section. The returned map is entirely
  plain Elixir terms (no PIDs, no references, no functions) so it can
  be inspected, serialised, or dropped into a structured logger.

  ## Options

    * `:root` -- directory to treat as the project root. Defaults to
      the current working directory.
  """
  @spec collect(keyword()) :: snapshot()
  def collect(opts \\ []) do
    root = Keyword.get(opts, :root, safe_cwd())

    %{
      at: DateTime.utc_now(),
      cure: cure_info(),
      vm: vm_info(),
      system: system_info(),
      tooling: tooling_info(),
      project: project_info(root),
      runtime: runtime_info(),
      doctor: doctor_info(root),
      logs: log_info(root)
    }
  end

  @doc """
  Render a snapshot as a Markdown string. The output is CommonMark and
  renders cleanly via `Marcli.render/2`; see `run/1`.

  ## Options

    * `:width` -- target width for section separators. Defaults to
      `80`.
    * `:banner` -- set to `false` to suppress the dedication banner.
      Useful in tests and automated parsers.
  """
  @spec render(snapshot(), keyword()) :: String.t()
  def render(snapshot, opts \\ []) do
    width = Keyword.get(opts, :width, 80)
    banner? = Keyword.get(opts, :banner, true)

    [
      if(banner?, do: banner_md(snapshot), else: nil),
      cure_md(snapshot.cure, snapshot.at),
      vm_md(snapshot.vm),
      system_md(snapshot.system),
      tooling_md(snapshot.tooling),
      project_md(snapshot.project),
      runtime_md(snapshot.runtime),
      doctor_md(snapshot.doctor),
      logs_md(snapshot.logs),
      footer_md(width)
    ]
    |> Enum.reject(&is_nil/1)
    |> Enum.join("\n\n")
  end

  @doc """
  Gather the snapshot, render it, and write it to `device` (default
  `:stdio`). Returns the rendered string.

  Calls `Marcli.render/2` when the richer renderer can be loaded (plain
  Mix task, `iex -S mix`, etc.). In escript-hosted contexts where
  MDEx's NIF is unavailable we transparently fall back to
  `Cure.REPL.Markdown.render/2`.

  ## Options

  Accepts every option of `collect/1` and `render/2`, plus:

    * `:device` -- IO device to write to (default `:stdio`).
    * `:theme` -- `Cure.REPL.Theme.t()` used by the fallback renderer.
      Defaults to `:dark`, or `:mono` when `NO_COLOR` / non-tty output
      is detected.
    * `:ansi` -- `true` / `false` to force Marcli on or off. Defaults
      to auto-detection.
  """
  @spec run(keyword()) :: String.t()
  def run(opts \\ []) do
    device = Keyword.get(opts, :device, :stdio)
    snapshot = collect(opts)
    md = render(snapshot, opts)
    rendered = render_markdown(md, opts)
    # `IO.write/2` is used here rather than `IO.binwrite/2` on purpose.
    # Under the `mix cure.john` entry point Mix owns the `:stdio` IO
    # server, and that server transcodes binaries handed to `binwrite`
    # byte-by-byte as Latin-1 into UTF-8 -- which double-encodes any
    # multi-byte glyph Marcli emits (notably its `\u25b8` bullet
    # marker, which then shows up as the infamous `\u00e2\u00b8`
    # mojibake pair). `IO.write/2` goes through the Unicode-aware
    # `io_request` path instead and writes the original UTF-8 bytes
    # untouched. The escript and REPL surfaces use the pure-Elixir
    # Markdown fallback, which uses only ASCII bullets, so they were
    # already safe; this aligns the Mix path.
    IO.write(device, rendered)
    IO.write(device, "\n")
    rendered
  end

  # ==========================================================================
  # Cure
  # ==========================================================================

  defp cure_info do
    %{
      version: Cure.version(),
      escript_main: "Cure.CLI",
      app_loaded?: app_loaded?(:cure),
      app_started?: app_started?(:cure),
      stdlib_loaded_modules: loaded_stdlib_modules(),
      pipeline_event_bus:
        safe(
          fn -> Registry.count(Cure.Pipeline.Events.Registry) end,
          :unavailable
        ),
      type_system: "dependent Core"
    }
  end

  defp cure_md(cure, at) do
    lines = [
      kv("version", cure.version),
      kv("escript", cure.escript_main),
      kv("application loaded", bool(cure.app_loaded?)),
      kv("application started", bool(cure.app_started?)),
      kv("stdlib modules loaded", inspect(cure.stdlib_loaded_modules)),
      kv("pipeline event bus", inspect(cure.pipeline_event_bus)),
      kv("type system", cure.type_system),
      kv("snapshot taken", DateTime.to_iso8601(at))
    ]

    section("Cure", lines)
  end

  # ==========================================================================
  # BEAM / OTP
  # ==========================================================================

  defp vm_info do
    mem = :erlang.memory()
    {reductions, _} = :erlang.statistics(:reductions)
    {total_runtime_ms, _} = :erlang.statistics(:runtime)
    {wall_clock_ms, _} = :erlang.statistics(:wall_clock)

    %{
      elixir: System.version(),
      otp_release: System.otp_release(),
      erts: to_string(:erlang.system_info(:version)),
      system_version: :erlang.system_info(:system_version) |> to_string() |> String.trim(),
      schedulers: :erlang.system_info(:schedulers),
      schedulers_online: :erlang.system_info(:schedulers_online),
      dirty_cpu_schedulers: :erlang.system_info(:dirty_cpu_schedulers),
      dirty_io_schedulers: :erlang.system_info(:dirty_io_schedulers),
      logical_processors: :erlang.system_info(:logical_processors),
      process_count: :erlang.system_info(:process_count),
      process_limit: :erlang.system_info(:process_limit),
      port_count: :erlang.system_info(:port_count),
      port_limit: :erlang.system_info(:port_limit),
      atom_count: :erlang.system_info(:atom_count),
      atom_limit: :erlang.system_info(:atom_limit),
      ets_count: length(:ets.all()),
      memory_total: Keyword.get(mem, :total, 0),
      memory_processes: Keyword.get(mem, :processes, 0),
      memory_atom: Keyword.get(mem, :atom, 0),
      memory_binary: Keyword.get(mem, :binary, 0),
      memory_code: Keyword.get(mem, :code, 0),
      memory_ets: Keyword.get(mem, :ets, 0),
      memory_system: Keyword.get(mem, :system, 0),
      reductions: reductions,
      runtime_ms: total_runtime_ms,
      wall_clock_ms: wall_clock_ms,
      wordsize_internal: :erlang.system_info({:wordsize, :internal}),
      wordsize_external: :erlang.system_info({:wordsize, :external})
    }
  end

  defp vm_md(vm) do
    lines = [
      kv("Elixir", vm.elixir),
      kv("OTP release", vm.otp_release),
      kv("ERTS", vm.erts),
      kv("system", vm.system_version),
      kv(
        "schedulers",
        "#{vm.schedulers_online}/#{vm.schedulers} online " <>
          "(dirty cpu: #{vm.dirty_cpu_schedulers}, dirty io: #{vm.dirty_io_schedulers})"
      ),
      kv("logical processors", inspect(vm.logical_processors)),
      kv("processes", "#{vm.process_count}/#{vm.process_limit}"),
      kv("ports", "#{vm.port_count}/#{vm.port_limit}"),
      kv("atoms", "#{vm.atom_count}/#{vm.atom_limit}"),
      kv("ets tables", vm.ets_count),
      kv("memory total", human_bytes(vm.memory_total)),
      kv("memory processes", human_bytes(vm.memory_processes)),
      kv("memory binary", human_bytes(vm.memory_binary)),
      kv("memory code", human_bytes(vm.memory_code)),
      kv("memory ets", human_bytes(vm.memory_ets)),
      kv("memory atom", human_bytes(vm.memory_atom)),
      kv("memory system", human_bytes(vm.memory_system)),
      kv("reductions", vm.reductions),
      kv("runtime", human_duration(vm.runtime_ms)),
      kv("wall-clock", human_duration(vm.wall_clock_ms)),
      kv("wordsize", "#{vm.wordsize_internal} internal / #{vm.wordsize_external} external")
    ]

    section("BEAM / OTP", lines)
  end

  # ==========================================================================
  # System
  # ==========================================================================

  defp system_info do
    {os_family, os_name} = :os.type()

    %{
      os_family: os_family,
      os_name: os_name,
      os_version: safe(fn -> :os.version() end, :unavailable),
      arch: safe_arch(),
      hostname: safe(fn -> :inet.gethostname() |> elem(1) |> to_string() end, "?"),
      user: safe(fn -> System.get_env("USER") || System.get_env("USERNAME") end, nil),
      home: System.user_home(),
      cwd: safe_cwd(),
      lang: System.get_env("LANG"),
      term: System.get_env("TERM"),
      shell: System.get_env("SHELL"),
      path_entries: safe(fn -> length(String.split(System.get_env("PATH") || "", ":")) end, 0)
    }
  end

  defp system_md(sys) do
    lines = [
      kv("os", "#{sys.os_family}/#{sys.os_name}"),
      kv("os version", inspect(sys.os_version)),
      kv("architecture", sys.arch),
      kv("hostname", sys.hostname),
      kv("user", inspect(sys.user)),
      kv("home", inspect(sys.home)),
      kv("cwd", sys.cwd),
      kv("LANG", inspect(sys.lang)),
      kv("TERM", inspect(sys.term)),
      kv("SHELL", inspect(sys.shell)),
      kv("PATH entries", sys.path_entries)
    ]

    section("System", lines)
  end

  # ==========================================================================
  # Tooling
  # ==========================================================================

  defp tooling_info do
    %{
      elixir: System.version(),
      otp: System.otp_release(),
      cure: Cure.version(),
      z3: System.find_executable("z3"),
      git: System.find_executable("git"),
      make: System.find_executable("make"),
      cc: System.find_executable("cc"),
      dependencies: loaded_dependency_versions()
    }
  end

  defp tooling_md(t) do
    deps_md =
      case t.dependencies do
        [] ->
          "  *(no dependencies loaded)*"

        deps ->
          deps
          |> Enum.map(fn {name, version} -> "  - `#{name}` #{version}" end)
          |> Enum.join("\n")
      end

    header_lines = [
      kv("Elixir", t.elixir),
      kv("OTP", t.otp),
      kv("Cure", t.cure),
      kv("z3", t.z3 || "(not on $PATH)"),
      kv("git", t.git || "(not on $PATH)"),
      kv("make", t.make || "(not on $PATH)"),
      kv("cc", t.cc || "(not on $PATH)")
    ]

    section("Tooling", header_lines ++ ["", "**Loaded dependencies**:", "", deps_md])
  end

  # ==========================================================================
  # Project
  # ==========================================================================

  defp project_info(root) do
    case safe(fn -> Cure.Project.load(root) end, {:error, :unavailable}) do
      {:ok, project} ->
        %{
          name: project.name,
          version: project.version,
          root: project.root,
          source_paths: Map.get(project, :source_paths, []),
          dependencies: project.dependencies,
          doc: Map.get(project, :doc, %{}),
          application: Map.get(project, :application, nil),
          lockfile: lockfile_status(project.root)
        }

      {:error, :no_project_file} ->
        nil

      {:error, reason} ->
        %{error: project_error_reason(reason)}
    end
  end

  defp project_error_reason(:unavailable), do: "the project document is unavailable"
  defp project_error_reason({tag, detail}) when is_binary(detail), do: "#{tag}: #{detail}"
  defp project_error_reason({tag, _detail}), do: "the project document is invalid (#{tag})"

  defp project_md(nil) do
    section("Project", ["  *(no `Cure.toml` found in the current directory)*"])
  end

  defp project_md(%{error: reason}) do
    section("Project", [kv("error", reason)])
  end

  defp project_md(proj) do
    deps_md =
      case proj.dependencies do
        [] ->
          "  *(no dependencies declared)*"

        deps ->
          deps
          |> Enum.map(fn d ->
            "  - `#{d.name}` #{describe_dep(d)}"
          end)
          |> Enum.join("\n")
      end

    lines = [
      kv("name", proj.name),
      kv("version", proj.version),
      kv("root", proj.root),
      kv("source paths", inspect(proj.source_paths)),
      kv("lockfile", proj.lockfile),
      "",
      "**Dependencies** (#{length(proj.dependencies)}):",
      "",
      deps_md
    ]

    section("Project", lines)
  end

  defp describe_dep(dep) do
    cond do
      v = Map.get(dep, :version) -> "#{v}"
      p = Map.get(dep, :path) -> "(path: #{p})"
      g = Map.get(dep, :git) -> "(git: #{g})"
      true -> "(unresolved)"
    end
  end

  defp lockfile_status(root) do
    path = Path.join(root, "Cure.lock")

    cond do
      not File.exists?(path) -> "missing"
      true -> "present (#{human_bytes(File.stat!(path).size)})"
    end
  end

  # ==========================================================================
  # Runtime
  # ==========================================================================

  # The runtime snapshot came from `Cure.Observe.Top`, which tracked the
  # supervisor/actor/fsm container runtimes. Those containers were removed with
  # the classic pathway rip-out (#18), so there is no live topology to report.
  defp runtime_info, do: nil

  defp runtime_md(nil) do
    section("Runtime", ["  *(Cure runtime not available in this context)*"])
  end

  defp runtime_md(rt) do
    base = [
      kv("supervisors", rt.supervisors),
      kv("actors", rt.actors),
      kv("FSMs", rt.fsms)
    ]

    sample =
      case rt.sample do
        [] -> []
        items -> ["", "**Top supervisors**:", "" | Enum.map(items, &("  - " <> &1))]
      end

    section("Runtime", base ++ sample)
  end

  # ==========================================================================
  # Doctor
  # ==========================================================================

  defp doctor_info(root) do
    safe(
      fn ->
        report = Cure.Doctor.run(root)
        counts = Enum.frequencies_by(report.findings, & &1.severity)

        %{
          ok?: report.ok?,
          info: Map.get(counts, :info, 0),
          warnings: Map.get(counts, :warning, 0),
          errors: Map.get(counts, :error, 0),
          total: length(report.findings)
        }
      end,
      %{ok?: nil, info: 0, warnings: 0, errors: 0, total: 0, error: "unavailable"}
    )
  end

  defp doctor_md(d) do
    status =
      case d[:ok?] do
        true -> "OK"
        false -> "issues"
        _ -> "unavailable"
      end

    lines = [
      kv("status", status),
      kv("info", d.info),
      kv("warnings", d.warnings),
      kv("errors", d.errors),
      kv("total findings", d.total)
    ]

    lines =
      if err = d[:error] do
        lines ++ [kv("error", inspect(err))]
      else
        lines
      end

    section("Doctor", lines ++ ["", "*Run `cure doctor` for the full report.*"])
  end

  # ==========================================================================
  # Logs
  # ==========================================================================

  defp log_info(root) do
    candidates =
      [
        Path.wildcard(Path.join(root, ".cure/logs/*.log")),
        Path.wildcard(Path.join(root, "_build/cure/logs/*")),
        Path.wildcard(Path.join(root, "erl_crash.dump"))
      ]
      |> List.flatten()
      |> Enum.uniq()
      |> Enum.filter(&File.regular?/1)

    candidates
    |> Enum.sort_by(
      fn path ->
        case File.stat(path) do
          {:ok, %File.Stat{mtime: m}} -> m
          _ -> {{0, 0, 0}, {0, 0, 0}}
        end
      end,
      :desc
    )
    |> Enum.take(5)
    |> Enum.map(fn path ->
      kind = classify_log(path)

      %{
        path: Path.relative_to_cwd(path),
        size: safe(fn -> File.stat!(path).size end, 0),
        kind: kind,
        content: read_log_content(path, kind)
      }
    end)
  end

  defp classify_log(path) do
    case Path.basename(path) do
      "erl_crash.dump" -> :crash_dump
      _ -> if crash_dump_header?(path), do: :crash_dump, else: :log
    end
  end

  defp crash_dump_header?(path) do
    case read_prefix(path, 64) do
      {:ok, head} -> String.starts_with?(head, "=erl_crash_dump:")
      _ -> false
    end
  end

  defp read_log_content(path, :crash_dump), do: summarize_crash_dump(path)
  defp read_log_content(path, :log), do: tail_lines(path, 10)

  defp logs_md([]) do
    section("Recent logs", ["  *(no log files found under `.cure/logs/`, `_build/cure/logs/`, or `erl_crash.dump`)*"])
  end

  defp logs_md(logs) do
    lines =
      logs
      |> Enum.flat_map(fn entry ->
        header = "### " <> entry.path <> "  (#{human_bytes(entry.size)})"

        case entry.kind do
          :crash_dump -> crash_dump_block(header, entry.content)
          :log -> log_tail_block(header, entry.content)
        end
      end)

    section("Recent logs", lines)
  end

  defp crash_dump_block(header, %{fields: fields, counts: counts, note: note}) do
    field_lines =
      fields
      |> Enum.reject(fn {_k, v} -> v in [nil, ""] end)
      |> Enum.map(fn {k, v} -> kv(k, v) end)

    count_lines =
      counts
      |> Enum.reject(fn {_k, v} -> v in [nil, 0] end)
      |> Enum.map(fn {k, v} -> kv(k, v) end)

    trailer =
      if count_lines == [],
        do: field_lines,
        else: field_lines ++ ["", "**Section markers (sampled from prefix)**:", "" | count_lines]

    body =
      if field_lines == [] and count_lines == [] do
        ["  *(crash dump did not expose any recognisable header fields)*"]
      else
        trailer
      end

    note_lines = if note, do: ["", "  *#{note}*"], else: []

    [header, "" | body] ++ note_lines
  end

  defp crash_dump_block(header, other) when is_binary(other) do
    # Falls through when `summarize_crash_dump/1` could not open / read
    # the file; treat it like an opaque log tail so the section still
    # renders rather than crashing the whole report.
    log_tail_block(header, other)
  end

  defp log_tail_block(header, content) do
    body =
      case content do
        "" -> "*(empty)*"
        t when is_binary(t) -> sanitize_binary(t)
        other -> inspect(other)
      end

    [
      header,
      "",
      "```",
      body,
      "```"
    ]
  end

  defp tail_lines(path, n) do
    case File.read(path) do
      {:ok, content} ->
        content
        |> sanitize_binary()
        |> String.split("\n")
        |> Enum.reject(&(&1 == ""))
        |> Enum.take(-n)
        |> Enum.join("\n")

      _ ->
        ""
    end
  end

  # ==========================================================================
  # erl_crash.dump summarisation
  # ==========================================================================
  #
  # An Erlang crash dump is a line-oriented text file. All the top-level
  # header fields (`Slogan:`, `System version:`, `Atoms:`, the `=memory`
  # section, ...) live in the first few kilobytes; process / ETS / module
  # sections follow. We read a bounded prefix so a multi-GB dump never
  # blows the heap when `john` runs, and we extract a structured
  # summary rather than `tail`ing the file (whose process state contains
  # binary blobs that display as `â` garbage in the terminal).
  @crash_prefix_bytes 65_536

  # Long values (an `io:put_chars` slogan carrying a multi-kilobyte
  # byte literal, for instance) are truncated when extracted. That
  # stops a single field from flooding the terminal while still
  # leaving the first portion of the payload -- normally enough to
  # identify the crash -- visible in the report.
  @crash_value_max_chars 240

  @spec summarize_crash_dump(String.t()) :: map() | String.t()
  defp summarize_crash_dump(path) do
    case read_prefix(path, @crash_prefix_bytes) do
      {:ok, ""} ->
        "(crash dump is empty)"

      {:ok, head} ->
        clean = sanitize_binary(head)
        total_size = safe(fn -> File.stat!(path).size end, byte_size(head))
        note = crash_dump_note(total_size, byte_size(head))

        %{
          fields: crash_dump_fields(clean),
          counts: crash_dump_counts(clean),
          note: note
        }

      :error ->
        "(crash dump could not be read)"
    end
  end

  defp crash_dump_note(total_size, head_size) when total_size > head_size do
    "Only the first #{human_bytes(head_size)} of #{human_bytes(total_size)} were scanned for this summary; process/ETS/module counts below are lower bounds."
  end

  defp crash_dump_note(_total_size, _head_size), do: nil

  defp crash_dump_fields(head) do
    [
      {"format", extract_first_line(head)},
      {"dumped", extract_field(head, "Crash dump is written")},
      {"slogan", extract_field(head, "Slogan")},
      {"system", extract_field(head, "System version")},
      {"compiled", extract_field(head, "Compiled")},
      {"taints", extract_field(head, "Taints")},
      {"atoms", extract_field(head, "Atoms")},
      {"calling thread", extract_field(head, "Calling Thread")},
      {"memory total", extract_memory(head, "total")},
      {"memory processes", extract_memory(head, "processes")},
      {"memory processes used", extract_memory(head, "processes_used")},
      {"memory system", extract_memory(head, "system")},
      {"memory atom", extract_memory(head, "atom")},
      {"memory atom used", extract_memory(head, "atom_used")},
      {"memory binary", extract_memory(head, "binary")},
      {"memory code", extract_memory(head, "code")},
      {"memory ets", extract_memory(head, "ets")}
    ]
  end

  defp crash_dump_counts(head) do
    [
      {"processes", count_sections(head, "=proc:")},
      {"ports", count_sections(head, "=port:")},
      {"ets tables", count_sections(head, "=ets:")},
      {"modules", count_sections(head, "=mod:")},
      {"scheduler slots", count_sections(head, "=scheduler:")},
      {"atoms sampled", count_sections(head, "=atoms")}
    ]
  end

  # Reads an ISO-8601-ish line from the first line of the dump
  # (`=erl_crash_dump:0.5`). Most dumps are happy to tell us their
  # format version right up front.
  defp extract_first_line(head) do
    head
    |> String.split("\n", parts: 2)
    |> List.first()
    |> case do
      nil -> nil
      "" -> nil
      line -> String.trim(line)
    end
  end

  # Header-style lookup: the first line of the crash dump that starts
  # with `<Key>:` (up to a newline). Handles the leading whitespace
  # variants OTP has shipped over the years. See
  # `@crash_value_max_chars` for how long values are truncated.
  defp extract_field(head, key) when is_binary(key) do
    # Anchored, multi-line, case-sensitive.
    case Regex.run(~r/^\s*#{Regex.escape(key)}\s*:\s*(.*)$/m, head, capture: :all_but_first) do
      [value] ->
        value
        |> String.trim()
        |> truncate_value(@crash_value_max_chars)

      _ ->
        nil
    end
  end

  defp truncate_value(value, max) when is_binary(value) do
    if String.length(value) > max do
      String.slice(value, 0, max) <> " ..."
    else
      value
    end
  end

  # The `=memory` block is a sequence of `<name>: <bytes>` pairs on
  # their own lines. We anchor on the line after the `=memory` marker
  # so we do not accidentally pick up fields named `total:` inside a
  # `=proc:` section.
  defp extract_memory(head, name) when is_binary(name) do
    with [memory_block | _] <- Regex.run(~r/=memory\s*\n(.*?)(?=^=|\z)/ms, head, capture: :all_but_first),
         [raw] <-
           Regex.run(~r/^#{Regex.escape(name)}:\s*(\d+)\s*$/m, memory_block, capture: :all_but_first) do
      case Integer.parse(raw) do
        {bytes, _} -> human_bytes(bytes)
        _ -> nil
      end
    else
      _ -> nil
    end
  end

  defp count_sections(head, marker) when is_binary(marker) do
    head
    |> String.split(marker)
    |> length()
    |> Kernel.-(1)
    |> max(0)
  end

  defp read_prefix(path, bytes) do
    case :file.open(to_charlist(path), [:read, :raw, :binary]) do
      {:ok, io} ->
        try do
          case :file.read(io, bytes) do
            {:ok, data} when is_binary(data) -> {:ok, data}
            :eof -> {:ok, ""}
            _ -> :error
          end
        after
          _ = :file.close(io)
        end

      _ ->
        :error
    end
  end

  # Replace any bytes that are not valid UTF-8 with `?` so that the
  # downstream Markdown pipeline (MDEx NIF or pure-Elixir fallback)
  # does not choke on raw process-state blobs embedded in crash dumps
  # or rotated log files. `:unicode.characters_to_binary/3` hands us
  # `{:error, ok, <bad_byte, rest>}` on the first ill-formed byte; we
  # drop that byte, swap in a literal `?`, and keep sanitising the
  # remainder until the whole input is valid UTF-8.
  defp sanitize_binary(bin) when is_binary(bin) do
    case :unicode.characters_to_binary(bin, :utf8, :utf8) do
      clean when is_binary(clean) ->
        clean

      {:error, ok, <<_bad::8, rest::binary>>} when is_binary(ok) ->
        ok <> "?" <> sanitize_binary(rest)

      {:incomplete, ok, _rest} when is_binary(ok) ->
        ok

      _ ->
        for <<b <- bin>>, into: <<>>, do: <<safe_byte(b)>>
    end
  end

  defp safe_byte(b) when b in 9..13 or b in 32..126, do: b
  defp safe_byte(_), do: ??

  # ==========================================================================
  # Markdown helpers
  # ==========================================================================

  # The headline is the only surviving piece of the old dedication
  # block. The longer italic paragraph was removed because `john`
  # tends to be invoked repeatedly during a debugging session and a
  # multi-line tribute grows tiresome fast. A single headline with
  # John's tagline keeps the attribution without shouting.
  #
  # The em dashes below are literal U+2014. Both rendering paths
  # handle them natively: Marcli (MDEx) treats them as plain inline
  # text, and `Cure.REPL.Markdown.render/2` decodes the source
  # byte-by-byte via a `<<c::utf8, rest::binary>>` clause, so the
  # codepoint round-trips untouched. `Cure.John.run/1` now writes
  # the rendered string via `IO.write/2`, so Mix's Unicode-aware
  # stdio no longer double-encodes the bytes.
  defp banner_md(snapshot) do
    "# Cure #{snapshot.cure.version}  \u2014  John  \u2014  \u2018What I need is visibility\u2019"
  end

  defp footer_md(width) do
    "\n" <> String.duplicate("-", max(20, div(width, 2)))
  end

  defp section(title, lines) do
    "## " <> title <> "\n\n" <> Enum.join(lines, "\n")
  end

  defp kv(key, value) do
    "  - **" <> key <> "**: " <> to_value_string(value)
  end

  defp to_value_string(v) when is_binary(v), do: v
  defp to_value_string(v) when is_integer(v) or is_float(v), do: to_string(v)
  defp to_value_string(v) when is_atom(v), do: inspect(v)
  defp to_value_string(v), do: inspect(v)

  # ==========================================================================
  # Marcli integration
  # ==========================================================================

  # Use Marcli when it can actually load its MDEx NIF. Fall back to the
  # REPL's pure-Elixir Markdown renderer otherwise (most importantly,
  # inside the `cure` escript).
  defp render_markdown(md, opts) do
    case Keyword.get(opts, :ansi, :auto) do
      false ->
        md

      _ ->
        try_marcli(md, opts) || Markdown.render(md, fallback_theme(opts))
    end
  end

  defp try_marcli(md, opts) do
    if Code.ensure_loaded?(Marcli) do
      try do
        apply(Marcli, :render, [
          md,
          [
            escape_sequences: ansi_enabled?(opts),
            newline: Keyword.get(opts, :newline, "\n")
          ]
        ])
      rescue
        _ -> nil
      catch
        _, _ -> nil
      end
    else
      nil
    end
  end

  defp fallback_theme(opts) do
    case Keyword.get(opts, :theme) do
      %Theme{} = t -> t
      name when is_atom(name) and not is_nil(name) -> Theme.for_name(name)
      _ -> Theme.default()
    end
  end

  defp ansi_enabled?(opts) do
    case Keyword.get(opts, :ansi, :auto) do
      true -> true
      false -> false
      _ -> IO.ANSI.enabled?()
    end
  end

  # ==========================================================================
  # Plumbing helpers
  # ==========================================================================

  defp app_loaded?(app) do
    Enum.any?(Application.loaded_applications(), fn {n, _, _} -> n == app end)
  end

  defp app_started?(app) do
    Enum.any?(Application.started_applications(), fn {n, _, _} -> n == app end)
  end

  defp loaded_stdlib_modules do
    :code.all_loaded()
    |> Enum.count(fn {mod, _} ->
      mod_name = Atom.to_string(mod)
      String.starts_with?(mod_name, "Cure.Std.") or String.starts_with?(mod_name, "Elixir.Cure.Std.")
    end)
  end

  defp loaded_dependency_versions do
    target_deps =
      Application.loaded_applications()
      |> Enum.map(fn {app, _desc, vsn} -> {app, to_string(vsn)} end)
      |> Enum.filter(fn {app, _} -> app in dependency_apps() end)
      |> Enum.sort_by(fn {app, _} -> Atom.to_string(app) end)

    target_deps
  end

  defp dependency_apps do
    [
      :cure,
      :metastatic,
      :marcli,
      :makeup,
      :makeup_cure,
      :md,
      :telemetry,
      :toml,
      :ex_doc,
      :excoveralls,
      :dialyxir,
      :credo,
      :oeditus_credo,
      :mdex,
      :nimble_parsec
    ]
  end

  defp safe(fun, fallback) do
    try do
      fun.()
    rescue
      _ -> fallback
    catch
      _, _ -> fallback
    end
  end

  defp safe_cwd do
    case File.cwd() do
      {:ok, cwd} -> cwd
      _ -> "?"
    end
  end

  defp safe_arch do
    case safe(fn -> :erlang.system_info(:system_architecture) end, ~c"?") do
      arch when is_list(arch) -> List.to_string(arch)
      arch when is_binary(arch) -> arch
      _ -> "?"
    end
  end

  defp bool(true), do: "yes"
  defp bool(false), do: "no"
  defp bool(other), do: inspect(other)

  defp human_bytes(n) when is_integer(n) and n >= 0 do
    cond do
      n >= 1_073_741_824 -> :io_lib.format("~.2f GiB", [n / 1_073_741_824]) |> IO.iodata_to_binary()
      n >= 1_048_576 -> :io_lib.format("~.2f MiB", [n / 1_048_576]) |> IO.iodata_to_binary()
      n >= 1024 -> :io_lib.format("~.2f KiB", [n / 1024]) |> IO.iodata_to_binary()
      true -> "#{n} B"
    end
  end

  defp human_bytes(other), do: inspect(other)

  defp human_duration(ms) when is_integer(ms) and ms >= 0 do
    total_s = div(ms, 1000)
    h = div(total_s, 3600)
    m = div(rem(total_s, 3600), 60)
    s = rem(total_s, 60)
    :io_lib.format("~2..0B:~2..0B:~2..0B", [h, m, s]) |> IO.iodata_to_binary()
  end

  defp human_duration(other), do: inspect(other)
end

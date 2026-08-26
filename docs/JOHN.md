# John

Everything-at-once diagnostic for Cure, the BEAM VM, and the project
under the cursor. `john` is a single feature exposed through three
surfaces that all funnel into one implementation:

- `mix cure.john` (`Mix.Tasks.Cure.John`)
- `cure john` (`Cure.CLI` subcommand)
- `:john` (`Cure.REPL` meta-command)

Named in tribute to **John Carbajal** (v0.30.0).

## Synopsis

```bash
mix cure.john
mix cure.john --width 120
mix cure.john --no-ansi --no-banner
mix cure.john --root path/to/project

cure john
cure john --width 120
```

```text
cure(1)> :john
```

## What it reports

`Cure.John.collect/1` gathers every observable corner of the
toolchain into a plain Elixir map (no PIDs, references, or functions)
that can be serialised, piped into a structured logger, or asserted
against in tests. Sections:

### Cure
- Version, escript entry point.
- Application loaded / started state.
- Count of loaded `Cure.Std.*` modules.
- Pipeline event-bus size.
- Type system label (`"dependent Core"`).
- UTC snapshot timestamp.

### BEAM / OTP
- Elixir / OTP / ERTS versions and the full system banner.
- Scheduler topology -- online / total / dirty CPU / dirty I/O.
- Logical-processor count.
- Process / port / atom counts, each with their limit.
- ETS table count.
- Memory breakdown: total, processes, binary, code, ETS, atom,
  system.
- Reductions, runtime, wall-clock uptime.
- Internal / external wordsize.

### System
- OS family and version, architecture, hostname.
- User, home, current directory.
- Selected environment variables: `LANG`, `TERM`, `SHELL`, `PATH`
  entry count.

### Tooling
- Resolved paths of `z3`, `git`, `make`, `cc`.
- Loaded versions of the project's declared dependencies
  (`:metastatic`, `:marcli`, `:makeup`, `:makeup_cure`, `:md`,
  `:telemetry`, `:toml`, `:ex_doc`, `:excoveralls`, `:dialyxir`,
  `:credo`, `:oeditus_credo`, `:mdex`, `:nimble_parsec`).

### Project
When `Cure.toml` is present in the chosen root:

- Name, version, root, source paths.
- Lockfile status (`missing` or `present (<size>)`).
- Full dependency table with per-entry `version` / `path` / `git`
  markers.

When the root has no `Cure.toml` the section reads
`(no Cure.toml found in the current directory)`; that is not an
error.

### Runtime
- Always reports unavailable. The `Cure.Observe.Top` supervisor/actor/FSM
  snapshot this section used to render depended on the classic-pipeline
  container runtimes, which were removed; the section is kept as a
  placeholder (`(Cure runtime not available in this context)`) pending a
  dependent-pipeline replacement.

### Doctor
- Severity counters from `Cure.Doctor.run/1` (info / warning /
  error).
- Overall `ok?` flag.

The full report still lives behind `cure doctor`; this section is
only a summary.

### Recent logs
- Tails of up to five log files, sorted by mtime, from:
  - `.cure/logs/*.log`
  - `_build/cure/logs/*`
  - `erl_crash.dump` at the project root.

## Options

### Mix task and escript subcommand

```text
--width N            target width for the section separators (default 80)
--ansi / --no-ansi   force ANSI rendering on or off
--banner / --no-banner   show or hide the dedication banner
--root PATH          treat PATH as the project root (default: cwd)
```

### `:john` inside the REPL

`:john` takes no arguments. The current session's theme and colour
setting (see `:theme` and `:color`) are threaded into the fallback
renderer, so `:john` inherits the look of everything else in the
session.

## Rendering pipeline

`Cure.John.render/2` emits CommonMark. `Cure.John.run/1` then prints
it through one of two backends:

1. **`Marcli.render/2`** -- when the richer renderer can load its
   MDEx NIF. That is the case under `mix cure.john`, `iex -S mix`,
   and any other runtime that can `dlopen` the MDEx shared object.
2. **`Cure.REPL.Markdown.render/2`** -- pure-Elixir, NIF-free
   fallback. Picked automatically when Marcli cannot load. That is
   the case inside the bundled `cure` escript archive, where the
   MDEx NIF path points at a file that does not exist on disk.

`--no-ansi` skips both renderers and emits the raw Markdown, which
is what you want in CI logs and machine parsers.

## Public API

```elixir
# Plain map; every value is serialisable.
snapshot = Cure.John.collect(root: "/path/to/project")

# Markdown string; no IO.
markdown = Cure.John.render(snapshot, width: 100, banner: false)

# collect + render + write; returns the rendered string.
Cure.John.run(root: ".", ansi: false, banner: false)
```

### Options

`collect/1`:
- `:root` -- directory to treat as the project root. Defaults to
  `File.cwd!/0`.

`render/2`:
- `:width` -- separator width (default `80`).
- `:banner` -- set to `false` to suppress the dedication banner.

`run/1`:
- every option of `collect/1` and `render/2`, plus:
- `:device` -- IO device to write to. Defaults to `:stdio`.
- `:theme` -- `Cure.REPL.Theme.t()` or a theme name
  (`:dark` / `:light` / `:mono`) for the fallback renderer.
- `:ansi` -- `true` / `false` / `:auto` (default). `:auto` honours
  `IO.ANSI.enabled?/0`.

## Tests

`test/cure/john_test.exs` exercises `collect/1`, `render/2`, and
`run/1` with and without a `Cure.toml`, with an injected log file,
and with `ansi: false` so the assertions match the raw Markdown
headers.

`test/mix/tasks/cure.john_test.exs` covers the Mix task's argument
parsing and `--width` propagation.

## Source

- `lib/cure/john.ex` -- collector, renderer, and fallback glue.
- `lib/mix/tasks/cure.john.ex` -- Mix task driver.
- `lib/cure/cli.ex` -- `cure john` subcommand dispatch.
- `lib/cure/repl.ex` -- `:john` meta-command.

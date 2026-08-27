# Cure REPL

Everything on this page landed in **v0.24.0**. Prior releases shipped an
`IO.gets`-backed line-mode loop; v0.24.0 replaces it wholesale with a
raw-mode line editor, live `Makeup`-powered syntax highlighting,
persistent history, incremental reverse search, Tab completion, a
minimal vi mode, and a `Marcli`-rendered `:help`. The architecture is
split across `Cure.REPL.{Terminal, LineEditor, History, Search,
Highlight, Theme, Completer, Render, Docs, Markdown}` so every piece
is individually testable.

The interactive REPL (`cure repl`) is a readline-grade environment for
evaluating Cure expressions, inspecting types and effects, and driving
ad-hoc experimentation with loaded modules.

Launch it with:

```sh
cure repl
```

There are two more entry points, both shipped since **v0.28.0**:

- `mix cure.repl` boots the same REPL from any Mix project that has
  `:cure` on its dependency path. Useful when you want to experiment
  against your own compiled modules without building the escript.
- `CureSiteWeb.Commands.CureRepl` (in `site/`) wraps the Mix task into
  a Yeesh command called `repl`, so visiting `/repl` on the Cure site
  (or any error page) drops you into a full REPL session inside the
  browser terminal.

The prompt reads `cure(N)>` where `N` is the expression counter. Every
submitted expression is wrapped into a synthetic `Repl.M<N>` module and
compiled + loaded on the fly; its `main/0` value is echoed back with an
ANSI-highlighted `=>` arrow.

## Key bindings (emacs mode)

### Cursor movement

- `Left` / `Right`               - move one grapheme
- `Ctrl+A` / `Home`              - beginning of line
- `Ctrl+E` / `End`               - end of line
- `Alt+B` / `Ctrl+Left`          - one word back
- `Alt+F` / `Ctrl+Right`         - one word forward

### Editing

- `Backspace` / `Ctrl+H`         - delete previous grapheme
- `Delete`                       - delete grapheme under cursor
- `Ctrl+D`                       - delete under cursor (or EOF on empty line)
- `Ctrl+K`                       - kill to end of line
- `Ctrl+U`                       - kill to start of line
- `Ctrl+W`                       - kill previous word
- `Alt+D`                        - kill next word
- `Ctrl+Y`                       - yank most-recent killed text
- `Alt+Y`                        - rotate the kill ring (after `Ctrl+Y`)
- `Ctrl+T`                       - transpose adjacent characters
- `Alt+T`                        - transpose adjacent words
- `Alt+U` / `Alt+L` / `Alt+C`    - upcase / downcase / capitalise word
- `Ctrl+_`                       - undo
- `Alt+_`                        - redo

### History

- `Up` / `Down`                  - step through history; drafts are preserved
- `Ctrl+R`                       - incremental reverse search
- `Ctrl+S`                       - forward search (while in search mode)
- `Ctrl+G` / `Esc`               - cancel search, restore original buffer

### Flow

- `Enter`                        - submit, or continue an open/indented block
- blank line                     - preserved inside an indented block; otherwise submit
- `;;` on its own line           - force-submit a multi-line buffer
- `Tab`                          - completion (meta-commands, paths, modules, keywords)
- `Ctrl+L`                       - clear screen
- `Ctrl+C`                       - abort current input; REPL stays running
- `Ctrl+D` on empty buffer       - exit

## Vi mode

`:mode vi` switches to a minimal modal editor; `Esc` enters normal
mode and `i` / `a` / `I` / `A` return to insert mode. Supported normal-mode
commands: `h`, `j`, `k`, `l`, `w`, `b`, `e`, `0`, `^`, `$`, `x`, `D`, `C`,
`u` (undo), `Ctrl+R` (redo). `:mode emacs` switches back.

You can also start directly in vi mode via `CURE_REPL_MODE=vi cure repl`.

## Meta-commands

### Types and effects

- `:t expr` (also `:type expr`)  - infer the type of `expr`
- `:effects expr`                - infer the effect set
- `:holes`                       - list typed goals retained from session definitions
- `:total name`                  - report whether a session function is kernel-certified total
- `:printdef name`               - print an authored session definition
- `:ast expr`                    - dump the parsed AST
- `:fmt expr`                    - pretty-print `expr`

### Modules and files

- `:load path`                   - compile and load a `.cure` file
- `:reload`                      - reload every previously loaded file
- `:use Mod`                     - bring `Mod`'s exports into scope
  (v0.28.0: warns and suggests the nearest stdlib module when unknown)
- `:env`                         - list all imports
- `:doc name`                    - show the docstring of `name`
- `:browse Mod`                  - browse a module's public API
- `:apropos term`                - search module, function, type, and protocol names

Indented function, match, induction, and proof blocks remain in the input
buffer while their body is deeper than the first line. `proof chain`, `have`,
`because`, `rewrite`, `simplify`, `induction`, and `case ... =>` are recognised
as continuation cues. Use `;;` to submit after the final indented line.

### Session

- `:reset`                       - forget all bindings, fresh session
- `:let name = expr`             - pin `expr` as a zero-arg session fn
  `name/0` so it survives across prompts (call as `name()`)
- `:save path`                   - write the session transcript to `path`
- `:snap save [path]`            - freeze the session to a `.cure-snap`
  file (default: `cure.snap`); see `docs/SNAP.md`
- `:snap load <path>`            - restore a session from a `.cure-snap` file
- `:snap list [dir]`             - list `.cure-snap` files in `dir` (default: `.`)
- `:edit`                        - open `$EDITOR` on the current buffer
- `:history [n]`                 - print the last `n` (default 20) entries
- `:search term`                 - non-interactive history grep
- `:clear`                       - clear screen

### Timing

- `:time expr`                   - evaluate and report elapsed wall time
- `:bench expr [n]`              - run `expr` `n` times, report min/avg/p95/max

### Appearance

- `:theme dark|light|mono`       - switch colour theme
- `:color on|off`                - toggle colour output
- `:mode emacs|vi`               - switch editing mode

### Diagnostics

- `:john`                        - print everything about Cure, the VM,
  the project, and the latest logs (see `docs/JOHN.md`)

### Quit

- `:help` / `:h`                 - show help
- `:quit` / `:q` / `:exit`       - leave the REPL

## Configuration

Programmatic options to `Cure.REPL.start/1`:

- `:history_path`  - override `~/.cure_history`; pass `nil` to disable persistence
- `:raw`           - `true`, `false`, or `:auto` (default); forces the raw-mode editor
- `:theme`         - `:dark`, `:light`, `:mono`, or `:auto`
- `:mode`          - `:emacs` or `:vi`
- `:stdlib`        - which stdlib modules to auto-import on startup. Accepts
  `:none` (default), `:all`, a single group atom, or a list of group atoms.
  Current groups are `:core`, `:collections`, `:text`, `:numeric`, `:system`,
  `:concurrency`, `:option`, `:test`, and `:network`.
- `:error_device`  - `:stderr` (default) or `:stdio`; use `:stdio` when the
  REPL is hosted behind a custom group leader (e.g. the Yeesh IOServer)
  so compiler diagnostics reach the embedder

### `.cure.repl.toml`

The REPL reads a per-user / per-project configuration file at startup,
following the same precedence as `iex` does for `.iex.exs`:

1. `./.cure.repl.toml` (project-local override)
2. `~/.cure.repl.toml` (user-wide fallback)

Both files are optional. When both are missing the REPL uses the
built-in defaults, which match the `:none` / explicit-over-implicit
rule applied across the preload stack.

The parser is `:toml` (pure-Erlang, escript-safe). Currently the only
recognised section is `[stdlib]`:

```toml
# ./.cure.repl.toml or ~/.cure.repl.toml
[stdlib]
# one of: "none" | "all" | ["core", "collections", ...]
preload = ["core", "collections"]
```

Accepted `preload` values:

- `"none"` (default) -- no stdlib modules are auto-imported.
- `"all"` -- every `Cure.Std.*` module is preloaded and added to
  `state.uses`.
- `"core"` (or any other single group name) -- preloads just that
  group.
- A TOML array of group names -- preloads the union of those groups.

See `Cure.Stdlib.Preload.known_groups/0` for the list of valid group
atoms (`:core`, `:collections`, `:text`, `:numeric`, `:system`,
`:concurrency`, `:option`, `:test`, `:network`). Every stdlib module
carries a `@group(:<group>)` module-level decorator that assigns
it to exactly one group; `docs/STDLIB.md` lists the current
membership.

## Mix task

```sh
mix cure.repl                                  # standalone, full raw-mode experience
mix cure.repl --theme=light
mix cure.repl --no-raw --error-device=stdio    # embedded under a custom group leader
mix cure.repl --no-history                     # ephemeral session, no `~/.cure_history`
```

Supported flags: `--raw` / `--no-raw`, `--theme`, `--mode`,
`--history PATH`, `--no-history`, `--error-device stdio|stderr`.
They map 1:1 to the options listed above.

## Embedding in Yeesh

`CureSiteWeb.Commands.CureRepl` (in `site/`) wraps `mix cure.repl`
with the flags needed to run inside a browser terminal
(`--no-raw --error-device=stdio --no-history --theme=dark`). Register
it on any `Yeesh.Live.TerminalComponent`:

```elixir
<.live_component
  module={Yeesh.Live.TerminalComponent}
  id="terminal"
  commands={[CureSiteWeb.Commands.CureRepl]}
  prompt="cure> "
/>
```

Then type `repl` at the Yeesh prompt to enter an interactive Cure
session. Every `IO.gets` round-trip the REPL performs is intercepted
by `Yeesh.IOServer`, turning the page into an actual Cure terminal.
Use `:quit` inside the REPL (or a bare `exit` at the Yeesh prompt) to
return to the normal Yeesh session.

Environment variables:

- `NO_COLOR`       - when set, forces the `:mono` theme
- `CURE_REPL_MODE` - `vi` to start in vi mode
- `VISUAL` / `EDITOR` - preferred external editor for `:edit`
- `TERM=dumb`      - disables colour and raw-mode editing

## History

Entries are persisted to `~/.cure_history` (atomic write-and-rename).
Consecutive duplicates are deduped and the file is capped at the most
recent 10,000 entries.

## Dependencies

The REPL builds on two companion libraries:

- [`makeup_cure`](https://hex.pm/packages/makeup_cure) -- Makeup lexer
  for the Cure language.
- [`marcli`](https://hex.pm/packages/marcli) -- Markdown-to-ANSI
  renderer and Makeup-token-to-ANSI formatter. `:help` and `:doc`
  output are pushed through `Marcli.render/2`.

%{
  title: "REPL",
  description: "The interactive Cure REPL: raw-mode line editor, live syntax highlighting, persistent history, incremental reverse search, Tab completion, and meta-commands.",
  order: 12
}
---
`cure repl` drops you into a readline-grade read-eval-print loop
backed by a raw-mode terminal, a pure-function line editor, live
`Makeup`-powered syntax highlighting, persistent history, incremental
reverse search, Tab completion, and a `Marcli`-rendered `:help`. Each
submitted expression is wrapped in a synthetic `Repl.M<N>` module,
compiled + loaded on the fly, and its `main/0` value is echoed back
with an ANSI-highlighted `=>` arrow.

```sh
cure repl
```

The prompt reads `cure(N)>` where `N` is the expression counter.

```text
cure(1)> fn add(a: Int, b: Int) -> Int = a + b
=> #Function<...>
cure(2)> :t add(1, 2)
add(1, 2) : Int
cure(3)> :bench add(1, 2) 10000
n=10000  min=1 us  avg=2 us  p95=3 us  max=42 us
```

Everything on this page landed in **v0.24.0**. Prior releases used an
`IO.gets`-backed line-mode loop; the arrow keys printed `^[[A`, there
was no persistent history, and no syntax highlighting. The
architecture is split across small modules (`Terminal`, `LineEditor`,
`History`, `Search`, `Highlight`, `Theme`, `Completer`, `Render`,
`Docs`, `Markdown`) so every piece is individually testable. See the
on-disk reference [docs/REPL.md](https://github.com/cure-lang/cure-lang/blob/main/docs/REPL.md)
for the full contract.

## When raw mode activates

The REPL defaults to raw-mode when stdin is a tty. When stdin is not
a tty (CI, pipes, `|` into `cure repl`, `TERM=dumb`), it falls back
to the legacy `IO.gets` loop automatically so test automation is
unaffected. The raw-mode path can be forced off with
`Cure.REPL.start(raw: false)`.

On raw-mode entry, the REPL captures the current `stty` state and
restores it on every exit path: normal `:quit`, EOF on an empty
buffer, `Ctrl+C` on a non-empty buffer, uncaught exception, SIGINT
and SIGTERM. Logger output is quieted to `:error` for the duration of
the session so stray `[warning]` lines from dependencies cannot
overwrite the prompt.

## Key bindings (emacs mode)

### Cursor movement

- `Left` / `Right` -- one grapheme
- `Ctrl+A` / `Home` -- beginning of line
- `Ctrl+E` / `End` -- end of line
- `Alt+B` / `Ctrl+Left` -- one word back
- `Alt+F` / `Ctrl+Right` -- one word forward

### Editing

- `Backspace` / `Ctrl+H` -- delete previous grapheme
- `Delete` -- delete grapheme under cursor
- `Ctrl+D` -- delete under cursor (or EOF on empty line)
- `Ctrl+K` -- kill to end of line
- `Ctrl+U` -- kill to start of line
- `Ctrl+W` -- kill previous word
- `Alt+D` -- kill next word
- `Ctrl+Y` -- yank most-recent killed text
- `Alt+Y` -- rotate the kill ring (after `Ctrl+Y`)
- `Ctrl+T` -- transpose adjacent characters
- `Alt+T` -- transpose adjacent words
- `Alt+U` / `Alt+L` / `Alt+C` -- upcase / downcase / capitalise word
- `Ctrl+_` -- undo
- `Alt+_` -- redo

### History

- `Up` / `Down` -- step through history; drafts are preserved
- `Ctrl+R` -- incremental reverse search
- `Ctrl+S` -- forward search (while in search mode)
- `Ctrl+G` / `Esc` -- cancel search, restore original buffer

### Flow

- `Enter` -- submit (auto-continues on unbalanced brackets)
- `;;` on its own line -- force-submit a multi-line buffer
- `Tab` -- completion (meta-commands, paths, modules, keywords)
- `Ctrl+L` -- clear screen
- `Ctrl+C` -- abort current input; REPL stays running
- `Ctrl+D` on empty buffer -- exit

## Vi mode

`:mode vi` switches to a minimal modal editor. `Esc` enters normal
mode; `i` / `a` / `I` / `A` return to insert mode. Supported normal-
mode commands: `h`, `j`, `k`, `l`, `w`, `b`, `e`, `0`, `^`, `$`, `x`,
`D`, `C`, `u` (undo), `Ctrl+R` (redo). `:mode emacs` switches back.

You can also start directly in vi mode via `CURE_REPL_MODE=vi cure repl`.

## Meta-commands

Every meta-command is prefixed with `:`. Typing `:` and pressing
`Tab` cycles through the full list.

### Types and effects

- `:t expr` (also `:type expr`) -- infer the type of `expr`
- `:effects expr` -- infer the effect set
- `:total name` -- report whether a session function is totality-certified
- `:holes` -- list holes from the last evaluation
- `:ast expr` -- dump the parsed AST
- `:fmt expr` -- pretty-print `expr`

### Modules and files

- `:load path` -- compile and load a `.cure` file
- `:reload` -- reload every previously loaded file
- `:use Mod` -- bring `Mod`'s exports into scope (v0.28.0: warns and
  suggests the closest stdlib module name when `Mod` is unknown)
- `:env` -- list all imports
- `:doc name` -- show the docstring of `name`
- `:browse Mod` -- browse a module's public API
- `:apropos term` -- search module, function, type, and protocol names

### Session

- `:reset` -- forget all bindings, fresh session
- `:defs` -- list top-level definitions (`fn`, `type`, `rec`, ...)
  entered this session
- `:printdef name` -- print a definition entered in this session
- `:let name = expr` -- pin `expr` as a zero-arg session function
  `name/0` so it survives across prompts (call as `name()`)
- `:save path` -- write the session transcript to `path`
- `:snap save [path]` (v0.32.0) -- freeze the entire REPL session
  to a `.cure-snap` file (default: `cure.snap` in the current
  directory). Captures all named declarations, up to 500 history
  entries, `use` imports, open holes, theme, and editing mode.
- `:snap load <path>` (v0.32.0) -- load and merge a session from
  a `.cure-snap` file. Definitions merge with last-writer-wins
  semantics; history is prepended; imports are unioned. An E070
  warning is emitted for each `:load`-ed path that no longer
  exists on disk; the rest of the session restores normally.
- `:snap list [dir]` (v0.32.0) -- list `.cure-snap` files found
  recursively in `dir` (default: current directory).
- `:edit` -- open `$EDITOR` / `$VISUAL` on the current buffer
- `:history [n]` -- print the last `n` (default 20) entries
- `:search term` -- non-interactive history grep
- `:clear` -- clear screen

### Timing

- `:time expr` -- evaluate and report elapsed wall time
- `:bench expr [n]` -- run `expr` `n` times, report min / avg /
  p95 / max

### Appearance

- `:theme dark|light|mono` -- switch colour theme
- `:color on|off` -- toggle colour output
- `:mode emacs|vi` -- switch editing mode

### Diagnostics

- `:john` (v0.30.0) -- print a panoramic diagnostic: Cure version,
  BEAM / OTP stats, system info, tooling, project, runtime,
  doctor summary, and the latest log tails. See the dedicated
  [John reference](https://github.com/cure-lang/cure-lang/blob/main/docs/JOHN.md)
  for the full list of sections and options.

### Quit

- `:help` / `:h` -- show help (rendered via `Marcli.render/2`)
- `:quit` / `:q` / `:exit` -- leave the REPL

## Tab completion

`Cure.REPL.Completer` handles four categories in one pass:

- **Meta-commands.** Typing `:` and pressing `Tab` cycles through
  every registered command.
- **File paths.** Inside `:load`, `:save`, `:edit`, completes
  against the filesystem.
- **Loaded modules.** Inside `:use` and `:doc`, completes against
  currently-loaded Cure modules.
- **Literal arguments and Cure keywords.** Theme / mode / colour
  argument values, and the reserved-word list elsewhere.

A single `Tab` cycles through candidates; repeated `Tab` presses
rotate. A single candidate is inserted directly.

## Live syntax highlighting

Input is piped through `Makeup.Lexers.CureLexer` and
`Marcli.Formatter` for ANSI syntax highlighting on every keystroke.
The highlighter caches by buffer hash so repeated redraws do not
re-tokenise.

Three themes ship out of the box:

- `:dark` -- default, optimised for dark backgrounds.
- `:light` -- inverted palette for light backgrounds.
- `:mono` -- no ANSI colour at all.

`:mono` is forced automatically when `NO_COLOR` is set, when stdout
is not a tty, or when `TERM=dumb`. Toggle at runtime with
`:theme dark|light|mono` or `:color on|off`.

## History

Entries are persisted to `~/.cure_history` via atomic write-and-
rename. Consecutive duplicates are deduplicated; the file is capped
at the most recent 10,000 entries.

`Up` / `Down` step through history while preserving the current
draft. Scrolling up and back down returns you to the exact buffer
and cursor position you had before exploring.

## Incremental reverse search

`Ctrl+R` opens an inverse-video status line:

```text
(reverse-i-search)`map': Std.List.map(xs, fn(x) -> x + 1)
```

- Each keystroke narrows the match.
- `Ctrl+R` again steps to the next older match.
- `Ctrl+S` flips direction to forward search.
- `Enter` accepts the match and submits it.
- `Tab` / `ArrowLeft` / `ArrowRight` accept-and-edit into the main
  buffer.
- `Ctrl+G` / `Esc` cancel and restore the original.

## Configuration

Programmatic options to `Cure.REPL.start/1`:

- `:history_path` -- override `~/.cure_history`.
- `:raw` -- `true`, `false`, or `:auto` (default); forces the raw-
  mode editor.
- `:theme` -- `:dark`, `:light`, `:mono`, or `:auto`.
- `:mode` -- `:emacs` or `:vi`.

Environment variables:

- `NO_COLOR` -- when set, forces the `:mono` theme.
- `CURE_REPL_MODE` -- `vi` to start in vi mode.
- `VISUAL` / `EDITOR` -- preferred external editor for `:edit`.
- `TERM=dumb` -- disables colour and raw-mode editing.

## Dependencies

The REPL builds on three companion Hex libraries, all maintained
alongside the compiler:

- [`makeup_cure`](https://hex.pm/packages/makeup_cure) -- Makeup
  lexer for the Cure language.
- [`makeup`](https://hex.pm/packages/makeup) -- the lexer framework
  itself; declared explicitly so `Makeup.Registry` is on the load
  path at runtime.
- [`marcli`](https://hex.pm/packages/marcli) -- Markdown-to-ANSI
  renderer and Makeup-token-to-ANSI formatter. `:help` and `:doc`
  output are pushed through `Marcli.render/2`.

None of these pull in further transitive deps, and all three are
optional at compile time: the REPL degrades gracefully when any of
them are missing from the load path (colour is dropped, help is
rendered as plain text).

## Non-goals

- No structural editing / paredit-style features -- the editor
  operates on graphemes, not s-expressions.
- No remote / networked REPL. `cure repl` drives a local BEAM VM.
- No Windows console support. The raw-mode path relies on `stty`
  and ANSI escape codes; Windows users fall back to the legacy
  line-mode loop automatically.

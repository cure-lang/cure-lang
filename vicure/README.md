# Vicure -- Cure Language Plugin for Neovim/Vim

[![Language](https://img.shields.io/badge/language-Cure-blue.svg)](https://github.com/cure-lang/cure-lang)
[![Editor](https://img.shields.io/badge/editor-Neovim%20%7C%20Vim-green.svg)](https://neovim.io/)
[![License](https://img.shields.io/badge/license-MIT-brightgreen.svg)](LICENSE)

Comprehensive syntax highlighting, indentation, filetype detection, and
LSP hook-up for the [Cure programming language](https://github.com/cure-lang/cure-lang)
in Neovim and Vim.

Target Cure version: **0.28.2** (Talk Back).

## What it covers

The syntax grammar is aligned with the canonical Cure lexer
(`Makeup.Lexers.CureLexer`) and the `highlightjs-cure` reference
implementation, so Neovim agrees with every other official Cure
highlighter on what is syntax vs. user code.

Recognised constructs:

- Containers: `mod`, `fn`, `rec`, `fsm`, `proto`, `impl`, `type`,
  `actor`, `sup`, `app`, `proof`, `use`, `local`, `extern`, `as`.
- Control flow: `if`/`then`/`else`/`elif`, `match`/`when`/`where`,
  `for`/`in`, `try`/`catch`/`finally`/`throw`, `return`/`yield`,
  `assert_type`, `rewrite`, `with`, `do`, `of`, `end`.
- Concurrency: `spawn`, `send`, `receive`, `after`, and the
  Melquiades send operator (`<-|` and the envelope glyph `✉`).
- FSM lifecycle hooks: `on_start`, `on_stop`, `on_transition`,
  `on_enter`, `on_exit`, `on_failure`, `on_timer`, `on_message`,
  `on_phase`.
- FSM transition literals: `State --event--> State`, including
  soft/hard event suffixes (`event?`, `event!`).
- Decorators / attributes: `@record`, `@derive(Json)`,
  `@deprecated`, etc.
- Typed holes: `?name` and the anonymous `?_`.
- Comments: plain `# line`, `## doc line`, and fenced
  `### multi-line ###` doc regions (with `@doctag` highlighting).
- Strings with `#{...}` interpolation and `\uXXXX` escapes.
- Regex literals (`~r/.../flags`).
- Char literals in both `'c'` and Erlang-style `?c` forms.
- Numbers with `_` digit separators across decimal, hex, binary,
  and float bases.
- Atoms (`:name` / `:name?` / `:name!`) and tuple/map prefixes
  (`%[...]`, `%{...}`).
- Operators: `->`, `-->`, `<-`, `<-|`, `=>`, `|>`, `<>`, `::`,
  `..`, `..=`, `++`, `--`, `**`, `==`, `!=`, `<=`, `>=`, `+=`,
  `-=`, `*=`, `/=`, `>>=`, `>>`, `<*>`, `<*`, `*>`, `<$`, `$>`,
  and the word operators `and`, `or`, `not`.
- Built-in types: `Int`, `Float`, `Bool`, `String`, `Atom`,
  `Bitstring`, `Binary`, `Char`, `Any`, `Unit`, `Void`, `Nat`,
  `List`, `Tuple`, `Map`, `Set`, `Pair`, `Vector`, `Option`,
  `Result`, `Pid`, `Ref`, `Sigma`, `Pi`, `Eq`, `DPair`.
- Canonical constructors: `Ok`, `Error`, `Some`, `None`, `Zero`,
  `Succ`, `Pred`, `Self`, `refl`.

Editing aids:

- 2-space `expandtab` with matching `softtabstop`/`shiftwidth`.
- `commentstring = "# %s"` so `gcc`, `Comment.nvim`, and
  `vim-commentary` pick the right comment leader.
- `iskeyword += ?,!` so `is_empty?` and `stop!` behave as single
  tokens under `w`, `e`, `*`, `#`, and `gd`.
- Trimmed `formatoptions` -- no paragraph auto-reflow, no auto-wrap,
  no forced comment leader after `o`/`O`.
- Bracket- and header-aware indentation covering every v0.28
  container shape, with `@decorator` lines treated as non-block so
  the following header still drives indent correctly.
- Automatic filetype detection for `*.cure` plus `Cure.toml` routed
  to `toml`.

## Installation

### Using [lazy.nvim](https://github.com/folke/lazy.nvim) (recommended)

Create `~/.config/nvim/lua/plugins/cure.lua`:

```lua
return {
  dir = "/path/to/cure/vicure",
  ft = "cure",
}
```

### Using [packer.nvim](https://github.com/wbthomason/packer.nvim)

```lua
use {
  '/path/to/cure/vicure',
  ft = 'cure',
}
```

### Using [vim-plug](https://github.com/junegunn/vim-plug)

```vim
Plug '/path/to/cure/vicure'
```

### Manual installation

```bash
# Neovim
mkdir -p ~/.config/nvim/{syntax,ftdetect,ftplugin,indent}
cp vicure/syntax/cure.vim   ~/.config/nvim/syntax/
cp vicure/ftdetect/cure.vim ~/.config/nvim/ftdetect/
cp vicure/ftplugin/cure.vim ~/.config/nvim/ftplugin/
cp vicure/indent/cure.vim   ~/.config/nvim/indent/

# Vim
mkdir -p ~/.vim/{syntax,ftdetect,ftplugin,indent}
cp vicure/syntax/cure.vim   ~/.vim/syntax/
cp vicure/ftdetect/cure.vim ~/.vim/ftdetect/
cp vicure/ftplugin/cure.vim ~/.vim/ftplugin/
cp vicure/indent/cure.vim   ~/.vim/indent/
```

### Verifying the install

1. Open any `.cure` file -- syntax activates automatically.
2. `:set filetype?` should report `filetype=cure`.
3. `:syntax` should list a long set of `cure*` groups.

## Syntax showcase

```text
### Multi-line fenced doc comment.
Demonstrates the surface area of modern Cure v0.28.x.
###

mod Showcase
  use Std.List
  use Std.Io as Io

  ## Records compile to BEAM maps with a `__struct__` discriminator.
  rec Point
    x: Int
    y: Int

  ## ADTs are declared with `type` and `|`-separated constructors.
  type Shape =
    | Circle(Int)
    | Square(Int)
    | Triangle(Int, Int, Int)

  ## Protocol + implementation (the v0.28 replacement for typeclasses).
  proto Stringify(T)
    fn stringify(x: T) -> String

  impl Stringify for Int
    fn stringify(x: Int) -> String = Std.String.from_int(x)

  impl Stringify for Point
    fn stringify(p: Point) -> String =
      "Point(#{p.x}, #{p.y})"

  ## Pattern matching with guards and multi-head clauses.
  fn classify(n: Int) -> String =
    match n
      0                   -> "zero"
      m when m < 0        -> "negative"
      m when m > 0 && m < 10 -> "small"
      _                   -> "big"

  ## Named and anonymous typed holes.
  fn sketch(x: Int) -> Int = ?todo
  fn another() -> Int      = ?_

  ## Regex and char literals.
  fn is_digit?(c: Char) -> Bool =
    let pattern = ~r/^[0-9]$/
    Std.Regex.is_match(pattern, c)

  fn main() -> Int = Io.println("Hello, Cure!")

## FSM with the v0.28 time-travel journal enabled.
@record
fsm TrafficLight
  Red    --timer-->     Green
  Green  --timer-->     Yellow
  Yellow --timer-->     Red
  *      --emergency--> Red

## Actor with an initial payload and a session-typed mailbox.
actor Painter with %[:idle, ""]
  on_start
    (state) -> state
  on_message
    (%[:submit, title], _state) -> %[:submitted, title]
    (:reset, _state)            -> %[:idle, ""]

## Supervision tree + OTP application.
sup Gallery
  strategy  = :one_for_one
  intensity = 3
  period    = 5
  children
    Painter as painter
    TrafficLight as lights (restart: :transient)

app Showcase
  vsn         = "0.1.0"
  description = "Vicure syntax showcase"
  root        = sup Gallery
  on_start
    (_kind, _args) -> :ok

## Propositional equality law, checked by the compiler.
proof Laws
  fn plus_zero(_n: Int) -> Eq(Int, n, n) = :cure_refl
```

## LSP integration

Cure ships a full LSP over stdio. Wire it up once and you get
diagnostics on every keystroke, hover, completion (on `.` and `:`),
go-to-definition, document symbols, code actions (including
`Add wildcard pattern` for non-exhaustive matches and "Did you mean?"
suggestions for unbound variables), and source-preserving formatting.

```lua
vim.api.nvim_create_autocmd("FileType", {
  pattern = "cure",
  callback = function()
    vim.lsp.start({
      name = "cure-lsp",
      cmd = { "cure", "lsp" },
      root_dir = vim.fs.dirname(
        vim.fs.find({ "Cure.toml", "mix.exs" }, { upward = true })[1]
      ),
    })
  end,
})
```

The `cure` escript must be on `PATH`. Build it from the Cure repo
root with `mix escript.build`.

## Formatting

The Cure LSP advertises `textDocument/formatting`, backed by
`Cure.Compiler.Formatter` -- a source-preserving formatter that
round-trip-validates its output against the original AST. Plain
`#` comments, string/regex/char literals, and doc comments are
preserved byte-for-byte. Format-on-save is safe by default.

What the formatter does:

- Normalises `\r\n` line endings to `\n`.
- Strips trailing horizontal whitespace from code lines.
- Expands leading tabs (a Cure lexer error) to two spaces.
- Collapses runs of two or more consecutive blank lines to one.
- Adds spaces around a fixed set of binary operators
  (`==`, `!=`, `<=`, `>=`, `|>`, `->`, `=>`, `<>`, `+=`, `-=`,
  `*=`, `/=`, `=`, `+`, `-`, `*`, `/`, `%`), with heuristics that
  leave unary `-`/`*`, variadic `*args`/`**kwargs`, and exponent
  signs alone.
- Ensures exactly one trailing newline.

`cure fmt --dry-run` (alias `--diff`) prints a coloured diff and
exits 1 when any file has pending changes, suitable for CI.

The destructive AST pretty printer is still reachable via
`cure fmt --aggressive`, which strips plain `#` comments and any
non-canonical whitespace in exchange for a fully canonical buffer.

To opt out of format-on-save per-buffer (without disabling the LSP
entirely), set the standard plug-in kill switches yourself in
`~/.config/nvim/after/ftplugin/cure.vim`:

```vim
let b:autoformat = 0
let b:disable_autoformat = 1
```

## Highlight groups

The plugin links every Cure group to a standard highlight group for
maximum colour-scheme compatibility. Customise selectively in your
config, e.g.:

```lua
vim.api.nvim_set_hl(0, 'cureFunctionDef',   { fg = '#61AFEF' })
vim.api.nvim_set_hl(0, 'cureKeyword',       { fg = '#C678DD' })
vim.api.nvim_set_hl(0, 'cureType',          { fg = '#E5C07B' })
vim.api.nvim_set_hl(0, 'cureAttribute',     { fg = '#D19A66' })
vim.api.nvim_set_hl(0, 'cureFsmTransition', { fg = '#56B6C2' })
vim.api.nvim_set_hl(0, 'cureHole',          { fg = '#E06C75', bold = true })
```

## Troubleshooting

### Syntax highlighting not working

1. Verify filetype: `:set filetype?` -- expect `cure`.
2. Force set: `:set filetype=cure`.
3. Reload the file: `:e`.
4. Check syntax: `:syntax` should list `cure*` groups.

### Indentation not working

Ensure filetype plugins are enabled:

```lua
vim.cmd('filetype plugin indent on')
```

### Save is reformatting or stripping comments

The default formatter (`Cure.Compiler.Formatter`, used by the LSP and
by `cure fmt`) is source-preserving; it does not touch comments or
non-code layout. If comments are disappearing, another tool is almost
certainly running `cure fmt --aggressive` or an old AST-based printer.
Diagnose:

```vim
:echo &filetype
:lua =vim.lsp.get_active_clients({ bufnr = 0 })
```

If a non-Cure LSP is attached, make sure its `root_dir`/`filetypes`
do not claim `.cure` files.

### Colours look wrong

Try a different colour scheme, or define your own overrides in the
`Highlight groups` section above. The plugin is tested with OneDark,
Gruvbox, Nord, Catppuccin, Tokyo Night, and Dracula.

## Contributing

Changes welcome -- see `CHANGELOG.md` and the Cure project on GitHub.
The canonical grammar reference is the Cure lexer
(`lib/makeup/lexers/cure_lexer.ex`) and the `highlightjs-cure`
grammar (`highlightjs-cure/src/languages/cure.js`). Keep the three
in sync.

## License

MIT, same as the rest of the Cure project.

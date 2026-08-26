# Cure support for Neovim / Vim

Detailed reference for the Vicure plugin. For the high-level tour and
installation paths, see `README.md`. Target Cure version: **0.28.2**
(Talk Back).

## What ships in this directory

```
vicure/
  ftdetect/cure.vim      " Filetype detection for *.cure and Cure.toml
  ftplugin/cure.vim      " Per-buffer editor defaults (indent, keywords, commentstring)
  indent/cure.vim        " Indent engine for container / control headers
  syntax/cure.vim        " Full Cure 0.28.x grammar
  test_syntax.cure       " Short feature tour
  test_syntax_comprehensive.cure
                         " Exhaustive fixture used to spot-check every syntax group
  README.md              " Installation and showcase
  NEOVIM_PLUGIN.md       " This file
  CHANGELOG.md           " Version history
  MODERNIZATION_SUMMARY.md
                         " Rationale for the v0.28 grammar overhaul
```

## Filetype detection

`ftdetect/cure.vim` sets the filetype to `cure` for any `*.cure`
buffer and to `toml` for `Cure.toml` project manifests. No Lua
autocommand is needed; classic vimscript detection works in both Vim
and Neovim.

## Per-buffer defaults (ftplugin)

`ftplugin/cure.vim` sets:

- `expandtab`, `shiftwidth=2`, `softtabstop=2`, `tabstop=2`.
- `commentstring = "# %s"`, so `gcc` / `Comment.nvim` /
  `vim-commentary` emit line comments with the right leader.
- `iskeyword += ?,!`, so Cure identifiers with trailing `?`/`!`
  (`is_empty?`, `stop!`) behave as single tokens in `w`, `e`, `*`,
  `#`, and `gd`.
- `formatoptions -= a t o` -- keeps automatic comment continuation
  (`r`, `c`) but drops paragraph auto-reflow, auto-wrap, and the
  forced comment leader after `o`/`O`.

Format-on-save is *not* disabled: the Cure LSP delegates to
`Cure.Compiler.Formatter`, a source-preserving formatter that
round-trip-validates its output against the original AST, so a naïve
`:w` with `format_on_save = true` is safe. If you still want to opt
out, set `b:autoformat = 0` / `b:disable_autoformat = 1` yourself in
`~/.config/nvim/after/ftplugin/cure.vim`.

## Syntax highlighting

`syntax/cure.vim` is aligned with `Makeup.Lexers.CureLexer` and
`highlightjs-cure` so the three authoritative Cure highlighters agree
on what is syntactic vs. user code.

### Keywords

| Bucket            | Keywords |
|-------------------|----------|
| Declarations      | `mod`, `fn`, `rec`, `fsm`, `proto`, `impl`, `type`, `let`, `actor`, `sup`, `app`, `proof`, `use`, `local`, `extern`, `as` |
| Control flow      | `if`, `then`, `else`, `elif`, `match`, `when`, `where`, `for`, `in`, `do`, `of`, `end`, `with`, `try`, `catch`, `finally`, `throw`, `return`, `yield`, `assert_type`, `rewrite` |
| Concurrency       | `spawn`, `send`, `receive`, `after` |
| FSM callbacks     | `on_start`, `on_stop`, `on_transition`, `on_enter`, `on_exit`, `on_failure`, `on_timer`, `on_message`, `on_phase` |
| Word operators    | `and`, `or`, `not` |
| Literals          | `true`, `false`, `nil` |
| Built-in types    | `Int`, `Float`, `Bool`, `String`, `Atom`, `Bitstring`, `Binary`, `Char`, `Any`, `Unit`, `Void`, `Nat`, `List`, `Tuple`, `Map`, `Set`, `Pair`, `Vector`, `Option`, `Result`, `Pid`, `Ref`, `Sigma`, `Pi`, `Eq`, `DPair` |
| Constructors      | `Ok`, `Error`, `Some`, `None`, `Zero`, `Succ`, `Pred`, `Self`, `refl` |

### Lexical shapes

- **Comments**: `# line`, `## doc line`, and fenced
  `### ... ###` multi-line doc regions. `TODO`, `FIXME`, `NOTE`,
  `XXX`, `HACK`, `BUG` are highlighted inside any comment, and
  `@doctag` words inside doc comments get the `Tag` group.
- **Strings**: double-quoted, with `\uXXXX` and common backslash
  escapes, and `#{...}` interpolation that re-enters the root
  grammar.
- **Regex literals**: `~r/.../flags`.
- **Char literals**: both `'c'` (single-quoted) and Erlang-style
  `?c` / `?\n`.
- **Numbers**: decimal, hex (`0x`), binary (`0b`), and floats, with
  `_` digit separators.
- **Atoms**: `:name`, `:name?`, `:name!`.
- **Holes**: anonymous `?_` and named `?identifier`.
- **Attributes**: `@record`, `@derive`, `@deprecated`, ...
- **FSM transition literals**: `State --event--> State` (event
  names may end in `?` or `!` for soft / hard events).
- **Melquiades send**: both ASCII `<-|` and the envelope glyph `✉`
  (U+2709).
- **Prefixes**: `%[...]` for tuples and `%{...}` for maps.

### Semantic heads

Dedicated syntax groups let colour schemes style the name in each
container header independently:

- `cureFunctionDef` -- the function name in `fn name(...) -> T`.
- `cureModuleHead`, `cureActorHead`, `cureSupHead`, `cureAppHead`,
  `cureProofHead` -- container names.
- `cureRecordHead`, `cureFsmHead`, `cureProtoHead`, `cureTypeHead`,
  `cureImplHead`, `cureImplFor`, `cureUseHead` -- type and
  protocol heads.
- `cureModulePath` -- dotted module paths (`Std.List`,
  `Cure.Types.Pi`).
- `cureTypeAnnotation` -- the type after `:` in `name: Type`.

## Indentation

`indent/cure.vim` increases indent after any line matching one of
the v0.28 block headers (`mod`, `fn`, `fsm`, `rec`, `proto`, `impl`,
`type`, `actor`, `sup`, `app`, `proof`, `use`, `match`, `for`,
`try`, `receive`) or ending in one of `=`, `->`, `then`, `else`,
`do`, `of`, `with`. Lines with unclosed brackets pull the next line
in one shiftwidth; a leading `)` / `]` / `}` or a leading `|`
continuation outdents accordingly.

`@decorator` lines (e.g. `@record` above an `fsm`) are treated as
non-block: the next line inherits the indent of the real header
below the attribute, so

```text
@record
fsm TrafficLight
  Red --timer--> Green
```

indents `Red --timer--> Green` under `fsm TrafficLight`, not under
`@record`.

## LSP integration

The Cure LSP is a standalone escript (`cure lsp`) that Neovim's
built-in client can start on demand:

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

Capabilities:

- Diagnostics (compile + type errors on every keystroke).
- Hover (signatures, types, inferred effects).
- Completion on `.` and `:` (keyword completions + stdlib module
  members).
- Go-to-definition (functions and modules).
- Document symbols (modules, functions, protocols, FSMs).
- Code actions -- add wildcard patterns for non-exhaustive matches,
  `Did you mean?` quick fixes for unbound variables.
- Document formatting (source-preserving; see `README.md`).

If the escript is not yet on `PATH`, build it from the Cure repo
root with `mix escript.build`.

## Testing the plugin

### Visual check

```bash
nvim vicure/test_syntax.cure                 # short feature tour
nvim vicure/test_syntax_comprehensive.cure   # exhaustive grammar fixture
```

`:set filetype?` should say `filetype=cure` and `:syntax` should list
`cure*` groups.

### Indentation check

- In `test_syntax.cure`, position the cursor inside a `fsm`, `actor`,
  `sup`, `app`, `proof`, or `match` block and press `o` -- the new
  line should indent under the header.
- Type `end` / `else` / `| pattern` at the start of a line -- the
  line should outdent to the matching header.
- Add `@record` above an `fsm` -- the transition lines below the
  `fsm` header should still align under `fsm`, not under `@record`.

## Troubleshooting

### Syntax highlighting not working

1. Ensure the files are in the correct locations (see `README.md`).
2. Restart Neovim.
3. Force reload: `:e` in the buffer.
4. Force set: `:set filetype=cure`.

### Indentation not working

```lua
vim.cmd('filetype plugin indent on')
```

### `:w` eats my comments or collapses the file

The default formatter (`Cure.Compiler.Formatter`, used by both the
LSP and `cure fmt`) is source-preserving and does not touch comments
or layout. If comments are disappearing, something is running
`cure fmt --aggressive` or a fork of the old AST-based printer on
save. Diagnose:

```vim
:echo &filetype                                  " must be 'cure'
:lua =vim.lsp.get_active_clients({ bufnr = 0 })  " only cure-lsp expected
```

One-shot opt-out for the current buffer:

```vim
:lua vim.b.autoformat = false
:lua vim.b.disable_autoformat = true
" conform.nvim:
:FormatDisable
```

## Contributing

Changes welcome. The canonical grammar lives in two places inside the
Cure repository:

- `lib/makeup/lexers/cure_lexer.ex` -- the lexer used by Makeup,
  `cure doc`, the REPL, and the Playground.
- `highlightjs-cure/src/languages/cure.js` -- the highlight.js
  grammar used by the cure-lang.org site.

Keep the Vicure syntax file in sync with both.

## License

MIT, same as the rest of the Cure project.

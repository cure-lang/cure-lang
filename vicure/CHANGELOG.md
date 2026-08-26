# Vicure Changelog

## [Unreleased] -- Cure 0.28 parity

Vicure is re-aligned with the modern Cure grammar, closing the gap
that had opened up since the plugin was last touched at Cure v0.17.
The canonical reference is now the Cure lexer
(`lib/makeup/lexers/cure_lexer.ex`) and the `highlightjs-cure`
grammar; the three should stay in lockstep.

### Added -- syntax

- Container heads: `actor`, `sup`, `app`, `proof`, `use`.
  New dedicated groups `cureActorHead`, `cureSupHead`, `cureAppHead`,
  `cureProofHead`, `cureUseHead` let colour schemes style the name
  independently.
- FSM lifecycle hooks: `on_start`, `on_stop`, `on_message`,
  `on_phase` (on top of the existing `on_transition`, `on_enter`,
  `on_exit`, `on_failure`, `on_timer`).
- Concurrency keywords: `spawn`, `send`, `receive`, `after`
  (new group `cureConcurrency`).
- Control keywords: `with`, `yield`, `assert_type`, `rewrite`,
  `do`, `of`, `end`.
- Declaration keywords: `local`, `as`, `extern` (plus `use`
  above).
- Regex literals (`~r/.../flags`) with `cureRegex` /
  `cureRegexDelim` groups.
- Erlang-style char literals (`?c`, `?\n`) alongside the existing
  `'c'` form.
- Typed holes: `?name` and anonymous `?_` (`cureHole`).
- Attribute / decorator lines: `@record`, `@derive`, etc.
  (`cureAttribute`).
- FSM transition literal `State --event--> State`, including
  `event?` / `event!` soft / hard event suffixes
  (`cureFsmTransition`).
- Melquiades send operator: ASCII `<-|` and the envelope glyph `✉`
  (U+2709).
- Power operator `**`.
- Map prefix `%{...}` recognised alongside the existing tuple
  prefix `%[...]` (unified `cureTuplePrefix`).
- Built-in types added: `Bitstring`, `Binary`, `Char`, `Any`,
  `Void`, `Pid`, `Ref`, `Map`.
- Numeric literals now accept `_` digit separators in decimal, hex,
  binary, and float bases.
- Fenced doc comments (`### ... ###`) now highlight `@tag` markers
  inside via the new `cureDocTag` group.

### Added -- indentation

- Block-header pattern extended to cover `actor`, `sup`, `app`,
  `proof`, `use`, `receive`.
- `opens_body` pattern extended to recognise lines ending in `with`
  or `of`.
- `@decorator` lines are now treated as non-block: the indent of
  the next line is driven by the real header below the decorator,
  so `@record\nfsm Foo\n  Bar --x--> Baz` indents correctly.
- `=end` added to `indentkeys` so typing `end` on a new line
  outdents to the matching header without manual reindent.

### Added -- editing defaults

- `ftplugin/cure.vim` now adds `?` and `!` to `iskeyword`, so
  `is_empty?` and `stop!` behave as single tokens under `w`, `e`,
  `*`, `#`, and `gd`. The undo hook restores `iskeyword` on
  ftplugin unload.

### Added -- filetype detection

- `ftdetect/cure.vim` routes `Cure.toml` to the `toml` filetype
  (the language proper remains on `*.cure`).

### Changed -- documentation

- `README.md` and `NEOVIM_PLUGIN.md` rewritten from the ground up
  so they describe modern Cure. The old `def` / `module` /
  `typeclass` / `trait` / `instance` / `curify` examples are gone;
  the showcase now uses `fn`, `mod`, `rec`, `fsm`, `proto`, `impl`,
  `type`, `let`, `actor`, `sup`, `app`, `proof`, `use`.
- Troubleshooting sections updated to describe the v0.28 LSP
  surface (source-preserving formatter, code actions, `Did you
  mean?` quick fixes).
- `MODERNIZATION_SUMMARY.md` replaced with a v0.28 rationale.

### Changed -- test fixtures

- `test_syntax.cure` and `test_syntax_comprehensive.cure`
  rewritten to exercise the modern grammar: containers, protocols,
  FSM transition literals, `@record`, actors, supervisors,
  applications, proofs, holes, regex/char literals, module paths,
  and the Melquiades send operator.

### Removed

- References to the pre-0.17 Cure surface (`def`, `module`,
  `typeclass`, `trait`, `instance Name(T) do ... end`,
  `impl Name for T do ... end`, `curify`, `def_erl`, `derive`,
  `class`). These keywords are no longer in the language and
  highlighting them would mis-colour modern Cure.

## [2026-04-17] -- Format-on-save re-enabled

### Changed

- The Cure LSP now advertises `textDocument/formatting` again,
  backed by `Cure.Compiler.Formatter`, a source-preserving
  formatter that round-trip-validates its output against the
  original AST. Plain `#` comments, string/regex literals, and doc
  comments survive a save.
- `ftplugin/cure.vim` no longer force-disables format-on-save. The
  `b:autoformat = 0` / `b:disable_autoformat = 1` kill switches are
  removed from the default buffer setup; if you still want to opt
  out, set them yourself in
  `~/.config/nvim/after/ftplugin/cure.vim`.
- `README.md` and `NEOVIM_PLUGIN.md` updated to describe the safe
  formatter and the `cure fmt --aggressive` opt-in for the AST
  rewrite.

## [2026-04-17] -- Format-on-save protection

### Added

- `ftplugin/cure.vim`: per-buffer editor defaults (2-space indent,
  `commentstring = "# %s"`, trimmed `formatoptions`) plus
  format-on-save kill switches (`b:autoformat = 0`,
  `b:disable_autoformat = 1`) that LunarVim, `conform.nvim`, and
  `none-ls`/`null-ls` all honour.
- `README.md`: `Formatting` section and a reformat-on-save entry
  in `Troubleshooting`.
- `NEOVIM_PLUGIN.md`: mirrors the new formatting policy and
  extends the `Troubleshooting` section with diagnostics for
  "`:w` eats my comments".

### Changed

- Manual installation snippets copy `ftplugin/cure.vim` alongside
  the syntax, ftdetect, and indent files.

## [Previous] -- Initial release

### Added

- Basic syntax highlighting for Cure.
- Keywords for the pre-v0.17 surface, including `def`, `module`,
  `fsm`, `state`, `match`, `when`.
- Operators: `->`, `|>`, `::`, arithmetic and comparison.
- String literals with interpolation support.
- Numeric literals (integers and floats).
- Comments with `TODO`/`FIXME` highlighting.
- Atoms (`:symbol` and `'quoted'`).
- Type annotations and constructors.
- FSM-specific constructs.
- Automatic indentation for blocks, filetype detection for
  `.cure` files, compatibility with standard Vim colour schemes.

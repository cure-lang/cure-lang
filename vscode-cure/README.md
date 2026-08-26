# Cure for VS Code

Cure language support for Visual Studio Code, aligned with Cure
**0.28.2** (Talk Back). Provides:

- Syntax highlighting via TextMate grammar (parity with
  `Makeup.Lexers.CureLexer` and `highlightjs-cure`).
- Language Server Protocol integration with the `cure` escript.
- Bracket matching, indentation rules, fenced-doc folding,
  comment toggling (`#` line, `###` block).

## What the grammar covers

- Container heads: `mod`, `fn`, `rec`, `fsm`, `proto`, `impl`,
  `type`, `actor`, `sup`, `app`, `proof`, `use`, `let`, `local`,
  `extern`, `as`.
- Control flow: `if`/`then`/`else`/`elif`, `match`/`when`/`where`,
  `for`/`in`, `do`/`of`/`end`, `try`/`catch`/`finally`/`throw`,
  `with`, `return`, `yield`, `assert_type`, `rewrite`.
- Concurrency: `spawn`, `send`, `receive`, `after`, and the
  Melquiades send operator (`<-|` and the envelope glyph `✉`).
- FSM lifecycle hooks: `on_start`, `on_stop`, `on_transition`,
  `on_enter`, `on_exit`, `on_failure`, `on_timer`, `on_message`,
  `on_phase`.
- FSM transition literals: `State --event--> State`, with `event?`
  / `event!` soft / hard suffixes.
- Decorators / attributes: `@record`, `@derive`, `@deprecated`, ...
- Typed holes: `?name` and anonymous `?_`.
- Comments: line (`#`), single-line doc (`##`), fenced doc
  (`### ... ###`) with `@tag` highlighting.
- Strings with `\uXXXX` escapes and `#{...}` interpolation.
- Regex literals (`~r/.../flags`).
- Char literals: `'c'` and Erlang-style `?c`.
- Numbers with `_` digit separators across decimal / hex / binary /
  float bases.
- Atoms (`:name` / `:name?` / `:name!`) and tuple / map prefixes
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

## Requirements

- VS Code 1.85 or newer.
- The `cure` escript on your `PATH` (or configure
  `cure.lsp.path` in settings). Build it from the Cure repo with
  `mix escript.build`.

## LSP features provided by the Cure server

Once the server is running, you get everything the v0.28 LSP
advertises:

- Diagnostics (compile + type errors on every keystroke, with OSC 8
  clickable file paths in supported terminals).
- Hover -- function signatures, type information, and inferred
  effects.
- Completion (triggered by `.` and `:`, with keyword and stdlib
  module-member completions).
- Go-to-definition for functions and modules.
- Document symbols -- hierarchical outline of modules, functions,
  protocols, FSMs.
- Code actions -- add wildcard pattern for non-exhaustive matches;
  "Did you mean?" suggestions for unbound variables.
- Document formatting (source-preserving; the formatter
  round-trip-validates its output against the original AST, so
  comments, regex literals, and doc comments survive a save).

## Settings

The extension adds a `Cure` section under VS Code settings:

- `cure.lsp.path` -- path to the Cure binary used to start the LSP.
  Default: `"cure"`.
- `cure.lsp.args` -- arguments passed to the binary.
  Default: `["lsp"]`.
- `cure.lsp.env` -- extra environment variables for the LSP
  process. Useful for `CURE_HYPERLINKS`, `NO_COLOR`, or pointing at
  a specific `Z3` binary. Default: `{}`.
- `cure.trace.server` -- `off` / `messages` / `verbose`. Written
  to the `Cure Language Server` output channel.

Changing any of the settings above automatically restarts the
language server.

## Commands

- **Cure: Restart Language Server** (`cure.restartLsp`) --
  stops and re-launches the LSP. Useful after rebuilding the
  `cure` escript.

## Building and running

```bash
cd vscode-cure
npm install
npm run compile
```

This produces `out/extension.js`. Press `F5` in VS Code to launch
the extension in a development host, or package it with:

```bash
npm run package       # runs `vsce package`
code --install-extension vscode-cure-0.2.0.vsix
```

## Status

Actively maintained alongside the Cure compiler. Marketplace
publication is still deferred; for now, package locally with
`vsce package` as shown above.

## License

MIT.

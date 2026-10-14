# highlightjs-cure

A [highlight.js](https://highlightjs.org) language definition for the
[Cure](https://cure-lang.org) programming language.

Cure is a dependently-typed functional language for the BEAM VM with
first-class finite state machines, typed supervision trees, OTP
applications, SMT-backed verification, and propositional equality. Its
syntax is indentation-significant and ML-influenced, with Erlang-style
bitstring segments and FSM transition literals.

The keyword lists are generated from the Cure compiler by
`mix cure.editors.sync` (keywords and contextual keywords from the lexer,
declaration heads from the standard library), the same source the Zed,
Neovim and VS Code grammars use. The rest of the grammar started as a port of
`Makeup.Lexers.CureLexer` from the
[makeup_cure](https://hex.pm/packages/makeup_cure) package.

## What it highlights

- Every reserved word of the Cure lexer, and the declaration heads
  `fsm`, `actor`, `sup`, `app`, `behavior`, `proof` when they head a
  declaration (`fsm Turnstile`).
- Contextual keywords in their positions (`have`, `requires`,
  `precedencegroup`, `infix`/`prefix`/`postfix`, `proof chain`, `because`)
  and macro-entry vocabulary (`syntax family`, `accepts`, `expands with`,
  ...).
- Control flow and pattern matching: `if` / `elif` / `else` / `then`,
  `match` / `when`, `for` / `in`, `try` / `catch` / `finally`, `throw`,
  `return`, `yield`, `end`.
- Typed holes (`?_`, `?name`) and predicate identifiers (`even?`,
  `is_empty?`).
- Lifecycle callbacks at the start of a line: `on_start`,
  `on_transition`, `on_enter`, ... (any `on_*`).
- Operators: pipe `|>`, string concat `<>`, range `..` / `..=`,
  Melquiades send `<-|` (and its unicode alias `U+2709`), binary
  generator `<-`, bitstring segment specifier `::`, augmented
  assignment `+=` / `-=` / `*=` / `/=`, FSM transitions
  `--event-->`.
- Literals: integers (including `0xFF`, `0b1010`, digit-grouped),
  floats, booleans, atoms, chars, strings with `#{...}`
  interpolation, regexes `/.../flags`, maps `%{...}`, tuples
  `%[...]`, binaries `<<...>>`.
- Comments: plain `#`, single-line doc `##`, fenced multi-line
  `### ... ###` (the last two carry `doctag` sub-scope for `@tag`
  annotations).

## Installation

### In the browser

Include highlight.js and the Cure grammar on the page:

```html
<link rel="stylesheet"
      href="https://cdn.jsdelivr.net/gh/highlightjs/cdn-release/build/styles/default.min.css">
<script src="https://cdn.jsdelivr.net/gh/highlightjs/cdn-release/build/highlight.min.js"></script>
<script src="path/to/highlightjs-cure/dist/cure.min.js"></script>
<script>hljs.highlightAll();</script>
```

The `dist/cure.min.js` bundle self-registers under the language name
`cure` when it finds a global `hljs` instance.

### With a bundler

```bash
npm install highlight.js highlightjs-cure
```

```js
import hljs from 'highlight.js/lib/core';
import cure from 'highlightjs-cure';

hljs.registerLanguage('cure', cure);
```

### Usage in Markdown / ExDoc

Tag fenced code blocks with the `cure` language:

    ```cure
    mod Hello
      fn greet(name: String) -> String = "Hello, " <> name <> "!"
      fn main() -> Int = 42
    ```

## Development

Edit `src/languages/cure.js`, except the block between the
`BEGIN/END generated` markers, then run `mix cure.editors.sync` from the
repository root. It regenerates the keyword block and builds
`dist/cure.min.js` from the source; `mix test` fails when either is stale.

## License

MIT -- see [LICENSE](LICENSE) for details.

# highlightjs-cure

A [highlight.js](https://highlightjs.org) language definition for the
[Cure](https://cure-lang.org) programming language.

Cure is a dependently-typed functional language for the BEAM VM with
first-class finite state machines, typed supervision trees, OTP
applications, SMT-backed verification, and propositional equality. Its
syntax is indentation-significant and ML-influenced, with Erlang-style
bitstring segments and FSM transition literals.

The grammar tracks the surface syntax of Cure as of **v0.28.0** (see
the Cure [CHANGELOG.md](../CHANGELOG.md)). It is a direct port of
`Makeup.Lexers.CureLexer` from the
[makeup_cure](https://hex.pm/packages/makeup_cure) package, so the
browser-side and ExDoc-side renderings stay in step.

## What it highlights

- Container declarations: `mod`, `fn`, `rec`, `type`, `proto`, `impl`,
  `fsm`, `actor`, `sup`, `app`, `proof`.
- Control flow and pattern matching: `if` / `elif` / `else` / `then`,
  `match` / `when`, `for` / `in`, `try` / `catch` / `finally`, `throw`,
  `return`, `yield`, `end`.
- Dependent-type constructs: `assert_type`, `rewrite`, typed holes
  (`?_`, `?name`), predicate identifiers (`even?`, `is_empty?`).
- FSM / actor / supervisor / application lifecycle callbacks:
  `on_start`, `on_stop`, `on_transition`, `on_enter`, `on_exit`,
  `on_failure`, `on_timer`, `on_message`, `on_phase`.
- Operators: pipe `|>`, string concat `<>`, range `..` / `..=`,
  Melquiades send `<-|` (and its unicode alias `U+2709`), binary
  generator `<-`, bitstring segment specifier `::`, augmented
  assignment `+=` / `-=` / `*=` / `/=`, FSM transitions
  `--event-->`.
- Literals: integers (including `0xFF`, `0b1010`, digit-grouped),
  floats, booleans, atoms, chars, strings with `#{...}`
  interpolation, regexes `~r/.../flags`, maps `%{...}`, tuples
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

## Versioning

The grammar version follows the Cure language version it targets. When
the Cure syntax changes, both `makeup_cure` and this package should be
updated together.

## License

MIT -- see [LICENSE](LICENSE) for details.

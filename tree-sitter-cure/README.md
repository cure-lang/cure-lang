# tree-sitter-cure

Lexical [tree-sitter](https://tree-sitter.github.io) grammar for Cure. The Zed
extension in [`../zed-cure`](../zed-cure) builds it from this directory.

It recognises Cure's tokens (keywords, identifiers, strings with `#{}`
interpolation, atoms, chars, `~r//` regexes, `#`/`##`/`###…###` comments,
operators, FSM transitions `--event-->`, decorators), declaration heads
(`mod`, `fn`, `type`, `rec`, `interface`, `fsm`, `actor`, `sup`, `app`,
`macro`, ...) and line boundaries. It does not model the indentation-structured
block grammar: macro vocabulary (`syntax family`, `accepts`, `expands with`,
family fields) is recognised by the highlight queries from its position at the
start of a line.

Token rules mirror `Cure.Compiler.Lexer` (`lib/cure/compiler/lexer.ex`); when
the lexer changes, update `grammar.js` and regenerate.

## Development

```sh
cd tree-sitter-cure
npx tree-sitter-cli generate          # regenerates src/ (commit it)
npx tree-sitter-cli parse ../lib/std/app.cure
npx tree-sitter-cli query queries/highlights.scm ../lib/std/app.cure
```

Every `.cure` file in the repository should parse without `ERROR` nodes:

```sh
find .. -name '*.cure' -not -path '*/deps/*' -not -path '*/_build/*' \
  | xargs npx tree-sitter-cli parse --quiet --stat
```

`queries/` is the source of truth for the editor queries; `zed-cure` carries
copies under `languages/cure/`.

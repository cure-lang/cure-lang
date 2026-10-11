# tree-sitter-cure

Lexical [tree-sitter](https://tree-sitter.github.io) grammar for Cure. The Zed
extension in [`../zed-cure`](../zed-cure) and the Neovim plugin in
[`../neovim-cure`](../neovim-cure) build it from this directory.

It recognises Cure's tokens (keywords, identifiers, strings with `#{}`
interpolation, atoms, chars, `~r//` regexes, `#`/`##`/`###…###` comments,
operators, FSM transitions `--event-->`, decorators), declaration heads
(`mod`, `fn`, `type`, `rec`, `interface`, `fsm`, `actor`, `sup`, `app`,
`macro`, ...) and line boundaries. It does not model the indentation-structured
block grammar: macro vocabulary (`syntax family`, `accepts`, `expands with`,
family fields) is recognised by the highlight queries from its position at the
start of a line.

Token rules mirror `Cure.Compiler.Lexer` (`lib/cure/compiler/lexer.ex`); when
the lexer changes, run `mix cure.editors.sync` from the repository root: it
regenerates `keywords.js` (keywords and contextual keywords from the lexer,
declaration heads from the standard library), the Vim syntax file's and
highlight.js's keyword lists, and reports what still needs regenerating here
and in `vscode-cure/`. `mix test` fails while anything is out of date.

After a grammar change lands on `main`, bump `rev` in
`zed-cure/extension.toml` to that commit; Zed fetches the grammar from it.

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
copies under `languages/cure/` and `neovim-cure` carries `highlights.scm`
under `queries/cure/`.

# Vicure Modernization Summary -- Cure 0.28

## Context

The previous `MODERNIZATION_SUMMARY.md` described an alignment with a
long-retired Cure surface that used `def`, `module`, `typeclass`,
`trait`, `instance`, `curify`, and `derive`. Modern Cure (v0.17
onwards, currently v0.28.2) has none of those keywords and instead
uses a small, consistent container vocabulary: `mod`, `fn`, `rec`,
`fsm`, `proto`, `impl`, `type`, plus the OTP layer (`actor`, `sup`,
`app`) and proof containers (`proof`).

This document captures what changed in Vicure to bring the plugin
from Cure v0.17 to v0.28.2.

## Grammar reference

The three authoritative Cure highlighters must agree on what is
syntactic vs. user code:

1. `Makeup.Lexers.CureLexer` (`lib/makeup/lexers/cure_lexer.ex`) --
   used by `cure doc`, the REPL, the Makeup-driven Playground, and
   every tool that embeds Makeup.
2. `highlightjs-cure/src/languages/cure.js` -- used by
   [cure-lang.org](https://cure-lang.org).
3. `vicure/syntax/cure.vim` -- this plugin.

Vicure's syntax file is now a direct translation of the highlightjs
grammar's keyword buckets, lexical shapes, and operator table, so
pull requests that change the language in any of the three places
have a clear sibling to keep in sync.

## What changed in Vicure

### Syntax file (`syntax/cure.vim`)

- Target bumped from `Cure 0.17.0 (Proofs & Polish)` to
  `Cure 0.28.2 (Talk Back)`.
- Keyword buckets rebuilt to cover every Cure 0.28 keyword:
  - **Declarations** now include `actor`, `sup`, `app`, `proof`,
    `use`, `local`, `extern`, `as` in addition to the existing
    `mod`, `fn`, `rec`, `fsm`, `proto`, `impl`, `type`, `let`.
  - **Control flow** gained `with`, `do`, `of`, `end`, `yield`,
    `assert_type`, `rewrite`.
  - **Concurrency** is a new bucket with `spawn`, `send`,
    `receive`, `after`.
  - **FSM callbacks** gained `on_start`, `on_stop`, `on_message`,
    `on_phase`.
  - **Built-in types** gained `Bitstring`, `Binary`, `Char`, `Any`,
    `Void`, `Pid`, `Ref`, `Map`.
- Fenced doc comments (`### ... ###`) now highlight `@tag` markers
  inside via the new `cureDocTag` group.
- Regex literals (`~r/.../flags`) are recognised.
- Erlang-style char literals (`?c`, `?\n`) are recognised alongside
  the existing `'c'` form.
- Typed holes (`?name`, anonymous `?_`) are a new group.
- `@decorator` / `@record` attribute lines are a new group.
- FSM transition literals (`State --event--> State`) are a new
  group; event names may end in `?` or `!` for soft / hard events.
- The Melquiades send operator is recognised in both ASCII
  (`<-|`) and glyph (`✉`, U+2709) forms.
- Power operator `**` added.
- Numeric literals accept `_` digit separators in decimal, hex,
  binary, and float bases.
- Map prefix `%{...}` recognised alongside tuple prefix `%[...]`.
- New semantic-head groups for `actor`, `sup`, `app`, `proof`,
  and `use` container names, so colour schemes can style them
  independently.

### Indent file (`indent/cure.vim`)

- Block-header pattern extended to `actor`, `sup`, `app`, `proof`,
  `use`, `receive` on top of the existing
  `mod|fn|fsm|rec|proto|impl|type|match|for|try`.
- `opens_body` pattern now matches lines ending in `with` or `of`.
- A new helper walks back past `@decorator` lines to find the real
  driving header, so `@record\nfsm Foo\n  Bar --x--> Baz` indents
  the transition correctly under the `fsm` header.
- `=end` added to `indentkeys` for on-the-fly outdenting.

### Editing defaults (`ftplugin/cure.vim`)

- `iskeyword` now includes `?` and `!`, so identifiers with those
  suffixes (`is_empty?`, `stop!`) behave as single tokens under
  `w`, `e`, `*`, `#`, and `gd`. The undo hook restores it on
  ftplugin unload.

### Filetype detection (`ftdetect/cure.vim`)

- `Cure.toml` project manifests are routed to the `toml` filetype.

### Documentation

- `README.md` and `NEOVIM_PLUGIN.md` rewritten from scratch. The
  old showcase described an unrelated dialect (typeclasses /
  traits / instances / curify); the new one shows modern Cure
  with containers, protocols, FSM transition literals,
  decorators, holes, actors, supervisors, applications, and
  proofs.
- Keyword table and lexical-shape table in `NEOVIM_PLUGIN.md`
  serve as a quick-reference for schema authors.

### Test fixtures

- `test_syntax.cure` -- short tour of every major Cure 0.28
  feature, suitable for a quick visual check.
- `test_syntax_comprehensive.cure` -- exhaustive fixture with
  every lexical shape and keyword the syntax file recognises.
  Useful when you want to spot-check that a recent change did not
  break anything else.

## Colour-scheme compatibility

All highlight-group links target standard Vim groups
(`Statement`, `Keyword`, `Type`, `Function`, `Operator`, `String`,
`Number`, `Float`, `Comment`, `SpecialComment`, `Special`,
`Constant`, `Boolean`, `Character`, `StorageClass`, `Structure`,
`PreProc`, `Include`, `TypeDef`, `Delimiter`, `Tag`, `Todo`), so any
reasonable colour scheme picks up sensible colours without manual
tweaks. See the `Highlight groups` section in `README.md` for
examples of how to override individual Cure groups.

## Verification checklist

When making further grammar changes, re-run this checklist:

- Open `test_syntax.cure` in Neovim. Every major shape should be
  highlighted and correctly indented.
- Open `test_syntax_comprehensive.cure`. Every keyword, operator,
  literal, decorator, hole, and FSM transition should be visually
  distinct.
- Compare against `highlightjs-cure/src/languages/cure.js` -- the
  keyword buckets, lexical shapes, and operator table must agree.
- Compare against `lib/makeup/lexers/cure_lexer.ex` -- any keyword
  added there must also appear here.

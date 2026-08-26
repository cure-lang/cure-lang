# Documentation Tooling

Cure ships three documentation surfaces that all read from the same
`.cure` sources:

- `cure doc` -- static HTML generator (ExDoc-like two-pane layout).
- `Cure.REPL.Markdown` -- ANSI renderer for `:doc` / `:help` in the
  REPL.
- `/stdlib` and `/stdlib/:module` on the Cure website.

v0.29.0 (*Make Documentation Great*) is the release that re-aligned
all three around a shared Markdown-to-HTML pipeline driven by the
NIF-free `:md` library and Makeup for syntax highlighting.

## `cure doc`

### CLI

```text
cure doc [path|dir] [-o DIR]
         [--title TITLE] [--main SLUG] [--extras PATH]
```

- Default discovery walks `lib/**/*.cure` and `lib/std/*.cure`. A
  positional path narrows the walk; passing a file compiles a single
  module.
- `--output-dir DIR` (`-o`) sets the output directory. Default:
  `_build/cure/doc`.
- `--title`, `--main`, `--extras` override the corresponding keys of
  the `[doc]` table in `Cure.toml`. `--extras` is repeatable.

### Output layout

```text
_build/cure/doc/
  assets.js                # filter / theme-toggle bundle
  style.css                # shared stylesheet
  index.html               # landing page (module index or a pinned main)
  <extra-slug>.html        # one per [doc].extras entry
  <module-slug>.html       # one per module extracted from .cure sources
```

The tree is self-contained. It can be zipped up, served from any
static host, or pointed at `file://` for offline browsing.

### The two panes

- **Sidebar (left).** Built once and embedded on every page. Lists
  every entry in `[doc].extras` followed by every module, optionally
  grouped via `[doc.groups_for_modules]`. A keyboard-focusable filter
  input (press `/`) narrows the list in place. A theme toggle honours
  `prefers-color-scheme` by default.
- **Content (right).** Extras render as the Markdown-to-HTML output
  of `Cure.Doc.Markdown.to_html/1`. Module pages render the module's
  extracted doc map: a title, the module-level docstring, a local
  table of contents, and one anchored block per public function,
  type, and protocol.

### Anchors

Every public symbol inside a module page gets a stable anchor so deep
links remain valid across rebuilds:

- `#fn-<name>` -- public functions.
- `#type-<name>` -- `type` aliases and ADTs.
- `#interface-<name>` -- `interface` declarations.

When `[doc].source_url` is configured (or the built-in Cure site
falls back to the repository's GitHub path), each entry also carries a
"View source" link pointing at the corresponding line in the
`.cure` file.

## `Cure.toml [doc]` section

All keys are optional; adding them progressively enhances the output.

```toml
[project]
name    = "my_lib"
version = "0.1.0"

[doc]
main       = "README"
title      = "My Library"
extras     = ["README.md", "CHANGELOG.md"]
logo       = "priv/logo.svg"
source_url = "https://github.com/you/my_lib"
source_ref = "main"

[doc.groups_for_modules]
"Core"        = ["MyLib.Core"]
"Accessories" = ["MyLib.Json", "MyLib.Http"]
```

### Keys

- `main` -- slug for the landing page. Matches either an extra slug
  (`README` -> `README.md`) or a module name (`MyLib.Core`). When
  unset, the landing page is the module index.
- `title` -- title shown in the sidebar header. Falls back to
  `<ProjectName> Documentation`.
- `extras` -- array of relative Markdown paths. Each path is expanded
  against the directory that contains `Cure.toml`, so the same
  configuration works whether `cure doc` runs from the project root
  or a sub-directory.
- `logo` -- optional path / URL shown next to the sidebar title.
- `source_url` / `source_ref` -- GitHub prefix used for
  per-function / per-module source links.
- `[doc.groups_for_modules]` -- ordered mapping from group name to a
  list of module names. Modules that do not appear in any group fall
  into a trailing `"Other"` bucket so nothing is dropped silently.

### Normalisation

The TOML parser and documentation-config normalisation live in
`Cure.Project`. The `[doc]` and `[doc.groups_for_modules]` tables become a
plain map shape that the generator consumes directly:

```elixir
%{
  main: String.t() | nil,
  title: String.t() | nil,
  extras: [String.t()],
  logo: String.t() | nil,
  source_url: String.t() | nil,
  source_ref: String.t() | nil,
  groups_for_modules: [{String.t(), [String.t()]}]
}
```

## `Cure.Doc.Markdown`

`Cure.Doc.Markdown.to_html/1` is a thin wrapper over `Md.generate/1`
with two escript-safe extras on top of the upstream behaviour:

### Placeholder interpolation

`{{cure_version}}` and `{{cure_vversion}}` are substituted before
parsing, so release-sensitive copy can live inside docstrings without
a preprocess step at each call site. `{{cure_vversion}}` is just the
bare version prefixed with `v`.

```markdown
Install with `mix escript.install hex cure {{cure_vversion}}` to get
this exact build.
```

### Fenced-code syntax highlighting

When a fenced code block carries a known language, its contents are
run through Makeup and emitted with the same CSS classes the Phoenix
site uses. Known languages:

- `cure`   -- `Makeup.Lexers.CureLexer`
- `elixir` -- `Makeup.Lexers.ElixirLexer`
- `erlang` -- `Makeup.Lexers.ErlangLexer`

Unknown languages round-trip as `<pre class="cure-doc-code"><code
class="language-<lang>">...</code></pre>` so downstream CSS can still
target them with a stable selector.

### Why `:md`?

Earlier revisions routed HTML rendering through `MDEx`, the Rust-NIF
backing `marcli`. Inside an escript archive the NIF cannot be loaded
(the `.so` lives under `priv/native/*` inside a single-file archive
that the dynamic loader cannot mmap), so `cure doc` would fail on
every invocation outside `mix run`. Switching to `:md` is enough on
its own to keep the escript binary production-ready.

## REPL Markdown renderer

`Cure.REPL.Markdown.render/2` renders docstrings to ANSI text for the
REPL's `:help` and `:doc` commands. v0.29.0 promotes it from a flat
line-by-line renderer to a small block-aware parser that handles:

- ATX headings (`#`, `##`, `###`).
- Fenced code blocks (` ```lang...``` `) and indented code blocks
  (four-space / tab indent).
- Bullet lists (`-`, `*`) and numbered lists (`1.`, `2.`, ...).
- Blockquotes (`> `).
- Inline backtick code, `**bold**`, `*italic*`, and `[text](url)`
  links (rendered as `text (url)`).
- Horizontal rules (`---`, `***`) and blank-line paragraph
  separation.

The renderer is NIF-free (unlike the richer Marcli path) so `:help`
keeps working inside the escript archive.

## `/stdlib` on the Cure website

The Cure website (`site/` in the repo) ships an auto-generated
standard-library browser that mirrors `cure doc` output.

- `site/lib/cure_site/stdlib.ex` walks `cure/lib/std/*.cure` at
  compile time and builds a doc map per module via
  `Cure.Compiler.Lexer.tokenize/2`, `Cure.Compiler.Parser.parse/2`,
  and `Cure.Doc.Extractor.extract/1`. A curated
  `@groups_for_modules` list drives the sidebar grouping; unlisted
  modules fall into a trailing `"Other"` bucket.
- `CureSiteWeb.StdlibController` serves `/stdlib` (index) and
  `/stdlib/:module` (single-module page). The templates live under
  `site/lib/cure_site_web/controllers/stdlib_html/`.
- The old hand-written `site/priv/pages/standard-library.md` is
  gone; `/standard-library` 301-redirects to `/stdlib` via
  `CureSiteWeb.RedirectController`.

The site uses the same `Cure.Doc.Markdown.to_html/1` as `cure doc`,
so the two views of the same stdlib module are visually consistent.

## Writing docstrings

### `##` blocks and blank-line merging

`##` comments above a definition (`mod`, `fn`, `type`, `rec`,
`interface`) attach as its docstring. Consecutive `##` blocks separated
by a blank-line gap (or by plain `#` comments that the lexer drops)
are merged into a single Markdown body with a paragraph break
between blocks -- so a module-level docstring can read as natural
prose:

```text
mod Std.List
  ## Eager, persistent, singly-linked lists.
  ##
  ## Every operation recurses over cons cells; there are no runtime
  ## arrays underneath.
  ##
  ## ## Examples
  ##
  ## ```cure
  ## use Std.List
  ##
  ## [1, 2, 3]
  ##   |> Std.List.map(fn(x) -> x * 2)
  ##   |> Std.List.sum()              # => 12
  ## ```
```

### `###` fenced multi-line docstrings

The `###` fence still works for cases where a docstring would
otherwise collide with indentation-sensitive parent containers.
Leading indentation common to every body line is stripped:

````cure
mod MyApp
  ###
  Longform prose here.

  Fenced code blocks work as you would expect:

  ```cure
  MyApp.run()
  ```
  ###
  fn run() -> Atom = :ok
````

### `## Examples` blocks

By convention every module-level docstring ends with an
`## Examples` section containing fenced `cure` blocks that actually
compile. The Cure stdlib enforces this end-to-end: the examples in
`lib/std/*.cure` round-trip through `mix cure.compile_stdlib`, and
four high-traffic `Std.Core` functions (`compose`, `map_ok`,
`and_then`, `map_option`) carry per-function examples on top of the
module-level block.

Repository Markdown and `.cure` docstrings follow the same rule. `mix cure.check.docs`
compiles every fence whose info string begins with the complete word
`cure`, including attributed forms such as `` ```cure path=demo.cure ``.
A fence may add `expr` or `declarations` when its shape is ambiguous.
An intentionally rejected example names its expected diagnostic, for example
`` ```cure E093 ``. The checker requires that exact error code and fails if a
different error appears, the example starts compiling, or the compiler crashes.

An example that compiles but cannot be written warning-free names the warning
instead, for example `` ```cure W000 ``. That fence passes only when the
snippet compiles *and* emits the warning, so the warning stays part of the
documented behaviour rather than being waived; if the compiler later stops
emitting it, the fence fails and the example gets revisited. Macros that lift
whole modules are the usual reason to need this — see `docs/MACROS.md` §7.

Multiple diagnostic tags on one fence are invalid, whether `E` or `W`. An
incomplete design sketch is not Cure source and uses a plain `text` fence.
Ordinary `cure` fences always have to compile with no warnings at all.

## See also

- `docs/TUTORIAL.md` Chapter 13 -- walk-through for adding
  docstrings, `Examples`, and `[doc]` configuration to your own
  project.
- `docs/LANGUAGE_SPEC.md` -- doc-comment grammar (including
  blank-line merging and Markdown body rules).
- `docs/STDLIB.md` -- standard-library reference; every module ships
  with an `## Examples` block.
- `lib/cure/doc/html_generator.ex` -- authoritative `cure doc`
  implementation.
- `lib/cure/doc/markdown.ex` -- the shared Markdown-to-HTML pipeline.
- `lib/cure/repl/markdown.ex` -- the REPL's Markdown-to-ANSI
  renderer.

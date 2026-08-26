# Playground

## Current status

The pre-0.34 Playground is not a supported compiler surface. Its LiveView still
calls the deleted classic checker and code generator, so it does not provide
authoritative checking or safe evaluation for the current language.

Use one of the supported interactive surfaces instead:

- `cure repl` for checked local exploration;
- `cure check <file>` for dependent elaboration without emission;
- `cure run <file>` for checked compilation and `main/0` execution;
- editor/LSP integrations for structured diagnostics and holes.

## Required dependent port

A restored browser Playground must use the same headless dependent front end,
canonical module loader, standard-library/prelude discovery, structured
diagnostics, and validated emission path as the CLI. It must not call a
compatibility checker or bypass Core validation. Evaluation must retain process
isolation, output capture, memory limits, and a hard deadline.

Until that port lands, `/playground` should be treated as unavailable rather
than as a weaker classic-only compiler.

## Historical implementation

The v0.27/v0.28 site provided a debounced editor, Makeup highlighting, a
classic-checker panel, and a sandboxed BEAM evaluator. Those UI ideas remain
useful, but their checker and emitter integration was removed with the classic
pipeline.

## Running locally

The site lives under `site/` inside the repository. Boot it with:

```sh
cd site
mix setup            # first time
mix phx.server
```

The documentation site still builds locally, but the `/playground` compiler
integration remains unavailable until the dependent port described above.

## Architecture

- `CureSiteWeb.PlaygroundLive` in `site/lib/cure_site_web/live/` is the stale
  classic integration point.
- `CureSiteWeb.Eval` in `site/lib/cure_site_web/eval.ex` is the stale compiler
  and sandbox integration point.
- Route wired at `/playground` via `CureSiteWeb.Router`.
- HTML formatter: `Makeup.Formatters.HTML.HTMLFormatter`.
- Lexer: `Makeup.Lexers.CureLexer` (from the `makeup_cure` Hex
  package).
- The port must call the same dependent compiler service as the command line;
  the site must not maintain a separate checker.

# cure_forge

An application example built from transparent Cure macros.

The source files define `app CureForge`, `sup Forge.Root`, and four
lifted actor modules. Each declaration expands to ordinary `behaviour`,
`callback`, and `lift module` syntax, then goes through checked `beam_ops` and
the common BEAM writer. The compiler does not contain Forge-specific or
actor/supervisor/application object classes.

## Layout

```text
cure_src/forge_app.cure       app CureForge
cure_src/forge_root.cure      sup Forge.Root
cure_src/{metrics,logger,queue,pool}.cure  actor declarations
lib/cure_forge.ex              Elixir facade
lib/cure_forge/application.ex  Mix application bridge
```

## Build and test

```bash
cd examples/cure_forge
mix deps.get
mix test
```

`compile_cure` emits all lifted units before the Elixir application starts.
Application phases and supervisor children are represented by ordinary Cure
values and callbacks; startup uses the transparent process algebra.

See [`docs/APP.md`](../../docs/APP.md), [`docs/SUPERVISION.md`](../../docs/SUPERVISION.md),
and [`docs/STDLIB.md`](../../docs/STDLIB.md).

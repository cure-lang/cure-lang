# cure_colony

A small supervision-tree example using the transparent Cure macros.

`cure_src/worker.cure` and `cure_src/echo.cure` define lifted actor modules;
`cure_src/colony.cure` defines the lifted supervisor. The declarations use the
same parser, recursive macro expansion, elaborator, and BEAM writer as ordinary
Cure modules. There is no actor or supervisor compiler class in the example.

## Layout

```text
cure_src/worker.cure        actor Worker
cure_src/echo.cure          actor Echo
cure_src/colony.cure        sup Colony
lib/cure_colony.ex          Elixir facade
lib/cure_colony/application.ex  Mix application bridge
```

## Build and test

```bash
cd examples/cure_colony
mix deps.get
mix test
```

The `compile_cure` task emits the lifted modules before Elixir compilation.
The supervisor child declarations are ordinary checked `ChildSpec` values and
start through the standard supervisor boundary.

See [`docs/SUPERVISION.md`](../../docs/SUPERVISION.md),
[`lib/std/actor.cure`](../../lib/std/actor.cure), and
[`lib/std/supervisor.cure`](../../lib/std/supervisor.cure).

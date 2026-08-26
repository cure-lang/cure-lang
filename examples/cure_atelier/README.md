# cure_atelier

Showcase project for Cure v0.27.0 ("See Your System Breathe") and
v0.28.0 ("Talk Back").

This example exercises every v0.27.0 and v0.28.0 surface in a single,
self-contained project.

## v0.27.0 features

- **`Std.CRDT.ORSet`** for the exhibit's tag set (so the curator and
  painter can add and remove tags concurrently without coordination).
- **`Std.Time.Instant`** for wall-clock timestamps on every curation
  event, exercised via the `:cure_std_time` runtime.
- **`Std.Regex`** for input validation of human-supplied titles.
- **`Cure.Protocol`** verifies a session-typed `Atelier.Gallery`
  protocol between `Painter` and `Curator` roles; the test suite
  asserts the happy path passes `Cure.Protocol.verify/1` and a
  deliberately broken variant surfaces `PROTO001`.
- **`Cure.Temporal`** specifies liveness properties over an
  `Exhibit` FSM (`always eventually Open`, `never (Open and Closed)`)
  and exercises both passing and failing variants.
- **`Cure.OTel`** with the bundled `MemoryExporter` captures every
  actor send and FSM transition; the test suite asserts spans are
  produced end-to-end.
- **`Cure.Term.Hyperlink`** is exercised indirectly via the shared
  compiler error path.
- **`cure top`** and **`cure trace`** are runnable against the
  spawned actors -- see the `docs` section of the test output.

## v0.28.0 features

- **`@record` on `Exhibit` FSM** -- `cure_src/exhibit.cure` carries
  the new `@record` decorator, so every `Closed -> Open -> Sold`
  transition is journaled to `Cure.Observe.Journal`. The test suite
  asserts that journal entries are recorded and that
  `Cure.Observe.Replay.replay/3` reproduces the same state sequence
  against a fresh FSM instance.
- **`cure bless` walkthrough** -- see "Fixing type errors interactively"
  below.
- **Parser error recovery (E063)** -- a `describe` block verifies that
  a file with two parse errors still emits both diagnostics in one pass.

## Fixing type errors interactively with `cure bless`

To see `cure bless` in action, introduce a deliberate type error in
`curator.cure` (for example change `n + 1` to `"one" + 1`), then run:

```sh
cure bless cure_src/curator.cure
```

The assistant will display the error, explain what went wrong (the `+`
operator expects numeric operands, got `String` and `Int`), and offer to
remove the return type annotation or widen it to `Any`. Answering `y`
applies the fix in-place and re-runs the checker to confirm the file is
now clean.

## Layout

```text
examples/cure_atelier/
  README.md           -- this file
  Cure.toml           -- project metadata
  mix.exs             -- Elixir harness
  cure_src/
    painter.cure      -- actor containing the painter role
    curator.cure      -- actor containing the curator role
    exhibit.cure      -- @record-annotated FSM (v0.28.0)
  test/
    cure_atelier_test.exs   -- end-to-end suite
    test_helper.exs
```

## Running

```sh
mix deps.get
mix compile_cure      # compiles cure_src/*.cure into _build/cure/ebin
mix test              # runs the showcase suite
```

To check formatting in CI (exits 1 if any file is unformatted):

```sh
cure fmt cure_src/ --dry-run
```

## Feature walk-through

Every `describe/2` block in `test/cure_atelier_test.exs` maps to one
feature. Read the tests top-to-bottom for the most compact tour.

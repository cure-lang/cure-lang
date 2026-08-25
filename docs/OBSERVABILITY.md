# Observability

v0.27.0 introduced three complementary observability surfaces for
running Cure applications: the `Cure.OTel` span bridge, the
`cure top` snapshot tool, and the `cure trace` typed tracer. `cure top`
has since been removed (see below); `Cure.OTel` and `cure trace` remain.

## Cure.OTel

`Cure.OTel` is an OpenTelemetry-compatible span emitter on top of
`Cure.Pipeline.Events`. It is started explicitly from an
application's `on_start` callback:

```elixir
Cure.OTel.start(
  exporter: &MyApp.Exporter.record/1,
  service_name: "my_app",
  sample_ratio: 1.0
)
```

When started, the bridge subscribes to every stage of the pipeline
event registry (`:lexer`, `:parser`, `:type_checker`, `:codegen`,
`:registry`) and re-emits each event as a span. Macro expansion and
lifted-module emission are reported through the generic parser, elaborator,
and writer stages.

Library code can also open manual spans through `Cure.OTel.span/3`:

```elixir
Cure.OTel.span("cure.process.send", %{"inbox" => "Ping.Pong"}, fn ->
  pid |> send(message)
end)
```

Nested spans share a trace id and chain through `:parent_span_id`.
`Cure.OTel.inject_ctx/1` / `extract_ctx/1` propagate the span chain
across process boundaries -- typically inside the metadata carried
alongside a Melquiades Operator `<-|` message.

If `opentelemetry_api` is on the load path, spans are forwarded
there. Otherwise, the bundled `Cure.OTel.MemoryExporter` captures
every span in a public ETS table (`:cure_otel_spans`) usable from
tests and from the REPL via `:all/0`, `:flush/0`, `:count/0`.

## cure top (removed)

`cure top`, `mix cure.top`, and `Cure.Observe.Top` no longer exist. The
snapshot depended on the classic-pipeline's supervisor/actor/FSM container
runtimes, which were removed when the compiler moved to the dependent-only
pipeline (see the Unreleased section of `CHANGELOG.md`); `Cure.John`'s
Runtime section, which used to embed the same snapshot, now always reports
it unavailable (see `docs/JOHN.md`). The section below documents the
pre-removal design for reference.

`cure top` used to print a point-in-time snapshot of every running
supervisor and lifted process module:

```sh
mix cure.top           # or `cure top` when the escript is installed
watch -n1 mix cure.top # low-tech live view
```

Output:

```text
cure top  2026-04-21T15:20:00Z              procs=85  reductions=12345
Supervisors (1)
  - Atelier.Root  (2 children)
Processes (2)
  - painter_1 (Atelier.Painter)  mbox=0  mem=9184  reds=301
  - exhibit_1 (Atelier.Exhibit)  state=Closed  events=0  uptime_ms=42
```

## cure trace

`cure trace` attaches a typed tracer to a single `Module.fun/arity`
triple:

```sh
mix cure.trace Cure.Std.List.map/2 --duration 10
```

Every call and return is formatted through `inspect/2` and, when a
compile-time signature is known, annotated with the Cure type of
each argument and the declared effect set:

```text
call #PID<0.212.0> Cure.Std.List.map/2([1, 2, 3] : List(Int), #Function<...>)  [pure]
return #PID<0.212.0> Cure.Std.List.map/2 -> [2, 4, 6] : List(Int)
```

Signatures are stored in `Cure.Observe.Trace.Registry`, an ETS table
intended to be populated by the type checker during a project compile.
Nothing currently calls `register_signature/4` (the classic checker's hook
for this was removed with the rest of that checker), so in practice every
call currently falls back to plain `inspect/2`.

## See also

- `examples/cure_atelier/` -- end-to-end exercise of all three
  surfaces plus the v0.27.0 stdlib and temporal checker.
- [`docs/TEMPORAL.md`](TEMPORAL.md) and [`docs/PROTOCOL.md`](PROTOCOL.md)
  for the verification side of the v0.27.0 toolkit.

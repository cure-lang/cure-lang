# Profile-Guided Optimisation (PGO)

> **Deferred after 0.33.** The profile format and v0.31 design are retained
> here for the future optimizer release, but profile-guided specialization is
> not part of the current dependent compiler. Checked dependent Core must
> become the optimizer input before these flags and decisions are restored.

The v0.31.0 PGO pipeline lets the optimiser see how a program behaves
at runtime and steer per-function decisions accordingly. Hot paths get
more inlining and a stronger SMT budget; cold paths stay small and
defer to the generic clone.

PGO is **strictly opt-in**: the optimiser never reads a profile unless
the caller asks for it via `--pgo` (or the equivalent
`Cure.Optimizer.optimize(ast, pgo: ...)`). An existing
`_build/cure/pgo/` directory is ignored by default.

## Pipeline at a glance

1. The user runs the program with `cure run --record-profile`. The
   `Cure.PGO.Recorder` GenServer is started; per-MFA call counts and
   wall-clock timings accumulate in a public ETS table.
2. On exit, the recorder serialises one
   `Cure.PGO.Profile` per module to
   `_build/cure/pgo/<module>.profile`.
3. On a subsequent `cure compile --pgo`, the optimiser loads every
   profile, partitions functions into a hot set (top 80% of total
   cost) and a cold set, and feeds the summary to the inliner and
   the SMT translator.

## Recorder API

`Cure.PGO.Recorder` is a `GenServer` that owns a public ETS table.
The `tick/*` operations are direct ETS writes for minimal overhead;
they are also no-ops when the recorder is not running so test
fixtures can import instrumented code without crashing.

* `Cure.PGO.Recorder.tick({mod, fun, arity})` -- bump the call counter.
* `Cure.PGO.Recorder.tick_with_us(mfa, micros)` -- bump call counter +
  wall-clock time.
* `Cure.PGO.Recorder.tick_branch(mfa, site_id)` -- bump a branch
  counter for an `if` / `match` arm. `site_id` is an integer the
  codegen pass allocates per arm.
* `Cure.PGO.Recorder.tick_smt(mfa, queries, micros)` -- accumulate
  SMT solver work attributable to an MFA.
* `Cure.PGO.Recorder.flush(dir)` -- write current state to disk and
  clear the table.
* `Cure.PGO.Recorder.flush_all(dir)` -- write without clearing.

## On-disk format

Each `_build/cure/pgo/<module>.profile` is a compressed Erlang
external term encoding a `Cure.PGO.Profile` struct:

```elixir
%Cure.PGO.Profile{
  module: :"Cure.MyMod",
  version: 1,
  captured_at: 1735126400000,        # ms since epoch
  entries: [
    %{
      mfa: {:"Cure.MyMod", :foo, 1},
      def_hash: 12345678,
      calls: 8421,
      total_us: 9_273_412,
      branches: %{0 => 6041, 1 => 2380},
      smt_queries: 0,
      smt_total_us: 0
    },
    ...
  ]
}
```

`def_hash` is `:erlang.phash2/1` of the live `function_def` meta
keyword list. The PGO loader compares it against the current source
to detect stale profiles; mismatched entries are dropped and the
classification falls back to `:default`.

## Loader

`Cure.PGO.load(dir, opts)` reads every `*.profile` file under `dir`
and returns a `%Cure.PGO{}` summary:

```elixir
%Cure.PGO{
  modules: %{atom => Profile.t()},
  hot: MapSet.t(mfa()),
  cold: MapSet.t(mfa()),
  branches: %{mfa() => %{site_id => count}},
  smt: %{mfa() => %{queries: int, total_us: int}},
  hot_threshold: 0.8,
  stale: []
}
```

Hot/cold partitioning sorts entries by `total_us` (or `calls` when
no timing is available) and walks the cumulative cost: every entry
that pushes the running fraction below `hot_threshold` joins the
hot set; the rest join the cold set. The default threshold is
`0.8` (the 80/20 split).

The loader emits two pipeline events:

* `:pgo_loaded` -- `{module, entry_count}` per profile file.
* `:pgo_load_failed` -- `{path, reason}` when a single file fails to
  decode. The build continues with the remaining profiles.

## Optimiser integration

When `Cure.Optimizer.optimize(ast, pgo: pgo, module: mod)` is called,
the inliner classifies each `function_def` via
`Cure.PGO.classify(pgo, mod, name, arity, meta)`:

* `:hot` -- size cap relaxed to **12**. More aggressive inlining.
* `:cold` -- size cap tightened to **2**. Effectively disables
  inlining for cold functions.
* `:default` -- pre-PGO behaviour. Size cap stays at **5**.

`Cure.SMT.Solver.check_sat/3` accepts the same hint:

* `:hot` doubles the Z3 timeout (`6 s` instead of `3 s`) and asks
  Z3 to use a stronger arithmetic solver via
  `(set-option :smt.arith.solver 6)`.
* `:cold` halves the timeout (`1.5 s`) and conservatively returns
  `:sat` on `:unknown` so flaky cold-path queries don't block
  compilation.
* `:default` is the pre-v0.31.0 behaviour.

## CLI surface

* `cure run --record-profile [--profile-dir DIR]` -- runs the program
  with the recorder attached and flushes profiles on exit.
* `cure profile run <file.cure>` -- alias for the above.
* `cure profile show [--top N] [--profile-dir DIR]` -- pretty-print
  hot/cold counts and the top N hot functions.
* `cure profile clear [--profile-dir DIR]` -- delete every
  `*.profile` under `DIR`.
* `cure compile --pgo [--profile-dir DIR]` -- load profiles and
  pass them to the optimiser. **PGO is strictly opt-in** -- without
  this flag, an existing profile directory has no effect.

## Pipeline events

* `:pgo_loaded` -- per profile file.
* `:pgo_load_failed` -- a profile failed to decode.
* `:pgo_stale` -- an entry's `def_hash` did not match the current
  source.

## Caveats

* The recorder relies on direct calls to `Cure.PGO.Recorder.tick/1`.
  v0.31.0 ships the data layer + optimiser integration; automatic
  codegen instrumentation (so every compiled function emits a tick at
  entry) is reserved for a follow-up release. Until then, users who
  want PGO-driven optimisation today can:
    1. Drive ticks manually from a top-level harness.
    2. Generate profiles from `Cure.Profiler` events.
    3. Hand-craft profiles for high-traffic modules.
* The pattern-aware SMT encoder ships the `:hot` arithmetic-solver
  switch and the budget-aware timeout machinery; richer
  trigger-pattern emission for `forall` predicates is reserved for a
  follow-up release.

# `cli` & `job` — Command-Line Apps and Supervised Background Work

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§7.3); built as `macro`s (§5). Both target **HOST** (full BEAM /
generic-unix) — no AtomVM constraints apply. `cli` is the first program most
new users actually write; `job` is the BEAM guarantee ("your job cannot
silently die") surfaced as one keyword.

---

## 1. Purpose

Two service-domain macros that share a spine: **typed declarations at the
boundary, ordinary total Cure inside.** `cli` declares commands, flags, and
positional args with types and refinements, and generates the parser, help,
and completion — argument validation and compile-time checking are the *same
rule stated once*. `job` declares scheduled, retrying background work that
compiles onto `sup`, so a crashed job is restarted, retried per policy, and —
only after exhaustion — dead-lettered with a notification, never silently
lost. Neither surface shows a dependent type; both are pure refinements +
newtypes over machinery that already exists.

## 2. `cli` — surface

```cure
cli Shrink
  ## shrink — compress images without visible quality loss.

  flag verbose: Flag                              # global; -v / --verbose
  flag config:  ExistingPath = "~/.shrink.toml"   # validated newtype (§2.2)

  cmd compress
    ## Compress one or more images in place.
    arg  files:   Many(ExistingPath)
    flag quality: {q: Int | q >= 1 and q <= 100} = 85
    flag count:   Int = 1
    run(args) =
      args.files |> each(fn(f) -> Image.compress(f, args.quality))

  cmd serve
    ## Run as a compression daemon.
    flag port: {p: Int | p >= 1 and p <= 65535} = 8080
    run(args) = Server.start(args.port)
```

Surface rules:

- **`cmd`** declares a command (nestable for subcommands: `cmd remote.add`).
  **`arg`** is positional, **`flag`** is named; `Flag` is the bare boolean
  switch type. Every parameter carries an ordinary type + optional refinement
  + optional default (`count: Int = 1`); a parameter without a default is
  required, and the parser says so.
- **`run(args)`** is the per-command handler. `args` is a **typed record**
  manufactured by the elaborator from the declarations (hiding principle 1:
  users write facts, the macro writes the type). Inside `run`, every field
  already satisfies its refinement — no re-checking, ever.
- **`##` doc comments** are the help text. Generated from the declaration:
  the parser, `--help` at every level, shell completion scripts
  (bash/zsh/fish), and a man-page-ish `cure <tool> help <cmd>`.

### 2.1 One rule, one message

A refinement is checked twice — at compile time when a literal flows in, at
parse time when `argv` does — but it is **one registered explainer**. The
runtime parser renders the *same* message the compile-time explainer would:

```
error: --port must be between 1 and 65535, got 70000

  shrink serve --port 70000
                      ^^^^^
```

Single source of truth by construction: the parser's error path calls the
macro's explainer with the same failure shape (`{:refinement_failed, …}`)
the elaborator would report. There is no second, hand-written validation
message to drift.

### 2.2 `ExistingPath` — the honest effectful refinement

`file: ExistingPath` looks like a refinement but its predicate touches the
filesystem — it cannot be a static refinement and we do not pretend it is.
It is a **validated newtype**: a type whose only constructor is the
parse-time check.

- At arg-parse, the parser runs the check (`fs.exists?`) and either
  constructs an `ExistingPath` or emits the boundary error ("no such file:
  ./phto.jpg — did you mean ./photo.jpg?").
- Inside `run`, the type *records that validation happened*. Functions taking
  `ExistingPath` never re-stat defensively; functions taking `String` cannot
  receive one by accident.
- This is parse-don't-validate at the process boundary: **validated at the
  boundary, trusted inside.** No dependent machinery beyond newtypes — the
  honesty is the point (the file may still vanish between parse and use;
  `ExistingPath` claims *was valid at parse*, not *is valid forever*, and the
  docs say so).

The same pattern is open to users (`newtype WritableDir from String via
check_writable`), which quietly teaches the whole design style.

## 3. `job` — surface

```cure
job Backup
  ## Nightly database snapshot to S3.
  schedule "0 3 * * *"                        # cron literal — compile-checked
  retry    max 5, backoff exponential(base: 30s, jitter: 0.2)
  overlap  :skip
  timeout  10m

  run = Db.snapshot() |> S3.put(cfg.bucket)

job Heartbeat
  schedule every 5m                            # units durations (§6)
  retry    max 3, backoff constant(10s)
  overlap  :queue
  timeout  30s

  run = Http.post(cfg.monitor_url, status())
```

Surface rules:

- **`schedule`** — a cron expression or `every <duration>` (reusing units
  literals). Cron strings are **validated at compile time**: the macro
  parses them internally (a `parse`-macro grammar), so an invalid cron
  string never ships. Timezone: **UTC-only in v1** — stated on the tin;
  local-tz semantics are ledgered (§8.4).
- **`retry`** — `max` attempts and a backoff family: `constant(d)`,
  `linear(d)`, `exponential(base:, jitter:)`. Jitter is a fraction; the
  refinement `{j: Float | j >= 0.0 and j <= 1.0}` catches `jitter: 20`.
- **`overlap`** — what happens when a run is due while the previous run is
  still going: `:skip` (drop this tick), `:queue` (run after), `:concurrent`
  (let them race — you asked for it).
- **`timeout`** — a run exceeding it is killed and counts as a failed
  attempt, entering the retry policy like any crash.

### 3.1 Machinery — riding `sup`

A `job` compiles onto the first-class `sup` container: the scheduler is a
supervised fsm holding next-fire state; each run is a supervised child. The
lifecycle is the pitch:

> crash → supervised restart → retry policy (backoff, bounded attempts) →
> after exhaustion, a **dead-letter record** (job name, args, error, attempt
> history) + a **notification hook** (`on_dead_letter(fn(d) -> …)`).

There is no path on which a failure evaporates. Observability comes with it:
last-run status and duration are queryable per job, and `cure jobs` prints
the table:

```
$ cure jobs
JOB        SCHEDULE     LAST RUN          STATUS   DURATION  NEXT
Backup     0 3 * * *    2026-07-08 03:00  ok       42.1s     2026-07-09 03:00
Heartbeat  every 5m     2026-07-08 09:35  ok       0.3s      09:40
Reindex    every 1h     2026-07-08 09:00  retrying (2/5)     10:00
```

## 4. Explainers

Per the parent's §4 template (*what you wrote → why the domain forbids it →
what to write instead*):

- **Invalid cron literal** (compile time):

  ```
  error: "0 3 * * 8" is not a valid cron expression
    --> jobs.cure:4
    Day-of-week runs 0–6 (Sunday = 0). Did you mean "0 3 * * 0"?
    That fires: Jul 12 03:00, Jul 19 03:00, Jul 26 03:00 (UTC).
  ```

  The next-3-fire-times line ships when the corrected suggestion is cheap to
  compute (it is — the schedule evaluator already exists); it turns a syntax
  correction into a semantic confirmation.

- **Refinement-failed argument** (runtime, §2.1) — the shared explainer.

- **Overlapping-job warning** (lint): when a schedule's interval is shorter
  than the job's typical duration, warn — "`Reindex` runs every 1m but its
  runs average 90s; with `overlap :queue` the queue grows without bound."
  Needs a duration estimate, so it is a lint fed by observed history or an
  optional `expect_duration` hint — the estimate source is ledgered (§8.7).

## 5. `check` integration (shipped templates)

- **`cli`: parser round-trip.** From each command's refinements, generate
  *valid* arg vectors (refinement generators — `port` draws from 1..65535)
  and *invalid* ones (draw just outside each bound, wrong arity, unknown
  flags). Valid vectors must parse to the typed record with the declared
  values; invalid vectors must produce exactly the declared boundary error.
  Users get a parser test suite they never wrote.
- **`job`: policy simulation.** A generated flaky job function (fails k
  times, then succeeds — k drawn up to and beyond `max`) run under the
  declared policy must terminate within the bounded attempt count, with
  backoff delays matching the family (jitter within its fraction). And the
  overlap property: under `:skip`, a simulated slow run plus due ticks
  **never** yields two concurrent instances.

## 6. Relations

- **units** — `every 5m`, `timeout 10m`, `backoff constant(10s)`: durations
  are the units macro's literals, nothing new.
- **parse** — the cron grammar is a `parse` declaration internally, and cli
  arg tokenization may reuse it; both macros are `parse` consumers, not
  reimplementers.
- **config** — jobs read `config`; CLI flags can override config values.
  **Precedence, stated once: flags > environment > config defaults.** The
  cli macro generates the override wiring so no user writes it.
- **schema** — job persistence and dead-letter records are natural `schema`
  tables when persistence lands (§8.2).
- **workflow** — a job is a fine *driver* for a workflow (nightly tick
  advances `Order` reducers); the job owns the clock, the workflow owns the
  state.
- **toolchain (dogfood)** — `cure` itself (`new`/`run`/`flash`/`jobs`/…)
  should eventually be self-hosted on the `cli` macro. If our own CLI
  can't be expressed in it, the macro isn't done — the §5.4 dogfood test,
  applied to services.

## 7. Open decisions (ledger)

1. **Interactive prompts** — ask for missing required args instead of
   erroring? v1: no (scriptability first; a prompt in CI is a hang). Revisit
   with a `prompt: true` opt-in per arg.
2. **Job persistence across restarts** — v1 is in-memory (schedules re-derive
   from source; in-flight runs are lost on node restart, honestly
   documented). Schema-backed persistence (durable dead-letters, missed-run
   catch-up policy) is the follow-up.
3. **Distributed / singleton jobs** — one-runner-per-fleet needs cross-node
   coordination (leader election or lock). Defer to the `fleet` relation;
   v1 jobs are per-node and say so.
4. **Local timezone + DST** — "03:00 America/New_York" hits the
   skipped/repeated-hour problem twice a year. UTC-only v1; a `tz:` option
   needs explicit skip/repeat semantics before it ships.
5. **Completion-script installation UX** — `cure <tool> completions zsh`
   printing to stdout vs. detecting and writing the user's shell config
   (mutating dotfiles is invasive; print-only is forgettable).
6. **Structured output modes** — `--json` on generated commands (and on
   `cure jobs`) for scripting; interacts with help generation and error
   rendering, so it's a macro feature, not per-app boilerplate.
7. **Overlap-lint duration estimate** (§4) — observed history vs. an
   `expect_duration` declaration vs. both; and where history lives before
   persistence (§8.2) exists.

## 8. Non-goals

- **No argparse-ecosystem parity.** No plugin middleware, no dynamic command
  registration, no hooks-around-parsing. The macro covers the declarative
  90%; the rest is ordinary Cure in `run`.
- **Not a cron daemon replacement.** Jobs live inside a running Cure app
  (that's what makes `sup` supervision real); nothing here manages system
  crontabs or survives the app it belongs to.
- **No TUI framework.** Terminal UIs are `view`-for-terminal, a someday of
  the web trio — not this spec. `cli` prints text and exits.

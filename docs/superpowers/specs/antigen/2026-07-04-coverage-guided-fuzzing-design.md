# Coverage-Guided Fuzzing for the Cure Kernel — Design

**Date:** 2026-07-04
**Status:** Design approved (operator: "both, staged … we want the real thing, get it made").
**Branch:** `autopilot/antigen-tier-b` (stay on it — no new worktree per sub-feature).

## Goal

Give Antigen **real code-coverage feedback over the trusted kernel** (`Cure.Core.*`),
the capability libFuzzer provides and Antigen currently lacks. Today's "coverage"
is a *semantic* feature-key (`Antigen.Coverage.key/1` → `{ctors, depth-bucket,
flags, label}`) used for corpus dedup + a health/bias loop; there is **no
instrumentation of the kernel's actual code paths**, so we cannot answer "which
lines of `Kernel`/`Normalise`/`Conv` has a campaign exercised, and which are
cold." This sub-project adds that, in two stages.

## Non-goals

- **No TCB edits.** Coverage is measurement infrastructure; it lives in Antigen /
  tooling. `:cover` instruments modules for measurement but does not alter kernel
  semantics — the assays still run the real kernel logic. (Consistent with spec §6
  "no `Cure.*` edits in assays"; this is a new tooling layer, not an assay.)
- **Not replacing the semantic coverage key.** The feature-key stays (it drives
  dedup + health). Code coverage is an *additional*, orthogonal signal.
- **No concurrency with the normal test suite.** `:cover` is **node/VM-global,
  not per-Erlang-process**: `cover:compile_beam/1` loads an instrumented version
  of a module via the code server, which replaces that module for *every*
  process on the node, and only one cover session/database exists per node
  (`cover:start/0` is a singleton). Coverage runs are therefore a dedicated,
  serial mode, never mixed into `mix test` — and slower, since instrumented
  code carries per-line counter increments.
- **v1 granularity is line-level.** `:cover.analyse(mod, :coverage, :line)` and
  `:cover.analyse(mod, :coverage, :clause)` are equally native — same function,
  same cost, different `Level` atom — so this is a **report-content choice, not
  an availability constraint**: `:clause` level returns per-clause `{Cov,NotCov}`
  as aggregate executable-line *counts* keyed by `{M,F,A,C}` (e.g. "clause 2 of
  `foo/3` has 2 cold lines"), not the identities of which lines those are; `:line`
  level gives the exact cold `{M,Line}` set the v1 report wants to print. Branch
  granularity (per-`case`-clause, below function-clause level) genuinely isn't a
  native `:cover` level and is the real future stretch.

## Architecture

Two phases, staged. Phase 1 ships and is useful on its own; Phase 2 reuses Phase
1's harness as its feedback signal.

### Phase 1 — Coverage measurement + report

A `:cover`-based harness (`Antigen.Cover`, new module) that:

1. **Instruments a fixed TCB module set** — `Cure.Core.Kernel`, `Normalise`,
   `Conv`, `Eval`, `Quote`, `Inductive`, `Serialize`, `Certificate`. (`Certificate`
   is included because its own moduledoc self-identifies as part of the trusted
   kernel — the termination check the kernel re-runs before certifying a global
   for δ-reduction — and carries real decision-procedure branching, not just
   data plumbing. `Term`, `Context`, `Universe`, `Value`, `Builtins` are excluded:
   they are data-structure/accessor modules with negligible branching, so
   line-coverage over them would mostly measure "was this record field read,"
   not kernel decision-path exercise. The list is a single `@cover_modules`
   constant, reviewed against what the assays actually call.)
2. **Runs a campaign** — reuse `Runner.explore/1`'s generation + assay loop
   (unchanged) with cover active around it.
3. **Analyses** line-level coverage via `:cover.analyse(mod, :coverage, :line)`
   after the campaign — this returns, per executable line, a `{Cov, NotCov}` pair
   that is always `{1,0}` (executed at least once) or `{0,1}` (never executed);
   summing `Cov` over all lines gives covered/total, and the **cold lines** are
   exactly those with `NotCov = 1`. (`:cover.analyse(mod, :calls, :line)` would
   give raw per-line call counts instead of this covered/not-covered pair — not
   needed for v1, since "never executed" is all the cold-line report requires.)
4. **Emits a report** — a deterministic markdown report
   (`docs/superpowers/reports/antigen-kernel-coverage.md` or a `--out` path):
   per-module summary table + a "cold lines" section (grouped by enclosing
   function for readability — matching the v1 line-level scope in Non-goals;
   NOT clause-level, see Risk #5).

**Isolation & lifecycle:** `:cover.start/0` → `:cover.compile_beam(@cover_modules)`
→ run → `:cover.analyse` → `:cover.stop/0`. `:cover.stop/0` unloads the
instrumented modules and restores the ordinary ones node-wide, so a crash between
`compile_beam` and `stop` must be handled (e.g. `after`/`try` around the campaign)
or the instrumented (slower, counter-carrying) modules stay loaded for the rest
of that VM's life. Handle the node/VM-wide, serial nature explicitly (one cover
run at a time, node-wide — see Non-goals). Cover-compiled modules are slower;
that's acceptable for a dedicated coverage campaign. The normal suite is never
run under cover.

**Entry point:** `mix antigen cover [--count N | --budget Nm] [--out PATH]`
(a new subcommand of the existing `mix antigen` task, alongside `generate`).

### Phase 2 — Coverage-guided loop (libFuzzer-style)

**Entry point (extends Phase 1's):** `mix antigen cover --guided [--precise]
[--edge-corpus PATH] [--count N | --budget Nm] [--out PATH]`. `--guided` turns on
the loop (step 4); `--precise` forces per-challenge attribution for every round
(see step 1); `--edge-corpus` overrides the edge-minimal corpus path (step 2).

Turn new-coverage into the **feedback signal** that steers generation.

1. **Per-input coverage delta.** Capture the coverage set a challenge triggers.
   Two modes, used together, not as alternatives — batch is a cheap *gate*,
   precise is the *attribution* step behind it:
   - **Batch (default outer loop)** — accumulate over a round (`:cover.analyse`
     once per round, not per challenge), attribute new edges to the round as a
     whole; cheap, coarse. This alone tells you *whether* a round was interesting,
     never *which* challenge in it was — it cannot drive step 2's per-input
     banking by itself.
   - **Precise (inner re-attribution, always runs when a round is interesting)**
     — once batch flags a round as having hit ≥1 new edge, re-run that round's
     challenges individually with `:cover.reset/0` + run + `:cover.analyse` to
     find exactly which challenge(s) caused it. `--precise` additionally forces
     this per-challenge mode for *every* round (not just interesting ones),
     trading speed for exact per-input attribution from the start — useful for
     debugging the loop itself, not the default operating mode.
2. **Interesting-input corpus.** An input identified as the (or a) cause of a
   round's new coverage — via the batch-then-reattribute sequence above, or
   directly under `--precise` — is "interesting" → banked to an **edge-minimal
   corpus** (keyed by its covered-line set, deduped via the existing
   `Antigen.Corpus`, stored at a new `--edge-corpus PATH`, default
   `test/antigen/edge_corpus.sexp`). This is the libFuzzer corpus model: keep the
   smallest input covering each new edge (the existing `Triage.minimize` provides
   the "smallest" step).
3. **Feedback into generation.** Antigen's generator is *generative* (mode-directed
   term synthesis), not byte-mutation, so there is no direct analogue of "take
   this exact interesting input and perturb it" — the guided step instead biases
   *which generative machinery runs next* toward the neighborhood of what proved
   interesting, via two existing (unmodified) mechanisms:
   - `Generators.Mutation`'s `gnat/1` filler already reads a closed-term pool from
     the process dictionary (`:antigen_seed_pool`, spec §3) and occasionally
     substitutes a banked term for a fresh one. Banking an interesting input into
     that pool (as a `:typed_term` seed, keyed by its checked type — the same
     shape `SeedPool.load/1` already expects) makes future mutants more likely to
     be *built around* it, at whatever Nat-typed filler slot a given operator/
     `deepen` wrapper happens to need. This is genuine reuse of existing crossover,
     but it is *indirect and probabilistic* — it does not target the specific
     kernel lines the interesting input hit, only increases the odds that
     interesting structure recurs somewhere in a later mutant.
     **Mechanism note:** `Process.get(:antigen_seed_pool)` is populated exactly
     once, at `mix antigen` startup, from the seeds file on disk — nothing in the
     reused code refreshes it mid-run. For a bank event to influence draws within
     the *same* guided run (not just a later, separate invocation), the guided
     loop must itself re-`Process.put(:antigen_seed_pool, ...)` a refreshed pool
     (e.g. via `SeedPool.load/1` against the edge-corpus path, or an in-memory
     merge) after each bank. This is new orchestration logic in `Antigen.Cover` /
     `Runner`, not a change to `SeedPool` itself — "no change" in Components/files
     refers to `seed_pool.ex`'s source, not to how often it gets invoked.
   - Edge-novelty replaces the health-metric as the round bias signal (parallel to
     today's `draw_biased` reweighting, but keyed on new-edge yield per generator
     group), which steers which of the 11 top-level generators (`default_gen`'s
     frequency mix) get drawn more, without needing per-input mutation at all.

   Because the coupling between "an input hit new coverage" and "the next draw is
   more likely to hit *nearby* coverage" is indirect for both mechanisms, this
   is the weakest link in Phase 2 — see Risk #3, which this section does not
   presume is resolved.
4. **The loop:** draw (generative + corpus-derived) → run under cover → new-edge
   delta → if new: bank + boost that lineage's weight; else discard → repeat until
   budget or plateau (K rounds with no new edge).
5. **Jackpot integration:** an input that hits new coverage AND trips an assay is a
   soundness bug in previously-cold kernel code. This is **one report, not two**:
   Phase 1's reused `explore/1` body already calls `Report.write_infection` once
   per violating challenge (its existing behavior, unchanged); the guided loop's
   only addition is passing the challenge's coverage delta into that *same* call
   (as part of the `health` map `write_infection/4` already takes), so the
   existing infection report gains a coverage-delta line rather than a second,
   separate report being written for the same violation.

## Components / files (indicative — the plan pins exact paths)

- **New:** `lib/antigen/cover.ex` — the `:cover` harness (instrument, run,
  analyse, cold-line extraction). Pure tooling.
- **New:** `lib/antigen/cover_report.ex` — render the coverage report (markdown).
- **Modify:** `lib/mix/tasks/antigen.ex` — add the `cover` subcommand + Phase-2
  `--guided`/`--precise`/`--edge-corpus` flags (see each phase's Entry point).
- **Modify:** `lib/antigen/runner.ex` — Phase 2: an edge-novelty bias hook
  alongside the existing health-based `draw_biased` (guarded behind the guided
  mode; the default explore path is unchanged).
- **Reuse (no change):** `Generators.Mutation`, `Triage`, `Corpus`, `SeedPool`.

## Testing strategy

- **Phase 1:** unit-test `Antigen.Cover` on a *tiny* controlled target — instrument
  a known module, run inputs that hit a known subset of lines, assert the analysed
  cold set matches. Assert report rendering is deterministic. Assert cover is
  stopped/cleaned up even on error (no leaked cover state into the suite).
- **Phase 2:** unit-test the interesting-input decision (an input with a new edge
  is banked; one with no new edge is discarded), the edge-minimal dedup, and the
  bias reweighting (a generator group that yields new edges gains weight). Test the
  jackpot path (new-edge + violation → infection report carries both).
- **Isolation guard:** a test asserting a cover run leaves `:cover` stopped and the
  module set restored (so the normal async suite is unaffected).
- **No coverage run inside the normal `mix test`** — the harness tests use a
  minimal fixture module, not the full kernel campaign.
- **`Antigen.CoverTest` (and any other test file that starts/stops `:cover`) uses
  `use ExUnit.Case, async: false`**, matching this repo's existing convention for
  global-state tests (`test/antigen/mix_task_test.exs`, the `TriageWiring` case in
  `runner_test.exs`). This is not optional: since `:cover` is a single node-wide
  session (previous point), two cover-touching test files running concurrently
  under `async: true` would race the same `cover_server`, not just pollute an
  unrelated suite.

## Risks / open questions (for spec-review to harden)

1. **`:cover` + already-loaded/compiled modules.** The kernel modules are compiled
   into `_build`; `:cover.compile_beam` re-instruments from the `.beam` (requires
   the beam to carry `debug_info`, which this project's default Mix compile
   config already produces — no `strip_beams` step runs outside release builds).
   Escript/AtomVM perturbation is a **non-issue, not just an expectation**:
   `cover:compile_beam/1` loads the instrumented module in-memory only, via
   `code:load_binary/3` — it never writes a `.beam` file to disk, so it cannot
   touch the artifacts `mix escript.build` or the AtomVM pipeline read from
   `_build`. The remaining open item is narrower: confirm each module in
   `@cover_modules` actually is cover-compilable (i.e. was compiled with
   `debug_info`) in the target `MIX_ENV`, which the Phase-1 harness should assert
   at startup rather than fail silently on.
2. **Per-input cost.** Under the default (batch-gates, precise-re-attributes)
   model, cost is: one `:cover.analyse` per round always (cheap) + one
   `:cover.reset`/run/`:cover.analyse` cycle per challenge **only** for rounds
   batch already flagged as interesting. Early in a campaign, most rounds are
   likely interesting (the edge set is still growing), so early-campaign cost
   can approach `--precise`'s per-challenge cost anyway; it should cheapen as the
   edge set saturates and interesting rounds become rare. `--precise` forces the
   expensive path for every round, unconditionally. Quantify both regimes in the
   plan — the "batch is cheap" claim only holds once coverage plateaus.
3. **Generative vs. mutation feedback.** The guided loop leans on seed-pool
   crossover (banking interesting inputs so `gnat/1` draws them as fillers more
   often) and edge-novelty group reweighting, neither of which targets the
   specific kernel lines an interesting input hit (see Phase 2 step 3). Validate
   that this indirect coupling actually explores nearby kernel edges measurably
   faster than the unguided generative baseline. If weak, the fallback is
   feature-key-correlated biasing (steer the generative mix toward semantic
   features observed to correlate with new edges).
4. **Determinism.** Coverage is deterministic given inputs + seeds; the report must
   be stable (sorted, no timestamps in the diffable body). The guided loop records
   seeds for replay.
5. **Cold-line → function mapping.** Line-level cold lines should be grouped by
   enclosing function for a readable v1 report. No `:cover.analyse` level gives
   this mapping directly: `:line` gives cold line numbers with no function
   association, and `:function`/`:clause` give only aggregate covered/uncovered
   *counts* per `{M,F,A}`/`{M,F,A,C}` — not which line numbers those are, so
   they can't be used to attribute a specific cold `{M,Line}` to its enclosing
   function either. The report renderer needs a genuinely separate data source
   for line-to-function boundaries — the module's abstract code (e.g.
   `beam_lib:chunks/2`'s `abstract_code` chunk, which carries per-clause line
   annotations) — as a second input alongside the `:line`-level analyse call.
   Branch (sub-clause) granularity is the true future stretch (see Non-goals).

## Staging

- **Phase 1** is independently landable: instrument + campaign + report. Delivers
  immediate value (kernel cold-spot visibility) with zero generator changes.
- **Phase 2** builds on Phase 1's harness: the guided loop + interesting corpus +
  edge-novelty bias. The plan will split each phase into TDD tasks.

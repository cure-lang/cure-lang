# Classic-Pathway Full Rip-Out Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Delete the classic (non-dependent) compiler pathway and every feature that exists only through it — fsm/actor/sup/app containers, proto/impl runtime protocols, classic type system, optimizer+PGO, session protocol, bless, observe/top, temporal — leaving the dependent pipeline as the sole compiler.

**Architecture:** Pure removal + rewire, per the hardened spec `docs/superpowers/specs/roadmap/2026-07-09-classic-ripout-design.md` (the SPEC below; its §2 tables are the authoritative cut line — this plan sequences them, it does not restate every row; where they conflict, the spec wins and the conflict is reported). Two code commits: **C1** (everything compile/test-affecting: lib, std, tests, examples, antigen) and **C2** (docs/site present-tense claims). Two NEW pin tests lock the single-pipeline behavior.

**Tech Stack:** Elixir, git. Executor: Opus.

---

## ⚑ DISPOSITION REFRESH — 2026-07-12 (authoritative; overrides stale rows below)

A Task-0 re-scout on the current tree (baseline suite **4082/0**, 2 skipped) found this plan (2026-07-09) materially stale: #21 (typeclass migration) + #23 (value surface) landed after it. Where this block conflicts with a row below, **this block wins**. Nothing was deleted during the scout.

**Concurrency family — DELETE THE WHOLE FAMILY (fork resolved).** The 5 std wrappers (fsm/actor/supervisor/app/process) elaborate clean as pure `@extern`, but they are NOT an independent raw base: `Std.Actor.spawn(actor_module: Atom)` / `fsm_spawn(module_atom)` take a callback-module atom that ONLY the classic container compiler produces. Remove container syntax → no valid module to spawn → the wrappers are a dead API. So the plan's original scope stands: delete `lib/cure/{fsm,actor,sup,app}` (compiler + runtime + builtins together), `lib/cure/process/builtins.ex`, the 5 std wrappers, and their tests. The future typed-process-algebra `Std.Otp.Raw` base is rebuilt kernel-founded later (not these).

**Stdlib disposition (replaces the plan's stale known-dead list `{fsm actor supervisor app process access equatable functor ord show}`):**
- **KEEP — elaborate dependent-clean (36):** atom, binary, bool, bounded, char, comparable, core, crdt, decision, equivalent, float, gen, int, iter, json, list, map, match, math, nat, non_empty, optic, option, proof, result, semigroup, set, **show**, sigma, string, system, telescope, test, time, tuple, unit, vector. ⚠️ **`show`/`equatable`/`functor` are KEEP** — they migrated to `interface`/`implementation` (NOT proto); the plan's list wrongly marks them dead. DO NOT delete show.cure/equatable.cure/functor.cure or their tests. (`ord.cure`/`access.cure` already gone from disk — optic replaced access, comparable replaced ord.)
- **KEEP-after-rewrite (1): `io`** — fails now only on `put_chars(text <> "\n")` (`<>`-on-String Semigroup wall) because io.cure has no `use`. Rip-out edit: add `use Std.Semigroup` to io.cure (the "lands at rip-out" rewrite; mirrors the @coexistence emit test's injected imports). Verify it then elaborates.
- **DELETE — dead-ends/retirement (3):** http (no :inets), regex (no :re), pair (retired — sole consumer was access→optic).

**Additional drift items (fold into the tasks named):**
- **NEW CUT-DOWN (Task 2): `lib/cure/migrate.ex`** — postdates the plan; `builtin_type_names/0` consumes `Cure.Types.Env.new().types |> Map.keys()` (just 9 name strings). Rewire: inline `~w(Int Float String Bool Atom Unit Any Never Char)` into the lint's own builtin set (it should own its surface vocab post-#18); reword the two `Cure.Types.Env` comments. Reword the 2 stale comments in `test/cure/migrate/uppercase_type_var_test.exs` (coverage-preserving, ledgered).
- **NEW TEST DELETIONS (Task 1.4):** `test/cure/core/no_gradual_any_test.exs` (aliases `Cure.Types.CoreBridge`; subject is the classic checker), `test/cure/compiler/codegen_binding_test.exs`, `test/cure/compiler/pattern_shape_test.exs` (classic PatternCompiler/Codegen tests).
- **SURVIVOR (no edit): `test/cure/dependent_pipeline_firewall_test.exs`** — classic names appear only inside its `@forbidden` regex; it's the firewall that PROVES the rip-out. Must stay green.
- **Optional reword:** `lib/cure/compiler/printer.ex:1316` stale `Cure.Actor.Builtins` comment example (printer round-trips any dotted atom generically — not a dep).
- **Tag-flip:** value modules (option/result/list/…) currently classic-compile (`dependent?`=false) → after rip-out route through Emit → ctor tags flip to canonical-(A) PascalCase (`{:Some,42}`, `:None`). The ~56 tag-asserting assertions migrate at the Task 4 gate (coverage-preserving, ledgered), per [[stdlib-ripout-readiness-locked]].

---

## Global Constraints

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch` (branch `autopilot/kernel-parity-batch`). NEVER read/touch the parent checkout `/Users/ch/Develop/esp32-beam/cure-lang/lib/...`.
- Ghost commits only: `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO Co-Authored-By/trailers/signatures.
- Explicit-pathspec staging only (`git add -- <path>`, `git rm -- <path>`); never `-A`/`.`.
- ONE `mix` command at a time, ever. No `iex`. Prefer scoped runs; the full suite runs exactly twice (Step 0 baseline, Task 4 gate) plus the §6.4 subproject/stdlib runs (each serial).
- Tests immutable except: (a) the spec §5 enumerated deletions, (b) mid-run EXTENSION deletions of tests that reference the deleted subsystem (ledgered with reason), (c) the observe_test.exs below-file edit (spec §5) and coverage-preserving assertion-list edits under the #19 preload_test precedent (each ledgered). ANY other surviving-test edit = STOP.
- All spec §7 STOP conditions apply verbatim.
- Maintain a running **LEDGER** in the final report: every deleted test file with count + reason class; every EXTENSION; every ledgered edit; the stdlib disposition table; the examples disposition table; the audit-dirs disposition table (Step 0.5).

---

### Task 0: Baseline + disposition evidence (no tree changes except scratchpad)

**Files:** none modified. Scratchpad: `/private/tmp/claude-502/-Users-ch-Develop-esp32-beam-cure-lang/787a9745-7066-417f-8041-b34d29076430/scratchpad/std_disposition.exs`.

- [ ] **Step 0.1: Record baseline.** Run `mix test` ONCE. Record passed/failures/skipped as **B** (spec §0 says do not assume 3141 — record what is actual).
- [ ] **Step 0.2: Stdlib disposition check (spec §4).** Write `std_disposition.exs` (scratchpad): for each `lib/std/*.cure` NOT in the known-dead list `{fsm, actor, supervisor, app, process, access, equatable, functor, ord, show}`, read the file and run it through `Cure.Elab.Program.elaborate/1`, printing `{module, :ok | {:error, reason}}` per file. Run via ONE `mix run` invocation. Record the disposition table: DEPENDENT-CLEAN → KEEP; FAILS(reason) → DELETE per spec decision 4. If a FAILS module's deletion would orphan a SURVIVING feature (something kept still imports it), STOP per §7. Also, in the SAME scratchpad script, grep every candidate `lib/std/*.cure` (the ones being elaborate-checked, i.e. excluding the known-dead ten themselves) for `use Std.\(Fsm\|Actor\|Supervisor\|App\|Process\|Access\|Equatable\|Functor\|Ord\|Show\)\b`: this catches the orphan hazard the elaborate-check itself cannot — at Step 0.2 time the known-dead files still exist on disk, so a KEEP candidate that transitively `use`s one of them would elaborate successfully today and only break once Step 1.3 deletes its dependency. Any hit = STOP per §7 (same orphan-a-surviving-feature condition, the other direction: a KEEP module depending on a hardcoded-dead one, not a FAILS one). (Verified clean on the current tree — `grep -ln "use Std\.\(Fsm\|Actor\|Supervisor\|App\|Process\|Access\|Equatable\|Functor\|Ord\|Show\)\b" lib/std/*.cure` returns only the ten known-dead files referencing each other — but the check must still run at execution time since source can drift before the plan executes, spec §0.)
- [ ] **Step 0.3: Grep pre-verification.** Run each §6.1 gate pattern (`Cure.Types\.`, `Cure.FSM`, `Cure.Actor`, `Cure.Sup\.`, `Cure.App\.`, `Cure.Compiler.Codegen`, `PatternCompiler`, `Cure.Optimizer`, `Cure.PGO`, `Cure.Observe.Top`, `ProtocolRegistry`) over `lib/ test/`. Every hit must be inside a spec §2.1 DELETE path, a §2.2 CUT-DOWN row, a §2.3 elab item, or a §5 test disposition. Any hit outside those = STOP and report (the spec missed a consumer).
- [ ] **Step 0.4: `dependent?/1` caller sweep.** `grep -rn "dependent?(" lib/ test/`. Permitted callers: `lib/cure/compiler.ex`, `lib/cure/types/checker.ex`, and the three pre-cleared test files (spec §2.3 item 1). Any other = STOP.
- [ ] **Step 0.5: Audit-dir disposition sweep (spec §5 audit-dirs paragraph).** For every file under `test/cure/e2e/`, `test/cure/stdlib/`, `test/cure/lsp/`, `test/cure/mcp/`, `test/cure/cli/`, `test/cure/doc/`, `test/cure/project/`, and `test/mix/tasks/`, grep for the §6.1 gate patterns plus the deleted-CLI/scaffold surface (`--pgo`, `--optimize`, `--monomorphise`, `--record-profile`, `cmd_profile`/`cmd_top`/`cmd_synth`/`cmd_bless`, `write_app_template`, `write_fsm_template`, `:app`/`:fsm` template dispatch, session `protocol`, `fsm |actor |proto |impl |app ` container-start source strings) and classify each file: SURVIVES unchanged (no reference), DIES (whole-file, reason recorded), or ledgered SELECTIVE EDIT (same precedent as the observe_test.exs/preload_test coverage-preserving edits — only when the file's subject survives and only the dead-module mention is dropped). For every file marked DIES, record its `grep -c 'test "'` count alongside the reason (same discipline as Step 1.4, needed for Task 4 arithmetic). Record the full disposition table in the LEDGER now, BEFORE any deletion — this must be done here (not discovered later) because the full suite has only one remaining budgeted run (Task 4 Step 4.3) and no budget for a second confirmatory run if these audit dirs surface failures for the first time there.

### Task 1: C1 part A — whole-subtree deletions

**Files (Delete; spec §2.1 is authoritative):**

- [ ] **Step 1.1:** `git rm -r --` on: `lib/cure/types`, `lib/cure/fsm`, `lib/cure/actor`, `lib/cure/sup`, `lib/cure/app`, `lib/cure/process/builtins.ex`, `lib/cure/compiler/codegen.ex`, `lib/cure/compiler/pattern_compiler.ex`, `lib/cure/optimizer.ex`, `lib/cure/optimizer`, `lib/cure/pgo.ex`, `lib/cure/pgo`, `lib/cure/protocol.ex`, `lib/cure/protocol`, `lib/cure/bless.ex`, `lib/cure/bless`, `lib/cure/observe/top.ex`, `lib/cure/temporal`, `lib/mix/tasks/cure.synth.ex`, `lib/mix/tasks/cure.bless.ex`, `lib/mix/tasks/cure.top.ex`.
- [ ] **Step 1.2: Antigen classic layer.** BEFORE deleting, verify each of `lib/antigen/assays/unifier.ex`, `lib/antigen/assays/normalizer.ex`, `lib/antigen/generators/surface_expr.ex`, `lib/antigen/generators/unify_problem.ex` aliases `Cure.Types.*` (not `Cure.Core`) — a `Cure.Core`-targeting file here = STOP (spec §2.1). Then `git rm --` the four files.
- [ ] **Step 1.3: Stdlib.** `git rm --` the ten known-dead `lib/std/*.cure` + every Step-0.2 FAILS module. Delete `lib/cure/stdlib/cure_std_*.ex` backings ONLY where the std module died AND `grep -rn "<BackingModule>" lib/` shows no surviving consumer (ledger each).
- [ ] **Step 1.4: Test whole-file deletions.** `git rm -r --` per spec §5: `test/cure/types`, `test/cure/fsm`, `test/cure/actor`, `test/cure/sup`, `test/cure/app`, `test/cure/protocol`, `test/cure/temporal`, `test/cure/optimizer`, `test/cure/pgo_test.exs`, `test/cure/elab/dependent_routing_test.exs`, `test/cure/k10_classifier_failsafe_test.exs`, `test/cure/v0_21_0_test.exs`, the §5 classic set in `test/cure/compiler/` (codegen_test, pattern_compiler_test, match_spec_test, integration_test, pickup_test, errors_test, comment_preservation_test, group_decorator_attr_test, melquiades_parser_test, shadow_codegen_test, with_abs_codegen_test), the 2 Antigen counterpart test files that actually exist on disk — `test/antigen/assays/unifier_test.exs`, `test/antigen/assays/normalizer_test.exs` (verified: despite 4 Antigen classic-layer lib files being deleted in Step 1.2, the two generator modules `lib/antigen/generators/surface_expr.ex` and `lib/antigen/generators/unify_problem.ex` have no standalone test files of their own — `grep -rln` shows they are referenced only by these same two assay test files and by each other, so no other test file is affected by their deletion; do not `git rm` a nonexistent `surface_expr_test.exs`/`unify_problem_test.exs`), and the dead std modules' test files (`test/cure/stdlib/` per-file by subject). Record per-file `grep -c 'test "'` counts in the LEDGER before deleting (needed for Task 4 arithmetic).
- [ ] **Step 1.5: observe_test below-file edit** (spec §5): delete the `Cure.Observe.TopTest` defmodule block from `test/cure/observe/observe_test.exs`; `Cure.Observe.TraceTest` stays byte-identical. Ledger the removed-test count.
- [ ] **Step 1.6: Audit-dir test deletions (from the Step 0.5 ledger).** `git rm --` every file the Step 0.5 sweep marked DIES; apply every ledgered SELECTIVE EDIT. This must land in C1 (same commit as the rest of Task 1-3) — deferring it past this point is what created the Step 4.3 budget contradiction the Step 0.5 sweep exists to avoid.

### Task 2: C1 part B — cut-downs and rewires

**Files (Modify):** every spec §2.2 row + §2.3. Work file-by-file in this order (dependency-safe):

- [ ] **Step 2.1: `lib/cure/application.ex`** — remove the three dead supervision children (spec anchor 9-14). This MUST be in C1 or boot crashes (§2.2 row).
- [ ] **Step 2.2: `lib/cure/compiler.ex`** — collapse to the straight-line pipeline (spec row 1): delete `maybe_check`/`maybe_optimize`/container-marker `case` blocks/classic branch; `codegen/5` becomes unconditional `Elab.Program.check_ast_with_locals` + `Elab.Emit.compile_forms` → BeamWriter. Keep `compile_file/2`, `compile_and_load/2` signatures and return contracts UNCHANGED (tests pin them).
- [ ] **Step 2.3: `lib/cure/elab/program.ex`** — the ONLY elab changes (spec §2.3): delete `dependent?/1` + `dependent_params?` (+ doc), reword the auto-prelude exclusion comment lines that name deleted modules. Nothing else in elab/.
- [ ] **Step 2.4: `lib/cure/compiler/errors.ex`** — remove E043 + the E045-E054 container cluster + classic-codegen entries; run the spec's produces-code audit over the remaining catalog (keep only codes surviving code can produce; E055 gets an individual verdict); reword the line-26 docstring. Keep all lexer/parser/dep_graph formatting.
- [ ] **Step 2.5: `lib/cure/cli.ex`** — per spec row: `cure check` → `Elab.Program.check_ast`; remove bless wiring, PGO/optimizer flags + `cmd_profile` family + dispatch cases, `cmd_top` + case, `cmd_synth` family + case.
- [ ] **Step 2.6: `lib/cure/watch.ex`, `lib/cure/mcp/server.ex`** — reroute check to `Elab.Program.check_ast`; drop MCP FSM-verify tool.
- [ ] **Step 2.7: `lib/cure/repl.ex` + `repl/session.ex`** — remove `cmd_type`/`cmd_effects`/`cmd_use`-fallback/`describe_let_type` classic paths + alias (spec row anchors); REPL keeps compile-and-load evaluation. session.ex docstring reword only.
- [ ] **Step 2.8: `lib/cure/john.ex` + `lib/mix/tasks/cure.john.ex`** — drop ProtocolRegistry probe row + `runtime_info/0` Observe.Top block + moduledoc lines.
- [ ] **Step 2.9: `lib/cure/project.ex` + `lib/cure/release.ex`** — remove app-container build path, `write_app_template`/`write_fsm_template` + their `--template` dispatch cases, release runtime-reference block.
- [ ] **Step 2.10: mix tasks** `cure.{compile,check,check.examples,check.stdlib,compile_stdlib,bundle_stdlib_beams}` — rewire through the single pipeline.
- [ ] **Step 2.11: `lib/antigen/runner.ex`** — delete the 7 doomed `assay_module/1` clauses (spec row, anchor 353-359); kernel clauses untouched.
- [ ] **Step 2.12: comment rewords** — parser.ex:422/3869/4171-4172/4783 (four stale doomed-module comments), `lib/cure.ex` moduledoc diagram, `lib/cure/doc/extractor.ex`, `lib/cure/stdlib/{cure_std_json,paths}.ex` docstrings.
- [ ] **Step 2.13: Examples** (spec decision 5): delete `examples/protocols.cure`, `examples/traffic_light.cure`, `examples/fsm_pipeline.cure`, and per-subproject apply the mixed-subproject rule to `examples/cure_motif/`, `examples/cure_atelier/`, and any other `examples/**/*.cure` using deleted features (grep for `fsm |actor |proto |impl |app ` container starts + `Std.Fsm|Std.Actor|Std.Supervisor|Std.App|Std.Process|Std.Show|Std.Ord|Std.Equatable|Std.Functor|Std.Access` uses). Ledger every file.

### Task 3: C1 part C — new pin tests, compile-green loop, commit

- [ ] **Step 3.1: Write the two NEW tests** at `test/cure/compiler/single_pipeline_test.exs`:

```elixir
defmodule Cure.Compiler.SinglePipelineTest do
  @moduledoc """
  Post-rip-out pins: (1) a plain, previously-classic-routed module compiles
  through the sole (dependent) pipeline and runs; (2) legacy container
  declarations are rejected at elaboration, not silently classic-compiled.
  """
  use ExUnit.Case, async: false

  test "a plain non-dependent module compiles via the sole pipeline and runs" do
    src = """
    mod Plain
      fn add3(x: Int) -> Int = x + 3
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :add3, [4]) == 7
  end

  test "an fsm container is rejected with unsupported_container" do
    src = """
    mod F
      fsm Light
        Red --go--> Green
        Green --stop--> Red
      end
    end
    """

    assert {:error, reason} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert inspect(reason) =~ "unsupported_container"
  end
end
```

(Verified against the grammar, not just plausible: `parse_fsm_items` (`lib/cure/compiler/parser.ex:3558-3583`) accepts only `@`-annotations, the fixed `on_*` callback names, or a `Source --event--> Target` transition line — there is no bare `state X` declaration, so a body of `state Red`/`state Green` would fail at `expect(state, :transition_open)` (`parser.ex:5126`) with a parse error, never reaching elaboration. The `Red --go--> Green` form mirrors the real, working `examples/traffic_light.cure` transition syntax. The `mod ... end` wrapping (with `end` dedented back to the enclosing container's own indentation, not the body's) mirrors the real, currently-passing `test/cure/compiler/dependent_vec_codegen_test.exs` `@src` heredoc and matches `Cure.Elab.Program.check_ast/1`'s own doc: "Unwraps a `mod ... end` container to its body." Once parsed, `declarations.ex`'s per-form `elaborate({:container, meta, variants}, env)` dispatch (`lib/cure/elab/declarations.ex:103-157`) sees `container_type: :fsm` and falls through to the `other -> {:error, {:unsupported_container, other}}` clause — the exact behavior spec §3 pins. If `Cure.Compiler.compile_and_load`'s error wrapping makes the `inspect(reason) =~ "unsupported_container"` assertion unreachable for some other reason, pin via `Cure.Elab.Program.elaborate/1` instead and note it in the ledger.)

- [ ] **Step 3.2: Compile loop.** Run `mix compile` (ONE command). Fix residual references to deleted modules ONLY in files already in the spec's DELETE/CUT-DOWN scope; a needed change in any file OUTSIDE that scope = STOP (spec missed a consumer). Repeat until clean. Warnings referencing deleted modules must be gone; pre-existing unrelated warnings stay.
- [ ] **Step 3.3: Scoped smoke.** `mix test test/cure/elab/ test/cure/core/` — all green (dependent pipeline untouched proof). Then `mix test test/cure/compiler/` — green (front-end survivors + new pins + surviving dependent codegen tests).
- [ ] **Step 3.4: Commit C1** (ghost, explicit pathspecs; single commit covering Tasks 1-3 changes): message `refactor!: delete classic compiler pathway — fsm/actor/sup/app, proto/impl, types/*, codegen, optimizer+PGO (operator-ordered full rip-out)` with a body summarizing scope + pointing to the spec.

### Task 4: Gates + C2 docs + report

- [ ] **Step 4.1: Grep gates** (spec §6.1) — all patterns zero over `lib/ test/` (parser comment rewords done; historical docs/site excluded).
- [ ] **Step 4.2: Diff-scope gates** (spec §6.2 + §2.4): `git diff <start>..HEAD -- lib/cure/core/` EMPTY; `lib/cure/elab/` diff = exactly program.ex §2.3 hunks; `lib/cure/smt/process.ex` and `lib/cure/elab/guard_lint.ex` diffs EMPTY.
- [ ] **Step 4.3: Full suite ONCE.** `mix test` → 0 failures. Reconcile: B − (sum of ledgered whole-file/module counts) − (extensions) + 2 (new pins) = final passed. State Antigen row-count drop and oracle replay 65/65 explicitly.
- [ ] **Step 4.4: Rewired stdlib + example gates** (spec §6.4), each a separate serial mix run: `mix cure.check.stdlib` green over surviving stdlib; each surviving example subproject's `(cd examples/<p> && mix test)` green.
- [ ] **Step 4.5: C2 commit** — docs/site present-tense claims (fsm/actor/proto/impl/refinement-era "supported features" lists, README, `site/priv/pages/*`; dated release posts stay untouched). Message `docs: classic pathway removed — update present-tense feature claims`.
- [ ] **Step 4.6: Report** — both commit hashes, baseline B vs final arithmetic with the full LEDGER (test deletions per file with counts+reasons, extensions, ledgered edits, stdlib disposition table, examples disposition table, audit-dirs disposition table, backing deletions), grep-gate outputs, diff-scope evidence (`git diff --stat` for core/elab/guard_lint/smt), and an honest statement of every deviation.

# Lean4lean bridge removal (task #17) — Design

## §0 Decision record

Operator order (2026-07-09, post-parity teardown batch): rip out the lean4lean bridge **by reverting the commits that added it**. The bridge = the artifact set of commit `3d6f739` "Route dependent checking through Lean backend" (2026-07-07, 16 files, +1209/−37), plus the encoder hunks later added by `ae02ba5`/`ccbe2d0` (identity-type work).

**Mechanism deviation, with empirical proof (the standing directive's bar):** `git revert --no-commit 3d6f739` was tested on HEAD and CONFLICTS in 4 files — `program.ex` (2 hunks spanning the check_ast routing region churned by 9 later commits), `module_encoder.ex` + its test (modify/delete vs `ae02ba5`/`ccbe2d0`), and `lib/compiler/kernel/README.md` (modify/delete vs `588bd46`'s stage1 revert). Worse, a hand-resolved revert would silently (a) re-privatize `local_def_names/1`, breaking three LATER non-bridge call sites (program.ex:268/:512/:575, the Approach-B re-key work), and (b) resurrect the stage1 `lib/compiler/kernel/README.md` that `588bd46` already deleted. A "Revert" commit implying a clean inverse would be dishonest; the adopted mechanism is **one manual deletion commit** whose message cites `3d6f739` (+ the `ae02ba5`/`ccbe2d0` encoder hunks) as the material removed. (Revert test left no trace: `git status --porcelain` clean before and after `git revert --abort` — verified.)

**Supersession note:** this removal supersedes cleanup-strategy decision 6 ("second backend is a long-term goal", `2026-07-07-dependent-kernel-cleanup-strategy-design.md:142-153`) by operator order. That spec and the other historical docs mentioning the bridge are records — they are NOT edited; the removal commit message carries the supersession line.

## §1 Scope — exact file dispositions

**DELETE outright (bridge-only, nothing else references them):**
- `lib/cure/lean/module_encoder.ex`, `lib/cure/lean/bridge.ex` (the whole `lib/cure/lean/` dir)
- `lib/cure/kernel/backend/lean.ex` (sole caller of ModuleEncoder + Bridge)
- `lean_bridge/` (4 tracked files: `CureLeanBridge.lean`, `README.md`, `lakefile.lean`, `lean-toolchain`)
- `test/cure/lean/module_encoder_test.exs`, `test/cure/lean/bridge_test.exs` (the whole `test/cure/lean/` dir)

**DELETE by collapse (backend-selection layer — created BY 3d6f739, no other purpose):**
- `lib/cure/kernel/backend.ex`, `lib/cure/kernel/backend/elixir_core.ex`, `test/cure/kernel/backend_test.exs`
- `program.ex:38` currently routes ALL dependent checking through `Cure.Kernel.Backend.check_ast`; rewire it to the elixir-core implementation DIRECTLY (inline `Backend.ElixirCore`'s body at the call site or as a private helper in program.ex — plan decides the mechanics). The `:elixir_core`/`:lean` selection (opt/config/`CURE_KERNEL_BACKEND` env) disappears entirely; no live caller ever selected `:lean` (verified: no mix task, pipeline event, CLI flag, or config references it).

**SURGICAL EDITS (bridge functions inside live files):**
- `lib/cure/elab/program.ex`: remove `check_ast_for_lean_backend/1` (:143), `elaborate_declarations_lean` (:693), `register_pass_lean` (:699), `body_pass_lean` (:774), and the `:lean_backend_unsupported_*` error rows (:150, :708) — the error rows sit INSIDE `check_ast_for_lean_backend`/`register_pass_lean` respectively and are removed as part of deleting those function bodies, not as separate edits.
- `lib/cure/elab/declarations.ex`: remove `elaborate_function_body_lean/2` (:74, `@doc false`, bridge-only).

**KEEP (explicitly, each load-bearing):**
- `local_def_names/1` stays PUBLIC (three later non-bridge call sites depend on it).
- `Program.check_ast/2` (opts arity) survives — `types/checker.ex` threads opts through `check_dependent_module`. (Task #18 may later delete checker.ex; not this task's concern.)
- `checker.ex`'s opts-threading from 3d6f739 stays (harmless, and removing it would churn a file #18 owns).
- ALL prose-only Lean mentions: design-comparison comments in core/elab/parser files, test prose, and the historical specs/plans (including `2026-07-02-lean-shape-matching-*`, which is unrelated pattern-matching work).

## §2 Test accounting (deletions, not flips)

Three test files are removed WITH their subsystem — `module_encoder_test.exs`, `bridge_test.exs`, `backend_test.exs`. Justification per the immutable-tests discipline: they test ONLY the deleted subsystem (encoder wire format, bridge shell-out/error paths, backend selection); no surviving behavior loses coverage. Notably `module_encoder_test.exs:64`'s `{:prim,…}` rejection row (which #15's plan:228 left out of scope as "stays green") is deleted wholesale, not broken — no landed #15 code depends on it. No other test file changes. No Antigen assay or oracle fixture exercises the bridge (verified — Antigen "lean" hits are the English word).

## §3 Verification gate

1. Full suite green ONCE at the end; expected delta vs 3291 = exactly the removed files' test counts (enumerate the actual counts in the plan from `grep -c "test "` per deleted file); zero surviving-test changes.
2. Antigen 503/503 unchanged; oracle replay 65/65 unchanged (replay-only, no `mix cure.oracle`).
3. Greps: zero references to `Cure.Lean`, `Cure.Kernel.Backend`, `lean_bridge`, `CURE_KERNEL_BACKEND`, `CURE_LEAN_BRIDGE`, `CURE_LEAN4LEAN_PATH`, `_lean` function suffixes under `lib/` and `test/` (prose comments mentioning the Lean LANGUAGE excepted).
4. `git status` clean; single ghost-authored commit (plus the spec/plan docs commits); explicit pathspec staging.
5. STOP conditions: any surviving (non-deleted) test needs a change; any reference to the backend layer found outside the enumerated file set; `local_def_names/1` privatization pressure from any edit.

## §4 Non-goals

- Editing historical specs/docs that mention the bridge (records stay; supersession lives in the commit message).
- Touching `lib/cure/types/checker.ex` beyond keeping it compiling (it belongs to task #18).
- Removing prose comparisons to Lean anywhere.
- Any change to the dependent pipeline's checking behavior — this is a pure removal; every program elaborates/checks identically through the (now-direct) elixir-core path.

## §5 Acceptance criteria

1. `lib/cure/lean/`, `lib/cure/kernel/backend*`, `lean_bridge/`, `test/cure/lean/`, `test/cure/kernel/backend_test.exs` gone; the five bridge functions (four in program.ex, one in declarations.ex) and the two nested `:lean_backend_unsupported_*` error rows stripped from program.ex/declarations.ex — seven items total per §1.
2. Dependent checking routes directly to the elixir-core path with NO selection layer; behavior byte-identical (full suite minus deleted files' tests, all green).
3. §3 greps clean; ghost authorship; commit message cites 3d6f739 (+ ae02ba5/ccbe2d0 hunks) and the decision-6 supersession.

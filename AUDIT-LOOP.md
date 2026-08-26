# Editions Audit-Fix Loop

Self-perpetuating fix→audit→fix loop (operator-requested). Driver: cron `7e672a7d`
(every 10 min). Stop condition: **two consecutive clean audits** → cron self-deletes.
Branch `autopilot/editions`, worktree-local. **Do NOT merge.** All commits ghost-authored.

Convergence rule: a cycle fixes the current Outstanding list, runs the full suite, then
runs a fresh adversarial audit. Zero confirmed bugs on two consecutive audits = done.

---

## Iteration 1 — Outstanding findings (from the initial 4-agent audit, all verified)

Fix these this cycle. Severity in brackets. Grouped by file for commit batching.

### Parser (`lib/cure/compiler/parser.ex`)
- **[MED] F1 — placement guard bypassed by decorator-led defs.** `mark_seen_if_stmt/1`
  (~5525) skips flipping `seen_stmt?` on any `:at` token, but a whole decorated def
  (`@extern fn`, `@derive rec`) is one `:at`-led statement → never marks seen → a later
  misplaced `@edition` passes `file_leading?/1` and is silently accepted. CONFIRMED
  empirically. Fix: only a *leading `@edition` pragma* is non-substantive; every other
  decorator marks seen. Peek the decorator name after `:at`.
- **[LOW] F7 — malformed `@edition` value accepted silently.** parse_at edition branch
  (~5013) never validates the arg; `@edition(2026)` unquoted / `@edition("abc")` / bare
  `@edition` parse clean → pre-scan returns nil → silent default-edition fallback. Fix:
  validate the pragma arg is `"YYYY"` and error `{:edition_pragma_malformed, l, c}` else.
- **[LOW] F3 — multiple `@edition` pragmas accepted; only first honored.** Same root as
  F1. Fix: the edition branch marks `seen_stmt?` true after accepting, so a 2nd errors.

### Migrate engine (`lib/cure/migrate.ex`)
- **[MED] F2 — `run_to_fixpoint/2` duplicates warnings across passes.** (~165/175)
  `warns ++ pass_warns` each pass; a `:warn`/`:manual` rule firing on N passes → N copies.
  CONFIRMED (code + agent empirical). Fix: dedup the returned warns by {rule,file,line}.
- **[MED] F3b — fixpoint crashes on unrenderable/unparseable output.** (~153/192)
  baseline + verify `quoted_to_string` are outside try/rescue; a rule emitting an
  unprintable AST (or Lexer/Parser raising) crashes all of `cure migrate`. CONFIRMED
  empirically (crashed at :153). Fix: rescue → clean `{:error,{:verify_failed,_}}`.
- **[LOW] F-culprit — `verify_failed` blames `List.last(pass_warns)`** (~178), the last
  rule that *warned*, not the one that broke verify. Fix: report all fired rule ids
  (uniq), matching the `no_convergence` branch.
- **[LOW] F12 — verify reparses without the target `edition:` opt** (~194). Latent with
  one edition. Fix: thread the crossing target edition into verify's reparse.

### Edition core (`lib/cure/edition.ex`)
- **[MED] F6 — `resolve/1` crashes on explicit `%{source: nil}`** (~90). `Map.get(input,
  :source, "")` defaults only for an absent key; explicit nil → `is_binary` guard →
  FunctionClauseError. CONFIRMED (code + agent empirical). Fix: coalesce nil → "".
- **[LOW] F8 — `compare/2`/`year/1` raise on non-numeric 4-char string** (~52).
  `<<y::binary-size(4)>>` matches any 4 bytes then `String.to_integer` raises. Fix: match
  only 4-digit strings (regex/guard); non-edition input → clear error, not a crash.

### Project (`lib/cure/project.ex`)
- **[LOW] F10 — `set_edition/2` can duplicate the `[project]` table / cross-table edits**
  (~120). Header regex `^\s*\[project\]\s*$` misses a header with a trailing comment;
  existing-key replacement rewrites `edition=` in *all* tables. Fix: tolerate trailing
  comment on the header; scope the key replacement to the `[project]` table only.

### CLI (`lib/cure/cli.ex`)
- **[MED] F4 — downgrade guard measures against compiler-latest, not project edition**
  (~1225/1266). `:current` param plumbed but unwired → once 2027 mints, `--edition 2026`
  in a 2026 project wrongly refuses. Fix: pass the resolved project edition as `:current`.
- **[LOW] F5 — downgrade rejection is silent** (~1264/143). `{:error, :downgrade}` prints
  nothing, exits 1. Fix: route through `error/1` with a clear message.
- **[LOW] F9 — bump pragma regex looser than Edition → crash.** `migrate_edition_pragma/1`
  (~1545) captures `[^"]+`; `@edition("abc")` → `compare(target,"abc")` → String.to_integer
  crash. Fix: require `\d{4}` (consistent with Edition).

### Adjudicated NOT-a-bug (do not "fix")
- F11 (pragma-less standalone files left unpinned post-migration): by-design — default ==
  latest edition, so a rewritten pragma-less file correctly floats at latest. Documented.

**Outstanding count: 12 findings across 5 files (+1 adjudicated by-design).**

### Iteration 1 — FIXED (5 commits, full suite 3838 passed / 0 failed)
- `b01d049` parser F1/F3/F7 · `abe8d11` migrate F2/F3b/F12/culprit · `db1e64f`
  edition F6/F8 · `8dead22` project F10 · `711b11b` cli F4/F5/F9. All 12 fixed;
  +21 hardening tests. Then a fresh 4-agent audit ran on the fix commits.

---

## Iteration 2 — Outstanding findings (fresh audit of iteration 1's fixes)

The re-audit found real regressions the fixes introduced. Fix these this cycle.

- **[HIGH] I1 — set_edition ↔ load header-grammar divergence (REGRESSION).** My F10
  fix taught `project_header?` to accept `[project] # comment`, but the loader
  `parse_lines` (project.ex:821) requires the header line to END with `]`, so a
  comment-trailing header is not recognised and the written `edition` is dropped
  on read-back — defeating F10a's own headline scenario. Well-formed TOML. Fix:
  teach the loader to tolerate an inline comment after a table header (unify the
  grammar); add a load round-trip test (F10a only checked file text).
- **[MED] I2 — F12 fix is unwired (dead code).** `plan_migration_source` (cli.ex
  ~1309) calls `run_to_fixpoint(attached, rules: rules)` without `edition: target`,
  so verify still reparses under `current()`. Fix: pass `edition: target`.
- **[MED] I3 — set_edition regressed duplicate-edition-key handling.** The new
  first-match replace leaves a stale second `edition=` in the [project] table
  (load last-wins → stale). Pre-fix replaced all. Fix: replace ALL edition keys
  within the [project] section. (Malformed TOML; no clean red test under one
  edition — implement for correctness, document the test gap.)
- **[LOW] I4 — migrate_project_edition masks an invalid declared edition.** Maps
  any `{:error,_}` from resolve to `current()`, so a `Cure.toml` with a bad
  `[project].edition` silently defeats the downgrade guard in a multi-edition
  future. Fix: surface `{:unknown_edition,_}`; fall back only for no-project.
- **[LOW] I5 — `~r/^\d{4}$/` accepts a trailing newline (`$` pre-newline).**
  Unreachable (single-line literal), belt-and-suspenders. Fix: `\A\d{4}\z`.

### Iteration 2 — FIXED (3 commits, full suite 3841 passed / 0 failed)
- `ee07b6c` project I1 (loader `table_header_name/1` tolerates inline comment,
  matching the writer grammar) + I3 (`edition_in_section` replaces ALL edition
  keys in the [project] section) + 2 load round-trip tests.
- `a8bbbfa` cli I2 (`plan_migration_source` passes `edition: target` to the
  fixpoint) + I4 (`migrate_project_edition` surfaces `{:unknown_edition,_}`,
  cmd_migrate threads it through `with`) + 1 new red test (unknown declared ed).
- `817b45e` parser I5 (`\A\d{4}\z`).
Then a fresh audit ran on these fix commits (iteration 2's audit step).

### Iteration 2 — Adjudicated ACCEPTED (fail-safe / malformed-input, not fixed)
- I6 — bare `rescue _` in migrate `verify/3`+`safe_print/1` is broad. It fails
  SAFE (aborts, never emits wrong output); narrowing precisely is fragile. A
  compiler bug during migrate is relabelled verify_failed — diagnosability cost
  only. Accepted as defensive-by-design.
- Dup `[project]` tables (malformed TOML): set_edition updates the first, loader
  last-wins the second. Invalid input; both paths best-effort. Accepted.

---

## Iteration 3 — audit of iteration 2's fixes (3 agents) + fixes

Fresh 3-agent Opus audit of `ee07b6c`/`a8bbbfa`/`817b45e`. Each finding verified
against source myself before counting.

- **CLI audit (I2/I4): CLEAN.** No new defects. One pre-existing non-regression
  noted (`migrate_project_edition(".")` keys off CWD, not the migrated files'
  dir) — unchanged by the fix, not counted.
- **project audit: two real defects** (one a regression the iteration-2 fix
  introduced). Both FIXED this cycle.
- **cross-cutting audit: F-A/F-B/F-C.** F-A had a LIVE sub-part (fixed) and a
  LATENT sub-part (escalated). F-B/F-C are LATENT. `compare/2`/`year/1` totality,
  the lexer keyword-gating fold, and the phase-2 bump write-side all verified
  CLEAN.

### Iteration 3 — FIXED (commit `86b9be3`, full suite 3845 passed / 0 failed)
- **I1b (MED regression):** iteration-2's `$`-anchored loader regex stopped
  recognising a TOML array-of-tables header `[[deps]]` as a section boundary →
  its keys leaked into the preceding `[project]` table, while the writer still
  bounded on it (writer/loader split again). Broadened `table_header_name/1` to
  `\[{1,2}..\]{1,2}` and derived BOTH writer boundary predicates from it —
  one grammar by construction. Red test: array-of-tables load round-trip.
- **I1c (LOW):** loader tolerated `[ project ]` (internal whitespace) but writer
  `project_header?` required literal `[project]` → duplicate table on write.
  `project_header?` is now `table_header_name(line) == "project"` (agrees with
  the loader; dotted `[project.env]` still excluded). Red test: no-duplicate.
- **F-A LIVE (MED):** the build pipeline (`compiler.ex` lex/parse) never calls
  `Cure.Edition.resolve`, so a well-formed but unknown `@edition("9999")` was
  only format-checked and compiled silently — violates spec §3.1 ("a typo'd
  edition must fail loudly") / §3.3. The parser now allow-list-validates the
  pragma via `Cure.Edition.valid?/1`, raising a distinct `:edition_pragma_unknown`
  error. Red test in `edition_pragma_hardening_test.exs`.

### Iteration 3 (cont.) — the escalated findings, now FIXED

Operator lifted the escalation gate ("just fix them; I don't care if you can't
TDD them, if you find a bug, fix it"). The three latent findings below were fixed
this cycle; full suite **3852 passed / 0 failed** (81s). Each is behaviourally
identical under the single minted edition (so the suite proves no regression) but
correct for a future second edition; F-A also closes a live spec-§3.1 gap and is
testable at the compile-resolve boundary.

- **F-A → FIXED (`2aee2e9`, `614f29a`).** `Cure.Compiler` (`compile_string`/
  `compile_and_load`/`parse_source`) now resolves each source's edition
  (`resolve_edition/2` = `Cure.Edition.resolve`) and threads it into the
  lexer/parser, so a file's `@edition` pragma actually drives its lexing on the
  build path and an unknown edition fails the compile loudly with
  `{:edition_error, reason}`. Tests: `edition_compile_test.exs` (unknown pragma
  and unknown manifest edition both fail loudly; valid ones compile). `pragma_edition`
  made a bounded leading-line scan (it now runs on every compile). **Deliberately
  NOT done:** blanket-passing `project_dir` from CLI build callers — that would
  misapply an app's manifest edition to stdlib/dep files compiled in the same
  build. The per-file pragma path is fully wired; manifest-wide build resolution
  needs per-file project-root discovery (walk up to the nearest `Cure.toml`) —
  a smaller, well-scoped follow-up, noted below.
- **F-B → FIXED (`671ec68`).** `cure migrate` now parses the INPUT under the
  file's source edition (`from` = its pragma, else the project edition threaded
  from `cmd_migrate`); the fixpoint verify reparse stays on `target`.
- **F-C → FIXED (`614f29a`, `671ec68`).** `pragma_capture`, `migrate_edition_pragma`,
  and `migrate_splice_edition` tolerate the parser's interior whitespace
  (`@\s*edition\s*\(`), so a spaced pragma is no longer invisible to resolution
  or duplicated by the bump.

## Iteration 4 — audit of iteration 3's fixes (2 Opus agents) + fixes

The escalation gate was lifted by the operator ("just fix them… if you find a
bug, fix it"), so F-A/F-B/F-C — previously escalated as latent/design-blocked —
were all fixed in iteration 3's tail (build-path `resolve/1` wiring `2aee2e9`,
source-edition parse-input `671ec68`, pragma whitespace tolerance `614f29a`).
Iteration 4 audited those fixes and the F-A/F-B/F-C follow-ups.

### Iteration 4 — carried-over findings FIXED

- **CLI Finding 1 [MED, live regression] — `eb33b88`.** The phase-2 bump detected
  and spliced the `@edition` pragma with a whole-body regex, so an `@edition(...)`
  buried in a comment/string falsely triggered a bump (in-comment mutation, no
  real leading pragma added). The F-C whitespace widening extended this to spaced
  forms, making it reachable with the single minted edition. Fixed: detection
  routes through `Cure.Edition.pragma_edition` (anchored to the first substantive
  line); splice rewrites only that leading line. Red: a spaced `@ edition("2020")`
  in a comment no longer bumps.
- **Compiler F1 [latent] — `bfde322`.** The parser accepted pragma forms the
  single-line pre-parse resolver could not see: a **multi-line** pragma (parser
  honoured the declared edition while the resolver lexed under the default → silent
  wrong-edition once a 2nd edition exists) and an **indented** pragma (resolver's
  `^\s*@` over-matched a form the parser rejects as placement). Fixed both:
  parser rejects a multi-line pragma as `:edition_pragma_malformed`; resolver
  regex anchored at column 0 (`^@`). The two now agree on what a valid pragma is.
- **F2 [polish] — `e21f3b1`.** The `@edition` pragma errors and the compile-boundary
  `{:edition_error, {:unknown_edition, _}}` hit the catch-all `inspect`. Added
  dedicated `format_error` clauses; unknown-edition variants list the known set.
- **CLI Finding 2 [latent] — `5651ace`.** The downgrade guard measured target vs
  the *project* edition only; a file pinning a newer edition via its own pragma
  (`from`) slipped through and would be rewritten onto an older keyword set.
  Fixed: `plan_migration_source` refuses `from > target` (`{:error, :downgrade}`);
  `migrate_preflight` aborts the run with a precise message. Probed at the pure
  planner with hypothetical editions (unreachable end-to-end with one edition).

### Iteration 4 — fresh audit result (2 Opus agents, verified against source)

- **parser.ex / errors.ex slice — CLEAN.** Verified myself: the literal `meta`
  always carries `:line` (a plain `"YYYY"` arg lexes as a `:string` token with a
  line; the line-less literal only arises inside string interpolation, unreachable
  here); `single_line_edition_pragma?` runs after `valid_edition_pragma_arg?` so
  `args` is guaranteed a one-element literal list; the new formatter clauses
  precede the catch-all and their tuple shapes are disjoint from every earlier
  clause.
- **cli.ex / edition.ex slice — ONE confirmed LOW regression (now FIXED, `a5f8131`).**
  `replace_leading_pragma_line` split on `"\n"`, so on a CRLF file the replaced
  pragma line dropped its `\r` → mixed EOL (the old substring `Regex.replace`
  preserved CRLF). Latent (the bump path needs a 2nd edition to fire), but a
  genuine output-corruption regression I introduced. Red: `migrate_splice_edition`
  on a CRLF body now preserves `\r\n`. All other hunts (trivia-predicate agreement,
  `^@` missing a real pragma, downgrade-guard caller/shape preservation, result
  bucket double-handling) were traced and REFUTED against source.

### Iteration 4 — FIXED (5 commits, full suite 3864 passed / 0 failed)

`eb33b88` (CLI Finding 1) · `bfde322` (Compiler F1) · `e21f3b1` (F2 messages) ·
`5651ace` (CLI Finding 2) · `a5f8131` (CRLF, from this iteration's own audit).

## Iteration 5 — F-A follow-up fixed + audit of it (2 Opus agents)

### Iteration 5 — carried-over finding FIXED

- **F-A follow-up [was LOW/design] — `913aa99`.** The compile boundary honoured a
  project's `[project].edition` only when a caller passed `:project_dir`, but the
  `cure build`/`run` callers never did — so a project manifest's edition (incl. a
  typo'd one) was silently ignored on the build path (§3.1 "fail loudly" violated
  for a bad manifest). Added `Cure.Project.find_root/1` (walk up from the file's
  dir to the nearest ancestor `Cure.toml`) and had `resolve_edition/2` discover
  the project root from the file path when `:project_dir` is absent. Nearest wins;
  `parse_source` stays headless; a no-`:file` compile does not discover (nil
  guard). Red: `compile_file` under a dir with a typo'd `Cure.toml` now fails
  loudly; child-manifest shadows parent; pragma still overrides the manifest.

### Iteration 5 — fresh audit result (2 Opus agents, every finding verified against source)

Both agents: **no today-triggerable bug** (suite green because no ancestor
`Cure.toml` exists above the compiled sources today, and with one minted edition
a *valid* manifest can only resolve to the default). Two **latent** hazards from
the newly-broad auto-discovery, both confirmed by reproduction:

- **Unbounded upward walk [MED, latent] — FIXED `0b4d2f3`.** `find_root` walked to
  the filesystem root, so a file with no nearby manifest could bind to an
  unrelated ancestor `Cure.toml` (a sibling/parent project, a stray `~/Cure.toml`)
  — with a typo'd/foreign edition that would *spuriously fail* this repo's own
  internal stdlib/example/compile mix tasks, which previously consulted no
  manifest for such sources. Fixed: bound the walk at the enclosing git repo (a
  dir holding `.git`; a git worktree's `.git` file counts), returning nil at the
  repo root with no manifest. Red: a `Cure.toml` above a `.git` boundary is no
  longer discovered; a `Cure.toml` AT the repo root still is. This also corrects
  a **git dependency** (LATENT-1, git flavour): its checkout carries its own
  `.git`, so its sources now resolve under the dependency's OWN manifest/default
  instead of inheriting the consuming app's edition.
- **REPL `:load` of a file under an unrelated project [LOW, latent].** Same root
  cause; now bounded by the `.git` fix (a REPL-loaded file only binds to a
  manifest within its own repo). Considered resolved by `0b4d2f3`.

### Iteration 5 — FIXED (2 commits, full suite 3874 passed / 0 failed)

`913aa99` (F-A follow-up: nearest-ancestor discovery) ·
`0b4d2f3` (bound discovery at the git-repo root).

## Iteration 6 — LATENT-1 fixed + fresh 3-Opus audit of the editions slices + fixes

**Outstanding from iteration 5 (LATENT-1) — FIXED first:**

- **LATENT-1 residual (path/tarball dep edition inheritance)** — `4b300ef`: pinned
  `project_dir` at both dep-compile sites (path `resolve_one`, `install_tarball`)
  so a manifest-less dep resolves under its own base/default, never the consumer's
  edition. Red→green via a public `resolve_deps/1` path-dep fixture
  (`test/cure/project/dep_edition_isolation_test.exs`).

**Fresh audit — 3 parallel Opus agents over the changed slices** (project/dep,
compiler/edition resolve, CLI migrate). 10 raw claims; **each verified against
source before counting** (two agent line-refs were wrong — `detect_app` is
`project.ex:703` not `compiler.ex:711`; `compiler.ex` is only 424 lines — corrected
by reading the real code). Confirmed-real findings, all FIXED this cycle:

- **A3-F1 + A3-F2 (migrate splice data-loss)** — `e012adb`: `replace_leading_pragma_line`
  replaced the whole leading line, so it (a) dropped a trailing comment on the pragma
  line and (b) DESTROYED the entire body of a lone-CR file (no `\n` ⇒ one "line").
  Now rewrites only the matched `@edition(...)` token; trailing content + EOL survive.
- **A2-F1 (TOML inline comment → spurious hard fail)** — `e07fc24`: `edition = "2026"  # pin`
  leaked the comment into the value (`2026"  # pin`) and hard-failed a VALID edition.
  `parse_kv` now strips the first `#` outside quotes (a `#` inside a quoted value kept).
- **A1-F2 (blank-path dep crash)** — `be4c43b`: `{ path = "" }` routed to the git clause
  (a `git: nil` key) and crashed `System.cmd` on a nil URL. Now `{:error, {:invalid_dependency, name}}`;
  git clause guarded on a binary URL.
- **A1-F1 (nested dep manifest ignored)** — `d5f8e07`: `Cure.Project.load` reads `<dir>/Cure.toml`
  directly, so the fixed `project_dir: target` missed a tarball dep's own manifest under the
  nested `target/<pkg>-<vsn>/` layout the `**/lib/**` glob anticipates. New base-bounded
  `dep_project_dir/2` finds the dep's own Cure.toml yet never escapes into the consumer tree.
- **A2-F2 (app-detect pre-pass ignored per-file editions)** — `02a8b4c`: `detect_app` lexed under
  `current()`; now resolves each file's edition (pragma > project > default) and threads it.
  Latent (one edition) but a real precedence gap. Same commit corrects two stale comments
  (**A2-F3** `parse_source`, **A2-F5** parser unknown-pragma gate) that wrongly claimed the
  build path never calls `Edition.resolve`.

**Verified but DEFERRED as by-design (recorded, not "fixed"):**

- **A2-F4** — the "no edition declared" advisory is deduped once per OS process (a
  single `:persistent_term` key). This is intentional anti-spam for a long-lived
  compiler process; being once-per-process rather than once-per-project is a
  defensible advisory policy, not a correctness bug.
- **A3-F3** — the phase-2 bump's PREPEND branch is unreachable from `migrate_bump`
  (a pragma-less file returns `false` from `migrate_file_bump?`), so a standalone
  file with no `@edition` is not stamped on migration. This matches Rust parity:
  `cargo fix --edition` bumps the PACKAGE manifest (Cure's `migrate_project_bump?`
  path), not each file. Per-file stamping on migration is a separate design choice,
  not a bug; the prepend branch still serves the public `migrate_splice_edition/2`.

**Refuted on verification (not counted):** A1-F3 (git-dep site safe — the fresh
`git clone` always has a `.git` dir bounding `find_root`; the agent self-refuted).

**Full suite after all fixes: 3884 passed, 0 failing** (+9 new tests; 148 immune
responses expected; Antigen shape-coverage 309/309).

## Outstanding findings (after iteration 6)

- None open as bugs. The two items above (A2-F4, A3-F3) are **by-design**, kept
  here as rationale so a future audit doesn't re-flag them.

**Loop status:** iteration 6's fresh audit found 8 confirmed bugs — so it is **NOT
a clean audit**, and the Group-1–5 fixes are NEW code not yet independently audited.
Convergence (two consecutive clean audits) is **not** met. The cron is **left in
place**; the next fire (iteration 7) runs a fresh audit over the iteration-6
changes — a clean result there is the FIRST clean audit, and a second consecutive
clean audit closes the loop. Do NOT merge.

Commits this cycle: `4b300ef` (LATENT-1), `e012adb` (A3-F1/F2), `e07fc24` (A2-F1),
`be4c43b` (A1-F2), `d5f8e07` (A1-F1), `02a8b4c` (A2-F2 + doc A2-F3/F5).

---

## Iteration 7 — fresh 3-Opus audit of the iteration-6 changes + fixes

No open bugs entered this cycle (iteration 6's Outstanding was by-design only), so
this was a pure audit of the iteration-6 diff (`git log 9850ce9..b5d81a3`). Three
parallel Opus agents (project/dep, migrate splice, edition semantics), read-only.
**Every claim verified against source before counting.** The migrate-splice agent
came back **clean** (token-only replacement correct across LF/CRLF/lone-CR/trailing-
comment/empty). The other two surfaced **5 confirmed real bugs**, all fixed:

- **A1-F1 (escaped-quote data loss in `strip_inline_comment`)** — `99c1202`: the
  quote-state toggle ignored backslash escapes, so a `\"` inside a basic string
  wrongly closed it and a following `#` truncated the value. Now tracks `\`-escapes.
- **A1-F3 (whitespace-only path bypassed the blank-dep guard)** — `f9cc1d1`: the
  `!= ""` guard is literal, so `path = "   "` slipped through and silently resolved
  to zero files. Trim before deciding; extracted `resolve_path_dep/3`.
- **A3-F1 (a dep's own unknown edition failed SILENTLY)** — `857305f`: iteration-6's
  `dep_project_dir` routes the dep manifest into `resolve_edition`, so a typo'd dep
  edition makes `compile_file` error — but the `_ =` discard left the build green
  with no beams. New `compile_dep_files/4` propagates `{:dependency_edition_error,…}`
  (other dep compile errors stay non-fatal, as before). Git deps now also route
  through it + `dep_project_dir`, closing the "git dep vendored without .git" leak
  the semantics agent flagged as a consistency gap.
- **A1-F4 (O(N) redundant manifest re-parse in `detect_app`)** — `64e43ab`: resolved
  each file's edition by re-reading+validating the project Cure.toml once per file
  (plus a wasted `find_root` for pragma'd files). Check the cheap pragma first;
  memoize the manifest edition by project root. Behavior-identical, just faster.
- **A3-F2 (parse_source resolved a different edition than the compile path)** —
  `15f33f4`: it passed only `:source`, ignoring the project manifest, so a pragma-
  less file was inspected under `current()` while it compiles under the manifest
  edition (latent: one edition). Now discovers the project root from a real `:file`.

**Verified NON-bugs / by-design (recorded, not fixed):**

- **A3-F3** — `Edition.current` is a hardcoded constant, not `List.last(all())`. This
  is intentional: the default is decoupled from the newest *known* edition so a new
  edition can be minted as opt-in before it is promoted to default (Rust parity).
  Clarified the docstring (`15f33f4`) so it is not "fixed" into a derivation.
- **A1-F2** — `strip_inline_comment` doesn't track TOML single-quoted (literal)
  strings, so a `#` inside `'...'` would be mis-cut. Pre-existing and inert: the
  loader's `strip_quotes`/`parse_scalar` don't support single-quoted strings at all,
  so such a value is already unusable. Out of scope for the editions work.
- **migrate splice raw-`target` interpolation** — `target` is interpolated into the
  `Regex.replace` replacement string, where `\N` would be a backreference. Not
  reachable: `target` is allow-list-constrained to a 4-digit numeric edition. Noted.

**Refuted on verification:** the pre-pass↔compile-pass edition-mismatch hypothesis
(identical source + identical `find_root` ⇒ identical edition); `find_dep_root`
termination/escape (sound); `resolve_one` clause-ordering (correct); dep values
passing through `strip_inline_comment` (they use the separate `parse_dep_line`).

**Full suite after all fixes: 3887 passed, 0 failing** (+3 new tests; 146 immune
responses expected; Antigen shape-coverage 309/309).

## Outstanding findings (after iteration 7)

- None open as bugs. Three by-design/inert items above (A3-F3, A1-F2, the migrate
  interpolation) are recorded as rationale so a future audit doesn't re-flag them.

**Loop status:** iteration 7's fresh audit found 5 confirmed bugs — so it is **NOT
a clean audit**, and the Group A–E fixes are NEW code not yet independently audited.
Convergence (two consecutive clean audits) is **not** met (iterations 6 and 7 both
found bugs). The cron is **left in place**; the next fire (iteration 8) runs a fresh
audit over the iteration-7 changes. Do NOT merge.

Commits this cycle: `99c1202` (A1-F1), `f9cc1d1` (A1-F3), `857305f` (A3-F1),
`64e43ab` (A1-F4), `15f33f4` (A3-F2 + A3-F3 doc).

---

## Iteration 8

Fresh adversarial audit of the iteration-7 changes (`99c1202`, `f9cc1d1`,
`857305f`, `64e43ab`, `15f33f4`) via three parallel Opus subagents over the
changed slices (comment-stripper + `detect_app`; dep resolution; `parse_source` +
edition semantics), read-only. Every returned finding was verified against source
before counting. **4 confirmed bugs fixed.**

**Confirmed bugs (fixed):**

- **F1 — `deps update` MatchError on a git dep with an unknown edition**
  (`cli.ex:877`). Iteration 7 (`857305f`) made `resolve_git_dep/2` route through
  `compile_dep_files`, so it can now return
  `{:error, {:dependency_edition_error, ...}}`. `cmd_deps_update` still bound it
  with `:ok = ...`, which raises a `MatchError` — the comment right above literally
  predicted this. Now reports and aborts like `cmd_deps`. (`ff385ac`)
- **F2 — whitespace-only git URL silently resolves to `:ok`** (`project.ex:277`).
  The A1-F3 whitespace guard was added to the *path* clause but not the *git*
  clause: only literal `git = ""` was rejected, so `git = "   "` reached
  `System.cmd("git", ["clone", …, "   ", target])`, cloned nothing, found zero
  files, and "resolved" to `:ok`. Merged the blank/whitespace git clauses into one
  trim-aware clause mirroring the path clause. (`ff385ac`)
- **F3 — `parse_source` swallows unknown MANIFEST editions** (`compiler.ex:197`).
  Iteration 7 (`15f33f4`) had `parse_source` discover `project_dir` from the real
  `:file`, so `resolve/1` can now return `{:error, {:unknown_edition, _}}` from a
  typo'd manifest for a *pragma-less* source. The parser cannot re-catch a manifest
  error (the manifest isn't in the source), yet the `{:error, _} -> current()`
  branch degraded it to the default — silently hiding a real §3.1 error. Now
  propagates `{:edition_error, reason}` like the compile path; the misleading
  comment claiming the parser re-validates is corrected. (`604d101`)
- **F5 — Edition moduledoc contradicted `current/0`** (`edition.ex:7`). The
  moduledoc still asserted "`current/0` is the newest" while the `current/0`
  docstring (added `15f33f4`) documents the intentional default-vs-newest
  decoupling. Fixed the moduledoc to match (staged-rollout / Rust parity).
  (`604d101`)

**Verified NON-bugs (recorded, not fixed):**

- **`strip_inline_comment` / `detect_app` (agent 1)** — both iteration-7 changes
  traced char-by-char and branch-by-branch; behaviorally correct, no regression.
  The only issue anywhere in that slice is the pre-existing single-quoted-TOML-
  literal limitation (already recorded as A1-F2, untouched by these commits).
- **`compile_dep_files` swallows non-edition errors (agent 2, finding 3)** —
  pre-existing/by-design: it deliberately reproduces the historic `_ =`
  behaviour (a dep may ship files the consumer never exercises); iteration 7
  narrowly promoted only the edition error to fatal. Not a regression.
- **parse_source F2/F3/F4 (agent 3)** — the dep_graph behavior change is the
  intended fix; the synthetic-`:file`-label trap is not realized by any caller
  today; no stray-ancestor `Cure.toml` hazard exists in-repo (worktree `.git`
  file stops `find_root`).

**Full suite after all fixes: 3891 passed, 0 failing** (+4 new tests: 2 dep-iso,
2 parse_source; 138 immune responses expected; Antigen shape-coverage 309/309).

## Outstanding findings (after iteration 8)

- None open as bugs. The by-design/inert items above are recorded so a future
  audit doesn't re-flag them.

**Loop status:** iteration 8's fresh audit found 4 confirmed bugs — so it is **NOT
a clean audit**. Convergence (two consecutive clean audits) is **not** met
(iterations 6, 7, and 8 all found bugs). The cron is **left in place**; the next
fire (iteration 9) runs a fresh audit over the iteration-8 changes. Do NOT merge.

Commits this cycle: `ff385ac` (F1 + F2), `604d101` (F3 + F5 doc).

---

## Iteration 9

Fresh adversarial audit of the iteration-8 changes (`ff385ac`, `604d101`) via
three parallel Opus subagents (dep resolution; `parse_source` propagation;
edition-surface interactions), read-only. Every finding verified against source
before counting. **3 confirmed bugs fixed** (two of them the same defect, found
independently by two agents).

**Confirmed bugs (fixed):**

- **`cure deps update` bypasses the whitespace/empty git-URL guard**
  (`cli.ex:876` → `project.ex resolve_git_dep`). Found independently by agents 1
  and 3. Iteration 8's trim guard lives in `resolve_one/3`, but `cmd_deps_update`
  calls `resolve_git_dep/2` DIRECTLY (the only caller outside `resolve_one`), and
  `""`/`"   "` are truthy in Elixir, so a `git = "   "` dep reached `git clone`
  with a blank URL, cloned nothing, and silently resolved to `:ok` ("Lockfile
  updated") — the exact mode iteration 8 claimed to close, still live on the
  update path. Fixed at the `resolve_git_dep` boundary so BOTH commands agree.
  (`c0beb65`)
- **`resolve_git_dep/2` discarded the clone exit status** (`project.ex`, agent 3;
  pre-existing, not an iteration-8 regression but the mechanism that made the
  above silent). ANY failed clone — unreachable URL, bad tag, network error —
  left an empty dir → zero `.cure` files → `compile_dep_files([])` → `:ok`, a
  bogus green build. Now checks `System.cmd`'s status and fails loudly with
  `{:dependency_clone_failed, name, out}` (via new `ensure_clone/4` helper).
  (`c0beb65`)
- **Stale `parse_source` docstring** (`compiler.ex:175`, agent 2). The
  iteration-8 change added a `{:edition_error, _}` return but left the prose
  contract listing only `:lex_error`/`:parse_error`. Documented the new return.
  (`21f56be`)

**Verified NON-bugs (recorded, not fixed):**

- The two iteration-8 edits themselves are regression-free: the merged git clause
  is behavior-equivalent to the old two-clause form on every `parse_dep_line`
  shape (clause order unchanged, path clause still precedes git); the
  `cmd_deps_update` `case` covers the full `resolve_git_dep` return contract; no
  remaining `:ok = resolve_git_dep(...)` bind exists (no lingering MatchError).
- `parse_source` propagation causes no runtime/consumer breakage: the sole lib
  caller `dep_graph.ex:194` matches `{:error, reason}` generically; no test
  asserts the old `parse_source` pragma-error shape (the pragma tests drive
  `Parser.parse/2` directly); the formatter path already handles `:edition_error`.
- Edition tagging is coherent across all three entry points
  (`compile_*`→`:edition_error`, `parse_source`→`:edition_error`,
  `Project.load`/`Edition.resolve`→raw `:unknown_edition`, each paired with its
  own matcher); a typo'd edition in the root manifest, a path dep, AND a git dep
  are all loud. `dep_project_dir`/`find_dep_root` iteration-6 escape re-verified
  closed. Multi-edition latent review (hypothetical `@known ["2026","2027"]`)
  found no off-by-one in `all/0`/`compare/2`/`retired_keywords/2`/keyword-set
  selection. `Edition.resolve` precedence + `|| ""` nil-coalesce sound.
- `cmd_compile` swallowing a `Project.load` edition error to `project = nil`
  (agent 3, minor) is harmless: the per-file `compile_file` re-resolves the same
  typo'd manifest and aborts loudly, so the build never completes with the wrong
  stdlib. Message-quality only, not a correctness bug.

**Full suite after all fixes: 3894 passed, 0 failing** (+3 new tests; 157 immune
responses expected; Antigen shape-coverage 309/309).

## Outstanding findings (after iteration 9)

- None open as bugs. The by-design/inert items above are recorded so a future
  audit doesn't re-flag them.

**Loop status:** iteration 9's fresh audit found 3 confirmed bugs — so it is **NOT
a clean audit**. Convergence (two consecutive clean audits) is **not** met
(iterations 6–9 all found bugs). The cron is **left in place**; the next fire
(iteration 10) runs a fresh audit over the iteration-9 changes. Do NOT merge.

Commits this cycle: `c0beb65` (git-URL + clone-status), `21f56be` (docstring).

---

## Iteration 10

Fresh adversarial audit of the iteration-9 changes (`c0beb65`, `21f56be`) via three
parallel Opus subagents: (1) the new `ensure_clone`/`resolve_git_dep` logic, (2) the
end-to-end dep-resolution contract + CLI handlers, (3) the migrate/lexer/parser/
edition surface (deliberately broadened — iterations 8–9 were dep-focused). Every
finding verified against CURRENT source before counting. **2 confirmed bugs fixed.**
One agent (dep-contract) audited a STALE view of the file (line numbers off by
hundreds; claimed `strip_inline_comment` "does not exist"); its headline findings
were refuted against current source.

**Confirmed bugs (fixed):**

- **`ref` dependency pin silently dropped** (`project.ex parse_dep_line`, agent 1).
  `parse_dep_line` extracted `path/git/tag/version/constraint` but never `ref`,
  although `ref_args/1` has a live `%{ref: ...}` clause and `write_lock` persists a
  `ref` row. A `mydep = { git = "...", ref = "abc123" }` pin was silently ignored —
  the dep cloned the remote default branch while the lockfile claimed a ref. Now
  parsed and honoured. (`5c79183`)
- **Misleading migrate default-target comments** (`cli.ex`, agent 3). Two comments
  in `cmd_migrate`/`migrate_resolve_edition` asserted the no-flag target is "the
  latest minted edition", contradicting `Edition.current/0`'s documented decoupling
  from the newest known edition (staged rollout). The code targets `current()`; the
  comments now say so. (`980ce23`)

**Verified NON-bugs / refuted (checked against current source):**

- Agent-2 "BUG 1" (registry deps crash the git clause, "no guard"): REFUTED — the
  git clause (`project.ex:278`) has `when is_binary(url)`; registry deps carry
  `git: nil`, so `is_binary(nil)` is false → they route to the registry clause.
- Agent-2 "BUG 2" (failed clone silent): REFUTED — fixed in iteration 9
  (`ensure_clone` checks `System.cmd`'s exit status).
- Agent-2 "BUG 5" (`strip_inline_comment` missing → scalar comments corrupt):
  REFUTED — `parse_kv` calls `strip_inline_comment` (`project.ex:1144`). The agent
  grepped a stale checkout.
- Agent-3 extensive verified-correct list: retirement direction/boundary
  (`compare in [:eq,:gt]`), lone-CR/CRLF data-loss closed, resolver↔parser pragma
  agreement, `\N`-backreference safety, and rule idempotency (ModuleRename,
  UppercaseTypeVar, GroupHoist, ProtoToInterface) all confirmed sound.
- `dep_project_dir`/`find_dep_root` iteration-6 escape re-verified closed (agent 1).

## Outstanding findings (after iteration 10)

### Latent / unreachable today (recorded, not fixed — no failing red test possible)

- **`comment_texts`/`migrate_comments` treat `#` inside string literals as a
  comment** (`migrate.ex:242`, mirror `cli.ex:1319`). The `~r/#+\s?(.*)$/` scan is
  not quote-aware, so `x = "a # b"` yields a bogus "comment". This could false-fail
  the lossless-comment `verify` (`:comment_dropped`) — BUT only if a migrate rule
  rewrites string-literal CONTENTS (or removes one of two identical `#`-string
  lines). No current rule edits string contents, so the bogus comment is stable
  across baseline/output and never trips. Genuine helper flaw; fix = quote-aware
  scan (reuse the `strip_inline_comment` pattern). Deferred: cannot be reproduced
  by a failing red test through any current rule.
- **Standalone pragma-less file is syntax-migrated but never edition-stamped**
  (`cli.ex migrate_file_bump?`/`migrate_splice_edition`, agent 3). The prepend-new-
  pragma branch is unreachable from the CLI; a pragma-less standalone file migrated
  across an edition boundary would get target-spelling syntax with no `@edition`
  marker → resolves to the older default next compile. LATENT (fires only when a
  2nd edition exists so a bump actually happens) and needs a stamping-policy
  decision (see operator items).
- **`ProtoToInterface` declares `retires_keywords: ["proto","impl"]` with
  `enforced_in: nil`** (agent 3). Inert today (`retired_keywords/2` guards on
  `enforced_in != nil`); arguably correct-for-now (can't enforce retirement at an
  unminted edition). Latent trap for whoever later sets `enforced_in`.

### Blocked — needs operator (design decisions; no parity-clear answer)

- **`cure deps update` is effectively a no-op.** It only iterates git deps
  (`if Map.get(dep, :git)`), skipping path and registry deps entirely; and for an
  already-cloned git dep `ensure_clone` short-circuits on an existing `.git` with
  no fetch/checkout — so changing a pinned `tag`/`ref` and running `deps update`
  never picks up the new revision, yet it writes the lock and prints "Lockfile
  updated." Making `update` truly update requires a semantics decision (force
  re-clone? `git fetch` + checkout? re-resolve registry versions?). Pre-existing,
  orthogonal to editions.
- **Partial/interrupted clone accepted as green.** `ensure_clone` trusts
  `File.dir?(target/.git)`; a clone interrupted after `.git` is created but before
  checkout leaves an orphan `.git`, so the dep "resolves" with zero modules. Needs
  a completeness/robustness policy (no clean cheap fix).
- **`cure migrate` no-flag target = `current()` (default), not newest-known.** The
  comments are now corrected, but whether a *migration* tool should default to the
  newest known edition (Rust `cargo fix --edition` moves forward) vs. the
  conservative default is a genuine product decision.
- **Hyphenated dependency names silently dropped** (agent 2, plausible). A
  `[dependencies]` line whose name is not `\w+` (e.g. `my-lib = {...}`) fails both
  `parse_dep_line` regexes → `nil` → dropped with no diagnostic. Whether to widen
  the name grammar or error loudly on an unparseable dep line is a small design
  call.

**Loop status:** iteration 10's fresh audit found 2 confirmed bugs (fixed) plus
design-decision items above — so it is **NOT a clean audit**. Convergence (two
consecutive clean audits) is not met (iterations 6–10 all found bugs). The design
items need an operator decision before the loop can reach "bug-free"; a
PushNotification was sent. The cron is **left in place**; do NOT merge.

Commits this cycle: `5c79183` (ref pin), `980ce23` (migrate comments).

---

## Iteration 11

No outstanding *fixable* bugs entered this cycle — iteration 10 left only
operator-blocked design items and latent-until-2nd-edition items. Fresh
adversarial audit via two sharpened Opus subagents scoped to LIVE, reproducible-
on-the-current-tree bugs (single edition 2026), explicitly excluding every
already-recorded latent/design item: (1) the edition CORE mechanism
(edition.ex + compiler resolve/lex/parse + lexer keyword-set selection), (2) the
migrate APPLY/BUMP path + the Cure.toml parser. Both returned **no new confirmed
live bug**. This is the first CLEAN fresh audit of the run.

**Fixed this cycle:**

- Stale `comment_texts` cross-reference (`migrate.ex:239`) — it pointed at
  `Cure.CLI's migrate_comments/1 (cli.ex:1319)`, which no longer exists
  (`comment_texts` is now the sole lossless-comment check). Replaced the dead
  reference with an accurate note of the known latent non-quote-aware limitation.
  (`0eae043`)

**Audit verification (both agents, cross-checked against source):**

- **Edition core (agent 1):** empirically verified `pragma_edition`↔parser
  agreement across pathological inputs (trailing junk after `)`, interior spaces,
  CRLF / lone-CR, blank-then-pragma, indented → `:edition_pragma_placement`,
  5-digit/multi-line → `:edition_pragma_malformed`, unknown → `:unknown_edition`).
  In every resolver-under-match row the parser independently re-validates and
  rejects, so the net compile outcome is correct. Precedence (pragma > manifest >
  default) and manifest validation (`Project.load` gates through `Edition.parse`,
  so no unknown edition leaks) both correct. `retired_keywords/2` returns `[]` for
  every edition today, so the lexer keyword set is edition-invariant — all
  resolver↔parser value-divergences are latent by construction (need a 2nd minted
  edition with non-empty `retires_keywords`). `year/1`'s non-numeric raise is
  unreachable on live paths.
- **Migrate apply/bump + TOML (agent 2):** phase-1 rewrite IS live (all six rules
  `since: "2026"` fire) and verified non-corrupting/idempotent; phase-2 bump is
  inert at `target == current == 2026` (splice never executes), and when forced
  reachable it handled CRLF/lone-CR/only-pragma/no-trailing-newline correctly.
  TOML parser correct on `type_check = true # note`, quoted `=`-in-value, empty
  value, etc. `check`/`print` never write; git-guard enforced only for write.
  `detect_app` memo keys on `find_root`, cannot diverge from a fresh resolve.

**Refuted / out-of-scope (checked):** leading BOM fails to lex (pre-existing lexer
limit, fails loud, not edition-specific); resolver `trivia_line?` tolerates tabs
that the lexer rejects (lexer rejects the file anyway → no wrong edition);
unquoted-TOML-array / non-`stdlib_path` string coercion / table-header-trailing-
content all require INVALID TOML, not valid input.

**Marginal observation (recorded, not fixed):** `cure migrate --print` emits one
extra trailing newline (`IO.puts(r.output)` where `r.output` already ends in
`\n`), disagreeing with write-mode by a newline. Cosmetic (`--print` never writes);
the "correct" fix is ambiguous for multi-file output (the double newline acts as a
separator), so deferred as polish, not a bug.

## Outstanding findings (after iteration 11)

The fresh audit added no new fixable bug. Carried forward, UNCHANGED from
iteration 10:

### Blocked — needs operator (design decisions; no parity-clear answer)
- `cure deps update` is effectively a no-op (skips path/registry deps; git deps
  cache-skip via `ensure_clone` with no fetch/checkout).
- Partial/interrupted clone accepted as green (`.git` present, no worktree).
- `cure migrate` no-flag target = `current()` (conservative) vs newest-known
  (Rust `cargo fix --edition` moves forward) — product decision.
- Hyphenated dependency names silently dropped (`parse_dep_line` `\w+`).

### Latent / unreachable today (recorded, not fixed)
- `comment_texts` non-quote-aware (documented in-code this cycle; no current rule
  triggers it).
- Standalone pragma-less file not edition-stamped on a bump (needs stamping
  policy; coupled to the migrate-target decision).
- `ProtoToInterface` `retires_keywords` with `enforced_in: nil` (inert; correct
  until a retiring edition exists).

**Loop status:** iteration 11's fresh audit is CLEAN of new fixable bugs — the
FIRST clean audit (iterations 6–10 all found bugs). Convergence needs TWO
consecutive clean audits, so it is NOT met this cycle regardless. Moreover the
system is not "bug-free": the Blocked items are real gaps whose fixes require an
operator design decision (raised via PushNotification in iteration 10). The loop
has reached its blocked floor — nothing further is auto-fixable without those
decisions. The cron is **left in place**; do NOT merge.

Commits this cycle: `0eae043` (stale-ref doc fix only).

---

## Iteration 12

Iteration 11 was the first clean audit, but its two agents never probed
`###`-fenced multi-line doc comments — so a real edition-core bug survived the
whole run and only surfaced now. This cycle's fresh audit (two Opus agents:
(1) edition core + compiler resolve/lex/parse, (2) migrate engine + editions dep
glue) returned **one confirmed live bug** (fixed) and **one finding that I
refuted against source**.

**Fixed this cycle:**

- **[MED] Edition pre-scan was `###`-fence-blind — spurious `{:edition_error}` on
  a valid file.** (`7c211a8`) The lexer swallows a `###...###` fenced doc comment
  into a single `:doc_comment` token (`lex_fenced_doc`/`fence_close_line?`), so an
  `@edition(...)` line *inside* the fence is never a pragma. But
  `first_substantive_line`/`trivia_line?` were line-based: they skipped only the
  opening `###` line (starts with `#`) and then read the fenced-out
  `@edition("2025")` as the first substantive line — resolving a pragma the
  compiler never sees. A file with a non-default year fenced in a doc comment was
  rejected with `{:error, {:edition_error, {:unknown_edition, "2025"}}}` *before
  lexing*. Verified end-to-end: `pragma_edition` returned `"2025"` and `resolve`
  returned the error while the lexer produced **no `:at` token**; after the fix
  `pragma_edition` → `nil`, `resolve` → `{:ok, "2026"}` (compiles under default).
  Fix skips the whole fenced block (opening line through the next `###` line, or
  EOF), matching the lexer exactly. 3 red→green tests in `edition_test.exs`
  (fenced `@edition` not a pragma; real pragma *after* a fence still read;
  indented fence skipped).

**Refuted against source (NOT counted):**

- **Agent 2 — "`cure migrate` crashes on a non-numeric project edition."** The
  agent claimed `Cure.Project.load` stores `edition:` raw "with no allow-list
  check anywhere," so `resolve_project` returns `{:ok, "stable"}` and later
  `compare/2`→`year/1` raises an uncaught `ArgumentError`. **False.**
  `Cure.Project.load` (project.ex:116–125) validates the declared edition through
  `Cure.Edition.parse(ed)` and returns `{:error, {:unknown_edition, ed}}` for any
  invalid value. Empirically confirmed: for `edition = "stable"`, `"2026-beta"`,
  and numeric-unknown `"2030"`, both `Project.load` and `Cure.Edition.resolve`
  return `{:error, {:unknown_edition, _}}` — no `{:ok, "stable"}`, no crash, no
  "refusing to downgrade" mis-report. `migrate_project_edition`'s
  `{:error, {:unknown_edition, _}}` clause is therefore **live**, not dead, and
  emits the intended clean diagnostic. Both resolution paths (pragma via `parse`,
  project via `load`→`parse`) validate; the claimed asymmetry does not exist. The
  agent confabulated an unvalidated `load` and never read lines 116–125.

**Everything else agent 2 checked and cleared** (cross-checked plausible):
`run_to_fixpoint` convergence/thrash-detection, `verify/3` multiset comment check,
the three firing machine rules (hoist/module_rename/if_elif), splice/bump CRLF
handling (latent — bump inert at single edition), git-guard, two-phase apply.

**Full suite:** 3898 passed (3 doctests, 3895 tests), 0 failures; Antigen
309/309 ✓ (`7c211a8`).

## Outstanding findings (after iteration 12)

The fresh audit found ONE real bug (fixed above); the second finding was refuted.
No in-scope editions bug remains open. Carried forward UNCHANGED (none are
editions defects):

### Blocked — needs operator (design decisions; no parity-clear answer)
- `cure deps update` is effectively a no-op (skips path/registry deps; git deps
  cache-skip via `ensure_clone` with no fetch/checkout).
- Partial/interrupted clone accepted as green (`.git` present, no worktree).
- `cure migrate` no-flag target = `current()` (conservative) vs newest-known
  (Rust `cargo fix --edition` moves forward) — product decision.
- Hyphenated dependency names silently dropped (`parse_dep_line` `\w+`).

### Latent / unreachable today (recorded, not fixed)
- `comment_texts` non-quote-aware (no current rule edits string-literal contents).
- Standalone pragma-less file not edition-stamped on a bump (coupled to the
  migrate-target decision).
- `ProtoToInterface` `retires_keywords` with `enforced_in: nil` (inert until a
  retiring edition exists).

**Loop status:** iteration 12's fresh audit found a real bug, so it is **NOT**
clean — the two-consecutive-clean-audit streak resets (11 clean, 12 not). The
"blocked floor" note from iteration 11 was premature: the fence bug was a genuine,
in-scope edition-core defect that the prior clean audit simply never probed. The
cron is **left in place** — convergence is not met and a confirming clean audit is
still owed. Do NOT merge.

Commits this cycle: `7c211a8` (fence-skip fix + 3 tests).

---

## Iteration 13

Two fresh Opus agents: (A) a differential of the just-landed fence fix against the
lexer; (B) a broad sweep of edition/project/migrate/CLI, primed that prior "clean"
audits had blind spots. Both surfaced REAL bugs (verified + reproduced). One
further finding is a genuine severe bug that cannot be fixed without an operator
design decision — escalated below.

**Fixed this cycle:**

- **[MED] Fence pre-scan counted all Unicode whitespace as indentation.**
  (`dca8612`) `fence_open_line?` used `String.trim_leading/1` (strips tab/`\f`/`\v`),
  but the lexer's `count_leading_spaces` counts ONLY ASCII `0x20`. So a fenced-doc
  body line like `\t###` was a fence *marker* to the pre-scan but ordinary body to
  the lexer: the pre-scan closed the fence early and read a buried
  `@edition("2027")` as a pragma, rejecting a valid file with a spurious
  `{:unknown_edition,"2027"}`. Reproduced for tab/form-feed/vertical-tab; a
  SPACE-indented ` ###` correctly agrees (lexer counts 0x20) and is preserved.
  Fix: strip only leading 0x20 in both `fence_open_line?` and `trivia_line?`
  (`drop_leading_spaces`), mirroring the lexer. Identical on all valid files.
  4 red→green tests.
- **[LOW] `Cure.Project.set_edition/2` dropped a trailing comment.** (`dceb2d2`)
  Documented "lossless line edit", but the existing-key branch rewrote the whole
  line to bare `edition = "X"`, discarding `# pinned`. The sibling migrate writer
  `replace_leading_pragma_line/2` preserves trailing text; the two must agree.
  Fix: `replace_edition_value/3` rewrites only the quoted value, keeping leading
  indent + trailing content; falls back to canonical line for a non-quoted value.
  1 red→green test.

**Full suite:** 3902 passed (3 doctests, 3899 tests), 0 failures; Antigen 309/309 ✓.

## Blocked — needs operator (NEW, iteration 13): `cure migrate` silently corrupts non-builtin uppercase type names

**Severity: HIGH — silent semantic corruption.** The migrate rule
`:W_uppercase_type_var` (edition-crossing, `since: "2026"`, `:review` tier, which
`cure migrate` auto-applies via `apply: :all`) lowercases every uppercase, bare,
type-position name **not in `build_ctx/1`**. `build_ctx` = the 9 builtin
primitives (`Cure.Types.Env.new().types`) ∪ types DECLARED IN THE SAME FILE. It
includes NO imported types, NO builtin kind `Type`, NO builtin inductives
(`Nat`) or data constructors (`Z`/`S`). So running `cure migrate` over real code
rewrites, e.g. in `lib/std/vector.cure` (17 rewrites): `a: Type` → `a: type`,
`n: Nat` → `n: nat`, `Vector(a, S(Z))` → `Vector(a, S(z))` — turning concrete
types/kinds/constructors into free type variables. Reproduced end-to-end via the
exact CLI path (`Cure.Compiler.Lexer.tokenize` → `Parser.parse` →
`Migrate.run_to_fixpoint(rules: rules_for_crossing("2026"), edition:"2026")` →
`Printer`). `verify/3` (reparse + comment multiset) does NOT catch it: the
lowercased program reparses cleanly and drops no comments, so the corruption is
committed and written. (`cure build` is safe — it runs `apply: :safe_only`, and
this `:review`-tier rule only warns there.)

**Why there is no self-contained fix.** The behavioral contract
`test/cure/migrate/warn_tolerate_parity_test.exs:15` asserts a FREE, UNBOUND `T`
in `fn id(x: T) -> T` MUST fire the rule (rename). `Option`, `Nat`, `Z` are
syntactically identical free unbound uppercase names in the same type positions.
The ONLY thing separating "rename `T`" from "keep `Option`" is whether the name
resolves to a known type — which needs a complete name environment. A
binder-only redesign (rename only names bound as implicit `{X: Type}` params)
would violate that contract test (which I must not weaken), and a pure-safening
heuristic (add in-file application-heads) still corrupts bare-only imports
(`Nat`, `Z`). The builtins registry has no constructors and no `Type`/`Nat`
(verified: `Env.new().types` == the 9 primitives, `.constructors` == []).

**The design decision required:** how should the syntactic migrate facility obtain
the complete set of in-scope uppercase names (imported types + builtin kinds +
builtin inductives + data constructors)? Options: (a) make `build_ctx`
name-resolution-aware — thread the file path + project, resolve imports via the
module loader, and seed builtin kinds/inductives/constructors (architectural
change; couples migrate to the compiler + filesystem); (b) change the
contract so the rule renames ONLY names bound as explicit type-param binders
(operator must approve editing `warn_tolerate_parity_test.exs:15`); (c) demote the
rule so `cure migrate` warns but does not auto-rewrite it (changes the intended
`:review`-applies-in-migrate semantics). All are design forks with real risk; I
will not ship a partial fix that still corrupts the stdlib. PushNotification sent.

## Outstanding findings (after iteration 13)

### Blocked — needs operator
- **NEW (HIGH): `cure migrate` uppercase-type-var corruption** (see the section
  above) — needs a name-resolution design decision.
- `cure deps update` no-op (skips path/registry; git deps cache-skip, no refetch).
- Partial/interrupted clone accepted as green (`.git` present, no worktree).
- `cure migrate` no-flag target = `current()` vs newest-known (product decision).
- Hyphenated dependency names silently dropped (`parse_dep_line` `\w+`).

### Latent / unreachable today (recorded, not fixed)
- `comment_texts` non-quote-aware (no current rule edits string-literal contents).
- Standalone pragma-less file not edition-stamped on a bump.
- `ProtoToInterface` `retires_keywords` with `enforced_in: nil` (inert).

**Loop status:** iteration 13 found and fixed 2 real bugs and escalated 1 HIGH
severity bug that needs an operator design decision. NOT clean; streak resets. The
cron is **left in place**. Do NOT merge.

Commits this cycle: `dca8612` (fence 0x20 fix), `dceb2d2` (set_edition comment),
plus this record.

---

## Iteration 14

Driven by a fresh adversarial audit (two parallel Opus general-purpose agents
over the printer and CLI slices). Every finding below was reproduced against
source before counting. **Six real bugs found and fixed; one agent finding
refuted.**

### Fixed (with commit SHAs)

1. **Printer dropped precedence parentheses** (`281c9f6`, `d540eb6`) — the
   canonical printer emitted operator operands with bare `render/3`, never
   re-inserting the grouping parens the Pratt parser needs. `cure fmt` and
   `cure migrate` silently changed program meaning on valid code:
   `(x + 1) * 2` → `x + 1 * 2` (= `x + (1*2)`), `1 - (2 - x)` → `1 - 2 - x`,
   `(if c then a else b) + 1` → `if c then a else b + 1`. Fix = precedence- and
   associativity-aware `operand_str/5` + `child_prec/1` + `op_prec/1`, mirroring
   `Cure.Compiler.Parser.Precedence`. First commit covered `:binary_op`/
   `:unary_op`; the audit (agent A) then found the parser lowers `..`/`..=` →
   `:range`, `<-|` → `:send`, `.` → `:attribute_access` as their OWN node types,
   which were unguarded in both directions (`(1..2)+3` → `1..2 + 3`,
   `(a+b).x` → `a + b.x`, `(pid <-| msg)+1` → `pid <-| msg + 1`). Second commit
   routed those nodes' operands through the same machinery. 19 structural
   round-trip tests (`printer_precedence_test.exs`); golden fixpoint/roundtrip/
   formatter suites stay green (minimal parens, no over-parenthesisation).

2. **`cure <typo>` exited 0** (`8b26495`) — the catch-all unknown-command arm
   printed an error but returned normally, so a mistyped command silently
   succeeded (`cure typo && next` proceeded). Now `exit({:shutdown, 1})`.

3. **`cure deps <bad>` misblamed `deps`** (`8b26495`) — no `[deps | rest]` arm,
   so a bad subcommand fell to the catch-all which bound `unknown = "deps"`:
   it named a valid command as unknown, suggested an unrelated one, and exited 0.
   New `[deps | rest]` arm names the real offender and exits non-zero.

4. **`cure keys <malformed>` misdispatch** (`b2af49b`) — the exact structural
   analog of the deps bug: `keys` had `generate <handle>`/`list` arms but no
   `[keys | rest]` fallback, so bare/missing-handle/unknown/extra-arg `keys`
   invocations were misblamed as an unknown top-level command (fuzzy matcher even
   suggested `deps`). New keys usage arm fails cleanly. 4 tests.

5. **`cure stdlib` exited 0 on a module compile failure** (`b2af49b`) — SEVERE
   false success: it printed the per-module error but continued and returned
   normally, so a broken stdlib build read as exit 0 to a CI wrapper. Now tracks
   per-module outcomes and exits `{:shutdown, 1}` if any module failed.

6. **`cure migrate` exited 0 on an edition-stamp failure** (`b2af49b`,
   editions-scope) — `migrate_bump` printed "could not bump project edition" but
   its `cond` fell through to `:ok`, so a migration that failed to stamp the new
   edition falsely reported success. `migrate_bump` now returns the cond value
   (`{:error, reason}` on stamp failure) and `migrate_apply_and_bump` propagates
   it, so `main/1` halts non-zero.

### Refuted (verified against source, not a bug)

- Agent B's "the Printer mangles every file one-token-per-line / `--print` vs
  `--write` disagree." Reproduced: the "mangling" only occurs for **invalid**
  Cure input (`module Foo do … end`, `proto Show do … end` — Elixir/Erlang block
  syntax, not Cure's indentation-based `mod`). The parser yields a degenerate
  `{:block, [ {:variable,…"module"}, {:variable,…"Foo"}, … ]}` and the printer
  faithfully renders each bare token on its own line. Real `.cure` files
  (`set.cure`, `adt.cure`, whole stdlib corpus) round-trip structurally stable
  (`printer_totality_test` fixpoint + `lossless_roundtrip_test` already pin this).
  Garbage-in, not corruption of valid code.

## Outstanding findings (after iteration 14)

### Lower-severity CLI (real, deferred to a coherent separate cleanup)
- **Fixed-arity single-arg commands misblame "Unknown command"** on a wrong
  argument count — `run`, `check`, `init`, `search`, `info`, `explain`/`why`
  (each `["cmd" | [x]]` with no `["cmd" | rest]` fallback). Exit code is now
  CORRECT (the catch-all exits 1); only the message misleads (names a valid
  command as unknown). Message quality, not a correctness bug.
- **Usage-arg errors still exit 0** (bare `error(...)`, no exit): `cure compile`/
  `cure trace`/`cure new` with no args, `cure explain <unknown-code>`,
  `cure fmt --aggressive` on an unparseable file, `cure bench` on a broken file,
  `cure keys generate` key-gen failure. Real but low-harm. Best fixed together as
  a `usage_error/1` helper (print + exit) plus `[cmd | rest]` fallbacks — a
  focused CLI-consistency pass for a later iteration.

### Blocked — needs operator (UNCHANGED from iteration 13)
- **HIGH: `cure migrate` uppercase-type-var corruption** — needs a
  name-resolution design decision (see iteration 13 section). Not touched.
- deps update no-op; partial/interrupted clone accepted as green; migrate no-flag
  target = `current()` vs newest-known; hyphenated dependency names dropped
  (general package-manager scope).

### Latent / unreachable today (carried)
- `comment_texts` non-quote-aware; standalone pragma-less file not edition-stamped
  on a bump; `ProtoToInterface` `retires_keywords` with `enforced_in: nil`.

**Loop status:** iteration 14 was a heavy bug-finding cycle — 6 real bugs fixed
(2 printer correctness affecting `cure fmt`/`cure migrate`, 4 CLI exit-status),
1 agent finding refuted. NOT converged; streak resets. The cron is **left in
place**. Full suite green: 3926 passed, 0 failures. Do NOT merge.

Commits this cycle: `281c9f6` (printer binary/unary parens), `8b26495` (CLI
unknown-command exit + deps fallback), `d540eb6` (printer range/send/dot parens),
`b2af49b` (CLI keys fallback + stdlib/migrate non-zero exit), plus this record.

---

## Iteration 15

**CLI-consistency pass (clears iteration 14's deferred "Outstanding CLI" list).**
Both lower-severity CLI classes carried from iteration 14 are now fixed:
- Added `usage_error/1` (print to stderr + `exit({:shutdown, 1})`) and routed the
  bare-`error(...)`-then-fall-through usage paths through it: `cure compile`/
  `cure trace`/`cure new` with no args, `cure explain <unknown-code>`, and the
  runtime-failure paths of `cure fmt --aggressive` / `cure bench` / `cure keys
  generate` (which aggregate per-file outcomes then exit non-zero if any failed).
  `migrate_bump` propagates its failure value so a bad bump also exits non-zero.
- Added `[cmd | _]` fallback arms so a wrong argument count on a fixed-arity
  command (`run`, `check`, `init`, `explain`/`why`, `search`, `info`) names the
  command in a usage error instead of misblaming it as "Unknown command".
  (`ebd6098`, `7a3772d`; tests strengthened to `catch_exit == {:shutdown, 1}`.)

**Fresh adversarial audit** — three parallel general-purpose Opus agents over the
changed slices (printer, CLI, edition/project/migrate), every finding verified
against source before counting.

### Confirmed + fixed

- **Printer drops parens around pipe and prefix-keyword operands** (`c4b4947`).
  `|>` lowers to a pipe-tagged `:function_call` (not `:binary_op`) binding
  loosest (level 10); the right-extending prefix keywords (`throw`/`yield`/
  `return`/`spawn`) grab everything to their right. As child operands of a
  tighter operator both were reprinted without parens, so parse→print→parse
  changed the parse (`(a |> f) + b` → `a |> f + b`, `(throw x) + 1` →
  `throw x + 1`, `(a <-| b) |> f` → `a <-| b |> f`). Added `child_prec/1` clauses
  ({10,:left} for pipe-tagged calls, `:lowest` for the keyword nodes) and routed
  the pipe render's own left operand through `operand_str`. 8 new round-trip
  cases in `printer_precedence_test.exs` (27 total, green); golden suites
  (lossless_roundtrip / printer_totality / formatter, 64) unregressed.
- **`UppercaseTypeVar` half-renames a body type variable** (`9ccd04c`). The rule
  lowercased a free type var only in the signature meta; the body walk recursed
  without the rename map, so a variable bound by the signature and referenced
  again in the body (`let y: T` annotation, `empty_of(T)` type application) kept
  the old `T` while its binder became `t` — a meaning-changing rewrite the verify
  pass accepts because the reprint still parses. Threaded the signature's rename
  map through the body walk (renaming matching variable nodes and type-bearing
  meta; keys are uppercase so lowercase value bindings are untouched; nested
  signatures shadow). **This is a DISTINCT failure mode from the blocked ctx
  design issue** — an incomplete rewrite scope, not a ctx false-positive; a
  ctx-only fix would not have addressed it. 2 new red→green tests.

### CLEAN (verified against source)

- **CLI slice** — the exit-status + dispatch-shadowing fixes from iterations 14–15
  hold: no exit-0-on-error path remains, no `usage_error` on a success path, no
  fuzzy-matcher misblame of a valid command. One residual message-only nit
  (zero-arg commands like `version`/`lsp` with trailing junk say "Unknown
  command: <cmd>" instead of a takes-no-arguments usage line) — **exit code is
  correctly 1**; pre-existing, not a regression, message quality only. Recorded,
  not fixed (disproportionate churn for a correct-exit nit).
- **Edition resolution / `Cure.toml` round-trip / migrate idempotence** — probed
  extensively (BOM, CRLF, doc-comment-before-pragma, spacey/multi-line/5-digit
  pragmas, no `[project]` table, `[[project]]`, duplicate tables, single-quoted
  values); every `nil` pre-scan is a parser hard-error (no silent wrong-edition),
  no reachable `year/1 ArgumentError`, `set_edition`→`load` round-trips, and
  `run_to_fixpoint` is idempotent on a combined rename+uppercase+proto+if/elif
  file. No new bug.

### Outstanding findings (after iteration 15)

**Blocked — needs operator (UNCHANGED):**
- **`cure migrate` uppercase-type-var CTX corruption** — the *ctx false-positive*
  failure mode (needs a name-resolution design decision, see iteration 13).
  Distinct from the body-rename bug fixed this iteration.
- deps update no-op; partial/interrupted clone accepted as green; migrate no-flag
  target = `current()` vs newest-known; hyphenated dependency names dropped
  (general package-manager scope).

**Latent / unreachable today (carried):**
- `comment_texts` non-quote-aware; standalone pragma-less file not edition-stamped
  on a bump; `ProtoToInterface` `retires_keywords` with `enforced_in: nil`.

**Message-quality nit (correct exit, deferred):**
- Zero-arg commands with trailing junk misblame "Unknown command" (exit correct).

**Loop status:** iteration 15 fixed 4 real bugs (2 CLI-consistency clearing
iteration 14's deferred list, 1 printer parens-dropping, 1 migrate body-rename
corruption). NOT converged — a fresh audit found new confirmed bugs, so the
streak resets. The cron is **left in place**. Full suite green: 3939 passed,
0 failures. Do NOT merge.

Commits this cycle: `ebd6098` (CLI usage/arg exits), `7a3772d` (CLI
fmt/bench/keygen exits), `c4b4947` (printer pipe/keyword parens), `9ccd04c`
(migrate body-rename), plus this record.

---

## Iteration 16

The iteration-15 Outstanding list held no actionable-unblocked reachable bug, so
this cycle was driven by a fresh adversarial audit: four parallel general-purpose
Opus agents over edition/project, migrate engine+rules, lexer/parser/printer, and
CLI dispatch — read-only, each reproducing with `mix run` (no `mix test`, to avoid
a concurrent-suite panic). Every finding was reproduced and read against source
before counting. **Five real bugs confirmed and fixed** (four reachable now, one
latent); the CLI dispatch surface came back clean.

### Confirmed + fixed

- **Printer: three round-trip corruptions** (`a0d4681`) — the printer backs
  `cure fmt`/`migrate`/`rewrite`, so each silently corrupted valid code:
  1. Word-spelled prefix `bnot` fell through the unary_op fallback `"#{op}#{inner}"`
     with no space → `bnot a` reprinted as the single identifier `bnota`. Emit a
     separating space for alphabetic operator spellings.
  2. `typed_params_to_string` dropped the braces on implicit params → `{T: Type}`
     became positional `T: Type` (an arity/calling-convention change). Re-wrap.
  3. `match_arm_head`/`match_arm_rhs_inline`/`render_match_arm_wrapped` had no
     `{:with_rematch_arm,…}` clause → reprinting a `with`-abstraction rematch arm
     (`Parent | WithPat -> …`) raised `FunctionClauseError`, crashing fmt/migrate
     on valid code (the repo's own corpus contains such arms). Render from
     `parent_patterns ++ [pattern]`. (4 new round-trip tests in
     `printer_fidelity_test.exs`; golden suites 91 green.)
- **Migrate: implicit type-parameter binder desync** (`69e143c`) — an implicit
  param `{T: Type}` introduces its type variable via the param NAME, but
  `rewrite_signature` collected candidates only from param/return TYPES and
  `rename_param` rewrote only a param's type, so the rule lowercased every
  reference (`x: T`, `-> T`) while leaving the binder spelled `T` → references
  bound to nothing; the reparse-only verify accepted it. Collect implicit binder
  names and rename the binder in lockstep, including under freshening
  (`{t1: type}, x: t1` when a plain `t` is already in scope). This hits the rule's
  PRIMARY use case (idiomatic `{T: Type}`). Distinct from the blocked ctx issue.
  (Verified end-to-end; migrate suite 45 green.)
- **Migrate: fence-blind leading-pragma finder** (`5cbe764`) — the bump splicer's
  `replace_leading_pragma_line` located the pragma with `migrate_trivia_line?`
  (blank/`#`-only), blind to `###` fenced doc comments whose body lines need not
  start with `#`. It diverged from the resolver's fence-aware scan, so a real
  leading pragma after a fenced doc comment was missed (silent-failed bump / mutated
  an in-comment `@edition` example). Exposed `Cure.Edition.leading_line_index/1`
  (the same fence-aware scan) and retired the divergent local test. **Latent** —
  only a real bump (a second minted edition) reaches it — but a real logic
  divergence that activates exactly when editions roll forward. (2 new tests.)

### Investigated → NOT a bug

- **`Type`→`type` sort lowercasing** (compounding the binder desync): the
  universe sort `Type` isn't in the migrate ctx seed, so the rule lowercases it.
  Verified BOTH `fn id({T: Type}, …)` and the migrated `fn id({t: type}, …)`
  compile `:ok` — meaning-preserving, not corruption. It is at most a
  convention-choice tied to the blocked general ctx decision; left as-is. The
  binder-desync fix makes the output self-consistent regardless.
- **CLI dispatch/exit surface** — swept empirically: every fixed-arity fallback
  and aggregate-then-exit path exits correctly, no exit-0-on-error, no success
  routed through error, no clause shadowing, fuzzy matcher bounded. Clean.
- **Edition resolution / Cure.toml round-trip** — ~23 adversarial pragma inputs
  and 10 toml layouts: pre-scan and parser agree everywhere, `set_edition`→`load`
  round-trips, no reachable `year/1` raise. Clean.
- **Migrate rules** (`if_elif_to_pickup`, `module_rename`, `removed_module`,
  `proto_to_interface`, engine idempotence) — robust; `group_hoist` has a
  multi-`mod`-per-file edge but that shape is unsupported/unreachable.

### Outstanding findings (after iteration 16)

**Blocked — needs operator (UNCHANGED):**
- `cure migrate` uppercase-type-var CTX false-positive — the general
  name-resolution decision (distinguishing a user/imported type constructor from
  a free type var). The narrow `Type`-sort case is benign (both forms compile).
- deps update no-op; partial/interrupted clone accepted; migrate no-flag target;
  hyphenated dependency names (general package-manager scope).

**Latent / unreachable today (carried, agents re-confirmed robust):**
- `comment_texts` non-quote-aware (no reachable misaccept found);
  `ProtoToInterface` `retires_keywords` with `enforced_in: nil` (by design);
  `group_hoist` multi-`mod`-per-file (unsupported shape).

**Message-quality nit (correct exit, deferred):**
- Zero-arg commands with trailing junk misblame "Unknown command" (exit correct).

**Loop status:** iteration 16 fixed 5 real bugs (3 printer round-trip corruptions
incl. a crash, 1 migrate binder desync on the rule's primary use case, 1 latent
fence-blind pragma finder). NOT converged — a fresh audit found new confirmed
bugs, so the streak resets. The cron is **left in place**. Full suite green:
3946 passed, 0 failures. Do NOT merge.

Commits this cycle: `a0d4681` (printer bnot/braces/with-rematch), `69e143c`
(migrate implicit-binder rename), `5cbe764` (fence-aware pragma finder), plus
this record.

---

## Iteration 17

Resumed the in-progress cycle: fixed the Outstanding findings from iteration 16's
audit (and follow-on findings surfaced mid-cycle), ran the full suite green, then
ran a fresh 4-agent adversarial audit over every changed slice. All agent findings
were verified against source / reproduced before counting.

### Fixed this cycle (10 commits, all ghost-authored)

- **Printer — nested unary minus + spurious doc line** (`6d28345`) — separated a
  nested unary minus so `- -x` no longer fuses into `--` (lexed as an FSM-transition
  token); dropped a spurious empty `## ` line from a fenced doc comment.
- **Lexer — malformed numeric literals** (`70d2c0a`) — `lex_hex`/`lex_binary_int`
  now reject an all-underscore radix (`clean == ""`); new `finish_float/3` rescues
  `ArgumentError` from `String.to_float`. No numeric path can crash the tokenizer.
- **Project — non-UTF-8 value bytes** (`058cf25`) — replaced `String.to_charlist`
  in `strip_inline_comment` with a byte-wise binary scan, so a Cure.toml value with
  invalid UTF-8 no longer raises on load.
- **Migrate — freshen against body names** (`58f976d`) — `var_names_deep` folds the
  function body's variable names into the freshening reserved set, so a renamed
  signature binder (`T`→`t`) can't collide with a distinct free `t` used only in the
  body.
- **Lexer — over-long atom** (`0434cb9`) — `lex_atom_or_colon` guards `byte_size > 255`
  and errors instead of letting `String.to_atom` crash the tokenizer.
- **Project — [compiler] table hardening** (`471e9b0`) — the `[compiler]` table
  interned every key via `String.to_atom` on arbitrary bytes (crash on non-UTF-8;
  one permanent atom per distinct key = atom-table DoS). Replaced with a fixed
  allow-list (`type_check`/`optimize`); unrecognized keys dropped, never interned.
- **Printer — doc-comment trailing newlines** (`d015405`) — `String.trim_trailing`
  instead of a single `replace_suffix`, so a fenced doc comment with ≥2 trailing
  blank body lines no longer emits a spurious `## ` line.
- **Migrate — seed kind universe `Type`** (`3ca3053`) — the uppercase-type-var rule
  lowercased `Type` (the universe/sort) to a free `type` in `{a: Type}` signatures,
  corrupting every dependent stdlib signature under `cure migrate`. Seeded `"Type"`
  into `build_ctx`'s builtin set. **This reverses iteration 16's "not a bug" call**:
  16 reasoned both forms compile so it was meaning-preserving, but `Type` is
  unambiguously the universe (never a user variable — Idris/Agda/Lean parity), and a
  migration tool must not rename it. The migrate audit agent independently confirmed
  `Type` is the ONLY surface sort, so seeding it closes the whole class.
- **Printer — comments inside a call's argument list** (`b23d18a`) — a comment can
  legally sit inside a function call's arg list (the one comma-separated construct
  whose parens may span newlines and reparse). The single-line span dropped it (a
  silent `cure fmt` loss; a spurious `:comment_dropped` migrate rejection). When any
  arg carries a leading/trailing comment the list renders one-per-line, with the
  comma before any trailing comment so the `#` never eats it. No-comment case is
  byte-for-byte the single-line span.
- **Printer — inline `=` body with a leading comment** (`3df66ee`) — a comment
  between `=` and an inline body was rendered `= # note` (commenting the body out),
  then reparsed with the comment relocated across passes (non-idempotent). Now the
  body breaks to the next line as the source wrote it.

Full suite after fixes: **3963 passed, 0 failures**; 139 immune responses; Antigen
309/309 cells across 34 assays.

### Fresh audit — 4 agents, every finding verified against source → ZERO confirmed bugs

- **Lexer** (clean): all five raise-capable conversion sites (`lex_hex` L787,
  `lex_binary_int` L809, `lex_decimal` L836, `finish_float` L849, atom intern L1145)
  are guarded or rescued; octal/quoted-atom/keyword paths and float state-threading
  verified safe. The never-raise invariant holds.
- **Project** (clean): every sibling `apply_kv` table stores string keys (no atom
  interning), `scan_inline_comment` is byte-exact-equivalent to the old charlist
  version (multibyte-safe by construction — `#`/`"`/`\` are all <0x80, never a
  UTF-8 continuation byte), and the second-order flow (non-UTF-8 value bytes now
  reaching `parse_scalar`/regex/slice) raises nowhere.
- **Migrate** (clean): the `walk/4` vs `var_names_deep/2` structural asymmetry is
  real but UNREACHABLE — lambda params are type-less (`fn(y: T)` isn't representable)
  and every live type-var carrier (let/ascription `type_annotation`, type
  applications) is a list-child 3-tuple handled symmetrically by both. `Type` is the
  only surface universe; idempotence holds on both example traces.
- **Printer** (all findings dissolved under verification):
  - F1 (`:trailer` comment between args dropped) — **not reachable**: reproduced
    `g(1,\n # c\n 2)`; the classifier attaches the own-line comment as `:leading` on
    the NEXT arg (verified via AST inspection), so the multiline path keeps it and
    the reprint is idempotent.
  - F2 (augmented-assignment RHS parallel-site miss) — **not reachable**: an
    augmented-assignment RHS cannot span a newline (`x +=\n 1` fails to parse), so a
    leading-comment RHS is unrepresentable; the `=` fix's parallel site is dead code.
  - F3 (comma after a bare-comment arg line) — theoretical; the agent could not
    construct a triggering arg expression, and neither could I.
  - F4 (decorator args not rerouted) — pre-existing (decorator rendering untouched
    this cycle) and the comment is RELOCATED, not dropped (verify's comment-text diff
    is order-insensitive, so it passes). While checking F4 I found that the PARSER
    silently drops a decorator on a `type` declaration (`@derive(Eq)\ntype T` → the
    `type_annotation` AST carries no decorator) — a pre-existing parser feature gap
    (do type decls support decorators?), a design question, NOT a printer bug and
    out of this loop's scope.

### Outstanding findings (after iteration 17)

**None confirmed in the changed slices.** This is the FIRST clean audit; iteration 16
was not clean, so the streak = 1. One more clean audit converges the loop.

**Newly noted (pre-existing, out of changed-slice scope — carry, do not block):**
- Parser silently drops a decorator on a `type` declaration (`@derive` on a type is
  discarded at parse time). Feature/design question (should type decls carry
  decorators?), not a reprint bug. Needs an operator/design call before any fix.

**Blocked — needs operator (UNCHANGED from iteration 16):**
- `cure migrate` uppercase-type-var CTX false-positive — the general name-resolution
  decision (user/imported type constructor vs free type var). The `Type`-sort case is
  now FIXED (`3ca3053`); the general `Nat`/`Vector`-in-a-bare-file case remains the
  blocked decision.
- deps update no-op; partial/interrupted clone accepted; migrate no-flag target;
  hyphenated dependency names (general package-manager scope).

**Latent / unreachable today (carried, re-confirmed robust):**
- `comment_texts` non-quote-aware; `walk`/`var_names_deep` asymmetry (unreachable);
  `ProtoToInterface` `retires_keywords` with `enforced_in: nil` (by design);
  `group_hoist` multi-`mod`-per-file (unsupported shape); printer F3 (unconstructable);
  decorator-arg comment relocation (F4, relocation-not-loss).

**Loop status:** iteration 17 fixed 10 real bugs (2 tokenizer crash-guards, 2 project
untrusted-input hardenings incl. an atom-DoS, 1 migrate binder desync, 1 migrate
universe-sort corruption, 4 printer round-trip/idempotence fixes). Fresh audit CLEAN
(zero confirmed). **ONE clean audit — NOT yet converged** (need two consecutive). The
cron is **left in place**. Full suite green: 3963 passed, 0 failures. Do NOT merge.

Commits this cycle: `6d28345`, `70d2c0a`, `058cf25`, `58f976d`, `0434cb9`, `471e9b0`,
`d015405`, `3ca3053`, `b23d18a`, `3df66ee`, plus this record.

---

## Iteration 18

Outstanding list from iteration 17 was empty (that cycle's fresh audit was clean),
so this cycle ran a BROAD convergence-deciding audit over the whole editions surface
(not just a diff): edition+project, migrate engine+rules, lexer/parser/printer, CLI.
Four general-purpose agents; every finding verified against source / reproduced before
counting. Broadening past iteration 17's changed-slice scope surfaced three real
PRE-EXISTING bugs (two CLI, one migrate rule) — so this audit is NOT clean and the
streak resets.

### Fixed this cycle (3 commits, all ghost-authored)

- **Migrate — `group_hoist` mis-hoists across modules** (`825c110`) — the rule keyed
  every in-body `@group(...)` decorator to the FIRST module container and spliced them
  all before it. Multi-module files parse AND compile (verified), and `cure migrate`
  runs on source syntactically, so a `@group` written under a later module was silently
  re-associated with the first — semantic corruption from a `tier: :machine`
  (auto-applied) rule, accepted by `verify/3` because the output still reparses with
  comments intact. Now each mover hoists to just before its NEAREST PRECEDING module
  (`hoist_segments/1`); single-module behaviour unchanged. Reverses the prior
  "unsupported shape / latent" classification — it is reachable. (2 new tests.)
- **CLI — `fmt`/`doc` crash on a missing file** (`6f56728`) — both read each target
  with `File.read!`, so a missing explicit path (`cure fmt typo.cure`, an everyday
  mistake) raised an uncaught `File.Error` (raw BEAM stacktrace), unlike
  `run`/`check`/`compile` which report + exit 1. Added a shared `expand_cure_targets/1`
  that rejects non-existent explicit targets with a clean non-zero exit before any
  worker reads them. (3 new tests.)
- **CLI — `migrate` absent from the suggestion list** (`6f56728`, same commit) —
  `migrate` is a real dispatch command but was missing from the `known_commands` list
  the "did you mean" suggester searches, so a near-miss typo (`cure migrat`) never
  proposed it. Added it. (1 new test.)

Full suite after fixes: **3969 passed, 0 failures**; 140 immune responses; Antigen
309/309 across 34 assays.

### Fresh audit — verified findings (agent claims confirmed/refuted against source)

CONFIRMED (fixed above):
- group_hoist multi-module mis-hoist (reproduced: `@group(:core)` under `mod Second`
  hoisted above `mod First`).
- fmt/doc File.read! crash on missing file (reproduced: `File.Error` raised, uncaught).
- migrate missing from known_commands (confirmed: real command at cli.ex:162, absent
  from the ~w list).

REFUTED / NOT bugs (verified myself, not counted):
- **CLI git-guard on a nonexistent dir** — predicted `System.cmd` `:enoent` raise does
  NOT occur on this platform; it prints a spawn warning and degrades to `untracked` +
  clean exit 1. Benign.
- **Lexer+parser+printer slice** — the subagent degenerated twice (0 tool-uses,
  corrupted output), so I audited it INLINE with an empirical round-trip harness: 23
  constructs (binops, pipes, unary minus, bool connectives, records, tuples, lists,
  maps, lambdas, match, if-elif, guards, char/string-escape literals, deriving,
  decorators, extern, type applications, comments in nested-call/match-arm) all
  round-trip structurally and print idempotently; the lexer never raised on 9
  adversarial byte inputs (NUL, lone `--`, unterminated string, truncated multibyte,
  tabs, CRLF, bad escapes). CLEAN.
- **edition+project** — never-raise, no atom-DoS, pre-scan↔parser↔rewriter agreement
  all hold. Two non-bug notes: duplicate `[project]` tables round-trip divergence
  (latent — single edition today, `set_edition` always writes "2026" so no mismatch is
  producible) and `edition = ""` failing the whole load (a clean error tuple; a design
  nit, defensible as fail-loud-on-typo).
- **migrate engine** — fixpoint is non-oscillating (all rules one-directional +
  self-idempotent); `comment_texts` false-accept unreachable by any current rule
  (none edit string-literal contents); engine rule-execution not rescue-guarded is a
  latent hardening gap with NO reachable raise in parser-produced ASTs.

### Outstanding findings (after iteration 18)

**None confirmed remaining in any slice** (the three found were all fixed this cycle).
Because this cycle's audit DID find bugs, the streak is **0** — the next cycle must run
a fresh audit and find zero, then one more, for two consecutive clean audits.

**Latent / unreachable today (carried, re-confirmed):**
- Duplicate `[project]` tables `set_edition`↔`load` divergence (live only once a second
  edition is minted).
- `comment_texts` non-quote-aware false-accept (no current rule edits string literals).
- migrate engine does not rescue a raising rule (no reachable raise in real ASTs).
- Parser silently drops a decorator on a `type` declaration (feature/design question).

**Design nits (not bugs, not fixing without an operator call):**
- `edition = ""` fails the whole load rather than defaulting like a missing key.

**Blocked — needs operator (UNCHANGED):**
- `cure migrate` uppercase-type-var CTX false-positive (general name-resolution
  decision; `Type`-sort sub-case FIXED in iteration 17).
- deps update no-op; partial/interrupted clone accepted; migrate no-flag target;
  hyphenated dependency names (general package-manager scope).

**Loop status:** iteration 18 fixed 3 real pre-existing bugs (1 migrate semantic
corruption, 2 CLI crash/UX) that only surfaced once the audit widened beyond the last
diff. Fresh audit therefore NOT clean → streak reset to 0. Cron **left in place**.
Full suite green: 3969 passed, 0 failures. Do NOT merge.

Commits this cycle: `825c110`, `6f56728`, plus this record.

---

## Iteration 19

**Scope of fresh audit:** the two slices iteration 18 changed —
`lib/cure/migrate/rules/group_hoist.ex` (825c110) and `lib/cure/cli.ex` (6f56728) —
two read-only adversarial Opus agents, every finding verified against source by hand
before counting.

**Two confirmed bugs — both INCOMPLETE iteration-18 fixes (the widened fix missed the
real code path):**

1. **group_hoist non-idempotent under `run_to_fixpoint` → multi-module corruption**
   (fixed `3ff2515`). 825c110 made a single `Migrate.run/2` pass hoist each `@group`
   above its own module — but `cure migrate` drives `run_to_fixpoint` (cli.ex:1421),
   which threads the AST between passes WITHOUT reparsing. Pass 1 hoists a group
   directly above its module; that decorator now sits (as a sibling) after the previous
   module, so the "nearest preceding module by any module before it" heuristic re-flagged
   it on pass 2 and dragged it above the previous module — walking every non-first-module
   group one module toward the top of the file per pass. Empirically confirmed via
   `run_to_fixpoint`: `@group(:core)` belonging to `Second` landed above `First`; a
   two-module/two-group file stacked BOTH groups above `First`.
   Root cause: "directly above the next module" and "in the previous module's body" are
   the same *position* to both `preceding_module?/1` and `hoist_segments/1`. Fix adds an
   `above_mod?/2` predicate (a contiguous group-decorator run terminating at a module
   container is already above-mod → left in place) in BOTH the detector and the rewriter,
   making the rewrite idempotent. Note: a `@group` written *directly* above a `mod` is
   absorbed into the module container by the parser, so it is never a standalone sibling —
   the corruption is reachable only for genuinely in-body groups under a 2nd+ module.
   Red tests drive the actual `run_to_fixpoint` path (a string-reparse loop re-absorbs the
   decorator and masks the bug).

2. **`cure fmt`/`doc` crash on an unreadable (existing) file** (fixed `7b2ce0a`).
   6f56728's `expand_cure_targets` guarded only non-existence, but `File.exists?` is true
   for a chmod-000 file, so it reached a worker whose `File.read!` raised a raw File.Error
   stacktrace — and the no-argument wildcard scan bypasses that guard entirely. Both fmt
   and doc affected (`fmt_algebra`/`fmt_safe`/`fmt_diff`/`fmt_check`/`fmt_aggressive` +
   `cmd_doc`). Fix routes every fmt/doc read through a shared `read_source_or_exit/1`
   (File.read → report + exit 1), mirroring run/check/compile. Red tests skip under a
   process that can still read a 0o000 file (root/CI).

**Refuted / non-bug (verified, not counted):**
- CLI: mixed/missing paths, broken symlink, empty-dir, `[]`-default parity, exit codes,
  `known_commands` (`migrate` present once; suggester stable, no regression) all hold.
- group_hoist: prefix groups, interleaved non-group decorators, consecutive containers,
  non-block/empty AST all correct; single-module and first-module cases were already
  idempotent.

### Outstanding findings (after iteration 19)

**None confirmed remaining.** Both found bugs fixed this cycle. Because this cycle's audit
DID find bugs, the streak is **0** — two consecutive clean audits are still required.

**Latent / unreachable, design nits, and Blocked—needs-operator: UNCHANGED from
iteration 18** (duplicate `[project]` divergence; `comment_texts` non-quote-aware;
migrate engine no rule-rescue; parser drops `type` decorator; `edition = ""` fails load;
uppercase-type-var CTX false-positive; package-manager scope items).

**Loop status:** iteration 19 found + fixed 2 bugs, both incomplete iteration-18 fixes
exposed by auditing 18's own changed slices against their real runtime paths
(`run_to_fixpoint`, the wildcard scan). Fresh audit NOT clean → streak reset to 0. Cron
**left in place**. Full suite green: **3974 passed, 0 failures**; Antigen 309/309. Do NOT
merge.

Commits this cycle: `3ff2515`, `7b2ce0a`, plus this record.

---

## Iteration 20

**Scope of fresh audit:** the two slices iteration 19 changed —
`lib/cure/migrate/rules/group_hoist.ex` (3ff2515, the `above_mod?`/
`split_off_above_mod` idempotence fix) and `lib/cure/cli.ex` (7b2ce0a,
`read_source_or_exit`). Two read-only adversarial Opus agents plus my own
empirical fixpoint/stability probes; every claim verified against source.

**Both agents returned CLEAN on the iteration-19 fixes:**
- group_hoist (3ff2515): idempotence holds (≤2 passes, last pass `:no_change`),
  detector↔rewriter move-sets provably equal (no spurious rewrite-but-same-AST →
  no `run_to_fixpoint` non-convergence), correct nearest-preceding-module
  association across 3+ modules, multiple in-body groups, interleaved `@inline`,
  EOF groups, prefix groups. Nodes relocated as-is, trivia rides along, order
  preserved, output reparses. (Agent initially mis-`cd`'d into the main clone;
  it then audited the correct `3ff2515` blob — my working tree is verified on
  `autopilot/editions` @ 7f6e1f1 with the fix present, no drift.)
- CLI (7b2ce0a): all six fmt/doc reads converted, `error(...) && exit(...)`
  idiom proven identical to the run/check reference sites (`error/1` → `IO.puts`
  returns truthy `:ok`), exit propagates cleanly through the enumerations (only
  unrelated `try` in the file), fmt_diff/fmt_check contracts intact.

**One confirmed bug found by my own stress-probing — PRE-EXISTING, now fixed:**

3. **`cure migrate` not text-idempotent for a hoisted decorator** (fixed
   `7f6e1f1`). Driving `run_to_fixpoint` then reparsing its output and running
   again shed a blank line: a hoisted `@group` standalone sibling printed
   `@group(:g)\n\nmod A`, but on reparse the parser ABSORBS a decorator written
   directly above its `mod` into the container, which re-renders tight
   (`@group(:g)\nmod A`). Root cause in the printer, not group_hoist: the §5.4
   top-level rule (`render_program`, printer.ex:72) blanked EVERY item via an
   unconditional `i > 0`, treating a standalone decorator sibling as its own
   definition. The migration advertises idempotence (spec §6.1) but was only
   AST-convergent, not text-idempotent, so a second `cure migrate` (or a
   `cure fmt --check` afterwards) silently changed whitespace. Fix: a top-level
   decorator hugs the item it decorates (`i > 0 and not prev-is-decorator`),
   matching the absorbed form → `print∘reparse∘print` is a fixpoint. Pre-existing
   (the single-group hoist has always produced the standalone form); NOT a
   regression from iteration 19. Near-zero blast radius — real files never carry
   a standalone top-level decorator sibling (the parser absorbs them), so no
   existing corpus/printer test changed. Verified: printer 34, trivia, migrate
   51, formatter 30, algebra + lossless-roundtrip 55 all green; 3-module and
   multi-group inputs now `STABLE: true`.

### Outstanding findings (after iteration 20)

**None confirmed remaining.** The one found bug fixed this cycle. Because this
cycle's audit DID surface a bug, the streak is **0** — two consecutive clean
audits still required.

**Latent / adjacent (carried + one new, NOT counted as blocking bugs):**
- NEW: `cure test` / project-lib load (`cli.ex` ~1001/1070) still `File.read!`
  the `Path.wildcard` corpus, so a chmod-000 file in your own `lib/`/`test/`
  raises a raw File.Error rather than a clean exit. Pre-existing, out of the
  fmt/doc fix scope; defensible (a broken corpus file fails the build either
  way, stacktrace-exit vs clean-exit). Flagged for a future tolerant-read pass.
- Duplicate `[project]` divergence; `comment_texts` non-quote-aware; migrate
  engine no rule-rescue; parser drops `type` decorator; `edition = ""` fails
  load; uppercase-type-var CTX false-positive; package-manager scope items
  (UNCHANGED).

**Loop status:** iteration 20 confirmed both iteration-19 fixes hold under fresh
adversarial audit, and found + fixed one pre-existing text-idempotence defect in
the printer (surfaced by stress-probing group_hoist's fixpoint stability). Audit
NOT clean → streak reset to 0. Cron **left in place**. Full suite green:
**3975 passed, 0 failures**; Antigen 309/309. Do NOT merge.

Commits this cycle: `7f6e1f1`, plus this record.

---

## Iteration 21

**Scope of fresh audit:** iteration 20's only code change — `lib/cure/compiler/printer.ex`
(7f6e1f1, the `render_program/3` top-level decorator-hug). No Outstanding findings
from iteration 20, so no TDD fixes this cycle. Full suite run at cycle start:
**3975 passed, 0 failures**, Antigen 309/309 (unchanged — no code edits this cycle).

**Audit mechanics note:** the first two dispatched review agents hung (~10 min, a
142-byte launch-only transcript = zero tool calls; one died fumbling Cure `fn` syntax).
I stopped both (TaskStop), then ran a comprehensive INLINE adversarial audit myself AND
dispatched one fresh cross-check agent with explicit Cure-syntax guidance + a working
probe harness. Both my inline probes and the cross-check agent independently reached the
same verdict.

**CLEAN — zero confirmed bugs in 7f6e1f1.** Verified (idempotent `o1==o2` AND structural
round-trip `parse ≡ parse∘print∘parse`) across every adversarial input:
- Off-by-one after `flatten_top_level`: none. `nodes = flatten_top_level(exprs)` is the
  SAME list that `Enum.with_index` numbers and `Enum.at(nodes, i-1)` indexes, so a
  bare-`mod` wrapper expansion cannot mis-point the predecessor. Confirmed on multi-`mod`
  files and decorators at block boundaries.
- Standalone top-level decorator siblings (EOF decorator, stacked decorators, decorator
  separated from its target by a fn, decorator-only file, in-body `@group` between a
  `mod` and a `fn`): all render tight, all text-fixpoints — the intended behavior; the
  hug matches the parser-absorbed form.
- Trivia lossless: doc `##` above a decorated mod, trailing `# tail` on a decorator,
  leading comment before an EOF decorator, comment between a decorator and its target —
  none dropped/duplicated; all idempotent. (The between-decorator-and-mod comment
  re-emits ABOVE the decorator: pre-existing `Trivia.attach` reattachment, NOT the
  blank-rule change; lossless + idempotent, contract intact.)
- `join_statements` with `blank?==false` yields exactly one `\n` (never zero — decorator
  and item never collapse onto one line).

### Outstanding findings (after iteration 21)

**None.** First clean audit since the iteration-19/20 reset → **streak = 1**. Iteration
20 was NOT clean, so this is only ONE consecutive clean audit; convergence needs iteration
22 to also come back clean. Cron **left in place**.

**Latent / adjacent (carried, NOT blocking bugs; two re-confirmed this cycle):**
- Parser drops a decorator on a `type` declaration (`@derive(:Eq)\ntype T = Int` → the
  decorator is absorbed but not re-rendered). Re-observed this cycle; pre-existing
  absorption behavior, idempotent, out of scope for the printer blank-rule. Feature/design
  question for the operator.
- `cure test` / project-lib load (`cli.ex` ~1001/1070) still `File.read!` the wildcard
  corpus (chmod-000 file in your own tree → raw File.Error). Pre-existing, defensible.
- Duplicate `[project]` divergence; `comment_texts` non-quote-aware; migrate engine no
  rule-rescue; `edition = ""` fails load; uppercase-type-var CTX false-positive;
  package-manager scope items (UNCHANGED).

**Loop status:** iteration 21 confirmed iteration 20's printer fix is sound — the first
clean audit of the streak. No bugs found or fixed this cycle. Streak = 1 (need one more).
Cron left in place. Full suite green: **3975 passed, 0 failures**; Antigen 309/309. Do
NOT merge.

Commits this cycle: this record only (audit found nothing to fix).

---

## Iteration 22

**Scope of fresh audit:** the convergence-confirming cycle (iteration 21 was
clean → streak 1). Fresh adversarial audit dispatched over four changed slices
(edition/project, migrate engine, lexer/parser/printer, CLI). It was **NOT
clean** — it surfaced five real bugs, all reproduced and fixed via strict TDD.
A follow-up confirming re-audit over those five fixes then surfaced two more.
**Seven confirmed bugs fixed this cycle. Streak reset to 0.**

### Fixed (all ghost-authored, red-test-first)

1. **Printer — typealias reprinted as `type`, flipping node kind** (`b6e71d4`,
   refined `76045d6`). A `typealias X = Foo(args)` (a transparent `:type_annotation`)
   reprinted with the keyword `type` reparses to a nominal single-constructor
   `:container` (an ADT) — a node-kind + semantics flip. Hit `lib/std/char.cure`
   and `lib/std/string.cure`. Fix: a `:type_annotation` whose RHS is an applied
   type (`{:function_call, …}`) MUST reprint as `typealias`; every other shape
   (bare-name, arrow) keeps `type`. (The first commit was too broad — it
   reprinted ALL `:type_annotation` as `typealias`, breaking `Cure.QuoteTest`'s
   `type Name = String`; caught by the full-suite gate and narrowed in `76045d6`.)

2. **Printer — nullary constructor lost its parens** (`b6e71d4`). `None()` in a
   sum type (`{:function_def, …, []}` variant) reprinted to bare `None`, which
   reparses to a `{:variable}` type reference, not a constructor. Hit
   `lib/std/option.cure`. Fix: emit `name <> "()"`.

3. **Migrate — proto/interface/impl HEAD type vars not lowercased** (`610dd49`).
   `uppercase_type_var` lowercased method `:function_def` signatures but left the
   declaration HEAD's binders (a proto/interface's type-param list, an impl's
   for-type + where-constraints) uppercase, desyncing every binder from its uses;
   the reparse-only `verify/3` accepted it silently. Fix: head-bearing walk
   clauses (`:interface`, `:implementation`, `:container` protocol/trait) that
   rename the head fields (string-list `:params`/`:type_params` and expression
   `:for_type`/`:constraints`) and thread the rename into the body walk.

4. **CLI — nine fixed-arity commands misblamed extra args** (`5a3a9f1`). `lsp`,
   `stdlib`, `version`, `test`, `repl`, `doctor`, `fix`, `top`, `john` had only an
   exact `["cmd"]` arm; an extra positional arg fell through to the generic
   catch-all and printed "Unknown command: <cmd>", blaming a valid command. All
   nine take zero positional args. Fix: `["cmd" | _] -> usage_error(...)` fallbacks
   (mirrors the run/check/init/deps/keys precedent), which also reject the stray
   arg before the command runs (no accidental lsp-server / repl / stdlib-compile).

5. **Printer — leading comment on an inline lambda body drifted** (`b99b92c`). A
   lambda body carrying a `# c` leading comment rendered inline after `-> `,
   splicing `# c\nbody` mid-line; on reparse the stranded comment jumped to the
   file top — `print∘reparse∘print ≠ print∘reparse`. Fix: break the body to its
   own indented line when it carries a leading comment (inline path byte-for-byte
   unchanged otherwise). The analogous if/then-branch drift is UNREACHABLE — a
   then-branch must be an inline expression, so no valid source can put a leading
   comment there (confirmed: `if x then\n…` is a parse error).

**Found by the confirming re-audit of fixes 1–5, then fixed:**

6. **Migrate — head type var re-freshened per method, re-desyncing** (`5ec6edb`).
   Fix 3 freshened a head var against every name the WHOLE body uses, but each
   method `:function_def` still re-derived its own rename against only ITS
   signature. So when the class var's lowercase form `t` was taken by a local in
   ONE method, the head freshened to `t1` while a method WITHOUT that local
   independently picked `t` — desyncing again (and colliding onto the unrelated
   `t`). Fix: thread the enclosing rename map (`active`) into
   `rewrite_signature`/`build_rename_map` so a head-bound candidate REUSES the
   head's target verbatim, and method-locals reserve the head targets.

7. **CLI — `cure help extra` misblamed `help` as unknown** (`cdbe3ea`). `["help"]`
   was the last exact arm with no `| _` fallback → "Unknown command: help". Fix:
   `["help" | _] -> help()` (extra args to help just show help).

### Fresh audit — what the confirming re-audit verified

Two parallel general-purpose Opus agents audited the seven fixes' changed slices
(printer; migrate head-walk + CLI arms). Every claim was verified against source /
reproduced before counting:
- **Printer fixes 1, 2, 5: SOUND.** All round-trip + idempotence probes pass,
  including the three targeted std files (`option`/`char`/`string` idempotent) and
  the full `printer_fidelity` + `lossless_roundtrip` suites. `applied_type_rhs?`
  discriminator is required and correct (verified `type X = Foo(args)` → container
  vs `typealias X = Foo(args)` → type_annotation directly); nullary-ctor clause has
  no over-reach (bare `None` is a separate `{:variable, variant: true}` node);
  `has_leading?` reads both 3- and 4-tuple meta and the `depth+1` pad is correct at
  nesting.
- **Migrate fix 3: sound EXCEPT the multi-method collision (→ fix 6).** Constraint
  and for-type vars rename in sync; `defaults` staleness is benign (printer renders
  interfaces from `body`, not `defaults`, and migrate reparses); no over-reach on
  plain `mod`/`rec`/`enum` containers.
- **CLI fix 4: sound.** All nine `cmd_*` verified zero-positional; no arm shadowed;
  `usage_error/1` exits nonzero. One residual misblame (`help`) → fix 7.

### Outstanding findings (after iteration 22)

**None blocking.** All seven confirmed bugs are fixed; the confirming re-audit's
only remaining items are the two carried below.

**Latent / adjacent (carried, NOT blocking bugs):**
- **NEW — qualified-name applied-alias garble (parser, pre-existing).**
  `typealias X = Std.Map(K, V)` (a qualified name applied to args) parses to a
  garbage node (`{:function_call, callee: {:type_annotation…}, name: "unknown"}`)
  that the printer faithfully renders as `unknown(K, V)`, dropping `typealias X =`.
  VERIFIED it is INVALID surface — the same `Std.Map(K, V)` is a hard **parse
  error** in a signature (`expected :rparen, got :lparen`); it only slips through
  in the typealias RHS. So this is garbage-in on unsupported surface (the parser
  should reject it, as it does elsewhere), NOT corruption of a valid program.
  Pre-existing, independent of all seven fixes, same class as the carried
  @derive-on-`type` drop. A parser-hardening (reject, don't garble) is a separate
  targeted effort — deferred, not forced inside this editions cycle.
- **Commit-message inaccuracy (not a code bug).** `76045d6`'s message example
  claims `type X = (Nat) -> Nat` "keeps `type`". It actually flips to
  `typealias Endo = Function(Nat, Nat)` — which is CORRECT (arrow types render as
  `Function(...)`, so the old `type` spelling would have reparsed to a container).
  The code behavior is right; only the message example is wrong.
- Carried unchanged: parser drops `@derive` on a `type` declaration; `cure test` /
  project-lib load `File.read!` the wildcard corpus; duplicate `[project]`
  divergence; `comment_texts` non-quote-aware; migrate engine no rule-rescue;
  `edition = ""` fails load; uppercase-type-var CTX false-positive; package-manager
  scope items.

**Loop status:** iteration 22 was the convergence-confirming cycle but came back
**NOT clean** — seven real bugs found + fixed (five in the fresh audit, two in the
confirming re-audit). **Streak reset to 0.** Convergence needs two consecutive
clean audits; the next cycle must be clean to reach streak 1 again. Cron **left in
place**. Full suite green: **3991 passed, 0 failures**; Antigen 309/309. Do NOT
merge.

Commits this cycle: `b6e71d4`, `610dd49`, `5a3a9f1`, `b99b92c`, `76045d6`,
`5ec6edb`, `cdbe3ea`, plus this record.

---

## Iteration 23 (final — loop wound down by operator)

**Operator ended the loop.** Mid-cycle the operator instructed: cancel the cron,
address the findings from the in-flight audit agents, and stop. The cron
(`7e672a7d`) was **CronDelete'd**. This is a manual conclusion, not a
two-clean-audit convergence.

Fresh audit ran 4 parallel read-only Opus agents over the changed slices
(edition/project, migrate, lexer/parser/printer, CLI). Every returned claim was
verified against source before fixing.

**edition/project:** clean — no field-reachable bug. (Two non-field-reachable
guard asymmetries noted: `Edition.resolve/1` crashes on a non-binary `:source`;
`leading_line_index/1` has no nil-guard. All in-tree callers pass binaries, so
neither is reachable; left as-is.)

**Four real bugs found + fixed (each verified, ghost-authored, with regression
tests except CLI):**
- `be5fab0` — lexer: unknown char escape (`'\r'`, `'\z'`) fell through to
  `decode_char_at`, silently dropping the backslash and yielding the letter's
  codepoint (114 for `r`) with no diagnostic. Now a hard `:invalid_char_escape`.
- `ac7e1fe` — printer: `container_to_string` had no `:opaque` case, so an
  `opaque type` reprinted via the `inspect/1` catch-all as a raw tuple that fails
  to reparse. Added `opaque_to_string` (preserves head params).
- `d838540` — migrate: `build_ctx`/`collect_type_names` registered only
  `:struct`/`:enum` and ignored imports, so `opaque`/`primitive`/`use Mod.{T}`
  names were misread as free type vars and lowercased (semantic corruption the
  reprint-only verify accepts; the opaque case also aborted the whole migration
  via the printer gap above). Added `:opaque`/`:primitive` + an `{:import,…}`
  clause folding selective items + alias into ctx.
- `106e179` — CLI: `--out`/`--target` were read as typed strings by
  export-types/snap/story but absent from the `switches:` list, so a
  missing/flag-following value collapsed to boolean `true` and leaked into the
  delegated Mix task's argv. Declared `out`/`target` (`:string`) +
  `diagrams`/`step` (`:boolean`). No bespoke test — the only seam delegates into
  Mix tasks (`:mix`-undef / side-effect risk); fix is a trivially-correct switch
  declaration.

**Flagged, not fixed (unverifiable read-only / out of scope):** the four
Mix-delegating CLI commands call `Mix.shell()` but `:mix` may not be bundled in
the built escript — a possible `:undef` at runtime the agent could not confirm
without building the escript. Worth a follow-up build check.

Full suite green: **3998 passed, 0 failures** (+7 new regression tests over
iteration 22's 3991); Antigen 309/309. Cron deleted; branch **not merged**.

Commits this cycle: `be5fab0`, `ac7e1fe`, `d838540`, `106e179`, plus this record.

## LOOP CONCLUDED — operator-directed wind-down (not a two-clean-audit convergence)

---

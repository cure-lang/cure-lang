# Refinement-Types Removal Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove refinement types entirely (parser grammar, SMT query layer, classic checker machinery, Std.Refine, examples/docs/site claims, Antigen surface) while keeping GuardLint + `Cure.SMT.Process` + the z3 binary byte-identical in behavior.

**Architecture:** Two green commits. C1 (Task 2) removes all lib/antigen machinery AND every test that dies with it — atomic, tree green at the boundary. C2 (Task 3) handles examples, docs, and site. Kernel (`lib/cure/core/`) and elaborator (`lib/cure/elab/`) diffs are EMPTY except the enumerated guard_lint.ex:194 comment reword AND the program.ex:220 comment reword (found during plan hardening: the spec's own §0 evidence citation — "program.ex:233 excludes `Std.Refine` from the dependent auto-prelude" — points at a comment that literally contains the string `Std.Refine`; the final grep gate (Task 4 Step 1) requires zero `Std.Refine` hits under lib/ with no exception for this file, so the comment must be reworded too).

**Tech Stack:** Elixir, git. Spec: `docs/superpowers/specs/kernel/2026-07-09-refinement-removal-design.md` (hardened `eede85a` + `dc6c35f` + `6d61e1a`) — read it IN FULL first; its §1/§2 file dispositions and §3 gate are normative.

## Global Constraints

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch` (branch `autopilot/kernel-parity-batch`). NEVER read or touch the parent checkout `/Users/ch/Develop/esp32-beam/cure-lang/lib/...`.
- Ghost commits: `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO Co-Authored-By, NO trailers. Explicit-pathspec staging only.
- ONE `mix` command at a time, ever — including the two subproject `mix test` runs (Task 3) and scoped runs; never overlap.
- Baseline (post-#17, commit `ed5f5de`): full suite **3277 passed / 0 failures / 0 skipped**; Antigen 503; oracle replay 65. All deltas reconcile against THESE numbers.
- Tests immutable except: (a) the whole-file deletions and by-name selective removals enumerated in Task 2; (b) the two non-behavioral exceptions — `guard_lint.ex:194` comment reword and `normalizer_test.exs` fixture-tag rename. ANY other surviving-test change = STOP.
- STOP conditions (spec §3.6, widened by plan hardening): any `lib/cure/core/` or `lib/cure/elab/` file needs a change beyond guard_lint.ex:194's comment AND program.ex:220's comment (the two permitted elab/ comment rewords — see Architecture note above); the `dependent_types` check.examples expectation changes; any surviving test needs modification beyond the two exceptions; an oracle fixture uses refinement syntax; GuardLint behavior changes; either subproject `mix test` fails post-rewrite.
- Two-pipeline steer: everything you delete is CLASSIC-side (`lib/cure/types/*`, `lib/cure/smt/*` minus process.ex, peripheral tooling) plus the shared parser grammar. The dependent pipeline (`lib/cure/elab/*` + `lib/cure/core/*`) is off-limits. Class-C "refinement" (dependent-match index/goal refinement: `refine_branch`, `:refine` challenge kind, `Indexed.refinement/1`, `wi01/wi05` oracle fixtures) is a DIFFERENT concept — touching it is a defect.

---

### Task 1: Survey + red baseline (read-only, no commit)

- [ ] **Step 1: Read the spec in full.** `docs/superpowers/specs/kernel/2026-07-09-refinement-removal-design.md`.

- [ ] **Step 2: Verify anchors still hold** (post-#17 line drift is possible — locate by NAME everywhere; spec line numbers are pre-edit hints):

```bash
grep -n "parse_refinement_type" lib/cure/compiler/parser.ex          # 3 grammar sites
ls lib/cure/smt/                                                     # solver translator parser process
ls lib/cure/types/ | grep -i "refine\|dependent"                     # the 5 delete files
grep -rn "SMT.Solver\|SMT.Translator" lib/ | grep -v "smt/solver.ex\|smt/translator.ex"   # all external callers — must all be in the spec's strip list
grep -n "run_with_z3" lib/cure/elab/guard_lint.ex                    # the :194 comment
grep -n "Std.Refine" lib/cure/elab/program.ex                        # the :220 comment (auto-prelude exclusion rationale) — the second permitted elab/ comment reword
```

Every `SMT.Solver`/`SMT.Translator` caller found must appear in spec §1's strip list (checker.ex, dependent.ex→deleted, proof/verifier.ex, pgo, doctor prose). An unlisted caller = STOP.

- [ ] **Step 3: Oracle syntax check (spec §3.3).** Match the SYNTAX, not the substring "refin":

```bash
grep -rln "| *[a-z_]* *[<>=]" test/oracle/**/*.cure | xargs -I{} grep -l "{.*:.*|" {} 2>/dev/null
```

Expected: empty (wi01/wi05 are Class-C with-abstraction fixtures, no `{x: T | p}` syntax — already verified; a hit = STOP).

- [ ] **Step 4: Record the red baseline.** Confirm test counts: whole-file deletions 34+3+19+6+18+5+15+16 = **116 tests**; selective candidates 9 (checker_test.exs) + 3 (stdlib_test.exs) + 2 (unify_test.exs) + 1 (parser_structural_test.exs) + 1 (quote_test.exs) + 3 (pgo_test.exs "SMT translator pgo_hint" block: "default hint produces today's query", "hot hint emits the arith-solver option", "cold hint omits the arith-solver option") = **19**, of which at most 18 die (checker_test.exs's "declared Int parameter survives multi-clause guard refinement" is expected to survive per Step 6's removal rule). Run NO mix command in this task.

### Task 2: C1 — core removal (lib + antigen + tests), green commit

**Files:**
- Delete: `lib/cure/smt/solver.ex`, `lib/cure/smt/translator.ex`, `lib/cure/smt/parser.ex`, `lib/cure/types/refinement.ex`, `lib/cure/types/guard_refinement.ex`, `lib/cure/types/path_refinement.ex`, `lib/cure/types/pattern_refinement.ex`, `lib/cure/types/dependent.ex`, `lib/std/refine.cure`, `lib/antigen/assays/smt_lint.ex`, `lib/antigen/generators/smt_query.ex`, `test/cure/smt/smt_test.exs`, `test/cure/smt/solver_k13_test.exs`, `test/cure/types/guard_refinement_test.exs`, `test/cure/types/path_refinement_test.exs`, `test/cure/types/pattern_refinement_narrowing_test.exs`, `test/cure/types/byte_size_refinement_test.exs`, `test/cure/types/dependent_test.exs`, `test/antigen/assays/smt_lint_test.exs`
- Modify (strip refinement clauses/fields/rows per spec §1): `lib/cure/compiler/parser.ex` (3 grammar sites), `lib/cure/types/checker.ex`, `type.ex`, `unify.ex`, `env.ex`, `stdlib.ex`, `pattern_checker.ex`, `reduce.ex`, `core_bridge.ex` (comment), `lib/cure/export_types/protobuf.ex`, `lib/cure/optimizer/monomorphise.ex`, `lib/cure/doc/extractor.ex`, `lib/cure/doc/html_generator.ex`, `lib/cure/compiler/errors.ex`, `lib/cure/compiler/printer.ex`, `lib/cure/project/proof.ex`, `lib/cure/project/proof/verifier.ex`, `lib/cure/pgo.ex`, `lib/cure/pgo/profile.ex`, `lib/cure/bless.ex`, `lib/cure/bless/advisor.ex`, `lib/cure.ex`, `mix.exs`, `lib/cure/doctor.ex` (message reword), `lib/cure/elab/guard_lint.ex` (ONLY the :194 comment), `lib/cure/elab/program.ex` (ONLY the :220 comment — drops the stale `Std.Refine` bullet from the auto-prelude exclusion-rationale comment; no code line changes, `@auto_prelude`/`@auto_prelude_types` untouched), `lib/antigen/runner.ex` (rows :366-368), `lib/antigen/generators/unify_problem.ex` (:71 row), `lib/antigen/assays/unifier.ex` (:131 strip clause), `lib/antigen/generators/surface_expr.ex` (:109-110 nodes)
- Test edits: selective removals + `test/antigen/assays/normalizer_test.exs` tag rename

**Interfaces:**
- Consumes: nothing new. Produces: `Cure.SMT.Process` remains the ONLY surviving `Cure.SMT.*` module; `types/checker.ex` still compiles and checks non-refinement programs identically.

- [ ] **Step 1: Delete the whole files** (git rm, explicit paths — the 11 lib + 8 test files above).

- [ ] **Step 2: Parser grammar.** Remove the three sites (locate by name/shape): `parse_refinement_type/1` (:3372-3387), the `type Name = {x:T|p}` alias branch (:3036-3041), the inline type-position branch (:4349-4353). Remove now-unused private helpers ONLY if the compiler warns about them.

- [ ] **Step 3: Strip the classic clauses.** Per spec §1: checker.ex (14 `{:refinement,…}` clauses + `strip_refinement/1`, `discharge_refinement/3`, `verify_return_refinement/7`, `verify_refinement_arg/5`, `non_refinement_or_non_numeric?/1`, the `check_sat` call), type.ex, unify.ex (:103-108/:237/:261-262), env.ex (2 struct fields + their touch-points), stdlib.ex (alias + `:refinement`-flag branch :345-346 + prose), pattern_checker.ex, reduce.ex, core_bridge.ex comment. Rule of thumb: after this step `grep -rn "{:refinement," lib/cure/types/` must be EMPTY.

- [ ] **Step 4: Peripheral strips.** protobuf E068 clause, monomorphise :196/:449, doc extractor/html, errors.ex E090/W091 formatters + refinement prose, printer rendering, proof.ex `:refinement` kind (KEEP `:smt` kind + `verify_smt/2` + `find_z3/0`), verifier.ex `:refinement` clause + `verify_refinement/2`, pgo hooks, bless mentions, `mix.exs:122` + `lib/cure.ex:4` strings, doctor message reword, guard_lint.ex:194 comment reword AND program.ex:220 comment reword (delete or reword the `#   Std.Refine     -- refinement predicates not yet dependent-clean` bullet so no literal `Std.Refine` string remains — NO code line changes to either file; `git diff -- lib/cure/elab/` must show exactly TWO comment hunks, guard_lint.ex:194 and program.ex:220).

- [ ] **Step 5: Antigen surface.** runner rows :366-368 (`smt/implication|unsat|witness`), unify_problem :71 row, unifier.ex :131 strip clause, surface_expr :109-110 nodes; `normalizer_test.exs` — rename the `{:refinement, …}` synthetic fixture tuples to `{:untranslatable_probe, …}` throughout (behavior-preserving; assertions keep passing because CoreBridge never special-cased either shape).

- [ ] **Step 6: Selective test removals — by name, with the removal rule.** Delete each candidate ONLY if it references deleted modules/syntax or fails post-removal; a candidate passing unchanged STAYS:
  - `checker_test.exs`: "local refinement aliases declared with `type` are visible to function signatures"; "forward-referenced local refinement alias still resolves"; "declared Int parameter survives multi-clause guard refinement" (EXPECTED TO POSSIBLY SURVIVE — verify before deleting); "provable: decrement(Positive) -> NonNegative type-checks"; "provable: identity on a refinement is accepted"; "failing return: bad(Int) -> Positive surfaces E090"; "failing call site: passing a non-Positive literal to decrement surfaces E090"; "caller refinement assumptions discharge nested call obligations"; "refinement_unknown warning fires when SMT cannot decide the obligation".
  - `stdlib_test.exs`: "all/0 exposes Std.Refine refinement aliases under qualified and short keys"; "Env.deref/2 resolves an aliased name to its underlying refinement"; "after `use Std.Refine`, a parameter declared as Positive resolves to a refinement".
  - `unify_test.exs`: "refinements are transparent to unification"; "substitutes through refinements".
  - `parser_structural_test.exs`: "refinement type" (:158).
  - `quote_test.exs`: "refinement type" (:348).
  - `pgo_test.exs`: the "SMT translator pgo_hint" describe block (:301+).
  - `compiler/errors*_test.exs`: expected ZERO removals (survey confirmed prose-only); if one fails, STOP.

- [ ] **Step 7: Scoped green runs (one at a time):**

```
mix test test/cure/types/ test/cure/compiler/     # classic side clean
mix test test/antigen/                            # expect 503 − 15 (smt_lint) ± retarget rows; runner has exactly 3 fewer rows
mix test test/cure/elab/                          # 454, byte-identical behavior (guard_lint 20/20)
```

Expected: 0 failures each. Any failure OUTSIDE the enumerated removals = STOP.

- [ ] **Step 8: Commit C1** (ghost, explicit pathspecs, message: `refactor!: remove refinement types — parser grammar, SMT query layer, classic machinery, Antigen surface (SMTCoq-era stretch goal; GuardLint/Process/z3 kept)`).

### Task 3: C2 — stdlib examples, docs, site, green commit

- [ ] **Step 1: Examples.** `git rm -- examples/refine_predicates.cure examples/path_refinement.cure examples/byte_size_refinement.cure`; delete the two `@expected` rows (`path_refinement`, `refine_predicates`) in `lib/mix/tasks/cure.check.examples.ex` (`byte_size_refinement` has none); rewrite the three mixed files per spec §1 (aliases → base types + one-line unchecked-invariant comment; moneta's INLINE `factor: {n: Int | n > 0}` → `factor: Int`; reword the enumerated doc-comments in all three). The `"dependent_types" => "6"` expectation row stays byte-identical — if it must change, STOP.

- [ ] **Step 2: READMEs + docs + site.** Per spec §1 "Live documentation": motif/moneta READMEs (reword refinement/Z3 claims), `docs/TUTORIAL.md`, `docs/STDLIB.md`, `docs/PROOFS.md:48`, `docs/STDLIB_DEPENDENT_CLAIMS_AUDIT.md`, `docs/DEPENDENT_TYPES.md:95`, `site/lib/cure_site/stdlib.ex:36` (drop `"Std.Refine"` from the list — live code), `site/priv/pages/type-system.md` (the heavy one), `getting-started.md`, `roadmap.md` (confirm past-tense only). Do NOT touch `docs/superpowers/specs/*`, `docs/superpowers/audit_categorised.md`, `CHANGELOG.md`.

- [ ] **Step 3: Subproject regression (the REAL motif/moneta coverage; one mix at a time):**

```
(cd examples/cure_motif && mix test)
(cd examples/cure_moneta && mix test)
```

Expected: both green. A failure = STOP (the alias rewrite broke something load-bearing).

- [ ] **Step 4: Commit C2** (ghost, explicit pathspecs, message: `docs+examples: refinement types removed — rewrite aliases, purge Std.Refine claims from docs/site`).

### Task 4: Final gates

- [ ] **Step 1: Grep gate (spec §3.4, all must be clean):**

```bash
grep -rn "{:refinement," lib/ test/                                  # zero (normalizer probe renamed)
grep -rn "SMT.Solver\|SMT.Translator" lib/ test/                     # zero incl. comments
grep -rn "Cure.SMT.Process" lib/ test/                               # ONLY guard_lint.ex + its tests + doctor/john/process itself
grep -rn "parse_refinement_type" lib/                                # zero
grep -rn "Std.Refine" lib/ examples/ docs/ site/ | grep -v "docs/superpowers/specs/\|docs/superpowers/audit_categorised.md\|CHANGELOG.md"   # zero
```

- [ ] **Step 2: Diff-scope gate:** `git diff --stat ed5f5de..HEAD -- lib/cure/core/` EMPTY; `git diff ed5f5de..HEAD -- lib/cure/elab/` shows EXACTLY two comment hunks — guard_lint.ex:194 and program.ex:220 — and no other file.

- [ ] **Step 3: Full suite ONCE:** `mix test`. Expected: **0 failures, 0 skipped**; passed ≈ 3277 − 116 (whole files) − (actual selective removals, report exact count) + 0 new. Antigen (500-ish rows post-removal) and oracle replay 65 run inside — green. Report exact numbers with reconciliation arithmetic.

- [ ] **Step 4: Report.** Both commit hashes, the selective-removal ledger (each name + died-or-stayed + why), the grep outputs, the diff-scope evidence, suite arithmetic, subproject test results, and any deviation however small.

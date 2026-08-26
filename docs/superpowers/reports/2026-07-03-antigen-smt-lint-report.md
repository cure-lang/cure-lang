# Antigen V6 — SMT Lint Soundness — Completion Report

**Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-03 · **Mode:** autopilot via `/loop` (autonomous continuation)

**Final** phase of the untrusted-machinery initiative (task #66), after V3/V1/V2/V5/V4.
Tests the untrusted SMT lint `Cure.SMT.Solver` (`prove_implication/4`, `check_sat/2`,
`prove_with_counterexample/4`) for **lint soundness** — framed by the locked decision
that Z3 is OUT of the dependent-kernel TCB. No `Cure.SMT.*`/`Cure.Core.*` edits, no
`:meck`, no new dependency.

## 🔴 HEADLINE FINDING — `Cure.SMT.Parser.parse_model/1` truncates negative witnesses

**Antigen's second genuine defect in the untrusted machinery** (after V4's erase
non-idempotence). `Cure.SMT.Parser.parse_model/1` mangles any **negative** Z3 model
value: Z3 emits negative integers as the s-expression `(- N)`, but the parser's outer
`[^\)]+` capture truncates at the first `)` — the one closing `(- N)` itself — yielding
the malformed string `"(- N"` (missing its close paren) instead of the integer `-N`.
That string then fails `parse_value`'s own `^\(-\s*\d+\)$` negative-literal pattern (the
trailing `)` is already gone) and falls through to the raw-string catch-all. So
`prove_with_counterexample` on any implication whose only counterexamples are negative
hands the caller a **`{:failed, %{"x" => "(- N"}}`** — a "counterexample" that is not a
usable value at all.

**Confirmed empirically at execution, not just traced.** The V6c assay ran the **real
Z3 subprocess** on `x > -100 ⇒ x >= 0` (counterexample space `{-99..-1}`, strictly
negative — so Z3 *must* return a negative witness regardless of its model-choice
heuristic) and correctly surfaced `{:violation, {:unusable_model, _}}`. Spec review
first traced it against `parser.ex` + a live `z3 -smt2 -in` session; plan review
re-verified the regex; execution reproduced it end-to-end.

**Severity: real but narrow.** It only bites when a refinement obligation's
counterexample is negative AND a caller consumes the model value (e.g. to render a
diagnostic). The soundness *verdict* (`:sat`/`:unsat`) is unaffected — Z3 still decides
correctly; it is the model *extraction* that corrupts. And `Cure.SMT.*` is **untrusted**
(a lint outside the TCB), so a mangled counterexample is a wrong/blank diagnostic, not
an unsound type. **Per the locked V6 non-goal, Antigen reports it; it does NOT patch
it** — the fix is a one-line regex change (match the full `(- N)` group before closing
`define-fun`), separately authorized. The V6c `unusable_model` known-finding test is the
natural regression guard: it flips to `:ok` the moment the parser is fixed.

## What shipped — three assays

| id | target | property | oracle |
|---|---|---|---|
| `smt/implication` | `prove_implication/4` | `true` ⟹ no bounded counterexample | bounded `eval_pred` |
| `smt/unsat` | `check_sat/2` | `:unsat` ⟹ no bounded satisfying witness | bounded `eval_pred` |
| `smt/witness` | `prove_with_counterexample/4` | `{:failed, m}` refutes; `{:proven, nil}` has no bounded counterexample | `eval_pred` at `m` / bounded |

The oracle is **not the kernel** (the kernel doesn't decide refinement arithmetic —
that's what SMT is *for*). It is an Antigen-owned **bounded brute-force evaluator**
`eval_pred/2` over the MetaAST predicate format (reusing V1's independent-evaluator
tactic), decided over `@domain = -32..32`. This gives a **sound-in-one-direction**
differential exactly matching the locked "lint soundness, not completeness" framing: a
concrete bounded counterexample proves the lint over-claimed; the converse
(`false`/`:sat`/`:unknown` while the domain shows nothing) never fires. `:unknown` is
always a legal, non-infecting answer. Plus `Antigen.Generators.SmtQuery` (fixed catalog)
and `assay_module/1` dispatch for the three ids + the `:smt_query` kind.

## Result of running it — the real Z3 lint is sound on the catalog

Beyond the parser finding: the real Z3 lint **proved** `x > 5 ⇒ x > 0` (V6a baseline),
returned **`:sat`** for the satisfiable `x > 0` and **`:unsat`** for `x > 0 ∧ x < 0`
(V6b), and produced a **genuine non-negative counterexample** for the invalid
`x > 0 ⇒ x > 5` (V6c baseline) — every clean-catalog entry re-checked `:ok` under the
real solver. The five negative controls each infect: `false_discharge`, `false_unsat`,
`bogus_counterexample`, `unusable_model`, and the `false_proven` control added at plan
review (see below).

## Stage-by-stage outcomes

| Stage | Outcome | Commit(s) |
|---|---|---|
| 0 — Spec | V6 three-family design; bounded-oracle framing; locked-decision constraints | `b6f53ff` |
| 1 — Spec review (Sonnet) | 5 passes; **traced the `parse_model` negative-value bug** (live `z3`); enumerated the full `translate_op/1` set; documented the `do_translate` catch-all `→ true` unsoundness as an out-of-scope non-goal | `07e1f04` |
| 2 — Plan | 5-task TDD plan; `parse_model` bug reconciled the V4 way (clean catalog non-negative + known-finding fixture) | `d9ff199` |
| 3 — Plan review (Sonnet) | 5 passes; **found a real coverage gap** — `prove_with_counterexample`'s `{:proven, nil}` is a distinct query/code path from `prove_implication`, so added a bounded `{:false_proven}` check + control (Reconciliation #4); test-immutability + "a real infection is a finding" constraints added | `4c80271` |
| 4 — Execute (Opus, TDD) | red → green per task, ghost-authored | `db1d0d7`, `fdbd328`, `5d19e77`, `25316ee` |
| 5 — Verify | full suite green; quarantine clean | (this report) |

### Per-task execution (Stage 4)

1. **`db1d0d7`** — `smt/implication` + `eval_pred/2`. Green 4/4 — real Z3 proves `x>5 ⇒ x>0`; false_discharge control fires.
2. **`fdbd328`** — `smt/unsat`. Green 7/7 — real Z3 decides sat/unsat correctly; false_unsat control fires.
3. **`5d19e77`** — `smt/witness` (+ `{:proven,nil}` bounded check + `unusable_model`/`false_proven` controls + the parse_model known-finding). Green 13/13 — **parser negative-value bug confirmed empirically via real Z3.**
4. **`25316ee`** — `SmtQuery` catalogs + dispatch + `:smt_query` kind + `@known_atoms`. Green 15/15 — clean catalog all `:ok`.

## Verification

- **Full suite (single authorized run):** `2728 passed` (3 doctests, 2725 tests),
  0 failures — +15 from V4's 2713.
- **StreamData quarantine:** `architecture_test.exs` green (`SmtLint` token-free).
- **Working tree:** clean (SMT catalog is replayed from the generator, no corpus banking).
- Every commit ghost-authored (`Made In Heaven`), no `Co-Authored-By`.

## Recommended follow-up (operator decision)

Fix `Cure.SMT.Parser.parse_model/1`'s regex to capture the full `(- N)` group before
the `define-fun` close paren (or special-case the `(- N)` form). One-line change in
untrusted code; the V6c `unusable_model` known-finding test is the regression guard
(flips to `:ok` once fixed). Independently, `Cure.SMT.Translator.do_translate/1`'s
catch-all-`→ true` for unrecognized AST nodes (spec §8) is a latent false-discharge
source outside V6's scope — worth a guard clause that fails loudly instead.

## Boundaries

V6 **finds**; it does not fix (the parser bug is reported, not patched). Curated fixed
catalog inside one-variable `QF_LIA`, not a fuzzer. Lint **soundness only** — a valid
implication the lint fails to prove is out of scope (the untrusted lint may be
incomplete). No differential outside decidable linear integer arithmetic/boolean; the
`do_translate` catch-all unsoundness stays out of scope by construction (§8). No SMTCoq
/ proof reconstruction (the someday the locked decision defers).

## 🏁 Initiative complete — all six untrusted-machinery verticals covered

V6 is the **final** umbrella vertical (task #66). The untrusted dependent-type machinery
is now under property-based soundness testing end to end:

| Vertical | Target | Verdict |
|---|---|---|
| V1 normalizer | `Types.Reduce` | sound |
| V2 unifier | `Elab.Unify` + `Types.Unify` | sound |
| V3 elaborator | elaboration surface | sound |
| V4 erasure/relevance | `Elab.Erase` + `Elab.Relevance` | **found:** `erase/2` non-idempotence |
| V5 totality-closure | closure driver | sound |
| V6 SMT lint | `SMT.Solver` (+ `SMT.Parser`) | **found:** `parse_model/1` negative-value truncation |

**Two real defects surfaced** across six verticals — both in untrusted (non-TCB) code,
both reported-not-patched per the initiative's find-don't-fix discipline, both with a
banked known-finding test as the regression guard. Remaining umbrella follow-ons are
generator-expansion and the deferred SMTCoq reconstruction.

**Do NOT auto-merge.** Operator merges `autopilot/antigen-tier-b` on return.

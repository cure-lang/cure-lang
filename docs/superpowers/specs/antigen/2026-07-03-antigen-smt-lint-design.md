# Antigen V6 — SMT Lint Soundness — Design

**Status:** design (Stage 0, autopilot Phase 6 — final umbrella vertical) · **Date:** 2026-07-03 · **Branch:** `autopilot/antigen-tier-b`
**Umbrella:** `2026-07-03-antigen-untrusted-machinery-design.md` §V6 · **Predecessors:** V3, V1, V2, V5, V4 (all complete)

## 1. Goal

Extend Antigen to the **untrusted SMT lint** `Cure.SMT.Solver` — the refinement-type
constraint checker the type system consults for arithmetic obligations. Framed by
the **LOCKED SMT trust-boundary decision** (memory `smt-trust-boundary-decision`):
**Z3 is OUT of the dependent-kernel TCB** — the SMT layer is an untrusted *lint*,
never a proof (SMTCoq-style reconstruction is a someday). So the property is **lint
soundness, not completeness**: the lint may give up (`:unknown`), but it must never
claim a *stronger* answer than the truth — never discharge a false obligation, never
call a satisfiable constraint `:unsat`, never hand back a bogus counterexample.

Also per the locked decision: **Z3 is a guaranteed part of the toolchain** (ships
with the language, not an optional test-env dependency), so this vertical is
**unconditional** — never skipped or gated on `Solver.available?/0`. The assay tests
whatever `Solver` returns (Z3 or its documented conservative fallback); both must be
sound. Solver *nondeterminism* (timeouts → `:unknown`) is handled by treating
`:unknown` as an always-legal, non-infecting answer, and by pinning a fixed timeout
budget so a banked antibody replays identically (§6).

## 2. Targets (verified against source: `lib/cure/smt/solver.ex`)

- `check_sat(constraint_ast, var_types \\ %{}) :: :sat | :unsat | :unknown`.
- `prove_implication(pred1, pred2, var_name, base_type) :: boolean() | :unknown` —
  proves `∀x. P1(x) ⇒ P2(x)` by checking `P1 ∧ ¬P2` unsat: `:unsat → true`,
  `:sat → false`, `:unknown → :unknown`.
- `check_refinement_subtype(sub, super, var, base) :: boolean() | :unknown` —
  delegates to `prove_implication` (so covered transitively).
- `prove_with_counterexample(p1, p2, var, base) :: {:proven, nil} | {:failed, model} | {:unknown, nil}`
  — the `:failed` model is a claimed counterexample to `P1 ⇒ P2` (i.e. satisfies
  `P1 ∧ ¬P2`). `model` is parsed by `Cure.SMT.Parser.parse_model/1` (a
  `%{var_name => value}` map — exact value shape pinned in the plan, open item #2).

**Predicate AST format (the MetaAST 3-tuple, verified: `translator.ex:5-8,127-151`)** —
the SAME surface format V1's normalizer consumed:
- `{:binary_op, [operator: op], [left, right]}` — `op ∈ {:+,:-,:*,:/,:%,:>,:<,:>=,:<=,:==,:!=,:and,:or}`
  (`translate_op/1`, translator.ex:225-239, ALSO accepts `:/` → `div` and `:%` →
  `mod`; the catalog stays inside the non-goals' linear/one-variable scope and does
  not need to exercise them, but the enumeration above is the translator's full
  accepted set, not a subset)
- `{:unary_op, [operator: op], [operand]}` — `op ∈ {:not, :-}`
- `{:literal, [subtype: :integer], n}` / `{:variable, _, name}` (single free var, string name).

## 3. The oracle — bounded brute-force, not the kernel

The kernel does **not** decide refinement arithmetic (that is precisely what SMT is
for), so — unlike V2/V5 — there is no kernel oracle. The V6 oracle is an
**Antigen-owned bounded evaluator** `eval_pred(ast, x)` over the MetaAST format
(reusing V1's independent-surface-evaluator tactic), decided over a fixed integer
domain `D` (e.g. `-32..32`). This gives a **sound-in-one-direction** differential —
exactly matching "lint soundness, not completeness":

- A **bounded counterexample** (a concrete `x ∈ D` witnessing the lint over-claimed)
  is a genuine soundness violation — the lint is wrong for that `x` regardless of
  what happens outside `D`.
- The **converse never fires**: if the lint says `false`/`:sat`/`:unknown` while `D`
  shows no counterexample, that is NOT a violation (the real counterexample may lie
  outside `D`, or the lint legally gave up) — completeness is out of scope.

`eval_pred/2` handles the full operator set above (comparisons → boolean,
arithmetic → integer, `:and/:or/:not` → boolean); the plan pins one clause per
operator (open item #1).

## 4. Properties (three families)

### V6a — implication soundness (`prove_implication` / `check_refinement_subtype`)

`prove_implication(p1, p2, var, :int) == true` (obligation discharged) ⟹ for **every**
`x ∈ D`, `eval_pred(p1, x)` implies `eval_pred(p2, x)`. A bounded `x` with
`eval_pred(p1, x) and not eval_pred(p2, x)` while the lint returned `true` is
`{:violation, {:false_discharge, %{x: x, p1: p1, p2: p2}}}` — a false refinement
obligation discharged, the unsound-refinement hole. `false`/`:unknown` are legal.

### V6b — unsat soundness (`check_sat`)

`check_sat(constraint, %{var => :int}) == :unsat` ⟹ **no** `x ∈ D` satisfies the
constraint. A bounded satisfying witness `x` while the lint returned `:unsat` is
`{:violation, {:false_unsat, %{x: x, constraint: constraint}}}`. `:sat`/`:unknown`
are legal (a `:sat` with an out-of-`D` witness is not observable here, and not a
soundness problem — V6c checks `:sat` witnesses that ARE produced).

### V6c — counterexample consistency (`prove_with_counterexample`, intrinsic)

`prove_with_counterexample(p1, p2, var, :int) == {:failed, model}` ⟹ the model's
value `xv` genuinely satisfies `P1 ∧ ¬P2`: `eval_pred(p1, xv) and not eval_pred(p2, xv)`.
A model that does not is `{:violation, {:bogus_counterexample, model}}` — the lint
handed back a witness that is not actually a counterexample. `{:proven, nil}` is
checked by V6a's discharge property; `{:unknown, nil}` is legal. (Note: the model
value `xv` need NOT be in `D` — the assay evaluates the predicate at the actual
returned value, so this family is not domain-bounded.)

## 5. Assay & injectable seam

New module `Antigen.Assays.SmtLint` with `run/1` → `run/2` (op-map seam), mirroring
the prior assays. Three assay ids:

| id | target | property | oracle |
|---|---|---|---|
| `smt/implication` | `prove_implication` | `true` ⟹ no bounded counterexample | bounded `eval_pred` |
| `smt/unsat` | `check_sat` | `:unsat` ⟹ no bounded witness | bounded `eval_pred` |
| `smt/witness` | `prove_with_counterexample` | `{:failed, m}` ⟹ `m` refutes | `eval_pred` at `m` |

**Op-map** (`@real`), injecting the **code-under-test** at the assay boundary:

```elixir
%{
  prove_implication: &Cure.SMT.Solver.prove_implication/4,
  check_sat: &Cure.SMT.Solver.check_sat/2,
  prove_with_counterexample: &Cure.SMT.Solver.prove_with_counterexample/4
}
```

`@domain -32..32` is a committed constant (the determinism/fuel analogue — §6).

Negative controls prove each assay load-bearing:
- `smt/implication`: a `prove_implication` stub returning `true` on a
  genuinely-false implication (`x > 0 ⇒ x > 5`, counterexample `x=3∈D`) →
  `{:false_discharge,…}`.
- `smt/unsat`: a `check_sat` stub returning `:unsat` on a satisfiable constraint
  (`x > 0`, witness `x=1∈D`) → `{:false_unsat,…}`.
- `smt/witness`: a `prove_with_counterexample` stub returning `{:failed, %{"x" => 99}}`
  for a case where `x=99` does NOT satisfy `P1 ∧ ¬P2` → `{:bogus_counterexample,…}`.

## 6. Determinism & unconditionality (locked-decision constraints)

- **Unconditional:** V6 never gates on `Solver.available?/0` (Z3 is guaranteed).
  The assay tests whatever `Solver` returns; Z3 and the conservative fallback are
  both required to be sound. No `@tag :skip`, no availability branch.
- **`:unknown` is always legal** — every property treats `:unknown`/timeout as a
  non-infecting answer (an untrusted lint may give up).
- **Committed budget** — `@domain` is fixed and the catalog uses only trivial
  `QF_LIA` queries that Z3 decides deterministically well within the default 3000ms
  timeout, so no `:unknown` is *expected* on the clean catalog, and a banked
  antibody replays identically. The plan must NOT pass `:hot`/`:cold` PGO hints
  (they change timeouts and, for `:cold`, remap `:unknown → :sat`, which would
  perturb determinism); use the plain `check_sat/2` and the default
  `prove_implication/4`.
- **Test isolation** — because these clauses spawn a Z3 subprocess
  (`Cure.SMT.Process`), the SMT test module may need `async: false` to avoid
  subprocess contention with the parallel suite (open item #3); confirm at GREEN.

## 7. Invariants (what must never regress)

- No `Cure.SMT.*` / `Cure.Core.*` edits — reached read-only through the op-map. No
  `:meck`, no new dependency.
- `Antigen.Assays.SmtLint` contains no literal `StreamData` token (comments too).
- Assay `run/1,2` returns only `:ok | {:violation, term()}` — completeness/`:unknown`
  are folded into `:ok`, never a third outcome.
- The whole clean catalog re-checks `:ok` under the real ops (a real infection ⟹
  STOP and report — a genuine false discharge / false unsat / bogus counterexample
  by the real `Solver` is a **soundness finding worth reporting**, given Z3 is
  trusted-as-lint but has been wrong before; do not weaken the test).
- New generator atoms added to `Challenge.@known_atoms` (V5's §8-5 lesson).

## 8. Non-goals

- No fix to `Cure.SMT.*` (V6 *finds*; a surfaced infection is reported, not patched).
- **No completeness testing** — a valid implication the lint fails to prove
  (`false`/`:unknown`) is out of scope by the locked decision (the lint is allowed
  to be incomplete).
- No differential outside decidable linear integer arithmetic / boolean — nonlinear
  (`x*x`), quantifiers, uninterpreted functions (`byte_size`) are out of scope; the
  catalog stays inside `QF_LIA` over one variable. This restriction is load-bearing
  for soundness, not just decidability: `Translator.do_translate/1`'s catch-all
  clause (translator.ex:210-221) approximates any AST node it doesn't recognize as
  the literal `true` (logging a warning) rather than failing the query. Confirmed
  traceable unsoundness OUTSIDE the catalog's scope: if such a node stood in for the
  WHOLE of `pred2` in `generate_subtype_query`'s `(and P1 (not P2))` encoding, `(not
  true)` is `false`, collapsing the conjunction to `unsat` regardless of `P1` —
  `prove_implication` would return `true` (proven) for an implication that may not
  actually hold, a false discharge caused purely by a translation gap, not a real
  proof. The MetaAST forms this vertical's catalog is restricted to
  (`:binary_op`/`:unary_op`/`:literal`/`:variable`, all of §2's operator set) are all
  fully translatable, so the clean catalog does not trigger this path and V6's
  "clean catalog is `:ok`" premise (§7) holds. This is documented here as a known,
  real soundness gap in `Cure.SMT.Translator` that stays out of V6's scope by
  construction — analogous to why the `:cold` PGO remap (§6) must also be avoided —
  not a hypothetical, and any future vertical widening the catalog past primitive
  arithmetic/boolean forms must re-litigate this non-goal.
- No SMTCoq / proof-reconstruction (that is the someday the locked decision defers).
- No random query fuzzer — a curated fixed catalog (elab pattern).

## 9. Open items (for the plan / review to pin)

1. **`eval_pred/2` operator coverage.** Pin one clause per MetaAST operator the
   catalog uses (`:+,:-,:*,:>,:<,:>=,:<=,:==,:!=,:and,:or,:not`), matching
   `Translator.do_translate/1`'s semantics EXACTLY (e.g. `:==` is equality, `:!=`
   is disequality, `:-` is both binary subtraction and unary negation — the arity
   disambiguates). Integer semantics only (base_type `:int`); the catalog uses no
   floats. `:/` and `:%` are in the translator's accepted set (§2) but out of the
   catalog's scope per §8 non-goals — `eval_pred/2` need not implement them.
2. **`prove_with_counterexample` model shape — confirmed parser bug on negative
   witnesses.** `Cure.SMT.Parser.parse_model/1` returns `%{var_name => value}`; for
   a NON-negative integer value it already returns a native Elixir integer (no
   parsing needed — confirmed: `parse_model` on `"...Int 3)"` yields `%{"x" => 3}`).
   But for a NEGATIVE value it is broken: Z3's real `get-model` output represents
   negative integers as `(- N)` (confirmed via live `z3 -smt2 -in`, e.g.
   `(define-fun x () Int\n    (- 99))`), and the outer regex's `[^\)]+` capture
   truncates at the FIRST `)` — the one closing `(- N)` itself — before reaching the
   `\)` the regex expects to close `define-fun`. The captured value string is then
   `"(- 99"` (missing its closing paren), which fails `parse_value`'s own
   `^\(-\s*\d+\)$` negative-literal pattern (that pattern requires the trailing `)`
   that was already stripped) and falls through to the raw-string catch-all —
   `parse_model` returns `%{"x" => "(- 99"}`, not `%{"x" => -99}`. Verified directly:
   `Cure.SMT.Parser.parse_model/1` on synthetic Z3-shaped multi-line output for a
   negative define-fun returns the malformed string, not an integer. This is NOT
   hypothetical for V6c: a plausible baseline predicate like `x > -100 ⇒ x > 0`
   makes Z3 pick a negative witness (confirmed live: `x = -99`) for exactly this
   shape. Since V6c evaluates `eval_pred` at the model's actual value (unbounded,
   spans negatives) this bug is squarely in V6c's path, not a corner the catalog can
   dodge by construction alone. The plan must pin ONE of: (a) the V6c assay's model
   extraction defensively re-parses the `"(- N"`-shaped malformed string itself
   (working around the untrusted `Parser`'s bug without touching
   `Cure.SMT.*`, consistent with §7's read-only invariant) before calling
   `eval_pred(p, xv)`; or (b) the catalog's V6c baseline entries are chosen/verified
   (by running them, not by assumption) to only ever produce non-negative witnesses.
   Do not assume `model[var_name]` is always a ready-to-use integer.
3. **Z3 availability + test async.** Confirmed during spec review: `z3` IS installed
   and invocable in this worktree (`/opt/homebrew/bin/z3`, verified live via
   `z3 -smt2 -in` producing real `sat`/`unsat`/model output for §9-item-2's checks
   above) — the clean catalog will exercise the real Z3 path, not the
   `:unknown`-only conservative fallback (`Process.z3_available?/0` → `false` branch
   in `Solver.run_query/2`). The plan should still verify this holds in CI (not just
   this worktree) and confirm the fallback path (if ever hit) doesn't crash — still
   sound, so the clean catalog stays `:ok` either way. Decide `async: true|false` for
   the SMT test module (subprocess contention). Neither gates the vertical.
4. **Challenge kind + atoms.** Add a `:smt_query` kind (typespec-only — the MetaAST
   predicate + var + mode payload doesn't fit an existing kind); add the var name
   atom(s) and any literal names to `@known_atoms`; add three `assay_module/1`
   clauses, one per assay id in §5's table (Runner has no catch-all). Precedent
   (verified): `:closure_env` (V5) also has no `Challenge.to_pieces/from_pieces`
   clause — kinds that never go through `explore/1`'s corpus-banking path don't need
   serialization support, only the `@type kind ::` union entry and `@known_atoms`
   (V5 added both defensively even without a `to_pieces` clause) — `:smt_query`
   follows the same shape.

## 10. Test catalog (for the plan — §5 of the plan will expand each)

1. V6a implication baseline (valid `x > 5 ⇒ x > 0`): lint `true`, no bounded counterexample → `:ok`.
2. V6a implication baseline (invalid `x > 0 ⇒ x > 5`): lint `false`, so no false discharge → `:ok`.
3. V6a negative control: `prove_implication` stub returning `true` on the invalid implication → `{:false_discharge,…}`.
4. V6b unsat baseline (unsat `x > 0 ∧ x < 0`): lint `:unsat`, no bounded witness → `:ok`.
5. V6b sat baseline (sat `x > 0`): lint `:sat` (not `:unsat`) → `:ok`.
6. V6b negative control: `check_sat` stub returning `:unsat` on the sat constraint → `{:false_unsat,…}`.
7. V6c witness baseline (invalid implication): `prove_with_counterexample` returns `{:failed, model}` (or `{:unknown, nil}`); if a model, it genuinely refutes → `:ok`.
8. V6c negative control: `prove_with_counterexample` stub returning a bogus `{:failed, model}` → `{:bogus_counterexample,…}`.
9. Generator+wiring: each catalog non-empty & correctly tagged; `Runner.replay_one/1` dispatches all three ids and the whole clean catalog is `:ok`.

## 11. Next (umbrella roadmap)

V6 is the **final** umbrella vertical. On completion, all six untrusted-machinery
verticals (V1 normalizer, V2 unifier, V3 elaborator, V4 erasure/relevance, V5
totality-closure, V6 SMT lint) are covered. Remaining umbrella follow-ons are
generator-expansion and the deferred SMTCoq reconstruction. **No auto-merge.**

# Infer/Check Coherence — params-on-spine ctor in checking mode (task #14) — Design

**Status:** approved design (operator standing batch authorization; TCB change pre-approved under the Agda/Lean-alignment blanket — Lean's kernel `check` IS `infer` + def-eq (`type_checker.h:130-136`, source-verified in the vendored clone), so making Cure's `check` subsume `infer`+conv on the shape its specialized clause cannot handle is the most literal possible alignment — FULL verification gate mandatory).
**Layer:** K (one clause-body restructure in `lib/cure/core/kernel.ex` `check/3`) + A (Antigen widening) + docs (sibling-finding ledger entry).
**Batch:** task #14, worktree `kernel-parity-batch`, branch `autopilot/kernel-parity-batch`, HEAD post-D2 (`77be1af`).
**Inventory source:** fresh in-worktree scout 2026-07-09 (post-D2 anchors; re-verify before editing).

## §0 The gap (verified in this worktree)

Constructor application in Core is one flat node `{:ctor, name, args}` with TWO legal spellings for a parameterized family: **fields-only** (`{:ctor, :reflexive, [a]}` — the checking spelling; params recovered from the expected `vdata`) and **params-on-spine** (`{:ctor, :reflexive, [ty, a]}` — the K6/§E.1 inference spelling, Lean's kernel form, params prepended to fields in the same list).

- `infer`'s ctor clause (kernel.ex:122-170) accepts BOTH-but-differently: fields-only for paramless families; `pc + fields` args against `ptele ++ tele` for param families (the K6 arm, :154-161, which RE-CHECKS the spine params against the family telescope); fields-only-on-param-family → `:ctor_requires_checking_mode`.
- `check`'s ctor clause (kernel.ex:237-265) pattern-matches `({:ctor,…}, {:vdata,…})` on SHAPE, hard-codes the fields-only telescope, and delegates to `check_ctor_app` whose length guard (:483, :491) returns `{:error, :ctor_arity}` for any other count — BEFORE any semantic judgement, and INSTEAD of falling through.
- `check`'s clause 4 (kernel.ex:267-278) is exactly the Lean fallback the moduledoc promises ("falling back to `infer` plus a cumulative conversion test"): `infer` then `subtype?`. **The spine term never reaches it** — Elixir first-match dispatch stops at clause 3, which conflates "this clause applies" (pattern) with "this term fits this clause's strategy" (arity).

Consequence, pinned live in `test/cure/core/k6_param_ctor_infer_test.exs:19-22`: for `t = {:ctor, :reflexive, [{:int_type}, {:int_lit, 3}]}`, `infer(ctx, t) = {:ok, A}` with `A = {:vdata, :Equivalent, [vint_type, vint 3, vint 3]}`, yet `check(ctx, t, A) = {:error, :ctor_arity}`. So `infer(t)=A ⇏ check(t,A)=:ok` — the coherence property every reference kernel guarantees fails.

**Reachability is not theoretical:** `check` with a vdata expected runs inside `infer` itself — the application rule checks every argument against the Π domain (kernel.ex:100-107), plus `do_spine` (:445), nested ctor args (:500), branch bodies (:698), `check_def` (:296). Plain inference of `(λ p : Equivalent(Int,3,3). p)(reflexive(Int, 3))` fails `:ctor_arity` today. Antigen's equality generator deliberately confines itself to the coherent fragment because of exactly this shape (equality.ex:15-22, quoted policy comment). (Note: `assays/elab.ex:268-284`'s check-fallback is a DIFFERENT, still-standing asymmetry — it catches `:ctor_requires_checking_mode` for a top-level fields-only ctor body, which §6 deliberately keeps un-inferable; it is not evidence for the spine/`:ctor_arity` bug this spec fixes, and is not cited as such.)

## §1 The fix (locked: scout option ii — route to the existing fallback)

Inside `check`'s ctor clause, branch on the arg count:

- `length(args) == length(tele)` → the existing fields-only path, byte-identical (its value-form `{:conversion_failure, vdata, vdata}` diagnostics are pinned at `param_index_split_test.exs:110-125` and MUST NOT reroute).
- `length(args) == pc + length(tele)` (`pc > 0`) → delegate to the generic infer+conv logic: `infer(ctx, term)` then `subtype?(inferred, expected, ctx)`, with the same error shape clause 4 produces (`{:conversion_failure, reified, reified}` on mismatch). Extract clause 4's body into a shared private helper (e.g. `check_via_infer/3`) so the logic exists ONCE — duplication is the failure mode being fixed (scout option i is rejected for exactly that reason).
- any other count → `{:error, :ctor_arity}` unchanged (genuinely malformed).

**Order is load-bearing, not cosmetic:** for a paramless family (`pc == 0`), `pc + length(tele)` collapses to exactly `length(tele)` — the fields-only and spine conditions become the SAME predicate. The three branches above MUST be tested in first-match order (an ordered `cond`/`if`-chain, fields-only checked first) exactly as the existing code does — never rewritten as independent `case` guards or reordered — or every `pc == 0` ctor would silently reroute through the new infer+conv path, violating the "byte-identical... MUST NOT reroute" pin on the fields-only path above.

**Soundness argument (TCB):** the new acceptance set is exactly `{t | infer(t) = {:ok, A'} ∧ subtype?(A', expected)}` — every such term is ALREADY accepted today wherever an inference position occurs (case scrutinee, standalone infer). The spine path re-derives everything through the existing K6 infer arm (which re-checks spine params against the family telescope) plus the existing conversion. No new judgement, no new equation; the change is the definition of coherence itself, and it is literally Lean's check (`infer` + def-eq at declaration boundaries, `environment.cpp:175/:205`).

**Alignment summary (scout §4, source-verified):** Lean — `expr_kind` (vendored `kernel/expr.h:84`) has no `Ctor` variant at all: `{BVar, FVar, MVar, Sort, Const, App, Lambda, Pi, Let, Lit, MData, Proj}`; a constructor is an ordinary `Const` applied via `App` spines carrying ALL args (params+fields together), and `check = infer + is_def_eq` (no checking mode in the kernel). Idris2 — `checkExp` (vendored `TTImp/Elab/Check.idr:779-810`) unifies got-vs-expected; no ctor-specialized check rule. Agda — HAS a ctor-specialized checking rule: `checkConstructorApplication` (vendored `TypeChecking/Rules/Application.hs:1006-1059`) derives the parameters `ps` from the expected type `t` (not from the surface args) at :1041-1047, then checks only the non-parameter `args'` (:1059) — so its internal syntax effectively stores constructors fields-only in the elaborated term, and only one spelling exists (incoherence cannot arise). Cure currently runs Lean's spelling in infer and Agda's in check with no bridge; this fix installs the bridge on the only incoherent pairing.

## §2 Antigen widening (the antibody is already armed)

The infer→check round-trip property ALREADY EXISTS as the `term/infer_check` assay (`lib/antigen/assays/term.ex:46-59`, violation class `{:check_disagrees, …}`), and `term/subject_reduction` (:67-76) asserts `check(nf(t), inferred)`. Widening the GENERATOR arms the antibody automatically:

1. `lib/antigen/generators/equality.ex`: (a) a top-level params-on-spine reflexive arm in `eq_term/0` (:57-64) — `{{:ctor, :reflexive, [ty, a]}, {:data, :Equivalent, [ty, a, a], []}, []}` (flat claimed-type spelling per the reify-flat note at :96-99); (b) a checking-position spine arm via the check-embedding idiom (`mutation.ex:141-148` precedent): `{:app, {:lam, eq_ty, {:var, 0}}, spine_refl}`; (c) REWORD the coherent-fragment policy comment (:15-22) to record the fix (it becomes a historical note, not a live restriction).
2. `lib/antigen/generators/rewrite.ex:179` — current comment reads "The proof sits in inference position, so it rides the params-on-spine form."; that framing (spine form ⇒ inference position) is no longer exclusive post-fix (the spine form now also checks), so the comment needs a clause noting the spine form is checkable too, not just an inference-position artifact.
3. Deterministic antibody pin: a NEW test file — name it distinctly, e.g. `spine_ctor_coherence_antibody_test.exs` (`test/antigen/eq_inductive_antibody_test.exs` ALREADY EXISTS and covers unrelated territory — the Eq-as-inductive retirement/GATE-C soundness properties — do NOT reuse or collide with that name/file). Style it after the existing `test/antigen/*_antibody_test.exs` files (e.g. `cycle_rule_antibody_test.exs`). Cover the EXACT historical counterexample — spine reflexive checks against its own inferred type `:ok`; wrong-endpoint expected still rejects (now `{:conversion_failure, _, _}`, not `:ctor_arity`); 3-arg reflexive still `:ctor_arity`.

## §3 Sibling finding — FILED, not fixed (the value-level spelling dichotomy)

The two spellings also diverge BELOW the typing judgement (scout §5 hazard, all pre-existing and reachable through pure `infer` today; this fix changes their incidence, not their existence):

- `Eval.eval` maps the whole spine into the value: `{:vctor, :reflexive, [ty_v, a_v]}` vs `{:vctor, :reflexive, [a_v]}` (eval.ex:38) — and `Conv` compares vctor spines length-strictly (conv.ex:88-89, :183-186), so **the two spellings of the same constructor are not definitionally equal**.
- case ι-reduction binds `reverse(args) ++ env` (eval.ex:56-62) against a branch typed for `arity = length(fields)` — an OPEN branch body over a spine-form scrutinee has every ambient de Bruijn reference shifted by `pc`: well-typed by `infer` today, evaluates wrongly. (Antigen's transport bodies are closed, which is why the property suite has not tripped it.)
- `Erase.erase` on a spine ctor takes its "already erased" branch and keeps both the param and the erased witness (erase.ex:20-36).

The principled endgame is ONE canonical spelling (Lean's params-always vs Agda's fields-only) — a real design fork with TCB-wide consequences, for the OPERATOR per the design-fork-prose preference. This spec's deliverable is a ledger row + memory note stating the fork and the evidence anchors; nothing below the typing judgement changes in #14. The completion report flags it explicitly.

## §4 Verification gate (mandatory, TCB blanket conditions)

1. Red-green: new kernel test red before the clause change (spine-check `:ctor_arity` → `:ok`), green after; all §5 pinned behaviors unchanged. The §5 pins are immutable: if the restructure makes any of them fail, the restructure is wrong — fix `check/3`, never loosen or edit a pinned test to fit.
2. Antigen: the widened generator green under the EXISTING `term/infer_check` + `term/subject_reduction` assays (this IS the new-antibody requirement — the property now patrols the widened space); the deterministic pin green; FULL Antigen suite green.
3. Full `mix test` green; count delta enumerated.
4. Oracle: replay green, zero verdict changes (no new cluster — the fix is Core-internal; surface programs were already coherent because the elaborator emits fields-only ctors, elaborator.ex:4065-4085).
5. Diff: kernel.ex shows ONLY the check-clause restructure + the shared helper extraction; nothing else under `lib/cure/core/`; no elaborator change; no decoy-pipeline change; ghost authorship.
6. Ledger: the §3 sibling finding (value-level spelling dichotomy) is recorded as a parity-ledger row plus a memory note, citing its evidence anchors (`eval.ex:38`, `:56-62`; `conv.ex:88-89`, `:183-186`; `erase.ex:20-36`), and explicitly flagged as an operator design fork — completion is not claimed until this is checked off alongside items 1-5.

## §5 Behaviors that MUST NOT change (pinned)

- `infer` spine accept (`k6_param_ctor_infer_test.exs:19-22`) and fields-only infer reject `:ctor_requires_checking_mode` (:28-29; also `param_index_split_test.exs:97-102`).
- Fields-only check accept/reject with VALUE-form `{:conversion_failure, {:vdata,…}, {:vdata,…}}` diagnostics (`param_index_split_test.exs:87-95, :110-125`; `equivalent_kernel_test.exs:55-83`; `eq_refl_retirement_test.exs:73-76`) — the fields-only path is untouched.
- Wrong-arity (neither fields nor pc+fields) still `:ctor_arity`.
- `resolve_free`/eta-expansion (C-3): no interaction — `eta_expand_bare_ctor` excludes erased-arg/result-param ctors, so `reflexive` is out of its scope (elaborator.ex:4789-4815; the fields-only ctor it emits is built at :4065-4085, not just :4070-4084 — the `Enum.split(all, pc)` at :4069 and the `{:ok, {:ctor, cname, args}, result_type}` construction at :4085 are the two anchors worth citing together); the `:ctor_arity` mentions in elab test docstrings are historical elaborator symptoms, not kernel pins.

## §6 Non-goals

- The canonical-spelling design fork (§3) — filed for the operator.
- Any change to `Eval`/`Conv`/`Erase`/case-ι — below the typing judgement, sibling finding's territory.
- Making fields-only INFERABLE (the `:ctor_requires_checking_mode` reject is deliberate and pinned).
- Elaborator changes — it already emits only fields-only ctors.

## §7 Acceptance criteria

1. `check(ctx, spine_refl, infer(ctx, spine_refl))` = `:ok` — the coherence counterexample dissolves; red→green documented.
2. All §5 pins green unchanged; wrong-endpoint spine check rejects with `{:conversion_failure, _, _}`.
3. Antigen: widened equality arms sampled by the existing round-trip assays, full suite green; deterministic pin green.
4. Full suite green; oracle replay zero-divergence.
5. kernel.ex diff = the one clause restructure + helper extraction, nothing else under core; ghost authorship.
6. The §3 sibling finding recorded in the parity ledger + memory with its evidence anchors, explicitly flagged as an operator design fork.

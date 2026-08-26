# Lean-Shape Dependent Pattern Matching (Safe FRP) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use `superpowers:executing-plans` (autopilot Stage 4, inline on Opus) with the `cure-porting` domain skill. Steps use checkbox (`- [ ]`) syntax. This plan is **oracle-driven**: for kernel/elaborator phases the exact diff emerges from a named failing probe — each task fixes its red test by diagnosis, never by a pre-guessed patch. Do NOT fabricate "complete code" for a diff that must be discovered; the red test + procedure + gate ARE the task contract.

**Goal:** Give Cure one unification-driven, context-generalizing `match`/`with` equation-compiler that subsumes today's A/B/C `with` paths and is strong enough to type-check the Sculthorpe–Nilsson Safe-FRP `SF` family (computed `++`/`∧` indices) in Cure.

**Architecture:** Elaborator equation-compiler (E) emitting kernel-checked `{:case}` trees over Cure's existing five-rule `unify_indices` (already landed); carried stuck-index equalities discharged by Cure's existing `rewrite` + a type-level lemma stock; TCB touched only where a phase proves an E-only route impossible (expected: Phase 5 signature-aware `reify`). Governing spec: `docs/superpowers/specs/types/2026-07-02-lean-shape-matching-design.md`.

**Tech Stack:** Elixir (Cure compiler); differential oracle (`mix cure.oracle <cluster>`, `idris2` at `~/Develop/Idris2/build/exec/idris2`); Antigen (StreamData property assays under `mix test`); Lean reference at `~/Develop/lean4`.

## Global Constraints (verbatim from spec §8 — every task inherits these)

- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>`; never `git add -A`/`.`. Work on the isolated worktree `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/lean-shape-matching` (branch `autopilot/lean-shape-matching`).
- **One build at a time.** Never two concurrent `mix` suites (a past concurrent full-suite run panicked the kernel). Scoped `mix test <file>`; full suite once, alone, at a gate.
- **Tests immutable once green**; behavioral, not implementation-coupled.
- **Reference-grounded:** verify against vendored Idris2/Agda AND `~/Develop/lean4`, never memory. Dump real normal forms when reasoning about conversion.
- **TCB gate (any `lib/cure/core/*` diff):** HARD-STOP-and-review — red-green + a new Antigen antibody proving the change terminates and equates no distinct normal forms + full Antigen + full suite + an **independent adversarial-verification subagent** (fresh context, tries to break soundness). Per `elaborator-hard-stop-principle`, first prove no E-only term closes the gap. **No auto-merge.**
- **Baseline:** capture `mix test` pass count at Phase 0 start; "0 regressions" is measured against it at every gate.

---

## Phase 0 — Acceptance oracle (E/none; non-TCB)

**Goal:** A minimal faithful `SF` probe that is **red in Cure for the stuck-`++`-index reason** and green in Idris — the anchor for "done."

### Task 0.1: Baseline + faithful minimal SF probe (Idris green, Cure red)

**Files:**
- Create: `test/oracle/frp/frp01_par_assoc.cure`, `test/oracle/frp/frp01_par_assoc.idr`
- Create: `test/oracle/frp/frp02_seq_meet.cure`, `test/oracle/frp/frp02_seq_meet.idr`
- Touch (regen): `test/oracle/frp/verdicts.json`

**Interfaces:**
- Produces: the `frp` oracle cluster; the concrete Cure error id for the stuck-`++` case (recorded in the task note — consumed by Phases 2/3/4 as the red target).

- [ ] **Step 1: record baseline.** Run `mix test 2>&1 | tail -3`; note the pass count in the task note (the regression baseline).
- [ ] **Step 2: write the Idris probe** (`frp01_par_assoc.idr`), `%default total`, no `module` line. Minimal faithful core:
  ```idris
  %default total
  data Sig = SigC | SigE
  data Dec = DDec | DCau
  dmeet : Dec -> Dec -> Dec
  dmeet DDec DDec = DDec
  dmeet _ _ = DCau
  data SF : List Sig -> List Sig -> Dec -> Type where
    Prim : SF as bs DCau
    Seq  : SF as bs d1 -> SF bs cs d2 -> SF as cs (dmeet d1 d2)
    Par  : SF as bs d1 -> SF cs ds d2 -> SF (as ++ cs) (bs ++ ds) (dmeet d1 d2)
  -- acceptance driver: re-associating parallel composition needs (as ++ bs) ++ cs = as ++ (bs ++ cs)
  parAssoc : SF ((as ++ bs) ++ cs) ((xs ++ ys) ++ zs) d
          -> SF (as ++ (bs ++ cs)) (xs ++ (ys ++ zs)) d
  parAssoc sf = ?assoc_hole   -- Idris: the rewrite is via `rewrite appendAssociative ...`
  ```
  Refine until `idris2 --check` passes (fill `parAssoc` with the real `rewrite appendAssociative` proof so it is genuinely total-accepted, not a hole). The point: a function whose well-typedness *requires* `++` associativity.
- [ ] **Step 3: write the faithful Cure transliteration** (`frp01_par_assoc.cure`) — same `SF` family (Cure `type … indices (…)`), same `parAssoc` signature and intended `rewrite` body. Same signature, faithful — not a different proof.
- [ ] **Step 4: run the oracle.** `mix cure.oracle frp` — writes `verdicts.json`. Expect `frp01`: Cure `reject`, Idris `accept` → a reach input.
- [ ] **Step 5: confirm red-for-the-right-reason.** Elaborate `frp01_par_assoc.cure` directly (a scoped `iex`/`mix run` snippet or `Cure.Elab.Program.elaborate/1`); confirm the error is the **stuck computed-index / rewrite-through-`++`** failure, NOT a parse/kind/unrelated error. Record the exact error id in the task note. If it fails for an unrelated reason, fix the probe until the failure is the intended one.
- [ ] **Step 6: add `frp02_seq_meet`** — a `Seq` composition needing only `dmeet` (∧) refinement, no `++`. This one may already be `accept/accept` (isolates the Dec-index path from the list-index path); record which.
- [ ] **Step 7: set relations + commit.** In `verdicts.json`, mark `frp01` `cure_stricter` with reason `"reach: stuck ++-index rewrite (the Phase-4 acceptance target); flips to same when the lemma stock + rewrite composition land"`; `frp02` per its actual verdict. Run `mix test test/oracle_replay_test.exs` (green replay). Commit `test(oracle): frp acceptance cluster — minimal SF, stuck-++-index reach (frp01) + Dec-meet (frp02)`.

**Gate:** oracle_replay green; `frp01` red-for-the-right-reason with its error id recorded; baseline pass count recorded.

---

## Phase 1 — Unifier audit (TCB only if a real gap is found)

**Goal:** Confirm the already-landed five-rule `unify_indices` (`kernel.ex:787-885`) exposes what the Phase-3 front-end needs; open a TCB diff only if the audit finds a real gap.

### Task 1.1: Audit `unify_indices` against the front-end's needs

**Files:** Read-only audit of `lib/cure/core/kernel.ex:787-885`, `2026-07-01-case-index-unification-design.md`, `~/Develop/lean4/src/Lean/Meta/Tactic/UnifyEq.lean`. Create: `docs/superpowers/notes/2026-07-02-unifier-audit.md`.

- [ ] **Step 1: Lean re-check.** Read `UnifyEq.lean` + `Meta/Tactic/Cases.lean`; note (in the audit doc) how Lean's `unifyEq?` classifies solution/injectivity/conflict/cycle and what it returns for a stuck non-injective application. Ground the audit against this.
- [ ] **Step 2: enumerate the front-end's demands.** For each of the five rules, write in the audit doc: does `unify_indices` expose the outcome the generalizing front-end (Phase 3) needs — specifically (a) does it return the branch substitution *and* a stuck-residual (the equations it could NOT solve) so Phase 2 can carry them? (b) does conflict yield `:impossible` for `{:absurd}`? (c) does occurs/cycle degrade to `:undecided` (never `:impossible`)?
- [ ] **Step 3: probe the stuck-residual question** with a scoped throwaway test: call `unify_indices` on `[as ++ cs]` vs `[fresh_var]` and inspect the return. Record whether the stuck equation is surfaced or swallowed.
- [ ] **Step 4: decide.** If the unifier already surfaces stuck residuals usably → Phase 1 closes with **no TCB diff** (audit doc committed). If it swallows them (Phase 2 can't get at the carried equation) → that is the real gap: define the minimal change (return the residual), and **escalate to the TCB gate** (red test: `test/cure/core/unify_indices_residual_test.exs`, asserting `unify_indices` on a stuck pair (e.g. `[as ++ cs]` vs `[fresh_var]`) returns the unsolved residual equation rather than swallowing it; verify: `mix test test/cure/core/unify_indices_residual_test.exs`; red-green + antibody: "unifier terminates + never equates distinct NFs + conflict⇒`:impossible` (never cycle) + stuck residual surfaced faithfully" + full suites + independent adversarial verification). Antibody must NOT require cycle⇒`:impossible`.
- [ ] **Step 5: commit** the audit doc (`docs(notes): unifier audit — <gap|no-gap> for the generalizing front-end`), plus the kernel diff + antibody as a **separate** commit only if Step 4 found a gap.

**Gate:** audit doc committed with an explicit no-gap/gap verdict; if a gap, the TCB gate fully green.

---

## Phase 2 — Carried equalities (E-first; escalate to TCB only on a proven wall)

**Goal:** Stuck unification carries an `Eq` into the motive instead of falling through unrefined — via the E-only generalization of capability B, escalating only on a named blocked kernel judgement.

### Task 2.1: E-only carried-index-equality (red → green on a non-indexed carrier)

**Files:** Modify `lib/cure/elab/elaborator.ex` (the with/match motive path). Test: `test/cure/elab/carried_index_eq_test.exs`.

**Interfaces:**
- Consumes: capability-B Eq-arrow motive `λw. Eq(T,e,w) → G[e↦w]` (existing); `unify_indices` stuck residual (Phase 1).
- Produces: `elaborate_*` emits, for a stuck index equation over a **non-indexed carrier** (`SVDesc = List Sig`, `Dec`), a branch motive `Π(Eq(carrier, lhs, rhs), G)` the kernel accepts.

- [x] **Step 1: Lean re-check.** DONE (subagent a34a4b73, opened by re-reading `~/Develop/lean4` source). **Lean is OPT-IN, NOT auto:** stuck index equations require explicit `match h:` syntax — `MatcherInfo.DiscrInfo.hName?` (`MatcherInfo.lean:16-18`) is populated ONLY from user syntax (`Elab/Match.lean:1159`); the equality hypothesis enters the motive telescope only `if let some hName := discrInfos[i]!.hName?` (`Match.lean:137-139`, bound :169-170); an UNNAMED stuck equation throws "Dependent elimination failed: Failed to solve equation" (`UnifyEq.lean:121-124`). Soundness = the kernel independently verifies the generated matcher: branch checked at the CONSTRUCTOR's index, use-site applies the motive at the SCRUTINEE's index, the named equation (a bound var, not trusted elaborator proof) bridges them. **Cure's Phase 2 deliberately AUTOMATES that opt-in** (chosen design; Step 1 anticipated it) — sound by the SAME kernel-checked Eq-arrow vehicle as capability B (`λw. Eq(T,e,w)->G` discharged by `refl`), generalized from the scrutinee VALUE to its computed INDEX. **Elaborator-hard-stop consequence:** that vehicle is E-only (kernel already accepts Eq-arrow motives via `check_motive_wf` + index-generalized motives via `build_motive`), so Phase 2 does NOT need the Phase-1 residual-surfacing TCB change — the elaborator builds the index-Eq-arrow itself. Attempt E-only first (Step 3); residual-surfacing stays a fallback only if the E-only vehicle hits a proven kernel wall.
- [x] **Step 2: red test.** DONE — `test/cure/elab/carried_index_eq_test.exs`. Family `F indices (xs: SList)` with computed result index `mk : F(as) -> F(bs) -> F(app(as,bs))` (mirrors the paper's `par`); `rebuild(v : F(app(p,q))) -> F(app(p,q))` reconstructs `mk(l,r) : F(app(as,bs))` in the `mk` branch. **RED confirmed:** fails `{:error, :branch_type}` (branch-body conversion `app(as,bs) ≢ app(p,q)` — needs the carried eq); the swapped-`mk(r,l)` soundness-control arm already returns `{:error, _}` (green). Root cause verified: `build_motive` only generalizes index positions that are *variables* (elaborator.ex:929), skipping a computed index like `app(p,q)` (:930) — so the goal is never refined to the ctor's index. Preamble (computed result index + auto-bound `as`/`bs`) elaborates fine, so the red is for the right reason.
- [x] **Step 3: implement E-only. DONE — 3a (commit b32702b) + 3b (commit c6c98e9), both E-only, no `lib/cure/core/*` edit.** TWO coordinated sub-parts:
  - **(3a) Computed-index goal generalization — needs NO carried eq. DONE (commit b32702b).** `build_motive` (`elaborator.ex:913`) now abstracts each *computed* index term (not just index *variables*) out of the result type into a fresh sentinel variable that rebinds to its motive binder (via existing `replace_term` + `generalize`; sentinels chosen above all free de Bruijn indices via new `max_free_ref`). Each branch's RETURN goal refines to the ctor's result index (`F(app(as,bs))`, `F(SNil())`). Grounded: Lean's casesOn reads each ctor's result-index *terms* and applies the motive to them (`inductive.cpp:643-646`, re-verified this pass by subagent a5b3fb5a) — mechanism (a), unconditional, no equation; the kernel checks each branch at `motive @ ctor_indices`, use site recovers the goal via `motive @ scrutinee_indices`. `carried_index_eq_test.exs` both green (goal-refinement + sharpened `mk(r,l)` soundness control). Change is monotonic (only refines goals mentioning the computed scrutinee index; constant motive elsewhere) — **full suite 2284, zero regressions**. CAVEAT: occurrence abstraction is sound but *incomplete* (a differently-reduced occurrence is missed → branch fails, never unsound); fine for the FRP cluster (literal index occurrence).
  - **(3b) Sibling refinement over an indexed scrutinee — the genuine carried eq. DONE (commit c6c98e9).** A sibling `w : F(app(p,q))` (not the scrutinee) returned in a 3a-refined branch needs the branch's stuck equation `app(p,q) = ctor_idx` carried and `w` transported. **Path finding:** the `match` path had 3a goal refinement but NO sibling transport; capability-B transport (`elaborate_with_value`) is restricted to NON-indexed families; `elaborate_with_rematch` refines siblings only by index-*variable* substitution — cannot help a *stuck computed* index. So 3b is a NEW combination in the match path: NEW `detect_carried_index` finds a single computed index term mentioned by an in-scope sibling (excluding the scrutinee, `collect_index_siblings`); `wrap_motive_carried_eq` peels build_motive's k+1 lams and injects `Eq(T, idx, jₚₒₛ)` → `motive = λj̄.λx. Eq(SList, app(p,q), jₚₒₛ) -> G'`, whole case applied to `(refl app(p,q))`; `elaborate_carried_eq_branch` binds `prf : Eq(SList, app(p,q), ctor_idx)` and transports each index-mentioning sibling via `rewrite prf (λz. H[idx↦z]) h` — the exact kernel-checked Eq-arrow + rewrite vehicle of capability-B `elaborate_with_eq_branch` (:864), lifted VALUE→INDEX. **Escalation check (Step 5): NO Phase-5 pull-forward needed** — the indexed family only ever appears as a `:rewrite` motive RESULT (`Eval.apply`'d, never reified into a Π domain), exactly as capability B avoids the collapse; the reify collapse was NOT hit. E-only: kernel re-checks the assembled case, so a frame bug → rejection, never unsound accept. Restricted to a single computed index with a CLOSED index type (SList/Dec); other shapes fall back to plain 3a (kernel rejects an un-transportable sibling). Controls green: sibling transport works; a wrong-FAMILY sibling is transported yet rejected (`G(SNil) ≢ F(SNil)`); an unrelated-index sibling is not transported and stays rejected. **NOT on the current FRP-probe critical path** (`frp01`/`frp02` use explicit `rewrite ... in`, never match on SF) — so 3b is spec-generality; a future SF-matching oracle probe should prove the generality end-to-end. **Independent adversarial verification: SOUND** (subagent a98a0035, re-derived Lean `MatcherInfo.lean:17`/`Match.lean:132-143,1242-1246` — eq opt-in, discharged by `mkEqRefl discr`, never an axiom; 12 attack probes all correct incl. swapped-arg sibling rejected, compound-scrutinee sound, and **param+index WRONG-param `P(Bool,…)` at `P(Nat,…)` REJECTED** — the Quote.reify param/index collapse does NOT launder a wrong param through transport). Root soundness: the assembled `{:app,{:case,…},{:refl,idx}}` is re-checked by `Kernel.check` (declarations.ex:42), so a frame/de-Bruijn bug yields rejection not unsound accept. Two completeness-only notes (≥2-computed-index families + non-closed index types fall back to 3a and reject legitimately-transportable siblings) — acknowledged conservative, not soundness.
- [x] **Step 4: green. DONE.** `carried_index_eq_test.exs` (3a) + `carried_index_sibling_test.exs` (3b) green; the carried `Eq` is load-bearing (the sibling-transport test is `:branch_type`-RED without 3b, confirmed via `--include skip` before implementing).
- [x] **Step 5: escalation check. DONE — NO escalation.** Step 3 hit NO blocked kernel judgement: the indexed family appears only as a `:rewrite` motive RESULT (never a reified Π domain), so the `Quote.reify` collapse was not reached. Phase 5 stays where it is; no Phase-2 TCB gate opened (the change is E-only, kernel-backstopped).
- [x] **Step 6: regression + commit. DONE.** Scoped regressions green (`with_abstraction_test`, `with_rematch_elab_test`, `with_rematch_match_test`, `dependent_match_surface_test` each alone) + full elab dir 117 + oracle replay + full suite 2287, zero regressions. Committed 3a `b32702b`, 3b red-test `dbb1fe5`, 3b impl `c6c98e9`. **Phase 2 closed E-only** — the spec's Phase-2 TCB listing (§3) should be dropped; Phase-1 residual-surfacing (kernel.ex:805) was NOT needed (the E-only Eq-arrow vehicle avoids it). Independent adversarial verification of 3b: **SOUND** (subagent a98a0035). **Phase 2 SEALED.**

**Gate:** carried-index-eq + sibling-transport tests green + load-bearing; no regressions; Phase-2 layer classification recorded as **E-only** (no escalation, no TCB gate). **Phase 2 COMPLETE & SEALED** — independent adversarial verification returned SOUND (a98a0035).

---

## Phase 2½ (operator-directed detour) — Elaborator Antigen vertical + value-in-goal fix — DONE

Not in the original plan; run between Phases 2 and 3 at the operator's direction ("merge antigen-tier-b, see if it can root out the cause" → "do (b)" → "yes").

- [x] **Merged `autopilot/antigen-tier-b`** (884ab35): dependent-term generator + corpus machinery onto this branch; conflicts resolved as unions; Antigen suite green post-merge.
- [x] **New elaborator completeness + metamorphic Antigen vertical** (8eb8c2c): `lib/antigen/generators/elab_complete.ex` + `lib/antigen/assays/elab.ex` (`elab/completeness`, `elab/metamorphic`), `:elab_program` challenge kind. First vertical to test the ELABORATOR (unsound-REJECT class, invisible to kernel-facing verticals). Blast radius found: 3 catalog shapes rejected (Idris-accepts) — goal mentions scrutinee VALUE.
- [x] **Value-in-goal fix** (8019e67, E-only): plain `match` was missing BOTH Lean scrutinee-refinement mechanisms (re-checked on Lean source): `Cases.lean:219-227` (variable major premise substituted by `ctor fields` in the subgoal → new `refine_scrutinee_in_body`, capture/shadow-guarded surface substitution) and `Elab/Match.lean:137` (`kabstract` of the discriminant TERM → `build_motive` now sentinel-abstracts a computed scrutinee; `branch_expected` replaces shifted scrut occurrences with the ctor). Branch expected type now driven by the kernel `branch_unify` verdict subst (the `n := Z` inverse the removed ad-hoc `branch_index_subst` missed). Blast radius closed: 5/5 catalog shapes ACCEPT; survey promoted to a zero-infection gate. Red-green `value_in_goal_match_test.exs`; elab 122/122; Antigen 167; oracle replay 9; full suite 2352, zero regressions.
- [x] **Deliberate capability graduation:** plain `match g(n)` at goal `SNat(g(n))` now ACCEPTS (agrees with Idris `case`; `with_abstraction_test` differential updated to an acceptance test). **Phase 3 impact:** capability-A *goal* refinement is already subsumed by plain match — Task 3.1's red test and Task 3.2's routing must re-verify their premises still fail before implementing (sibling refinement remains `with`-only, so 3.1's combined-mechanism case should still be red via the sibling half).
- [x] **Independent adversarial verification** of 8019e67 (subagent `af8d3002f52886cb4`): **verdict SOUND (SOUND-WITH-NOTES)**. Lean grounding re-confirmed from source at the top of the pass (`Cases.lean:219-227` FVarSubst `majorFVarId → ctor us params fields`; `Match.lean:137` `kabstract result.matchType discr`). 13 probes + 8 bisect variants against parent `8019e67^`: wrong-ctor control **rejects on both commits**; every probe accept hand-verified well-typed (Idris would accept each); no unsound accept was constructed or is statically reachable. **`replace_term`/`replace_branch_vars` binder-shift gap is CONFIRMED latent but not live** — three independent backstops (kernel recomputes each branch goal from motive-at-ctor `check_case_branches` kernel.ex:702-746; whole term re-checked at declarations.ex:43; every Pi-in-goal shape rejected at `check_motive_wf` `:bad_motive` on the parent too, shielding the collision path). `mix test test/cure/elab/` 122/122; completeness assay 6 passed / 0 infections; probe files deleted, `git status` clean. **Sealed SOUND.** Completeness corners it surfaced are reach-pinned in the governing plan's Task A6 (all pre-existing, none regressions).

---

## Phase 3 — Generalizing match front-end (E) + retire A/B/C

**Goal:** One equation-compiler path composing (1a) dependency-reversion + (1b) occurrence-abstraction, running the per-branch unifier + carried eqs, emitting nested case trees; retire A, then B, then C as each is provably subsumed.

### Task 3.1: The composed generalizing motive ((1a)+(1b) together)

**Files:** Modify `lib/cure/elab/elaborator.ex`. Test: `test/cure/elab/generalizing_match_test.exs`.

- [x] **Step 1: Lean re-check. DONE (this pass, from source).** `Match.lean:879-916` `generalize`: fvars whose types depend on the discriminants (`getFVarsToGeneralize discrExprs`) are generalized by **adding them as NEW DISCRIMINANTS** (`discrs ++ ys.map …`) with a fresh pattern variable appended to EVERY alt (`altView.patterns ++ ysIds`, shadow-aware fresh naming); the match type becomes `∀ ds, ∀ ys, type` with discriminant fvar occurrences replaced by the bound `ds` (`type.replaceFVars discrs' ds'`), validated by `isTypeCorrect` with graceful fallback (no generalization if ill-typed). No `clear` in term mode — originals become shadowed/inaccessible. `elabMatchAltViews` (:919+) runs this in a *discriminant-refinement retry loop* (elaborate alts; on failure, re-generalize). **Composition for Cure:** (1a) reversion = scrutinee-dependent siblings become extra motive/case binders at (1b)-abstracted types; each branch rebinds them at the constructor-refined types — i.e. extend `build_motive`'s existing kabstract (post-Phase-2½ it already abstracts computed scrutinees) with Π-wrapping of dependent siblings, the same convoy shape `elaborate_with_rematch` uses for restated params.
- [x] **Step 2: red test. DONE.** `test/cure/elab/generalizing_match_test.exs` gm01: indexed with-rematch (`with view(n)`, capability C) whose goal `Eq(NV(n), view(n), view(n))` names the scrutinee value (capability A). Failed today with `{:error, :not_definitionally_equal}` — the rematch branch refined only the index, not the scrutinee value. (Re-verified premise per Phase 2½: plain match subsumes A-goal refinement, but the *rematch* path did not.)
- [x] **Step 3: implement the combined motive. DONE.** (1a) is the existing index inversion (`branch_unify` verdict subst + `specialize_branch_context_subst`, which reverts index-dependent siblings); (1b) is the Phase-2½ value-refinement ported from `elaborate_matched_branch` into `elaborate_rematch_branch` — thread `scrut_term`, replace the scrutinee (var → subst key `i+arity`; computed → `replace_term` whole-term) with `branch_constructor_term` in the shifted goal, plus `refine_scrutinee_in_body`. Shared `build_motive` already abstracts the computed scrutinee. E-only; kernel re-checks. (Scope note: sibling types depending on the scrutinee's *value* rather than its *index* remain on capability-B's Eq-transport, not exercised by gm01.)
- [x] **Step 4: green + load-bearing. DONE.** gm01 red→green; gm02 (index-only control, needs 1a) and gm03 (soundness — mismatched ctor rejected) hold; elab suite 135, `mix cure.oracle with` 7/7 `same`, full suite 2384 zero-regress.

### Task 3.2: Subsume + retire capability A (bare value-abstraction only — B shares this function, see caveat) — DONE (2c83330)

Steps 1–5 done: `need_eq == false` routes to `elaborate_match`; bare-value motive
removed; B (`need_eq == true`) untouched; `elaborate_with_value` retained.
with_abstraction 6/6, oracle `with` 7/7 `same`, full suite 2384 zero-regress.

**Caveat (checked against the actual tree):** `elaborate_with_value` (`elaborator.ex:527`) is **not** capability-A-only code — its own comment reads "Capability A/B (no LHS re-match)... This is the original `elaborate_with` body, unchanged," and it branches internally on `need_eq` (false → A's bare motive, true → B's eq-arrow motive). `test/cure/elab/with_abstraction_test.exs` (cited below as "A's suite") contains both: `wi01` is A-only, `wi04`/`wi05`/`wi06` are B's proof/sibling-transport cases. Deleting `elaborate_with_value` wholesale in this task would retire B too, before Task 3.3's mandatory boundary decision (HEq vs non-indexed-permanent) has run. This task is therefore scoped to the `need_eq == false` path only.

- [ ] **Step 1:** route the `need_eq == false` (bare value-abstraction, capability-A) branch of `elaborate_with_value` through the unified front-end; the `need_eq == true` (capability-B, proof/sibling) branch stays on the existing `elaborate_with_value` code path untouched. **Step 2:** `mix test test/cure/elab/with_abstraction_test.exs` (covers both A and B) green under this partial routing — confirm specifically that `wi01` now runs through the unified path and `wi04`/`wi05`/`wi06` still pass via the untouched B branch. **Step 3:** delete only the bare-value-motive special-case code (the `need_eq == false` arm); the `need_eq == true` arm and its supporting code (`eq_arrow_motive`, sibling collection) remain until Task 3.3 decides B's fate. **Step 4:** suite still green (`with_abstraction_test.exs` in full) + `mix cure.oracle with` still `same`. **Step 5:** commit `refactor(elab): subsume+retire capability-A (bare value-abstraction) under the generalizing front-end; capability-B branch untouched pending Task 3.3`. **Note:** `elaborate_with_value` itself is only fully deleted once Task 3.3 completes (whichever scope it settles on for B) — do not delete the function here.

### Task 3.3: Subsume + retire capability B — with the HEq decision — DECISION MADE: case (a), HEq NOT needed

**Step 1 (Lean re-check, from source) DONE.** `Lean/Meta/AppBuilder.lean:74 mkEqHEq a b`:
returns `Eq aType a b` when `isDefEq aType bType`, else `HEq aType a bType b`. In
`Match.lean` `withEqs` a discriminant equality is introduced (via `mkEqHEq`) ONLY
when `discrInfos[i].hName?` is set — i.e. a NAMED discriminant equation (Lean's
`match … h : e with`, our capability-B `with … proof`). So HEq arises exactly for
a *named proof* over a discriminant whose branch pattern has a type NOT defeq to
the scrutinee's — i.e. a named proof over an INDEXED scrutinee with a refined-index
pattern.

**Step 2 (re-derivation) DONE → case (a).** The FRP combinators `≫`/`∗∗`/`loop`/
`switch` are SF *constructors* computing indices (`++` on `SVDesc`, `∧`/`∨` on
`Dec`). Matching an SF scrutinee refines those indices via the case eliminator
(capability C's convoy: `branch_unify` inversion + `specialize_branch_context_subst`
sibling refinement); the computed-index GOALS (`as++cs`, `d₁∧d₂`) are discharged by
Phase-4 `rewrite` + algebraic lemmas, NOT by a proof bound at the match. None of the
combinators needs `with <indexed SF> proof pf`. **⇒ HEq is not needed for this
slice; capability B is scoped to NON-INDEXED scrutinees, permanently.** No TCB change.

**Correction to the deletion premise (found in the actual tree).** The plan assumed
case (a) lets us "route the remaining `need_eq == true` arm through the unified path
and delete `elaborate_with_value` entirely." The code shows the deletion is not
*free*: plain `match` (the unified front-end) has **no named-proof binding** —
wi04's body `lemma(g(n), Z(), pf)` *consumes* `pf`, which only capability-B's
Eq-arrow motive provides. Fully deleting `elaborate_with_value` therefore requires
**merging B's Eq-arrow proof-binding INTO `elaborate_match`** (moving proof/sibling
transport into the unified path), which is a non-trivial refactor whose only
benefit is one fewer entry point — both variants already emit a kernel-checked
`{:case}` over the SAME shared branch machinery (`elaborate_with_branches` /
`elaborate_matched_branch` refinement). Since the case-(a) DECISION (no HEq, no
TCB) does not depend on that merge, it is **deferred as cleanup**: `elaborate_with_value`
(now the B-only path after Task 3.2 routed A away) is **retained** as the permanent,
non-indexed, proof-carrying `match` variant. Phase 3's "one equation-compiler path"
goal is met at the machinery level — A subsumed; B (and C, Task 3.4) are thin
distinct front-ends over the shared refinement. **Step 2b revisit-trigger stands:**
re-run this derivation if Phase 6 surfaces a named-proof-over-indexed-SF need.

_(Original task text preserved below for reference.)_

- [ ] **Step 1: Lean re-check.** Read `Meta/Match/Match.lean:128-143` (`mkEqHEq`): confirm Lean uses `HEq` exactly where a branch's pattern value has a refined-index type. **Step 2: decide the boundary (spec §4 completeness check) — by analytical re-derivation now, not by waiting for Phase 6 to run.** Phase 6 has not executed yet at this point in the sequence, so this cannot literally consult "the Phase-6 SF port" — instead, re-derive the answer analytically from the paper the same way spec §2 already did for `≫`/`∗∗`/`loop`: walk every combinator (`≫`, `∗∗`, `loop`, and, from Task 6.1's later index-algebra note if already drafted, `switch`) and determine whether any of them ever pattern-matches an **indexed** `SF`-scrutinee while ALSO needing a *named* proof-equation (`with … proof`) — i.e., a rematch (capability C) combined with a carried proof over the indexed scrutinee itself. Record the derivation in the task note. (a) If capability C's convoy already covers every indexed case the paper needs (no combinator needs the combination) → scope B's subsumption to **non-indexed scrutinees, permanently**; document it; retire B for that scope. (b) If an indexed named-proof is needed → adding `HEq` to the kernel is a **new TCB item**: STOP and open its own HARD-STOP gate (antibody: `HEq` intro/elim terminates + equates no distinct NFs + collapses to `Eq` on equal types; red test: `test/cure/core/heq_test.exs`; verify: `mix test test/cure/core/heq_test.exs`) before claiming subsumption. **Step 2b (revisit trigger):** this analysis is necessarily made before Phase 6's actual port is written — if Phase 6 (Task 6.1/6.2) later surfaces a named-proof-over-indexed-scrutinee need that this derivation missed, that reopens this Step 2 decision (do not treat it as settled once and for all; re-run this step before Phase 6 proceeds past the point of contradiction). **Step 3:** retire B for the decided scope; suites green (name the concrete suite: `test/cure/elab/with_abstraction_test.exs`'s proof/sibling cases, `wi04`/`wi05`/`wi06`); commit (E-only for case (a); TCB-gated for case (b)). **Deletion outcome (completes Task 3.2's deferred deletion):** for case (a) (non-indexed-permanent), route the remaining `need_eq == true` arm through the unified path for non-indexed scrutinees and delete `elaborate_with_value` in its entirety — both A's and B's special-case code are now gone. For case (b) (HEq), delete `elaborate_with_value`'s non-indexed `need_eq == true` arm (now routed through the unified path) but the new HEq-authorized indexed extension lives in its own reviewed TCB diff, not in `elaborate_with_value` — confirm no special-case A/B code remains in `elaborate_with_value` after this step either way.

### Task 3.4: Subsume + retire capability C — DONE (d36ef9a)

Given the 3.3 finding (C, like B, is a distinct front-end — the with-rematch path
restates the parent LHS, which plain `match` does not), C is not deleted; instead
the DUPLICATED branch-refinement code Task 3.1 introduced is retired: `elaborate_
matched_branch` and `elaborate_rematch_branch` now share `refine_branch_goal/6`
(one refinement, two thin front-ends). with_rematch_match/elab + generalizing_match
green, oracle `with` 7/7 `same`, full suite 2384. **Phase 3 gate: PASSED** — shared
generalizing-motive machinery (`build_motive` + `refine_branch_goal`) behind match /
with-value(A subsumed) / with-rematch; A retired, B/C thin front-ends, no HEq/TCB.

_(Original task text below.)_

- [ ] Route `elaborate_with_rematch` through the unified path; `with_rematch_match_test` + `with_rematch_elab_test` green (under the unified path, before deletion); delete special-case C code; **re-run `with_rematch_match_test` + `with_rematch_elab_test` (still green, post-deletion)** + `mix cure.oracle with` (wi01–wi07) all `same`; commit `refactor(elab): subsume+retire capability-C rematch under the generalizing front-end`.

**Gate:** `generalizing_match_test` green; A/B/C special-case code deleted (or B explicitly scoped non-indexed-permanent); `with_abstraction`/`with_rematch_*`/`dependent_match_surface`/`match` suites green; `mix cure.oracle with` all `same`; full suite 0-regress (once, alone).

---

## Phase 4 — Type-level lemma stock + `rewrite` composition (E/C)

**Goal:** `++`/`∧`/`∨`/`<:` lemmas that let `rewrite` discharge the carried stuck-index equalities; flip `frp01` to `same`.

### Task 4.1: Lemma stock + single-occurrence discharge

**Files:** Create `test/oracle/frp/lib_frp.cure` (or stdlib module) with `++` assoc/right-identity, `∧`/`∨` laws as total functions + refl-bodied bridge lemmas. Modify elaborator only if `rewrite`↔carried-eq composition needs it.

- [ ] **Step 1: Lean re-check.** Read `UnifyEq.lean:60-136`: confirm Lean's equation solving is single-shot discharge-or-fail and multi-step algebraic rewriting is always human-composed — set the expectation that multi-occurrence is NOT automatic.
- [ ] **Step 2:** red test first — write `test/cure/stdlib/frp_lemma_stock_test.exs` asserting each planned lemma (`++` assoc, `++` right-identity, `∧`/`∨` laws) type-checks with its stated total signature; confirm it fails (red — the lemmas don't exist yet). Then write the lemma stock (refl-bodied, total) to make it green.
- [ ] **Step 3:** make `frp01`'s `parAssoc` discharge via the assoc lemma + `rewrite`. Re-run `mix cure.oracle frp`. If `frp01` needs only a single reducible occurrence → it flips to `accept`; update `verdicts.json` relation to `same`, reason cleared.

### Task 4.2: Multi-occurrence reach (only if frp01/∗∗/loop needs it)

- [ ] **Step 1:** if Task 4.1 shows `_∗∗_`/`loop` goals need MORE than one occurrence rewritten (interchange-law shape), STOP — this is the separately reach-pinned multi-occurrence gap, **new work, not an rw07 corollary** (spec §Phase-4 caveat). **Step 2:** scope it: either (a) a multi-occurrence rewrite driver in the elaborator (E; red test: `test/cure/elab/multi_occurrence_rewrite_test.exs` against a multi-occurrence probe derived from the `_∗∗_`/`loop` goal shape; verify: `mix test test/cure/elab/multi_occurrence_rewrite_test.exs`; red-green), or (b) if it needs a kernel conversion change, the TCB gate (red test: `test/cure/core/multi_occurrence_conversion_test.exs`; verify: `mix test test/cure/core/multi_occurrence_conversion_test.exs`; full HARD-STOP gate). **Step 3:** record the decision in the task note; this gates Phase 6. **Step 4:** commit lemma stock + discharge `feat(frp): type-level lemma stock; frp01 ++-assoc discharge`.

**Gate:** `frp01` `same` (accept/accept) OR the multi-occurrence gap explicitly scoped as gating Phase 6; oracle_replay green; full suite 0-regress.

---

## Phase 5 — Signature-aware `Quote.reify` (TCB; gated) — may be pulled forward

**Goal:** Recover the params/indices split from the signature (Agda/Lean-style), closing the residual Eq-endpoint incompleteness. **Pull forward if Phase 2/3 hits the indexed-Eq-endpoint wall** (spec ordering contingency).

### Task 5.1: Signature-aware reify

**Files:** Modify `lib/cure/core/quote.ex` (+ minimal callers). Test: migrate `test/antigen/reach_reify_split.sexp` / `reify_split_gap_reach_test`. New antibody in `lib/antigen/generators/indexed.ex` + corpus.

- [ ] **Step 1: Lean/Agda re-check.** Confirm both recover the split from the signature (Lean `inductive_val.get_nparams/nindices`; Agda `getNumberOfParameters`) — reify should consult the family signature, not reconstruct blindly. Note in task.
- [ ] **Step 2: red.** Drive the value path: `Eq(Type, SNat x, SNat x)` reflexive motive → `:bad_motive` today. Assert it SHOULD accept (the reach test flips to green-forcing).
- [ ] **Step 3: implement** signature-aware split in `reify` (thread the signature; split `{:vdata,name,args}` into params/indices via `Inductive.param_count`/family kind). **Step 4:** TCB gate — new antibody ("signature-aware reify: split faithful, terminates, equates no distinct NFs"); full Antigen; full suite; **independent adversarial-verification subagent**. **Step 5:** commit kernel diff + antibody + migrated reach test as one reviewed unit; present the diff (no auto-merge).

**Gate:** reach test migrated red→green-forcing; TCB gate fully green incl. independent adversarial verification; full suite 0-regress.

---

## Phase 6 — FRP capstone (E + probes)

**Goal:** Port the real `SF` + `≫`/`∗∗`/`loop`/`switch` + `Dec` + `Init` indices; oracle confirms well-formed nets accept, instantaneous cycles + uninitialised escapes reject.

### Task 6.1: Re-derive `Init`/`switch` index algebra (scope-expansion gate)

- [ ] **Step 1:** from the paper (§4.1 `Dec`, §5.1 `Init`, §3.3.2/§4.2.1 `switch`/`rswitch`/`dswitch`), re-derive — the same way spec §2 did for `≫`/`∗∗`/`loop` — `Init`'s index algebra and `switch`'s computed-index/constructor shape, into `docs/superpowers/notes/2026-07-02-frp-index-algebra.md`. **Step 2:** confirm Phases 1–5's mechanisms generalize to the 4-index family with NO new gap; if a new gap appears (e.g. `Init` arity-change needs machinery beyond carried-eq), scope it explicitly as gating work here. Commit the note.

### Task 6.2: FRP acceptance/rejection probes

- [ ] **Step 1:** paired `.cure`/`.idr` for (a) a well-formed net using `≫`/`∗∗`/`loop` with correct decoupledness → accept/accept; (b) an instantaneous (undecoupled) `loop` → reject/reject; (c) an uninitialised-signal escape through a `switch` → reject/reject. Faithful transliterations. **Step 2:** `mix cure.oracle frp`; every entry `same` (or sound written `cure_stricter`). **Step 3:** oracle_replay green; commit `test(oracle): FRP capstone — well-formed nets accept, cycles + uninitialised escapes reject`.

**Gate:** `frp` cluster all `same`; the paper's safety property demonstrated in Cure; full suite green (once, alone) — this is the Stage 5 gate.

---

## Phase→Stage-5 handoff

At Phase 6 completion: full suite ONCE; completion report (per-phase commits, each TCB gate's antibody + independent-verification outcome, the A/B/C-retirement proof, the `frp` cluster table); push notification `autopilot done — review & merge autopilot/lean-shape-matching`; **do NOT auto-merge** — operator reviews all TCB diffs (Phase 1 if any, Phase 2 if escalated, Phase 3.3 if HEq, Phase 5, **Phase 4a** below) and merges.

---

## Execution findings (Stage 4) — amendments discovered during the run

### Phase 0 finding (commit 9785763): the acceptance driver bottoms out in a NORMALIZER WHNF gap (TCB), not lemma plumbing

`frp01` is red for the right reason (`:not_definitionally_equal` on a nested `++`), but the root cause is deeper than Phase 4 assumed: **Cure's conversion/normalisation does not force a `case` scrutinee that is itself a function redex to WHNF.** Evidence (isolation probes): `app(SNil,y) ≡ y` ✅, `app(SNil, app(y,z)) ≡ app(y,z)` ✅, but `app(app(SNil,y),z) ≡ app(y,z)` ❌ (and the Nat analog `plus(plus(Z,y),z) ≡ plus(y,z)` ❌). At the SF-index level this is exactly `{:conversion_failure, SF(app(app(SNil,y),z),…), SF(app(y,z),…)}` — the computed-`++`-index conversion.

**Consequence — new discovered TCB task, inserted as Phase 4a (runs BEFORE Phase 4's lemma stock, likely pulled forward per the spec ordering contingency):**

### Task 4a.1: Nested-redex-scrutinee WHNF in conversion (TCB; gated)

**Files:** `lib/cure/core/normalise.ex` (whnf/`unfold_head` seam — likely an extension of the `d37721f` stuck-eliminator seam so a `case`/eliminator forces its SCRUTINEE to WHNF when the scrutinee is itself a redex) and/or `lib/cure/core/conv.ex`. Test: `test/cure/core/nested_redex_conv_test.exs`. Antibody: `lib/antigen/…` + corpus.

- [x] **Step 1: Lean/Agda re-check.** DONE — the source refined the fix shape: Lean's kernel whnf leaves a stuck recursor's major premise UN-rewritten; the completeness lives in CONVERSION: `type_checker.cpp` `is_def_eq_app` (:815, fallback :1115) compares each argument of a stuck application with full `is_def_eq`; `is_def_eq_args` (:767) same during lazy-delta (:917-930). Agda agrees: `Conversion.hs` `compareAtom` compares blocked terms' elims via `compareElims` (:221). So the fix belongs in `conv.ex`, not `normalise.ex`.
- [x] **Step 2: red.** DONE — `test/cure/core/nested_redex_conv_test.exs`: 3 positive assertions RED (plus/append nested-redex + flipped orientation), 2 negative controls green.
- [x] **Step 3: implement.** DONE — one line in `conv.ex` `conv_neutral?`/`:ncase`: scrutinees lift to values and compare via `conv_val?` (whnf both sides) instead of structural `conv_neutral?`. Exactly Lean's `is_def_eq_app` treatment of the major premise.
- [x] **Step 4: TCB gate.** DONE — antibody banked as 3 `stuck_elim` corpus entries (positive = nested-redex congruence under binders; 2 negative merge-controls). Red-green PROVEN: with the fix stashed the positive entry reports `{:violation, {:unsound_verdict, expected: true, got: false}}`; restored, all `:ok`. Full Antigen 107 passed; full suite 2282/2282 (0 regressions vs 2275 baseline). Independent adversarial verification: **SOUND** (subagent a9962257d888e90ff, fresh context, opened by re-reading Lean `type_checker.cpp` + Agda `Conversion.hs` from source, confirmed the congruence claim, then ran 10 attack probes — lossy-projection whnf, η+δ scrutinee, non-ctor non-neutral scrutinee, one-sided-ctor conflation, weakened motive/branch coupling, forged-cert non-termination, nil-sig asymmetry — all matched sound predictions). Load-bearing invariant it derived: `conv_struct?` is only reached on values already whnf'd, and `unfold_certified_head` whnfs a case's scrutinee before declaring it stuck, so the new `conv_val?` on scrutinees re-runs an already-terminating whnf and recurses on strictly-smaller neutrals — no new divergence class, fuel-accounted via the same process-dict counter. Two PRE-EXISTING (not introduced by 09a80f3) exposures flagged out-of-scope: (1) `unfold_certified_head` evals a certified body in the EMPTY env, so a malformed signature with an *open* certified body could alias context vars at low de Bruijn levels — rests on `check_def` rejecting open bodies; (2) `Env.certify/2` is an unchecked trust marker — a forged cert for a non-total global makes no-fuel `conv?` diverge (never mis-answer). Both predate the commit; noted for a future independent audit. Hard-stop note, honest version: an E-only dodge exists for `appAssoc`'s BASE CASE alone (rewrite by a refl-bodied `app(SNil,ys)=ys` bridge — that conv works pre-fix), but not for the kernel-internal index-conversion judgements during case/branch checking that Phase 2/3 route through, and the congruence-completeness gap would otherwise force propositional patches at every nested-redex site — the fragmentation this run was authorized to remove.
- [x] **Step 5:** DONE — `frp01_par_assoc` flips reject→accept with 4a alone: the probe's inductive `appAssoc` (refl base case + rewrite step case) AND `parAssoc`'s two SF-index rewrites all check. Oracle regenerated: frp cluster now accept/accept `same` on both entries. Committed as one reviewed unit: **09a80f3** (kernel diff + red-green test + antibody + verdicts).

**Gate:** ✅ nested-redex conv test green; ✅ `appAssoc` provable; ✅ antibody red-green + full Antigen + full suite 2282/2282; ✅ independent adversarial verification **SOUND** (a9962257d888e90ff); no auto-merge — operator reviews 09a80f3.

**Impact on Phase 4 (reassessed post-4a):** `frp01` flipped with 4a alone — the acceptance driver no longer needs a lemma stock for the single-occurrence case. Phase 4 shrinks to: (a) the multi-occurrence discharge case (Task 4.2) and (b) whatever `Dec`-lattice lemmas Phase 6's capstone actually demands; treat Phase 4 as demand-driven from Phase 6 rather than a standing stock.

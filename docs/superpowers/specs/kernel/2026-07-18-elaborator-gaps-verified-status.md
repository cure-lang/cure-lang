# Elaborator gaps — verified status (2026-07-18)

**Status:** investigation complete. Six independent Sonnet agents, each in isolation,
re-verified the six OPEN items from the handoff
(`2026-07-18-open-elaborator-gaps-handoff.md`) — E9, E6-residual, E8, E2-residual, E10,
E11-Stage-2 — **empirically** against the live elaborator on branch `elaborator-gaps`
(HEAD `235d20d1`), with a differential Idris2 cross-check where the "Idris accepts" claim
was load-bearing. This spec records what is actually true as of this commit, separates the
**kernel-layer** bugs (Antigen targets) from the **elaborator/parser** gaps, and captures
the findings that overturn the catalog's own framing.

Method per gap: build a faithful `.cure` repro, get Cure's real verdict via
`Cure.Elab.Program.elaborate/1`, root-cause in the **dependent** pipeline
(`lib/cure/elab/*` + `lib/cure/core/*`) only — the `lib/cure/compiler/*` and
`lib/cure/types/*` same-named symbols are decoys and were explicitly excluded — and, where
relevant, run `idris2 --check` on the byte-equivalent program. No `lib/**` was modified.

## 1. Summary

| Gap | Verdict | Layer | Fix shape | Reach gap? |
|---|---|---|---|---|
| **E9** — stuck-index eqn on GADT match | OPEN; **premise falsified** | K (+E) | headline: architectural & beyond-Idris; sub-bug: trivial kernel fix | **NO** for the headline (Idris rejects too) |
| **E6-residual** — shared metacontext | OPEN | E | **architectural** (thread one metacontext; ~6 entry points) | YES |
| **E8** — sequential-match refinement | **✅ LANDED** | E | bounded — narrowed `invertible_index?` to head-only (ctor-headed index inverts structurally) | YES |
| **E2-residual** — name relevant ctor index | OPEN; **design-gated, not bounded** | E | new surface grade syntax + quantity policy | YES |
| **E10** — HO-fn arg not reduced in index | OPEN; **root cause overturned** | (a) P + K, (b)/(c) K | (a)-parser trivial; kernel part HARD-STOP | YES (all three, Idris-verified) |
| **E11-Stage-2** — type-directed overload | **✅ LANDED** | E | bounded — routed index-position overloads through term-position resolver | partial |

**Net:** none were already fixed; none is trivial-and-done. Two carry a **kernel** bug
(E9 sub-bug, E10 (b)/(c)); two were **mis-framed** by the catalog (E9 premise, E10 root
cause); two are **more bounded than feared** (E8, E11-Stage-2); two are **bigger than the
handoff's ordering implied** (E2-residual, E6-residual). Four **new** items surfaced that the
catalog did not list: E11 elaborator crash, E10a parser misparse, and (from the OTP-metatheory
branch) E12 rewrite-δ-blind-occurrence-finder and E1-sub scrutinee-var-not-substituted-in-bodies —
both zero-TCB E-layer ergonomics gaps in the scrutinee/rewrite-refinement family (see §3; naming
matches the handoff spec).

> **Update 2026-07-18 (post-investigation):** re-verifying the E1 family against the live tree found
> **E1 (the headline) and E1-sub are ALREADY CLOSED** — the intervening
> `specialize_branch_context_subst` work refines both `ctx.types` and `ctx.env`, so sibling
> refinement reaches the coverage checker (E1) and written body terms (E1-sub). Both are now locked
> by oracle probes (`e1sib`, `e1sub`, `rel=same`) and a two-direction antibody. See §3. The handoff
> spec's OPEN listing for E1/E1-sub is stale.

## 2. Kernel-layer bugs — the Antigen targets

These are the items the Antigen expansion must trip on **before** any kernel change. Both are
**completeness** gaps (Cure is conservative — it rejects/undecides a term Idris accepts), not
soundness gaps; the trusted kernel never accepts anything ill-typed. So the antibodies are
**must-eventually-decide / must-certify** reach pins, not "never-equate-distinct-NF" pins.

### K-bug 1 — order-dependent constructor-injectivity in `unify_one`/`bind_index`
- **File:** `lib/cure/core/kernel.ex`, `unify_one/4` (~1330–1428), `bind_index/4` (~1465–1503).
- **Symptom (differential, order-flip):** `Equivalent(Nat, S(a), S(Z()))` (var first) →
  `:conversion_failure`; `Equivalent(Nat, S(Z()), S(a))` (ground first) → **ACCEPT**. The
  decidable equation is silently dropped in one argument order only.
- **Cause:** the top-level r/s var-side asymmetry ("r-side vars `< arity`, s-side vars
  `>= arity`") is violated in the resolve-before-bind re-unify path (`bind_index` ~1498 calls
  `unify_one(old, rterm, ...)` on arbitrary previously-bound terms). There is a clause for an
  outer var on the **right** (`unify_one(r, {:var,j}, ...) when j >= arity`, ~1336) but **none
  for it on the left**, so that pair falls through to `:undecided` and is dropped.
- **Antibody shape:** a symmetric-decidability pin — for a ground/var constructor-injectivity
  pair, both argument orders must reach the same verdict. Currently red for the var-first order.
- **Fix (HARD-STOP, TCB-approved):** add the missing symmetric `unify_one` clause (or
  canonicalize argument order before the re-unify). Aligned with Idris/Agda/Lean (symmetric
  constructor injectivity is standard).
- **Caveat:** this does **not** unblock the E9 headline (`msadd(m1,m2)` stays correctly
  `:undecided` — it is a non-injective stuck app, not a var/ctor pair).

### K-bug 2 — size-change checker rejects guarded-lambda recursion (`certificate.ex`)
- **File:** `lib/cure/core/certificate.ex`, `size_change_total?/2`, `walk_node/4` for
  `{:lam,...}` (~197–198), `arg_relation/2` (~320–334).
- **Symptom:** a continuation-style `bind` whose recursive self-call sits **inside an
  unapplied lambda** (`Bind(e,g) -> Bind(e, fn(y) -> bind(g(y), f))`) fails certification, so
  `Cure.Core.Conv` (δ-unfolding gated on `Env.certified?`, `conv.ex:10–15`) treats `bind` as
  **opaque and never δ-unfolds it**. Every `bind(...)` in a type/index position is therefore
  stuck (`:conversion_failure`), independent of the continuation's shape.
- **Cause:** `walk_node` descends into the unapplied-lambda body and evaluates the call
  argument `g(y)` (an application of a bound field, not a bare var/ctor), so `arg_relation`
  returns `:unknown`, no diagonal `:smaller`, certification fails. A genuine incompleteness of
  the Lee–Jones–Ben-Amram port vs Idris's real `Core/Termination/SizeChange.idr`.
- **Differential:** byte-equivalent `bind` + all three `Refl` goals **type-check in Idris2**
  under `%default total` (harness sanity-checked against a real non-terminating loop, which
  Idris rejects). So this is a true reach gap.
- **Antibody shape:** a must-certify pin — a guarded/deferred self-call under an unapplied
  lambda that is genuinely size-change-terminating must certify (and thus δ-unfold in
  conversion). Currently red.
- **Fix (HARD-STOP, TCB-approved):** extend the size-change criterion to recognize
  guarded/deferred self-calls under an unapplied lambda as not owing the decrease at that
  syntactic point (mirror Idris's checker). **No elaborator-only route exists** — the blocker
  is that `bind` never certifies at all.

## 3. Elaborator / parser gaps (fix after the kernel bugs are green)

### E11-Stage-2 — type-directed overload in type/index position — **✅ LANDED** (E, `fix(elab): resolve type-directed overloads in index position`)
- **Was:** Ph1 overload shipped for **term position only**
  (`elaborator.ex:elaborate_named_call_resolved`, ~335–344). The type/index-lowering path
  (`declarations.ex:lower_applied_type`, `lower_applied_type_head/7`, `applied_def_key/3`) ran the
  pre-Ph1 Stage-1 logic and was never wired to `Overload.resolve/5` /
  `Resolution.overload_candidates/2`. Bare `plus(...)` in an `Equivalent` index →
  `{:ambiguous_name, :plus, [...]}`; qualified spelling accepted; term-position overload worked.
- **Fix landed:** factored the term-position overload branch into a public
  `Elaborator.elaborate_overloaded_app/7` (`map_present_args` → `Overload.resolve/5` →
  `elaborate_global_app`), and added a first `cond` branch to `lower_applied_type`
  (`declarations.ex` ~2204): when a bare, unshadowed, unqualified applied name has
  `overload_candidates ≥ 2`, route it through `elaborate_overloaded_app/7` — the SAME machinery
  term position uses. A name with a single local/direct winner collapses to <2 candidates and is
  untouched. No new `idx_to_core`/`map_idx_to_core` plumbing was needed: the term elaborator
  infers each argument's type itself.
- **Verified:** oracle `tdoidx/tdoidx01_overload_in_index` rel=same (cure=accept, idris=accept);
  antibody `test/antigen/overload_in_index_resolution_antibody_test.exs` (REACH + false-equation
  CONTROL A + genuine-ambiguity CONTROL B, 3 green). Real-code demonstration: `Otp.Meta.EffAlgebra`
  gains a `render` measure OVERLOADED across its two carriers (`Eff` monoid / `HEff` free monad),
  proved in an `Equivalent` index (`render_eff_nil`, `render_heff_pure`) — a program that
  previously crashed the kernel and now type-checks. (No pre-existing shipping workaround existed
  to remove: the same-module pattern crashed, so no such code was ever written — confirmed by a
  corpus grep for qualified names inside `Equivalent` indices.)

### E11 elaborator crash on same-module-overload vs ambient provider — **✅ FIXED** (folded into E11-Stage-2)
- **Was:** when a bare name had a **same-module overload set** (discriminated keys, no bare local
  key) **and** an ambient/prelude same-name provider (e.g. `Std.Nat#plus`), the index path's
  `applied_def_key`/`resolve_bare` silently dropped the local overloads and returned the ambient
  candidate as if unambiguous. The mis-resolved global was applied to the wrong ctor args and the
  elaborator **crashed with an uncaught `RuntimeError`** (`ι: no branch for constructor …`) out of
  `Cure.Elab.Program.elaborate/1` instead of a clean `{:error,_}`.
- **Fixed by the same change:** the new overload branch now fires *before* `applied_def_key`, so a
  same-module overload set is resolved by argument type (type-distinguishable → the intended
  member; genuinely ambiguous → a clean `{:ambiguous_overload, …}` error, verified by antibody
  CONTROL B). The kernel-crash path is unreachable — it now fails closed.

### E8 — sequential-match refinement across scrutinees — **✅ LANDED**
- Root cause (final): the carried-index-equality mechanism was **misfiring on a
  constructor-headed scrutinee index that merely carried a computed subterm**. The trigger was
  `invertible_index?` (`elaborator.ex:3694`): it recursed into a constructor's arguments, so
  `Node(p, twist(q))` / `PTimes(a, deriv(b, t))` were classified **non-invertible** just because
  a subterm (`twist(q)`, `deriv(b,t)`) is a function application. That routed the branch through
  `elaborate_carried_eq_branch`, whose `cod_expected` (`elaborator.ex:5606–5609`) refines only the
  single carried index position and **drops the branch-unify `subst`** that the plain
  `refine_branch_goal` path threads — so an invertible sibling measure (`n ↦ add(n1, n2)`) never
  reached the goal and a `rewrite` over the refined measure failed `:rewrite_no_match`.
- **Fix (bounded, one line):** narrow `invertible_index?` to test the **head only** —
  `invertible_index?({:ctor, _name, _args}), do: true`. A constructor-headed index is invertible
  by ordinary structural unification (it descends through the ctor head and binds the computed
  subterm to the ctor's argument binder); only a **non-constructor head** (a defined function like
  `app(p, q)` — the FRP-carrier case the mechanism was built for) keeps the carried-eq detour.
- **Verification:** oracle cluster `e8seq` (`test/oracle/e8seq/e8seq01_carried_index_refine.{cure,idr}`)
  `rel=same` (both accept); antibody `test/antigen/carried_index_invertibility_antibody_test.exs`
  (REACH RED→GREEN, CONTROL A false-measure still rejected, CONTROL B function-app-headed carried-eq
  still fires and fails closed on a wrong-family sibling). Real workaround removed:
  `https://github.com/cure-lang/cure-otp/tree/main/metatheory/src/otp_mailbox_pattern.cure`'s `deriv_sound` no longer delegates its `PTimes`/`PStar` arms
  through `ds_times`/`ds_star` helpers — they are inlined and elaborate directly. Full elab +
  oracle-replay + carried-index regression suites green (1274 tests).

### E6-residual — shared metacontext through the app tree — **OPEN, architectural**
- Repro reproduced (`{:unsolved_metavariables, AStar0}`; typed-helper workaround elaborates).
  Root cause confirmed: `finish_ctor_app/6` (`elaborator.ex` ~7315) finalizes eagerly, and it is
  **systemic** — 6+ entry points each mint a fresh `MetaCtx.new()`
  (`elaborator.ex:7216/7378/7899/8069/8126`, `proof_search.ex:236`), so no solution crosses
  nesting levels. The E6 **core** (direct sibling) is already fixed (`check_ctor_args`
  postponement, `fb4c240e`); this is the enclosing-application residual.
- **Fix:** ARCHITECTURAL — one `MetaCtx` created per top-level elaboration and threaded through
  the recursive descent, with per-ctor finalization postponed to the top-level solve. Multi-day
  refactor across most of `elaborator.ex`'s ctor/app paths. Typed-helper workaround stands.
- **Out of scope (do not "fix"):** the floating-OUTPUT-index `PStep` variant — rejected by
  Idris too; reformulate the index family instead.

### E2-residual — name a relevant ctor index existential — **OPEN, design-gated**
- The naming/binding machinery already works (a bound-but-unused named implicit elaborates).
  The wall is downstream: `declarations.ex:1556–1562` hardcodes ctor-index quantity purely by
  **surface position** (auto-implicit ⇒ erased/quantity-0), and `erase.ex` genuinely drops those
  fields from the runtime tuple — so the `{:erased_used_relevantly}` rejection is a **sound
  erasure gate**, not a patchable false-positive. Commit `4cf73e9d` (2026-07-18) *hardened* this
  same wall, confirming it is treated as correct behavior.
- **Fix:** needs a **design decision + new surface syntax** for per-slot grades on constructor
  fields (the deferred QTT-grades item), a quantity-policy change in `declarations.ex`, and a
  third pattern-slot category (implicit-at-application / relevant-at-runtime) in
  `constructor_pattern`/`branch_scope`/`split_named_implicits`. Not a bounded edit.
- Explicit-field + congruence-helper workaround still required (live in
  `https://github.com/cure-lang/cure-otp/tree/main/metatheory/src/otp_conversation.cure`).

### E1 (headline) — sibling/context refinement on evidence match — **✅ ALREADY CLOSED** (E, no change needed; locked by oracle `e1sib` + antibody)
> Naming: the handoff spec tracks the parent gap as **E1** ("refinement does not reach sibling
> context binders on match"), its written-body sub-case as **E1-sub**, and the rewrite-δ-blind gap
> below as **E12**. Aligned here to match.
- **Re-verified empirically 2026-07-18** on branch `elaborator-gaps`: a dependent `match` on the
  **evidence** refines the SIBLING binder in the local context, not just the motive. In the repro,
  matching `SendsIn` evidence `SendSendK` forces the sibling behaviour `b` to `BSend(y, k)`, so a
  nested `match b` covering **only** the `BSend` arm is exhaustive — the coverage/impossibility
  checker sees the refined `b` and prunes the `BNil`/`BRecv` arms. Elaborates `:OK`.
- **Root of the close:** `specialize_branch_context_subst` (`elaborator.ex`) rewrites BOTH
  `ctx.types` and `ctx.env` by the branch-unify substitution, so the refined binder reaches the
  coverage checker. This landed as part of the intervening sibling/scrutinee-refinement work; the
  handoff spec's "OPEN" listing is **stale**.
- **Soundness locked:** the same program with a WRONG nested arm (`BRecv` under the `b = BSend`
  refinement) is **rejected** (`:index_mismatch`) — the refinement is genuine, not a blanket accept.
- **Regression guard:** oracle probe `test/oracle/e1sib/` (`rel=same`, both accept) + antibody
  `test/antigen/sibling_context_refinement_antibody_test.exs` (REACH accept + CONTROL reject).

### E1-sub — scrutinee-var substituted into branch-body written terms — **✅ ALREADY CLOSED** (E, no change needed; locked by oracle `e1sub` + antibody)
- Reported OPEN from the OTP-metatheory branch: a `match` on a **bare variable / evidence** was said
  to refine the goal/motive but **not** the branch body's **written term occurrences** — a
  hand-written `project(k, r)` would dereference the un-refined binder and the kernel would reject
  `project(k, nvar)` vs `project(k, RA)` with `:conversion_failure`.
- **Re-verified empirically 2026-07-18:** this is **no longer true in this tree**. The same
  `specialize_branch_context_subst` that closes E1 rewrites `ctx.env` by the branch-unify subst, so
  the written occurrence of `r` in `reflexive(project(k, r))` evaluates through the refinement
  `r := RA` and is convertible with the goal RHS `project(k, RA)`. Elaborates `:OK`; the old
  concrete-literal workaround (`project(k, RA())`) is unnecessary.
- **Soundness locked:** the same program with goal RHS `project(k, RB)` — where the refinement
  reaches the written `r`, making `RA` vs `RB` distinct — is **rejected** (`:conversion_failure`).
- **Regression guard:** oracle probe `test/oracle/e1sub/` (`rel=same`; the faithful Idris mirror
  keeps `r` implicit — Idris rejects a bare explicit pattern var in a forced position — cf. e8seq) +
  antibody `test/antigen/sibling_context_refinement_antibody_test.exs` (REACH accept + CONTROL reject).

### NEW — E12 `rewrite` occurrence-finder is δ-blind (target hidden under an unreduced definition) — **OPEN, E-layer**
- Reported from the same lemma. `rewrite n1 in …` sugar calls `abstract_term` to find LHS
  occurrences (`role_eq(fr, r)`) in the goal and abstract them into a motive, then applies the
  `Equivalent` eliminator. The occurrence-finder walks the goal **without δ-unfolding defined
  functions**, so when the LHS is buried — `role_eq(fr,r)` only appears *after* `project` takes a
  δ-step and the inner `case` ι-reduces — it finds nothing and reports `:rewrite_no_match`.
- **Asymmetry (the interesting part):** the **kernel's** conversion *does* see through `project`
  (δ/ι), which is exactly why the concrete-cased reflexive version type-checks — once roles are
  concrete, `project` reduces and both sides are definitionally equal. So the redex is reachable
  by conversion but **not** by the elaborator's syntactic occurrence-matcher. Genuine E-layer
  limitation (rewrite target hidden under an unreduced definition), **not** a kernel gap.
- **Workaround (live):** case the scrutinees concretely so `role_eq`/`project` reduce and you lean
  on the kernel's conversion instead of the elaborator's syntactic matching.
- **Fix shape:** E-layer — let `abstract_term`'s occurrence-finder WHNF/δ-reduce (or reduce-on-miss)
  while searching, matching Idris (its evaluator WHNF-reduces `project` to the exposed `case`). No
  TCB change — kernel conversion already sees through `project`.
- **Distinct from E8** (same `:rewrite_no_match` tag, different mechanism): E8's redex is
  PRESENT-but-unrefined (an outer match failed to refine `m`); E12's redex is ABSENT-until-unfolded
  (buried under a defined-function application). Do not conflate them.

### E9 headline — stuck-index equation — **OPEN, but NOT a reach gap**
- The catalog's headline "Idris accepts via `with`-style abstraction" is **empirically false**
  for this repro. Three genuine Idris idioms (clause split, `case`, real `with … proof p`) all
  **reject** with `Can't solve constraint between msadd ?m1 ?m2 and MkMS 0 0 0`. Idris needs the
  same index-generalization helper Cure already has; the committed oracle pair is `rel=same`.
- The stuck `msadd(m1,m2)` index is a non-injective `{:app}` — `unify_one` correctly returns
  `:undecided` (kernel, correctly conservative; not a bug). Closing the stated "definition of
  done" would require **inventing** auto-synthesis of an `Equivalent(I, ctorIdx, scrutIdx)`
  hypothesis on stuck index pairs — machinery **beyond Idris parity**, architectural, lower
  payoff than advertised. The index-generalization workaround stays (used by both sides of the
  oracle). The only actionable kernel item from E9 is **K-bug 1** above.

### NEW — E10a parser misparse — **✅ LANDED** (P + E, `fix(elab): lower a lambda in a dependent index position`)
- `parse_type_arrow` mis-parsed a `fn(y) -> …` lambda literal in **type/index** position as a
  parenthesized arrow-type, emitting a bogus `Function(y,…)` node → `:unknown_global`. Term
  position parsed the lambda fine.
- **Two-part fix.** (P) `parse_type_arrow` now recognises the `fn` keyword token and routes it to
  the same `parse_fn_or_lambda` expression entry, producing a real `{:lambda, …}`. (E) `idx_to_core`
  had no lambda clause — a bare binder has no domain until CHECKED against the callee's Π-domain, so
  `lower_applied_type` delegates an applied term-level **def** carrying a lambda argument to
  `elaborate_implicit_app_bidirectional` (reusing the implicit-global path; guarded on a real def +
  threaded ctx). A lambda directly indexing a **family/ctor** (needs index-telescope checking) is a
  separate, deferred case; a lambda index in a non-return-type position (no ctx) is the documented
  §7.5-class residual.
- **Verified.** Oracle `hoidx/hoidx01_lambda_in_index` cure=accept idris=accept **rel=same**;
  negative antibody `lambda_in_index_lowering` (REACH + false-equation + ill-typed-body controls);
  `:lambda` added to the MetaAST conformance vocabulary. Workaround removed from `Otp.Meta.EffAlgebra`
  (value-returning free monad `HEff`/`hbind` + left-identity law now live beside the monoid).
  Combines with K-bug 2 (guarded-lambda `hbind` totality). Full suite green (4851).

## 4. Execution order (this thread)

1. **This spec** (done).
2. **Antigen red** — antibodies for K-bug 1 and K-bug 2; verify each is red at HEAD.
3. **Kernel fixes (HARD-STOP, TCB-approved)** — green K-bug 1 then K-bug 2; each with red-green +
   new antibody + full Antigen + full suite as its own reviewed step. Note K-bug 1 does not close
   the E9 headline; K-bug 2 is the sole unblock for E10 (b)/(c).
4. **Elaborator/parser gaps**, tractability order: E11-Stage-2 + E11 crash (bounded) → E10a parser
   (trivial) → E8 carried-eq (bounded-for-repro) → E6-residual (architectural) → E2-residual
   (design-gated). Each: paired `.cure`/`.idr` oracle probe red-green, plus a negative antibody
   proving the widening admits nothing unsound. Remove the workaround it replaces from ≥1 real
   module and confirm `rel=same`.

Discipline throughout: ghost-writer commits, explicit pathspec, one build at the gate,
`cure_stricter` reproduced before fixing, tests immutable once green.

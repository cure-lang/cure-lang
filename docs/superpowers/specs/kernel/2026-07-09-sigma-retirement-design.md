# Primitive-Sigma Retirement (Sigma D2) — Design

**Status:** approved design (operator standing batch authorization, 2026-07-08 "get the Sigma work queued behind C"; TCB changes pre-approved under the Agda/Lean-alignment blanket — all three reference kernels keep Σ/DPair in the LIBRARY, not the kernel — with the FULL verification gate mandatory).
**Layer:** K (clause STRIP under `lib/cure/core/` — removal only, no new kernel judgements) + E (surface re-point) + C (emit/erase builtin hooks) + A (Antigen migration) + stdlib/prelude.
**Batch:** task #13 part D2, worktree `kernel-parity-batch`, branch `autopilot/kernel-parity-batch`. Depends on D1 (LANDED: `2019648`/`644ec78`/`0171461` — dependent second projection through a user-defined GADT Sigma elaborates and runs).
**Inventory source:** fresh in-worktree scout, 2026-07-09, at HEAD `0171461` (the earlier scout inventory was parent-checkout-contaminated and is superseded). Line anchors below are from that sweep; re-verify any anchor before editing (earlier tasks in this spec shift lines).

## §0 What is being retired, and why

The kernel today carries a PRIMITIVE dependent pair: Core nodes `{:sigma, dom, cod}`, `{:pair, a, b}`, `{:fst, p}`, `{:snd, p}`; value forms `{:vsigma, dom, closure}`, `{:vpair, a, b}`; neutrals `{:nfst, n}`, `{:nsnd, n}` — ~115 match/construct sites across 13 files under `lib/cure/core/` alone. Agda, Lean, and Idris all define Σ/DPair as an ordinary library inductive; Cure having it in the TCB is unjustified kernel surface (the same argument that retired `bool_elim` and primitive `eq`/`refl`/`rewrite`).

D1 proved the replacement is fully expressible: `type MySigma(a: Type, b: (a) -> Type) indices ()` with `mk_pair : (x: a) -> b(x) -> MySigma(a, b)` declares, eliminates (`first`/`second` by match, including the dependent motive `b(first(p))`), and runs on BEAM (oracle `sg01` accept/accept/same).

D2 = replace the primitive with a canonical stdlib inductive registered `@builtin(:sigma)` (Bool/Nat/Eq registry precedent), re-point all surface sugar (`%[x, y]` pairs, `.1`/`.2` projections, `Sigma(x: T, U)` type syntax) at the inductive, keep the BEAM bare-2-tuple representation via emit builtin hooks, migrate Antigen, and strip the kernel clauses behind a `no_sigma_node` validator ratchet.

## §1 Locked design decisions

1. **Universe haircut accepted.** Primitive `{:sigma, a, b}` sorts at `max(l1, l2)` for any level (kernel.ex:100-107); the inductive `Sigma(a: Type, b: (a) -> Type) : Type` is level-0. Cure has no universe polymorphism, so level-0 is the faithful-within-means encoding — the identical haircut Eq/`Equivalent` took. Survey confirms nothing needs more: Antigen `type_former.ex:50` seeds only level-0 sigmas; no surface test uses Σ over `Type`. Any Antigen seed that would exercise a higher level is pruned, not preserved.
2. **The grade-wave 4-tuple sigma forms die with the node.** `validator.ex:110-111` (`children({:sigma, _grade, a, b})`) and `meta_check.ex:52` (`canonical_head?({:sigma,_,_,_})`) anticipated a graded sigma; there is no graded sigma once the node is gone. Both 4-tuple clauses are removed in the strip. The `no_sigma_node` predicate fires on 3-tuple `{:sigma,_,_}` (and pair/fst/snd); it does not need a 4-tuple clause.
3. **The D1 napp sort clause SURVIVES; the D1 defensive pair-infer clause dies with the node.** `infer_type_value_sort(ctx, {:vneutral, {:napp,…}})` (kernel.ex:636) is what sorts the inductive Sigma's dependent-projection motives — it is load-bearing for D2's own probes and is NOT part of the strip. `infer(_ctx, {:pair,_,_}) -> {:error, :pair_not_inferable}` (kernel.ex:125-128) guards a node that no longer exists after the strip and is deleted with it (its Antigen §2.4 pin is retired in the same commit — the pinned adversarial term is no longer expressible in the grammar, which is a STRONGER guarantee than a clean rejection).
4. **Registry-lookup consumption, not hard-coded atoms.** The Eq inductive is consumed via hard-coded `:Equivalent` family atoms in the elaborator (elaborator.ex:1042/1031/270/1093) — a known wart. Sigma consumers use `Inductive.builtin(sig_or_env, :sigma)` lookups (the Bool/Nat pattern: kernel.ex:1112, emit.ex:399/405) so local redeclaration and the registry stay coherent.
5. **BEAM ABI is preserved exactly: bare 2-tuples.** Today `{:pair, a, b}` emits `{A, B}` and `{:fst,p}`/`{:snd,p}` emit `element(1|2, P)` (emit.ex:194-199, 304-306). Generic ctor lowering produces TAGGED tuples (`{:mk_pair, A, B}`, emit.ex:158-175) — so emit gains `:sigma` builtin hooks: ctor → bare 2-tuple, case branch on `mk_pair(x, y)` → 2-tuple pattern (template: `nat_branch_clause`, emit.ex:329-341), projection stdlib globals inline to `element/2`. `lib/std/pair.cure`'s `@extern(:erlang, :element, 2)` interop and AtomVM stay byte-compatible.
6. **Programmatic seed + stdlib decl, both.** `%[..]`/`.1`/`.2` must work in every module without `use`, so the Sigma family is seeded in `Cure.Core.Builtins.seed/2` (like bool/nat/eq): schema `sigma: [{:mk_pair, 2}]` (`validate!` checks ctor names+arities only — the function-typed param needs no schema extension), family `Inductive.family(:Sigma, [a: {:type,0}, b: {:pi, {:var,0}, {:type,0}}], [], 0)`, ctor `mk_pair` with 2 present fields. A new `lib/std/sigma.cure` carries the `@builtin(:sigma)` surface declaration plus `first`/`second` defined by match, pinned byte-equal to the seed by a conformance drift test (precedent: `test/antigen/builtin_bool_drift_test.exs`; registration path `program.ex maybe_register_builtin` :724-759, prelude gating :224-225).
7. **Surface behavior is invariant.** Every `Sigma(…)`/`%[..]`/`.1`/`.2` program that elaborates today elaborates after; every oracle verdict (dpair, sg, match mt13-mt19, erasure er02) is unchanged; runtime values are unchanged. Core-SHAPE test assertions flip (pair → ctor, sigma → data, fst/snd → case); surface-behavior assertions do not.
8. **Ordering defends the gate:** producers re-pointed BEFORE the kernel strip, with the validator's `no_sigma_node` at `:warn` in between and `:reject` only at the end — at no point does a green build depend on smuggling primitive nodes past a half-stripped kernel. (Order: §5 T1→T2→T3→T4-warn→T6→T7→T5-strip→T4-reject.)
9. **`indices ()`-drop parser nicety is OUT of D2.** It is orthogonal grammar work (parser.ex:2972-3021 requires the `indices` keyword to enter GADT ctor-block parsing); bundling it risks a grammar bug blocking the retirement. Queued as an ergonomic follow-up.

## §2 The replacement, per area

### §2.1 Stdlib inductive + registry (T1)

- `Cure.Core.Builtins` `@schemas` gains `sigma: [{:mk_pair, 2}]` (builtins.ex:14-18); `seed/2` (builtins.ex:56-62, eq template at :112-119) declares the family + ctor and `Inductive.register_builtin(env, :sigma, :Sigma)`.
- `lib/std/sigma.cure`: `@builtin(:sigma) type Sigma(a: Type, b: (a) -> Type) indices ()` with `mk_pair : (x: a) -> b(x) -> Sigma(a, b)`, plus `fn first({a: Type}, {b: (a) -> Type}, p: Sigma(a, b)) -> a = match p …` and `second : … -> b(first(p))` (the D1 shapes verbatim). Registered in `Cure.Stdlib.Preload.module_groups()`.
- Drift pin: seed and stdlib decl proven equal (bool-drift-test pattern).

### §2.2 Elaborator re-point (T2 — the crux)

Producers, each re-pointed to `{:ctor, :mk_pair, [a, b]}` / `{:data, :Sigma, [a, b], []}` / projection-by-match:

- **Checking-mode `%[a, b]`** (elaborator.ex:918-935): currently matches the NORMALIZED TERM `{:sigma, dom, cod}` and instantiates the codomain binder via `Subst.instantiate(cod, [a_term])`. Replacement matches normalized `{:data, :Sigma, [dom, b_fn], []}` (registry-resolved family atom) and computes the second component's expected type by APPLYING `b_fn` to `a_term` — `b_fn` is an arbitrary term (lambda, global, or neutral), so this is `{:app, b_fn, a_term}` handed to the kernel/normalizer, NOT a binder-body substitution. The branch-body path (elaborator.ex:3557) delegates straight into this same `elaborate_expr_checked` clause, so it gets the b_fn-application change for free — no separate edit there.
  `declarations.ex:344-361` (`elaborate_body` tuple fallback) is a DIFFERENT site and needs a DIFFERENT edit, not "the same change": its primary path (line 351) already calls `Elaborator.elaborate_expr_checked`, so it inherits the b_fn-application change above automatically. But its FALLBACK (lines 355-360, reached only when the checked call errors — e.g. the declared return type isn't a Σ the checker can use) independently infers both components with `elaborate_expr_typed` and builds a raw pair with no codomain in hand at all. That fallback only needs its pair construction re-pointed to `{:ctor, :mk_pair, [a_term, b_term]}` (the same bare-ctor move as the scope-based path below) — there is no `b_fn` available there to apply.
- **Scope-based `%[..]`** (elaborator.ex:4715-4724): emits `{:ctor, :mk_pair, [a, b]}`; ctor-app inference then handles the implicits like any GADT ctor. If the two implicits are underdetermined in pure argument position, that is the SAME non-pattern-HO boundary D1 documented (`?b(Z()) =?= Nat` unsolvable — faithful); the checked path above is the main road.
- **`.1`/`.2`** (`sigma_projection`, elaborator.ex:437-438 + 670-676; literal-tuple β-shortcut :423-433): lower to applications of the stdlib `first`/`second` globals (`{:global, :first}` spine with implicits solved from `p`'s inferred `Sigma(a, b)` type — the machinery D1b built). The β-shortcut on literal tuples keeps taking the component directly (pure surface move, representation-independent).
- **Type positions**: `idx_to_core({:sigma_type, [binder: b], [dom, body]})` (declarations.ex:974-979) → `{:data, :Sigma, [dom_core, {:lam, dom_core, body_core}], []}` (the binder becomes a real lambda — `body` was elaborated with the binder in scope, same de Bruijn frame, so wrapping it under one new `{:lam,…}` is exactly the frame it was computed in). `type_to_core` twin at declarations.ex:1195-1200 needs the SAME wrap but NOT the same justification: the comment there (declarations.ex:1188-1194) is explicit that ctor field telescopes are non-dependent — `body_ast` is elaborated by a 1-arg `type_to_core(body_ast)` with no binder pushed at all, so `body_core` is closed w.r.t. the new binder. `{:lam, dom_core, body_core}` is still well-formed (a constant family that ignores its argument), it's just trivially so — there is no "binder in scope" to appeal to at this site, and the plan should not imply there is. Type-position `p.1`/`p.2` (declarations.ex:1013-1025) → the projection-global spines; these sort via the D1 napp clause + D1b type-position insertion (decision §1.3).
- **Keep firing:** `program.ex:281 dependent?({:sigma_type,…})` still routes Σ-typed decls into the dependent pipeline (the surface node is unchanged; only its lowering is).
- **Parser untouched** except nothing: `parse_sigma_type` (parser.ex:4405-4416) keeps producing `{:sigma_type, [binder: b], [dom, body]}`; the surface AST is stable, only elaboration re-points. (`{:pair, meta, [k, v]}` at elaborator.ex:128/153 is a surface record-field AST node — a look-alike, not the Core pair; do not touch.)
- Mechanical traversal strips (`generalize`, `abstract_term`, `replace_branch_vars`, `has_meta?`, unify `mabs`/`escapes?`/`whnf_pre`, subst.ex, resolution.ex, relevance.ex, totality_closure.ex — full list in the scout report §3) happen in T5 with the kernel strip, AFTER producers are gone. Unify's Σ–Σ congruence (unify.ex:301) must be confirmed subsumed by `:data` spine unification against dpp01's deferred-domain machinery before deletion.
- Relevance check: relevance.ex:172 stops at `{:sigma,…}` type positions; `{:data, :Sigma, [a, b], []}` is walked as an ordinary data node — verify no spurious erased-binder-use reports on `b`-mentioning params (red-green with a dependent-record-style probe).

### §2.3 Emit/erase hooks (T3)

- `sigma_ctor?` hook (pattern: `bool_ctor?`/`nat_ctor?`, emit.ex:399/404-406, registry lookup): `{:ctor, mk_pair, [a, b]}` → `{:tuple, @line, [A, B]}`.
- Case-branch hook: a `:case` on a Sigma-typed scrutinee with the `mk_pair` branch → 2-tuple pattern match (template `nat_branch_clause`, emit.ex:329-341).
- Projection globals `first`/`second`: inline to `element(1|2, P)` when applied saturated (keeps `.1`/`.2` zero-cost and `Std.Pair` interop identical); the general global stays callable.
- erase.ex: pair/fst/snd/sigma identity-traversal clauses die in T5; the inductive path needs no new erase clause beyond what ctors/cases already have. CAUTION on the exact lines: `erase/2`'s pair/fst/snd clauses are erase.ex:80-82 and its sigma clause is :84, but line :83 sitting between them is `erase(env, {:pi, d, c})` — Pi is a PERMANENT kernel construct, not part of this retirement, and must survive. Likewise `has_hole?`'s sigma clause is :140 and its pair/fst/snd clauses are :142-144, but line :141 between them is `has_hole?({:app, f, x})` — also permanent. Delete exactly {80, 81, 82, 84} and {140, 142, 143, 144}; do NOT delete lines 83 or 141 (a blind "delete the range" would silently strip Pi erasure and App hole-detection, breaking every non-Sigma dependent program).
- Gate: `test/cure/e2e/frp_beam_test.exs` + `test/cure/compiler/dependent_surface_codegen_test.exs` green unchanged (they pin the 2-tuple ABI).

### §2.4 Validator ratchet (T4)

`no_sigma_node` in `validator.ex` mirroring `no_eq_node` exactly (:27-40 clause list, :42-59 wave0, :84-88 release ratchet, predicate shape :160-164): four predicates (`{:sigma,_,_}`, `{:pair,_,_}`, `{:fst,_}`, `{:snd,_}`), `:warn` first (after T2/T3 land), `:reject` at the end (after T5/T6). Keep a `children` walker clause for sigma even after rejection so smuggled nodes are descended-into and reported (the eq precedent, validator.ex:119).

### §2.5 Kernel/core strip (T5)

Removal-only, mirroring the eq-retirement commit shape (727a673's per-file strip): kernel.ex (`infer` sigma/fst/snd + defensive pair clause + `check` pair + `ensure_sigma` + `infer_type_value_sort` vsigma + `rigid_index?` sigma + `replace_branch_vars` arms), eval.ex, quote.ex, conv.ex (vpair/vsigma/nfst/nsnd — no pair eta exists to lose, verified), normalise.ex (nf arms + the δ+ι nfst/nsnd arms of `unfold_certified_head`/`reduce_unfolded` — the ncase arms right above them already serve the inductive), term.ex grammar, serialize.ex enc/decode, value.ex, inductive.ex (`strictly_positive?`/`occurs?` arms), certificate.ex walkers, meta_check.ex, validator children 4-tuple + grade clause. The napp sort clause stays (§1.3).

### §2.6 Antigen migration (T6)

18 lib files + serialized corpora (scout §6 table is the checklist). Highlights:
- Generators re-point Σ-typed goals/fields/indices at `{:data, :Sigma, …}` and pair intros at `{:ctor, :mk_pair, …}`; projection eliminations become single-branch cases (or the stdlib globals) — `term.ex` intro/elim rules, `sig_menu` canonical inhabitants, `dep_match` Σ-index rows, `check_mode`, `type_former`, `positivity` (its `sigma_negative_family` negative needs an inductive-equivalent encoding), `totality`, `beta_subst` σ-law row, `surface_expr` tuple encoder.
- `conv_pair` rows: β-projection positives become ι-on-case positives; nfst/nsnd negatives become ncase negatives. `delta_reduce`'s certified `kpair` rows are the regression guard for the Θ(2ᵈ)-avoidance engine — port FIRST, red-green, before stripping the nfst/nsnd δ arms.
- `equality.ex` neutral-endpoint rows over Σ-var projections re-encode over case-neutrals.
- `mutation.ex` malformation seeds (`{:fst, nat}`, `bad_pair`, β-redex wrapper) become inductive-shaped malformations (ill-typed case on non-Sigma, wrong-component ctor).
- `shrink.ex`/`runner.ex` traversal arms strip with T5.
- **seeds.sexp (132 occurrences) + corpus.sexp (3)**: regenerate/migrate BEFORE serialize.ex decode clauses die (11ea830 precedent), and check serialize's other consumers for wire-form dependence.
- New antibody: `no_sigma_node` ratchet pin (Malformed seed feeding a primitive-Σ term to the validator expects rejection at `:reject` stage) + a positive pin that the seeded builtin Sigma round-trips (declare/eliminate/normalize) under the property families.

### §2.7 Tests, examples, docs (T7)

- `test/cure/core/sigma_test.exs` rewritten as the inductive-Sigma kernel suite (formation via family, intro via ctor check, dependent snd via case + napp motive, ι-reduction, mismatch negative). eval/quote/serialize/term/value/stuck_elim_delta pins flip per §1.7. One sub-test has no direct translation: "iota: both projection rules hold definitionally" (current sigma_test.exs:54-58) builds an UNTYPED `{:pair, {:type, 0}, {:type, 1}}` and checks raw ι-conversion on universe-literal payloads with no enclosing Σ formation or check at all — that is precisely what the primitive's untyped `{:pair}`/`{:fst}`/`{:snd}` allowed and the inductive's checked `mk_pair` ctor does not (constructing `mk_pair({:type,0}, …)` would need `a` instantiated to `{:vtype,1}`, which is a level-1 domain and would violate the §1.1 level-0 haircut on top of just not being how ctor-checking works). Drop this sub-test rather than force-translate it; its actual property (ι holds regardless of payload) is already covered generically by ordinary ctor/case ι-reduction elsewhere and was never Sigma-specific — replace it with a same-family case-ι test over the file's existing Dec/Box concrete payloads instead.
- `test/cure/elab/sigma_surface_test.exs`: behavior identical; the two Core-shape asserts (`{:pair,…}` :40, `{:snd,_}` :52) flip to ctor/case shapes.
- Oracle: dpair + sg + match mt13-mt19 + erasure er02 re-verified UNCHANGED (no `mix cure.oracle` run needed if replay is green — replay against frozen verdicts IS the invariance check; a verdict change = STOP).
- `examples/sigma_pairs.cure` rewritten to actually demonstrate dependent Sigma (today it advertises Σ in comments but uses only plain tuples — stale, not crashing).
- Roadmap/parity-ledger §2 row updated; memory updated on landing.

## §3 Verification gate (mandatory, TCB blanket conditions)

1. Red-green per task; tests behavioral and immutable once green.
2. Antigen: new antibodies (§2.6) green; FULL Antigen suite green at every task boundary that touches kernel/Antigen; `delta_reduce` kpair ported red-green BEFORE the δ-arm strip.
3. Full `mix test` green at the end (count re-derived; Core-shape pin flips are enumerated per task in the plan, each with a one-line justification — the C-3 "authorized flips" discipline).
4. Oracle: replay green with ZERO verdict changes (any change = STOP; a new cluster is NOT needed — sg/dpair already differential-cover the surface).
5. Final diff verification: after T5, `grep -rn "{:sigma,\|{:vsigma,\|{:vpair,\|{:nfst,\|{:nsnd," lib/cure/core/ lib/cure/elab/` finds ZERO constructors of the retired forms. The `{:pair,`/`{:fst,`/`{:snd,` forms are NOT grep-safe (elaborator.ex:128/153's surface record-field AST node is `{:pair, meta, [k, v]}` — same arity as the retired Core `{:pair, a, b}`, so a textual grep cannot tell them apart) and this criterion does not rely on grep for them: the authoritative check is that `Term.term?/1` (term.ex, post-strip) has no `{:pair,_,_}`/`{:fst,_}`/`{:snd,_}` clause left and `Validator`'s `no_sigma_node` runs at `:reject` — both are live checks against actual definitions, exercised by the full Antigen + `mix test` run in criterion 5 below, not by text search. Treat the grep above as a fast sanity pass for the five unambiguous atoms only. `lib/cure/types/*` + `lib/cure/compiler/*` (except nothing — parser untouched) show NO diff; ghost authorship only.
6. AtomVM sanity is NOT in this gate (host-only worktree) — but the ABI-preservation tests (§2.3 gate) stand proxy; note it in the completion report.

## §4 Non-goals

- `indices ()`-drop parser nicety (§1.9) — follow-up.
- Universe-polymorphic Sigma — Cure has no universe polymorphism anywhere; level-0 like Eq.
- Decoy-pipeline Sigma (`lib/cure/types/sigma.ex` and friends) — different pipeline, untouched.
- Surface syntax changes — `%[..]`, `.1`/`.2`, `Sigma(x: T, U)` all keep their exact grammar.
- Pair eta — the primitive never had it (verified conv.ex:69-104); the inductive doesn't add it.
- Erasure-of-Sigma-to-native beyond the existing 2-tuple (no unboxing work).

## §5 Task decomposition (plan skeleton)

T1 registry+stdlib → T2 elaborator re-point → T3 emit hooks → T4a validator `:warn` → T6 Antigen migration → T7 test/example sweep → T5 kernel/core strip → T4b validator `:reject` → full gate. Each task commits separately; T2 is the crux and may split into T2a (checked/infer `%[..]` + type positions) and T2b (projections). Estimated 5-7 focused days of agent time; every task names its red first.

## §6 Acceptance criteria

1. Zero primitive-Σ node constructors under `lib/cure/core/` + `lib/cure/elab/` (grep-verified per §3.5); `Term.term?` no longer admits them; serialize no longer encodes/decodes them; validator rejects them at `:reject`.
2. The D1 napp clause is still present and still covered (its Antigen arm + sg01 replay green).
3. All surface-behavior tests green unchanged (sigma_surface, sigma_field, tuple_pattern, tuple_scrutinee_match, dependent_construction, dependent_routing, slice1_conformance, frp_beam e2e, dependent_surface_codegen); every oracle verdict byte-identical.
4. BEAM representation of `%[a, b]` is a bare 2-tuple; `.1`/`.2` compile to `element/2`; `Std.Pair` untouched and green.
5. Full Antigen + full `mix test` green; seeds/corpus replay green post-migration.
6. Ghost authorship; explicit-pathspec staging; per-task commits.

## §8 T5 adjudication (2026-07-09): `core_bridge.ex` is a Core-grammar consumer, not a decoy

Execution STOPped at T5 on a coupling the scout inventory missed: `lib/cure/types/core_bridge.ex` — inside the classic pipeline this spec mandated zero-diff for — PRODUCES primitive `{:pair}`/`{:fst}`/`{:snd}` nodes (`to_core`, :69-76) and reads them back (`from_core`, :118-120), because `Cure.Types.Reduce` deliberately delegates all constant folding to the trusted kernel (`reduce.ex:98-99`, "No arithmetic is folded outside `Cure.Core`"). Stripping the kernel clauses breaks exactly 4 classic-pipeline tests (ReduceTest tuple/fst/snd folding, EqualityTest rewrite).

**Ruling:** the zero-diff mandate is AMENDED with a single carve-out. The two-pipeline steer exists to keep dependent-type FEATURE work out of the wrong pipeline; `core_bridge.ex` is not that — it is a downstream consumer of the Core grammar, the same category as `serialize.ex` and the eq-retirement's Lean-bridge lesson (`ccbe2d0`). When the grammar changes, consumers track it.

**Authorized change, tightly bounded:**
- File: `lib/cure/types/core_bridge.ex` ONLY. `reduce.ex` and every other `lib/cure/types/*` / `lib/cure/compiler/*` file remain zero-diff.
- `to_core` `{:tuple,…}` → `{:ctor, <mk_pair>, [ca, cb]}` (registry-consistent ctor atom); `to_core` `"fst"/"snd"` → the single-branch case encoding of the projection (a motive sufficient for eval's ι-rule; eval never motive-checks); `from_core` gains the inverse clauses (`{:ctor, <mk_pair>, [a,b]}` → surface tuple; the single-branch mk_pair case shape → surface `fst(x)`/`snd(x)` call) so the translation stays total on everything it can produce.
- BEHAVIOR-PINNED: the 4 affected classic tests must pass with their existing assertions untouched (they assert surface shapes). If any of them asserts a Core shape, that flip is enumerated and justified like every other pin flip.
- The primitive-node clauses in `from_core` are deleted with the strip (they become dead once `to_core` no longer produces the forms and the kernel grammar rejects them).

§3.5's final-verification grep list gains `lib/cure/types/core_bridge.ex` as an explicitly-allowed diff (the ONLY types/compiler diff); everything else under those trees must remain empty. Acceptance criterion §6.1's "zero producers" scope extends to core_bridge.ex (post-change it produces only inductive forms).

**Also ratified from the same execution report:** (a) T6's corpus PURGE (115 seed + 3 corpus records) follows the `11ea830` precedent — purge, not transform — and is the accepted mechanism; (b) the malformed "Nat-head napp reject" Antigen seed routes through the SURVIVING napp clause, not the deleted defensive pair clause, so keeping it is correct (the plan's presumption it exercised the defensive clause was wrong); (c) the pre-existing `Equivalent(int, x, y)` nf-idempotence "infection" in the coverage fuzzer reproduces on the clean pre-T6 tree — NOT a D2 regression; it is queued as a separate finding, not fixed in D2.

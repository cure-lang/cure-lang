# Antigen Tier-B Reach Expansion — Design

**Status:** design (Stage 0, autopilot) · **Date:** 2026-07-04 · **Branch:** `autopilot/antigen-tier-b`
**Builds on:** `2026-07-02-antigen-tier-b-term-generator-design.md` (+ its report's "Reach left open")
**Predecessor initiative:** untrusted-machinery (V1–V6, complete; both findings fixed 2026-07-04)

## 1. Goal

Widen the reach of the **existing** dependent Core term generator
(`Antigen.Generators.Term`, mode-directed bidirectional inversion) and add two new
assays that consume the richer stream. Operator-selected scope: **all three** of the
Tier-B report's "reach left open" items that concern the generator itself —

1. **Richer generator menu** — Π/Σ goal seeds + a parametric (type-parameter) family.
2. **`erasure_preservation` assay** — erasure preserves computation, on the generated stream.
3. **Ill-typed mutation for the new type formers** — extend `mutation/rejection` with
   operators that break the Π/Σ/parametric terms Phase 1 unlocks.

One initiative, **three sequentially-committed phases**. Phase 1 is first because the
richer stream is what Phases 2 and 3 consume — they are strictly deeper with it in place.

## 2. Current state (verified against source)

- **`Antigen.Generators.Term`** (`term.ex`): `gen_term(ctx, goal) = Gen.sized(...)`,
  `@max_size 12`, `@gen_fuel 500`; lazy `gen/3`; `intro_rules/4` already dispatches on
  `{:pi,_,_}`, `{:sigma,_,_}`, `{:data,:Vec,_,_}`, `{:data,:Nat,_,_}`, `{:data,:Bd,_,_}`,
  `{:type,_}`. Produces `:typed_term` challenges tagged for the three assay ids.
- **`SigMenu`** (`sig_menu.ex`): `goal_types = [nat(), bd(), vec(z()), vec(s(z()))]` — the
  **top-level goal seeds are only closed data types** (no Π/Σ, no type parameters).
  `canon/2`, `inhabitable?/2` already cover `:pi`/`:sigma` (they arise only as *sub-goals*
  today). `env_of(:v1)` holds the fixed signature (Nat, Bd, Vec, plus/dbl defs).
- **`Antigen.Assays.Term`** (`term.ex`): op-map seam `@real_kernel %{infer: &Kernel.infer/2,
  check: &Kernel.check/3}`, `run/1`→`run/2`, dispatch on assay id
  (`term/infer_check`, `term/subject_reduction`, `term/normalization`); payload `p` has
  `.term`, `.type`, `.ctx`. Uses `Normalise.quote`, `Conv`, `Serialize`.
- **Mutation** already exists and **already consumes `Term.gen_term`**: generator
  `Mutation.build(ctx, op)` with `op ∈ {head_swap, ctor_arg, index_mismatch, app_domain,
  out_of_scope_var, proj_non_pair, universe}` (7 operators, not 6 — `:universe` was
  missing from an earlier draft of this list); assay `mutation/rejection` — ill-typed
  `:mutant_term` MUST be rejected by `Kernel.infer` (`{:error,_}`→`:ok`; `{:ok,_}`→antibody).
  `Runner.explore/1` banks every well-formed challenge as a seed regardless of assay, and
  banks an antibody on any violation — so `mutation/rejection` violations DO bank (open
  item #4's question), through the generic `explore/1` path, not bespoke code in
  `Assays.Mutation`.
- **Erasure** (`Cure.Elab.Erase.erase/2`) — just made idempotent (2026-07-04); erased terms
  are non-dependent runtime forms (validated by `Term.term?`, NOT kernel typing — a locked
  V4 fact). **`Eval.eval/2`** maps a Core term + env to a value (`:vctor`/`:vlam`/`:vpair`/…).
  **Load-bearing fact for Phase 2 (verified against source, §8-2 below): `env_of(:v1)`
  currently declares NO `:erased` quantities anywhere** — `Inductive.ctor/3` (used for
  every v1 ctor: `Z`/`S`/`T`/`F`/`vnil`/`vcons`) defaults every argument to `:present`, and
  `Env.add_def/4` (used for `plus`/`dbl`) passes `quantities: nil`, which `Erase.erase/2`'s
  `:app` clause treats as all-`:present`. So `Erase.erase(env_of(:v1), t) == t` structurally
  for every term the current — or Phase-1-enriched-as-drafted — generator can produce; see
  §8-2 for why this makes `erasure_preservation` vacuous as scoped and the required fix.

## 3. Phase 1 — Richer generator menu

**Files:** `lib/antigen/generators/sig_menu.ex` (+ possibly `term.ex` for new intro/elim
coverage); **`lib/antigen/challenge.ex`** (`@known_atoms` — verified missing today: `:List`,
`:Nil`, `:Cons`, and whichever param-binder name is chosen (e.g. `:A`) are not in the
current `@known_atoms` list). This is required, not optional: `Runner.explore/1` banks
every well-formed challenge as a `:typed_term` seed regardless of phase (§2), so a
Phase-1-generated term containing `{:ctor, :Nil, []}`/`{:ctor, :Cons, [...]}`/`{:data,
:List, ...}` can land in `test/antigen/seeds.sexp` immediately; replaying that seed in a
fresh process calls `String.to_existing_atom("Nil"/"Cons"/"List")` (`Challenge.from_pieces`)
and crashes unless those atoms are already force-interned by `@known_atoms` — the exact
failure mode `Challenge`'s own moduledoc documents this list as existing to prevent.
Antigen-only otherwise; no kernel edits.

- **Π and Σ goal seeds.** Add closed, inhabitable function/pair goal types to
  `goal_types/0` — e.g. `{:pi, nat(), nat()}` (`Nat→Nat`), `{:pi, nat(), bd()}`,
  `{:sigma, nat(), vec(<idx>)}` (`Σ Nat. Vec`). The `intro_rules` for `:pi`/`:sigma`
  already fire, so top-level goals now produce λ-abstractions and pairs. Confirm
  `inhabitable?/2` returns true for each new seed in the empty context (it already
  recurses through `:pi`/`:sigma`) so `canon/2` gives a total fallback.
- **Parametric (type-parameter) family.** Add ONE parametric family to `env_of(:v1)` that
  exercises the `params` slot of `{:data, name, params, indices}` — a `List(A)` (param `A`,
  no index) is the minimal clean choice: ctors `Nil : List(A)`, `Cons : A -> List(A) ->
  List(A)`. Add its goal seed(s) (`List(Nat)`, `List(Bd)`), `intro_rules` for
  `{:data, :List, [A], []}` (choose `Nil`/`Cons`, recursing on `A` and `List(A)`),
  `canon` (`Nil`), and `inhabitable?`. (Exact eliminator support is an open item — §8-1.)
- **Health gate.** The existing static-health meta-tests (discard-rate, binder-usage,
  reduction-activity) must stay green — a richer menu must not tank the well-typed-not-
  useless ratios. This is the acceptance gate for Phase 1, alongside the three differential
  assays continuing to pass (now over deeper terms). **Verified to exist:**
  `test/antigen/typed_term_meta_test.exs` (its "banked :typed_term seed corpus meets the
  health floors" test reads `test/antigen/seeds.sexp` and asserts `Runner.health_metrics/1`
  against the `0.60`/`0.25` binder-usage/reduction-activity floors defined in `runner.ex`)
  and `test/antigen/health_gate_test.exs` (unit-tests `health_metrics/1` directly). Both
  already include a `{:pi, nat(), nat()}` goal in their fixed matrices
  (`typed_term_meta_test.exs`'s "canonical-fallback totality over a fixed goal matrix"),
  confirming Π-goal inhabitability/canon already work end-to-end today — corroborating
  §8-3.

**Effect:** no new assay — Phase 1 automatically deepens `term/infer_check`,
`term/subject_reduction`, `term/normalization` by feeding them λ/pair/list terms.

## 4. Phase 2 — `erasure_preservation` assay

**Files:** `lib/antigen/assays/term.ex` (new dispatch clause) or a new
`lib/antigen/assays/erasure_preservation.ex`; `term.ex` generator (`@assay_ids` +1);
`runner.ex` (one dispatch clause). Consumes the same `:typed_term` stream. **Assay id:**
`"term/erasure_preservation"` — namespaced like the three existing ids
(`term/infer_check`, `term/subject_reduction`, `term/normalization`) in `@assay_ids`, since
it's added to that same list and dispatched by the same `Runner.assay_module/1` string-match
convention (no catch-all clause there — §2/§6).

**Precondition (blocking, verified against source — see §2 and §8-2): the v1 menu must
gain at least one real `:erased` quantity before this assay means anything.** As drafted,
`env_of(:v1)` (and Phase 1's planned `List(A)` addition, which likewise doesn't propose
marking any argument erased) has zero `:erased` quantities anywhere, so
`Erase.erase(env_of(:v1), t) == t` for every generated `t` — erasure is the identity
transformation on the whole corpus. Both candidate formulations below would then hold
*trivially* and would never exercise `Erase.erase/2`'s actual arg-dropping branches
(erase.ex's `:ctor`/`:app` clauses) — precisely the "dead branch" failure mode this
section's own negative-control rationale warns against (V2's lesson). **Phase 2 must
therefore also mark one v1-reachable constructor argument `:erased`**, not just wire the
assay: recommend `Vec`'s `vcons` witness argument `n` (`{:n, nat()}` in
`Inductive.ctor(:vcons, [{:n, nat()}, {:x, nat()}, {:xs, vec({:var, 1})}], [s({:var, 2})])`
in `sig_menu.ex`), since `n` is forceable/derivable from the result index — a canonical
forced-argument-erasure case, and the same `:present`/`:erased` vocabulary the existing
`erasure/selective` vertical (`Antigen.Generators.ErasureTerm`, a separate generator/env)
already exercises elsewhere in Antigen. Concretely: change that ctor declaration to
`Inductive.ctor(:vcons, [{:n, nat()}, {:x, nat()}, {:xs, vec({:var, 1})}], [s({:var, 2})],
[:erased, :present, :present])`. This does not change `vcons`'s registered arity/types (so
`Kernel.infer`/`check`/`Term.term?` and existing banked-seed replay are unaffected — see
§8-5) and does not touch `plus`/`dbl`'s quantities.

**Property (to pin precisely in review — §8-2).** For a generated well-typed `t : T`:
erasure preserves the computational result. Candidate formulations, strongest-first:
- **(a) Commutation:** `nf(erase(t)) ≡ erase(nf(t))` structurally — erasure commutes with
  normalization. Strong and oracle-free (both sides are Core terms; compare via `Serialize`
  or structural `==`). **Analytically tractable and recommended, scoped to ctor-level
  erasure only** (see §8-2 for the proof sketch and the scoping boundary that excludes
  erased *global-def* parameters, which are not part of this phase).
- **(b) Value-totality + well-formedness:** `Term.term?(erase(t))` is true AND
  `Eval.eval(erase(t), env)` produces a value without raising. Weaker but unconditionally
  tractable; catches an erase that yields an ill-formed or non-evaluable term (exactly the
  pre-fix drop-a-present-arg failure mode). Fallback if (a) turns out to be more fragile in
  implementation than the proof sketch suggests.

The assay returns `:ok | {:violation, {:erasure_not_preserved, detail}}` **plus a distinct
`{:violation, {:fuel_exhausted, stage}}` class**, mirroring `Assays.Term`'s existing
convention (never conflate fuel exhaustion with a genuine mismatch — §6's invariant).
This is not cosmetic here: `Normalise`'s fuel counter (`spend_fuel/1` in normalise.ex) is a
single shared, globally-decremented `Process` counter across an entire `nf` call, not
per-subterm-independent. Erasing before normalizing (`nf(erase(t))`) does strictly less
total reduction work than normalizing first (`erase(nf(t))`, which spends fuel reducing the
soon-to-be-dropped erased argument too) — so the two `nf` calls the assay makes are not
guaranteed to consume identical fuel, and one could exhaust while the other completes. At
`@assay_fuel` (500,000) against `@max_size 12`-depth terms this is far from the exhaustion
boundary in practice, but the assay implementation must still check each `nf` call's result
for `:fuel_exhausted` independently and report it as its own violation class rather than
comparing a `:fuel_exhausted` atom against a Core term as if it were a structural mismatch.
Wire via the op-map seam (`erase`, plus `infer` to gate on well-typedness).

**Negative control (must infect).** Inject a broken erase into the op-map — e.g. the
pre-fix zip-realignment behavior, or a stub dropping a `:present` arg — and confirm the
assay reports `{:violation, {:erasure_not_preserved, _}}` on a term where the real erase
passes. (This is what makes the assay load-bearing; V2's dead-branch lesson.)

## 5. Phase 3 — Ill-typed mutation for the new type formers

**Files:** `lib/antigen/generators/mutation.ex` (+ new operators), `challenge.ex`
(`@known_atoms` for any new op kinds), tests. Reuses the existing `mutation/rejection`
assay unchanged (it already asserts kernel rejection of `:mutant_term`).

New mutation operators targeting Phase 1's type formers (each builds a
construction-guaranteed ill-typed term the kernel must reject):
- **`pair_component`** — in a Σ-typed pair, replace one component with a well-typed term of
  the wrong type (breaks the Σ's dependent second component or first-component type).
  **Must self-wrap in `build/2`, never submit a bare `:pair` (verified against source, a
  crash risk, not just a documentation gap):** `Kernel.infer/2` has NO clause matching
  `{:pair, a, b}` at all (`kernel.ex` only defines `check(ctx, {:pair, a, b}, {:vsigma,
  ...})` — pairs are check-mode-only, like param-bearing ctors, only with no infer clause
  whatsoever rather than an explicit `{:error, :ctor_requires_checking_mode}`). A bare
  `:pair`-headed mutant handed to `mutation/rejection`'s `Kernel.infer(ctx, p.term)` call —
  reachable whenever `Gen.int(0, max_depth())` draws `deepen`'s depth `d = 0`, which leaves
  the term unwrapped — would raise `FunctionClauseError`, an uncaught crash, not a clean
  `{:error, _}` → `:ok` rejection. `build(ctx, :pair_component)` must therefore construct
  its mutant ALREADY embedded in a check-inducing application, e.g. `{:app, {:lam,
  sigma_type, {:var, 0}}, bad_pair_term}` — the exact technique the codebase already uses
  for its `:pair` deep-propagation wrapper (`wrap(inner, :pair, filler) = {:app, {:lam,
  sig(), z()}, {:pair, inner, filler}}` in `mutation.ex`), just applied inside `build/2`
  itself rather than left to chance in `deepen`'s randomly-chosen wrapper stack.
- **`lam_body_type`** / **`app_result`** — for a Π-typed λ or its application, supply a
  body/argument that violates the codomain (result-type mismatch). **Corrected distinction
  from the existing `app_domain`** (verified against source: `build(ctx, :app_domain)` in
  `mutation.ex` already constructs `{:app, {:lam, nat_t(), {:var, 0}}, v}` — a Π-application
  with a wrong-typed *argument*, i.e. a domain mismatch, not "first-order data application"
  as an earlier draft of this line claimed). The real, still-genuine distinction: (1)
  `app_domain` always applies a single hand-built, hardcoded `Nat→Nat` identity lambda —
  never a real function-typed term drawn from the Phase-1-enriched generator — whereas the
  new operators should mutate actual generator-produced Π-typed λ/application terms from
  the richer stream; and (2) `app_domain` only ever breaks the *domain* side (wrong-typed
  argument to a fixed-good function), while `lam_body_type`/`app_result` break the
  *codomain* side (a well-typed function applied correctly, but whose body/result violates
  its declared return type) — a distinct fault class the existing operator cannot produce.
- **`type_param_mismatch`** — for a parametric `List(A)` term, `Cons` an element of the
  wrong parameter type (`Cons (b : Bd) : List(Nat)`), which the kernel must reject. **Must
  NOT follow the bare-ctor pattern `ctor_arg`/`index_mismatch` use** (verified against
  source, a real construction-technique gap, not just documentation): `Kernel.infer(ctx,
  {:ctor, name, args})` (kernel.ex) checks `Inductive.param_count(sig, family_name) > 0`
  and, if so, unconditionally returns `{:error, {:ctor_requires_checking_mode,
  family_name}}` — for EVERY bare `:ctor` term of a param-bearing family, well-typed or
  ill-typed alike. `List` has exactly one param (`A`) by design (that's the point of adding
  it), so a bare `Cons(...)` term submitted directly to `mutation/rejection`'s
  `Kernel.infer` call would *always* error this way, including the correctly-typed analog —
  which would make Phase 3's own load-bearing check ("without the mutation, the analogous
  well-typed term is accepted") FAIL for this operator, since `infer` never succeeds on any
  bare `List`/`Cons` ctor. (This is exactly why `ctor_arg`/`index_mismatch` work today as
  bare ctors: `Vec`/`Nat`/`Bd` all have zero params, so those hit `Kernel.infer`'s
  `param_count == 0` branch instead.) `type_param_mismatch` must instead embed the bad
  `Cons` term where the kernel type-CHECKS it against an expected `List(Nat)` — e.g. as the
  argument of a manufactured identity application `{:app, {:lam, list_nat_t(), {:var, 0}},
  bad_cons_term}` (the same "wrap so `:app`'s infer-then-check-domain path forces a CHECK
  of the inner ctor" technique `app_domain` already uses for Vec, just with `list_nat_t()`
  as the lambda's domain instead of `nat_t()`). The existing `deepen`/`@wrappers`
  deep-propagation machinery does NOT apply here without change: every current wrapper
  (`app_arg`/`ctor_nat`/`case_scrut`/`case_branch`/`pair`) is `Nat→Nat` by design (its own
  moduledoc says so) and has no hole that accepts a `List(Nat)`-typed term, so either
  `type_param_mismatch` skips `deepen` (submits its own pre-wrapped, non-deepened mutant —
  losing the deep-propagation coverage the other operators get), or Phase 3 must add a
  `List(Nat)→List(Nat)`-shaped wrapper variant to make it deepen-compatible. Record this
  choice explicitly in the plan; don't leave it implicit.

Each new operator gets a test asserting the produced mutant is rejected by `Kernel.infer`
(the `mutation/rejection` `:ok`), and — the load-bearing check — that WITHOUT the mutation
the analogous well-typed term is *accepted* (so the operator genuinely introduces
ill-typedness, not a term that was already rejected for another reason).

## 6. Invariants (what must never regress)

- **No kernel/TCB edits.** `Cure.Core.*`/`Cure.Elab.*` reached read-only through op-maps.
  Phase 1's menu additions and Phase 3's operators live entirely in `Antigen.*`.
- **StreamData quarantine.** Nothing under `Antigen.Generators.*`/`Antigen.Assays.*` may
  contain the literal `StreamData` token (arch test). New generator code uses the `Gen` DSL.
- **Assays return only `:ok | {:violation, term()}`** (non-normalization stays a distinct
  tagged violation, never conflated).
- **Health gate holds** after Phase 1 (discard-rate/binder-usage/reduction-activity).
- **The full existing suite stays green** each phase (2732 baseline); each new assay/operator
  ships with a negative control that demonstrably infects.
- New `Challenge` payload shapes/atoms interned in `Challenge.@known_atoms` if banked.

## 7. Non-goals

- **No `Backend.ChoiceSeq`** (the Hypothesis-style shrinking backend) — a separate reach
  item, its own initiative.
- **No `conversion_termination` assay** — the other listed reach item; deferred.
- No new kernel *features* (e.g. we add a `List` family to the Antigen *menu env*, not to
  the language's stdlib).
- No unbounded generator growth — `@max_size`/`@gen_fuel` stay the committed budgets; the
  richer menu adds breadth (more goal shapes), not depth blow-up.
- Not a fuzzer rewrite — the generator stays the reified-`Gen` inversion generator.

## 8. Open items (for the plan / spec-review to pin)

1. **`List(A)` eliminator support — CORRECTED claim.** Phase 1's parametric family needs
   `intro_rules` (Nil/Cons) at minimum. Whether to also generate a `List` *eliminator*
   (recursor/case) — which the differential trio would exercise for reduction — depends on
   how the existing `gen` handles `:case`/eliminators for data families. **Verified against
   source: Vec does NOT already have a case-eliminator.** `term.ex`'s `case_rule`/`case_for`
   only ever build a `:case` scrutinizing family `:Nat` or `:Bd` (`case_rule`'s three
   branches dispatch on `{:type,_}` → none, `{:data,:Nat,_,_}` → Bd- and Nat-case, anything
   else → Bd-case only; `:Vec` is never passed as `fam` to `case_for`). Vec's only generator
   support is constructor introduction (`ctor_rules_for_vec`) and generic context-variable
   reference (`var_rules`, which offers any in-scope variable whose type converts with the
   goal — not a real eliminator). So there is **no existing case-eliminator pattern to
   reuse** for List; adding one would mean extending `case_rule`/`case_for` to a new family
   from scratch (new motive shape, branch-argument binding for `Cons`'s two fields), which
   is materially more work than "reuse the Vec pattern" implies. This strengthens rather
   than weakens the fallback: **ship intro-only (`Nil`/`Cons`) in Phase 1** and track a
   `List` case-eliminator — and, notably, a first Vec case-eliminator, since neither exists
   today — as explicit follow-up work, not a Phase-1 deliverable.
2. **Exact `erasure_preservation` property — RESOLVED by this review.** Two sub-questions,
   both now pinned:
   - **(i) The corpus must actually erase something.** `env_of(:v1)` has no `:erased`
     quantities today (§2/§4 above) — fix required: mark `vcons`'s `n` argument `:erased`
     in `sig_menu.ex` (§4's precondition). Without this, the assay is vacuous regardless of
     which of (a)/(b) is chosen.
   - **(ii) Commutation (a) vs. value-totality (b).** `Erase.erase/2` never drops a `:lam`/
     `:pi` BINDER — it only filters the flat argument list of a `:ctor` node (by the
     family's static per-ctor quantity vector) or a saturated `{:global,name}`-headed
     `:app` spine (by that def's static quantity vector); it never rewrites inside a
     function body to remove references to an erased parameter. Given that, and given the
     ctor-only fix in (i): `Normalise.nf`'s `:vctor` clause (`nf_struct` in normalise.ex)
     maps normalization independently over each sibling constructor argument — no argument
     depends on another's *value* at reduction time (only their shared outer `env`). Erase's
     ctor clause is a static-position filter+map over that same flat list. Filtering and
     independently-mapping over a fixed-position list commute, so **`nf(erase(t)) ≡
     erase(nf(t))` holds for ctor-level erasure and (a) is the recommended, provable
     property for Phase 2 in its current scope.** Scoping boundary (record, don't build
     yet): this proof does NOT extend to erased **global-def** parameters — `nf`'s
     δ-unfold (`unfold_certified_head` in normalise.ex) replaces a `{:global,name}`-headed
     neutral with its evaluated body *before* erase ever runs, so by the time
     `erase(nf(t))` sees the result there is no `{:global,name}` node left for it to
     consult that def's quantity vector against; `nf(erase(t))`, by contrast, drops the
     def's erased argument BEFORE unfolding. Whether these agree is a separate, harder
     claim resting on the elaborator's erased-binder relevance check (not yet analyzed
     here) and is explicitly OUT of scope for Phase 2 — `plus`/`dbl` keep `quantities: nil`
     (all-present), so this boundary is never crossed by v1's generated stream. If a future
     menu version marks a global def's parameter erased, (a) must be re-derived for that
     case before being trusted. **`Eval.eval` env for an erased term — CORRECTED:** an
     earlier draft of this item assumed erased terms need "the empty/rebuilt env" because
     they have no dependent context. Verified false: `erase/2` never removes or renumbers a
     BINDER (`:lam`/`:pi`/`:sigma`/`:case`-branch clauses all recurse structurally, keeping
     the same binder shape) — it only drops elements from the flat sibling-argument list of
     a `:ctor` node or a global-headed `:app` spine, never a `:var`-introducing form. So
     `erase(t)`'s free variables reference the exact same de Bruijn positions as `t`'s did;
     `Eval.eval(erase(t), env)` must use the **same** `env` as `Eval.eval(t, env)` —
     `Context.env(ctx)`, the same context the challenge's `p.ctx` rebuilds — not a separate
     empty or rebuilt one.
3. **`inhabitable?` for Π/Σ/List seeds in the empty context.** Confirm each new `goal_types`
   seed is actually inhabitable so `canon/2` never fails (a non-inhabitable seed would make
   the size-0 fallback raise). Π into an inhabitable codomain and Σ of inhabitables are fine;
   confirm the chosen index terms for any `Vec` inside a Σ seed. **Partially pre-verified:**
   `inhabitable?`/`canon` already handle a top-level `{:pi, nat(), nat()}` goal correctly
   today — `test/antigen/typed_term_meta_test.exs`'s "canonical-fallback totality over a
   fixed goal matrix" test asserts exactly this. Sigma and the `List` family's seeds have no
   equivalent existing coverage and still need the check this item calls for.
4. **Mutation `@known_atoms` + payload.** New operators may introduce new atom tags
   (`:pair_component`, `:type_param_mismatch`, …) — intern them if mutants are banked to the
   corpus; confirm whether `mutation/rejection` banks (it does bank antibodies).
5. **Menu-version bump — RESOLVED by this review: extend `:v1` additively, no `:v2`
   needed.** Banked challenges (`test/antigen/typed_term_meta_test.exs` reads
   `test/antigen/seeds.sexp`) carry only `sig: :v1` (an atom, via `Challenge.to_pieces`'s
   `"sig" => Atom.to_string(sig)`) plus raw Core-term bytes for `ctx`/`type`/`term` — never
   a snapshot of the env itself. Replay always calls `SigMenu.env_of(p.sig)` **fresh**
   against whatever `env_of(:v1)` is defined as *at replay time* (`Assays.Term.run/2`,
   `Assays.Mutation.run/2`, `Runner.replay/2` all do this). A banked term's de Bruijn
   indices, ctor names (`:Z`/`:S`/`:T`/`:F`/`:vnil`/`:vcons`), and def names (`:plus`/
   `:dbl`) resolve correctly as long as those stay registered with unchanged arities/types
   — which a purely *additive* change (new `List`/`Nil`/`Cons` family; Phase 2's `:erased`
   quantity mark on `vcons`'s existing `n` argument, which changes erasure behavior but not
   `vcons`'s arity, types, or kernel typechecking) guarantees. Neither Phase 1's `List`
   addition nor Phase 2's quantity-marking fix (§4) removes or reshapes anything already in
   `env_of(:v1)`, so **both are safe to land as additive extensions of `:v1`**; banked
   `:v1` seeds replay unchanged. A `:v2` would only be needed for a change that alters or
   removes an existing family/ctor/def — out of scope for this initiative.

## 9. Test strategy (per phase, red-green)

- **Phase 1:** red — a test asserting `SigMenu.goal_types` includes a Π/Σ/List seed and that
  `Term.gen_term` over a Π goal produces a `:lam` (and over `List(Nat)` a `:ctor :Cons/:Nil`)
  fails today; green after the menu additions. Health-gate meta-tests + the three differential
  assays stay green over the richer stream.
- **Phase 2:** red (precondition) — a test asserting `Inductive.ctor_quantities(env_of(:v1),
  :vcons)` contains `:erased` fails today (all-`:present`); green after marking `vcons`'s `n`
  argument erased in `sig_menu.ex` (§4's precondition — do this fix FIRST, before wiring the
  assay, so the assay is never validated against a vacuous erase). Then red — the
  `erasure_preservation` assay clause doesn't exist (dispatch raises); green after
  implementing it against formulation (a) (§8-2); the negative control (broken erase)
  infects.
- **Phase 3:** red — each new mutation operator (`build(ctx, :pair_component)` …) is undefined;
  green after adding it; `mutation/rejection` returns `:ok` on the mutant AND the un-mutated
  analog is accepted (the operator genuinely ill-types). For `pair_component` and
  `type_param_mismatch` specifically, the "un-mutated analog is accepted" red test is also
  what proves the §5 self-wrapping requirement was actually implemented — run it BEFORE
  trusting the mutant-rejection green: if `build/2` emits a bare `:pair`/param-bearing
  `:ctor`, that acceptance check fails (or, for `:pair`, crashes) rather than passing for the
  wrong reason.
- **Each phase:** full suite green before moving on (one build at a time).

## 10. Next (roadmap)

Remaining Tier-B reach items after this initiative: `Backend.ChoiceSeq`,
`conversion_termination`, and A10's broader wiring of the known-label verticals onto the
generated stream. **No auto-merge.**

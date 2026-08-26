# Antigen V4 — Erasure & Relevance Soundness — Design

**Status:** design (Stage 0, autopilot Phase 5) · **Date:** 2026-07-03 · **Branch:** `autopilot/antigen-tier-b`
**Umbrella:** `2026-07-03-antigen-untrusted-machinery-design.md` §V4 · **Predecessors:** V3 (elab), V1 (normalizer), V2 (unifier), V5 (totality-closure)

## 1. Goal

Extend Antigen to the **untrusted erasure & relevance machinery**: the `{0,ω}`
erasure that strips computationally-irrelevant (quantity-0 / `:erased`) sub-terms
before emission (`Cure.Elab.Erase`), and the relevance checker that guarantees no
`:erased` binder is used relevantly (`Cure.Elab.Relevance`). These implement the
**LOCKED** erasure relevance-check decision (memory `erasure-relevance-check-decision`):
the `{0,ω}` check enforces the spec-§2 "computationally-relevant" rule — reject
return / present-arg / scrutinise / apply of an erased binder; make params present;
do **not** auto-promote (preserving the zero-footprint guarantee). Erasure soundness
matters two ways: dropping a **relevant** (present) sub-term loses runtime data (a
wrong program), and **keeping** an erased sub-term breaks the zero-footprint
guarantee the whole `{0,ω}` design rests on.

**What is already covered vs. what is new.** The existing
`Antigen.Generators.ElabErasure` produces **surface-program** challenges
(`kind: :elab_program`, `assay: "elab/erasure"`) that test the relevance rule
*end-to-end through elaboration* (accept/reject whole programs). V4 targets the
**Core-level** functions those depend on, with no elaboration confound:

- `Cure.Elab.Erase.erase/2` — the Core→runtime term stripper (zero existing
  direct coverage).
- `Cure.Elab.Relevance.check/4` — the relevance decision, tested **directly** on
  Core bodies with known relevant-use sites (complements, does not duplicate, the
  surface-program `elab/erasure` assay).

## 2. Targets (verified against source)

### `Cure.Elab.Erase` (`lib/cure/elab/erase.ex`)

- `erase(env, term) :: term` — recursively drops `:erased` constructor arguments
  (`{:ctor, c, args}` keeps only positions where `Inductive.ctor_quantities(env, c)`
  is `:present`; `nil` quantities ⇒ all `:present`), drops `:erased` application
  arguments for a `{:global, name}` head (via the def's `quantities`, padding
  extra args as `:present`), and structurally recurses through
  `:lam/:app/:pair/:fst/:snd/:pi/:sigma/:data/:case`. Non-computational forms
  collapse: `{:refl, _} → {:ctor, :cure_refl, []}`, `{:eq, …} → {:ctor, :cure_eq, []}`,
  `{:rewrite, _p, _m, body} → erase(body)`. `erase(_env, term) → term` (leaves).
- `has_hole?(term) :: boolean` — structural hole detector over the full taxonomy.

### `Cure.Elab.Relevance` (`lib/cure/elab/relevance.ex`)

- `check(env, name, quantities, body) :: :ok | {:error, {:erased_used_relevantly,
  %{def: atom(), binder: non_neg_integer(), site: site()}}}` where
  `site :: :returned | :present_arg | :scrutinee | :applied`. Non-list `quantities`
  ⇒ `:ok` (vacuous). Walks `body` tracking de Bruijn depth; an `:erased` binder
  used at any of the four relevant sites is the violation. Erased argument
  positions are exempt (an erased binder may appear in another erased position).

### `Cure.Core.Inductive.ctor_quantities(env, cname) :: [:present | :erased] | nil`

The quantity vector `Erase`/`Relevance` both consult — the shared oracle for
"which positions are erased."

## 3. Properties (two families)

### V4a — `Erase.erase/2` (intrinsic + differential)

- **Idempotence:** `erase(env, erase(env, t)) == erase(env, t)` — erasure is a
  normal form; re-erasing changes nothing. A non-idempotent erasure is
  `{:violation, {:erase_not_idempotent, t}}`.
  **Verified hazard, catalog-critical:** the real `:ctor` clause re-reads
  `Inductive.ctor_quantities(env, cname)` (the ORIGINAL full-length vector for
  `cname`, unchanged by a prior erase) and zips it *positionally* against
  whatever `args` list it is given. After a first erase shrinks `args` to only
  the `:present` positions, a second erase zips the SAME full vector against
  the now-shorter list — `Enum.zip/2` pairs by index, not by original
  position, so surviving args silently re-align to the vector's *leading*
  entries. Concretely, `qs = [:erased, :present]`, `args = [a, b]` (leaves):
  first erase → `{:ctor, c, [b]}`; second erase re-zips `[b]` against
  `[:erased, :present]`, pairing `b` with `qs[0] = :erased`, and drops it →
  `{:ctor, c, []}`. `{:ctor, c, [b]} != {:ctor, c, []}` — **idempotence is
  FALSE for this ordering.** The bug is not synthetic: the *same* production
  ctor shape already exercised by `test/cure/elab/erase_test.exs` (`seq`,
  quantities `[:erased,:erased,:erased,:erased,:erased,:present,:present]`,
  a contiguous erased-block-then-present-block) reduces to the empty ctor
  `{:ctor, :seq, []}` on a second application, by the identical mechanism.
  `erase/2` is currently only ever invoked once per def body
  (`lib/cure/elab/emit.ex:95,110`, both read the raw body fresh from `Env`),
  so this is presently dormant, not a live-pipeline defect — but it is a real
  defect in `erase/2`'s algebraic behavior under composition, exactly the
  class of bug V4a exists to surface. **Order sensitivity means the catalog
  choice matters:** the *specific* 2-element ordering `[:present, :erased]`
  that §5 proposes (present position first) does **not** trigger this bug —
  the single surviving arg is always at index 0 in both passes, so it keeps
  re-aligning with `qs[0] = :present` by coincidence — so a catalog built only
  from that ordering would make the idempotent baseline pass while the real
  bug goes undetected. The catalog (§5, §9-1) MUST also include at least one
  ctor challenge where an `:erased` position precedes a kept `:present`
  position (e.g. `[:erased, :present]`, or the real `seq` shape above) so the
  property is non-vacuously exercised. Per §6, if V4a's idempotent baseline
  legitimately fails against the real `erase`, that is a genuine finding —
  STOP and report it (do not weaken the test to dodge it).
- **Hole preservation:** `has_hole?(t) == false ⟹ has_hole?(erase(env, t)) ==
  false` — erasing a hole-free term never introduces a hole (erasure only removes
  and structurally recurses; it must not synthesise a `{:hole,_}`). Violation
  `{:hole_introduced, t}`.
- **Selective drop (differential vs `ctor_quantities`, the core soundness
  property):** for `{:ctor, c, args}` with quantity vector `qs`, `erase`'s kept
  arguments are **exactly** the `args` at `:present` positions of `qs` (each
  recursively erased). Dropping a `:present` position (runtime-data loss) or
  keeping an `:erased` position (zero-footprint violation) is
  `{:violation, {:wrong_positions_kept, c}}`. This is the direct differential
  against the locked `{0,ω}` decision.
  **Second selective-drop surface (verified, not covered above):** `erase`'s
  `{:app, …}` clause for a `{:global, name}` head is a structurally distinct
  code path — it looks up quantities via `Env.get_def/2` instead of
  `Inductive.ctor_quantities/2`, and pads with `List.duplicate(:present, …)`
  for over-application (`lib/cure/elab/erase.ex:39-54`) — not merely a
  re-dispatch onto the ctor logic. It has the identical zip-realignment
  mechanism as the `:ctor` clause and is confirmed to exhibit the identical
  non-idempotence hazard traced above (a global `f` with `quantities =
  [:erased, :present]` re-erases from a 1-arg application down to a bare
  `{:global, f}` head with no args). The ctor-only differential and catalog
  in this section do not exercise this path at all. §5/§9 must add a
  parallel app-head selective-drop catalog entry (a `{:global, name}`
  application against a def with mixed quantities) rather than assuming
  ctor coverage transfers.
- **Structural validity preservation:** `Cure.Core.Term.term?(t) ⟹
  Term.term?(erase(env, t))` — erasure yields a structurally well-formed Core
  term. (Full **kernel** acceptance-at-a-runtime-type is a non-goal — an erased
  term is a non-dependent runtime form that need not re-typecheck at the original
  dependent type; the umbrella's "where a runtime type applies" hedge. V4a asserts
  structural validity, the checkable invariant.) Violation `{:erase_ill_formed, t}`.
  Verified: `Term.term?/1` (`lib/cure/core/term.ex:51`) is a shape-only check
  (node arities, universe-level bound, non-negative de Bruijn indices) with no
  arity constraint tying a `{:ctor, name, args}` node's `length(args)` to the
  family's declared telescope — so it holds trivially for `erase`'s output
  regardless of how many/which positions were dropped (including the
  idempotence hazard above: `{:ctor, c, []}` is still `term?/1 == true`).
  This property is real but weak; it will not by itself catch the
  idempotence or selective-drop defects above.

### V4b — `Relevance.check/4` (known-label differential; oracle = construction)

- **Relevant-use rejection (soundness):** a body that **by construction** uses an
  `:erased` binder at a relevant site must be **rejected** —
  `check(env, name, qs, body) == {:error, {:erased_used_relevantly, %{site: s}}}`
  for the intended site `s`. A `:ok` on such a body is
  `{:violation, {:relevance_unsound, site}}` — an erased binder leaking into
  runtime-relevant position, exactly the zero-footprint hole the check exists to
  prevent. One catalog entry per site (`:returned`, `:present_arg`, `:scrutinee`,
  `:applied`).
- **Clean acceptance (control):** a body that uses its erased binder only in
  erased positions (or not at all) must be accepted (`:ok`), so rejection is
  use-specific, not a blanket `:error`. A `{:error, …}` here is
  `{:violation, {:clean_body_rejected, name}}` (a construction-sanity assertion,
  per the V5 accept-control precedent).

## 4. Assay & injectable seam

New module `Antigen.Assays.Erasure` with `run/1` → `run/2` (op-map seam), mirroring
`Antigen.Assays.{Elab,Normalizer,Unifier,TotalityClosureAssay}`. Four assay ids:

| id | engine | property | oracle |
|---|---|---|---|
| `erasure/idempotent` | `Erase` | `erase∘erase == erase` (ctor **and** app-head) + hole preservation | intrinsic |
| `erasure/selective` | `Erase` | keeps exactly `:present` ctor **and** app-head positions | `ctor_quantities` / def `quantities` |
| `erasure/wellformed` | `Erase` | `term?(t) ⟹ term?(erase t)` | `Term.term?` |
| `relevance/soundness` | `Relevance` | erased-used-relevantly ⟹ rejected | construction |

No `@assay_fuel`/`Conv` — `erase`/`has_hole?`/`check` are static structural walks
that terminate on their own; no term is evaluated.

**Op-map** (`@real`), injecting the **code-under-test** at the assay boundary:

```elixir
%{
  erase: &Cure.Elab.Erase.erase/2,
  has_hole?: &Cure.Elab.Erase.has_hole?/1,
  ctor_quantities: &Cure.Core.Inductive.ctor_quantities/2,
  get_def: &Cure.Core.Env.get_def/2,         # app-head selective-drop oracle (§3)
  term?: &Cure.Core.Term.term?/1,            # verified name/arity (lib/cure/core/term.ex:51) — NOT `valid?/1`
  relevance_check: &Cure.Elab.Relevance.check/4
}
```

Negative controls prove each assay load-bearing:
- `erasure/idempotent`: an `erase` stub wrapping its output in an extra ctor each
  call (never a fixpoint) → `{:erase_not_idempotent,…}`; and a stub returning a
  `{:hole,_}` on a hole-free input → `{:hole_introduced,…}`.
- `erasure/selective`: an `erase` stub that drops a `:present` position (or keeps
  an `:erased` one) → `{:wrong_positions_kept,…}`, for BOTH the ctor differential
  (injected via a `ctor_quantities` the assay compares against, kept real; the
  `erase` op is the weakened one) and the app-head differential (injected via
  `get_def`, kept real, against a weakened `erase`).
- `erasure/wellformed`: an `erase` stub returning a malformed term → `{:erase_ill_formed,…}`.
- `relevance/soundness`: a `relevance_check` stub returning `:ok` on a
  relevantly-using body → `{:relevance_unsound,…}`.

## 5. Generator

New module `Antigen.Generators.ErasureTerm` producing **fixed catalogs** (the
established fixed-catalog reconciliation — no Corpus/Coverage surgery; a lightweight
`:erasure_term` challenge kind, typespec-only, wired via `assay_module/1` + a
dedicated test):

- `erase_challenges/0` — Core terms + an env registering a ctor with a **mixed**
  quantity vector so `erase`'s selective drop is actually exercised (a ctor with
  an all-`:present` vector would make selective-drop vacuous), AND a global def
  (via `Env.add_def/5`) with a mixed **`quantities`** list so the app-head path
  (§3) is exercised too — a ctor-only catalog misses that surface entirely.
  Covers idempotent / selective / wellformed ids.
  **Ordering requirement (see §3 idempotence hazard):** the ctor catalog must
  include AT LEAST ONE case where an `:erased` position precedes a kept
  `:present` position (e.g. `[:erased, :present]`, or a shape mirroring the
  production `seq` ctor's `[:erased×5, :present×2]` from
  `test/cure/elab/erase_test.exs`) — a catalog built only from `[:present,
  :erased]`-style (present-before-erased) orderings will NOT exercise the
  known idempotence hazard and would give false confidence. Same requirement
  applies to the app-head def-quantities catalog (identical hazard, verified
  in §3).
  Registration mechanism (open item #1, resolved): `Generators.SigMenu.env_of/1`
  is NOT itself an example of mixed quantities — its `Inductive.ctor/3` calls
  omit `quantities` (defaulting to all-`:present`). The correct template is
  `Inductive.declare/2` + `Inductive.ctor/4` (explicit `quantities` list,
  arity-unchecked against the arg telescope — verified in
  `lib/cure/core/inductive.ex:159-162`); `Antigen.Challenge.from_pieces/7`
  (`lib/antigen/challenge.ex:260`) already exercises the same explicit-`quantities`
  constructor family (there via the 5-arity `Inductive.ctor/5`, which additionally
  threads `result_params`) to reconstruct banked ctors with custom quantities,
  confirming the mechanism is already load-bearing elsewhere in Antigen.
- `relevance_challenges/0` — Core bodies + `quantities` (with at least one
  `:erased` binder) for each of the four sites (`:returned`, `:present_arg`,
  `:scrutinee`, `:applied`), plus one clean-body control. Reuse
  `Antigen.Generators.ElabErasure`'s known relevant-use constructions where a
  Core-level body can be lifted from them (open item #2).

## 6. Invariants (what must never regress)

- No `Cure.Core.*`, `Cure.Elab.*` edits — reached read-only through the op-map. No
  `:meck`, no new dependency.
- `Antigen.Assays.Erasure` contains no literal `StreamData` token (the
  `architecture_test` grep — banked from V1's Stage-5 trip; comments too).
- Assay `run/1,2` returns only `:ok | {:violation, term()}` (matches the `@spec`
  and `Runner.replay_one/1`/`explore/1`'s no-catch-all dispatch). V4's
  incompleteness/reach directions are out of scope.
- The catalog re-checks `:ok`/expected-verdict under the real ops (a real
  infection ⟹ STOP and report; do not weaken a test). In particular, if the
  real `erase` keeps an `:erased` position or drops a `:present` one, that is
  a genuine V4a finding — report it. **This is not merely hypothetical for
  V4:** §3/§9-2 already trace, by hand, a concrete case (`erase`'s `:ctor`
  clause under an erased-before-present quantity ordering) where the real
  `erase` is expected to fail this exact check on first execution. That
  catalog entry is deliberately included anyway — the "whole catalog clean"
  bar is the target state, and an entry failing on arrival is itself the
  STOP-and-report outcome this bullet describes, not evidence the entry or
  the property is wrong.
- New generator atoms added to `Challenge.@known_atoms` (V5's §8-5 lesson).

## 7. Non-goals

- No fix to `Erase`/`Relevance` (V4 *finds*; a surfaced infection is reported, not
  patched, without separate authorization).
- No duplication of the existing surface-program `elab/erasure` assay (which tests
  the relevance rule end-to-end through elaboration) — V4b tests `Relevance.check/4`
  directly on Core bodies.
- **No** kernel-acceptance-at-runtime-type differential for `erase` (an erased term
  is a non-dependent runtime form that need not re-typecheck at the original
  dependent type; V4a asserts structural `Term.term?/1` instead — §3).
- No auto-promotion or any change to the locked `{0,ω}` semantics — V4 tests the
  decision as locked, it does not revisit it.
- No random term fuzzer — a curated fixed catalog (elab pattern).
- No SMT (that is V6).

## 8. Open items (for the plan / review to pin)

1. **Ctor/def-quantity registration in the generator (resolved — see §5).**
   `Inductive.ctor/4` (explicit `quantities`, no arity check against the arg
   telescope — `lib/cure/core/inductive.ex:159-162`) plus `Inductive.declare/2`
   registers a mixed-quantity ctor; `Env.add_def/5`'s `quantities` param
   (`lib/cure/core/env.ex:40-51`) does the same for the app-head path. Remaining
   for the plan: pick concrete quantity vectors satisfying the §3/§5 ordering
   requirement (at least one `:erased`-before-`:present` case) for BOTH surfaces.
2. **Core-body relevant-use construction for each site (verified constructible
   for all four).** Pin the exact Core `body` term (with de Bruijn `{:var, k}`
   referencing an `:erased` binder) that triggers each `Relevance` site —
   traced against `walk/4`:
   - `:returned` — `body = {:var, k}` directly (the initial call is
     `walk(body, length(quantities), :returned, st)`).
   - `:applied` — `body = {:app, {:var, k}, arg}` (any `arg`); the `:app`
     clause's `with :ok <- walk(head, depth, :applied, st) do …` walks the
     head first and short-circuits on its error, so an erased var at the
     head position reports `:applied` regardless of what `arg` is — the
     argument is never reached.
   - `:present_arg` — `body = {:app, {:global, g}, {:var, k}}` with `g`
     registered in `env` (`Env.add_def`) with `quantities` marking that
     position `:present`; or the `:ctor` form with `Inductive.ctor_quantities`
     marking a `:present` position, reusing the §5/open-item-#1 registration.
   - `:scrutinee` — `body = {:case, {:var, k}, motive, branches}` (`branches`
     may be `[]`; the scrutinee walk fires before any branch is inspected).
   `quantities` is a flat list indexed by parameter position (telescope
   order); `check/4` maps position `p` to de Bruijn level via
   `level = depth - 1 - i` with initial `depth = length(quantities)` — verified
   against `relevance.ex:62-76,80-88`.
3. **`Term.term?/1` (resolved).** The structural-validity predicate in
   `lib/cure/core/term.ex:51` is `term?/1`, NOT `valid?/1` — there is no
   `valid?` function in that module. Use `Cure.Core.Term.term?/1` throughout
   the `erasure/wellformed` op-map and the `term?(t) ⟹ term?(erase t)` guard
   (only assert on catalog terms that are themselves `term?`).
4. **Challenge kind + atoms.** Add a `:erasure_term` kind (typespec-only) unless
   `:elab_program`'s payload can carry a Core term + env (it cannot — it carries
   surface source); add every generated ctor/def/binder name to `@known_atoms`.
   Verified: `Challenge.new/1` uses `struct!` with no runtime `kind` validation
   (`lib/antigen/challenge.ex:87-88`), so adding the atom to the `@type kind`
   union is enough there — but `Runner.assay_module/1` (`lib/antigen/runner.ex`)
   has NO catch-all clause (unmatched assay ids raise `FunctionClauseError`), so
   the plan must add explicit clauses for all four new assay ids, consistent
   with §5's "wired via `assay_module/1`" note.

## 9. Test catalog (for the plan — §5 of the plan will expand each)

1. V4a idempotent baseline (ctor, present-before-erased ordering): `erase(erase(t)) == erase(t)` on a mixed-quantity ctor term → `:ok`.
2. V4a idempotent baseline (ctor, **erased-before-present ordering — the §3-verified hazard shape**, e.g. `[:erased, :present]` or the `seq`-mirroring shape): `erase(erase(t)) == erase(t)`. **This entry is expected to legitimately FAIL against the real `erase`** (§3 traces the exact counterexample) — per §6, that is not a broken test, it is V4a doing its job; the implementer reports the finding rather than weakening or dropping this entry. This is the entry that makes the idempotence property non-vacuous — without it, only the "lucky" ordering in #1 is exercised.
3. V4a idempotent baseline (app-head, `{:global, name}` with mixed def `quantities`, both orderings as in #1/#2): same property, second surface (§3) — the erased-before-present sub-case here is, like #2, **expected to legitimately FAIL** against the real `erase` (§3 traces this exact app-head counterexample: `quantities = [:erased, :present]` re-erases a 1-arg application down to a bare `{:global, f}` with no args); the present-before-erased sub-case is expected to pass.
4. V4a hole-preservation baseline: hole-free term stays hole-free → `:ok`.
5. V4a idempotent negative control: wrapping `erase` stub → `{:erase_not_idempotent,…}`.
6. V4a hole negative control: hole-introducing `erase` stub → `{:hole_introduced,…}`.
7. V4a selective baseline (ctor): erase keeps exactly the `:present` ctor positions → `:ok`.
8. V4a selective baseline (app-head): erase keeps exactly the `:present` positions of the callee's def `quantities` → `:ok`.
9. V4a selective negative control: `erase` stub dropping a `:present` position → `{:wrong_positions_kept,…}` (both surfaces).
10. V4a wellformed baseline: `term?(erase t)` on a `term?` `t` → `:ok`.
11. V4a wellformed negative control: malformed-output `erase` stub → `{:erase_ill_formed,…}`.
12. V4b relevance baseline: one rejected body per site (`:returned/:present_arg/:scrutinee/:applied`) → `{:error, {:erased_used_relevantly, %{site: s}}}` for the intended site `s` (a body accepted here — an `:ok` — is the violation, `{:violation, {:relevance_unsound, site}}`, per §3).
13. V4b clean-body control: erased binder used only in erased position → accepted → `:ok`.
14. V4b relevance negative control: `:ok`-returning `relevance_check` stub on a relevant body → `{:relevance_unsound,…}`.
15. Generator+wiring: each catalog non-empty & correctly tagged; `Runner.replay_one/1` dispatches all four ids and every entry produces its expected verdict — `:ok` for baselines/controls, the documented `{:error, …}` for V4b rejection baselines, EXCEPT items #2 and the erased-before-present sub-case of #3, which (per §6) are expected to surface a genuine `{:violation, …}` on first execution — that is the intended outcome, to be reported per §6's STOP rule, not treated as a wiring failure.

## 10. Next (umbrella roadmap)

After V4: **V6 SMT lint** (framed by the locked "Z3 out of the TCB" decision) is the
last umbrella vertical. **No auto-merge.**

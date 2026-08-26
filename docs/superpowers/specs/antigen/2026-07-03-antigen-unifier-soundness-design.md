# Antigen V2 — Unifier Soundness — Design

**Status:** design (Stage 0, autopilot Phase 3) · **Date:** 2026-07-03 · **Branch:** `autopilot/antigen-tier-b`
**Umbrella:** `2026-07-03-antigen-untrusted-machinery-design.md` §V2 · **Predecessors:** V3 (elab soundness), V1 (normalizer soundness)

## 1. Goal

Extend Antigen to the two **untrusted** unification engines, per the operator's
locked scope (umbrella open-item #4): **both** `Cure.Elab.Unify` (Core terms with
metavariables — feeds elaboration) and `Cure.Types.Unify` (surface types — solves
implicit arguments). A unifier that reports `{:ok, …}` with a substitution that
does **not** actually make the two sides equal is a soundness hole: the elaborator
trusts the solution, assembles a core term around it, and — while the kernel
*re-checks* the assembled term (so a wrong solve is often caught downstream) — the
unifier is exactly the kind of untrusted machinery this initiative exists to
pin independently.

The two engines are one vertical but have **different oracle situations**, which
drives a two-family split:

- **V2a — `Elab.Unify`** operates on Core terms and the trusted `Cure.Core.Conv`
  is a genuine external oracle for "do these two terms unify." → a real
  **differential**.
- **V2b — `Types.Unify`** operates on surface types and has **no** trusted
  external equality (it accepts non-syntactic matches: `:any` widening,
  `int`/`float` widening, refinement-stripping, named/record/adt matching). No
  kernel oracle applies. → **intrinsic algebraic laws + a fixpoint
  self-consistency** check (the same oracle-free tactic V1c used on the
  untranslatable fragment).

## 2. Targets (verified against source)

### `Cure.Elab.Unify` (`lib/cure/elab/unify.ex`)

- `unify(t1, t2, ctx, sig \\ nil) :: {:ok, MetaCtx.t()} | {:error, term()}` —
  first-order unification of Core terms bearing metavariables `{:meta, id}`,
  refining `ctx`. With `sig` (a `Cure.Core.Env`), closed meta-free syntactic
  failures fall back to δ-capable `Conv` (a documented *completeness* improvement
  that itself rests on `Conv`).
- `zonk(t, ctx) :: uterm()` — finalises a term by substituting every solution away.
- `Cure.Elab.MetaCtx`: `new/0`, `fresh/1 :: {t, id}`, `solution/2`, `solved?/2`.
- Metavariables live only in the elaborator; a term reaching the kernel must be
  fully zonked. Error tags observed: `{:cannot_unify,…}`, `{:arity_mismatch,…}`,
  `{:occurs_check, id, t}`, `{:escaping_variable, id}`.

### `Cure.Types.Unify` (`lib/cure/types/unify.ex`)

- `unify(t1, t2) :: {:ok, subst, trace} | {:error, reason, trace}`; `unify/3`
  (starting subst); `unify_many/1`. `subst :: %{String.t() => type}`.
- `apply_subst(type, subst) :: type` — substitutes solved vars through a type.
- Flex variables are `{:type_var, name}` (string `name`), occurs-checked in `bind`.
- **Non-syntactic accepts** (these are why no external structural oracle exists):
  `do_unify(t, t) → reflex`; `{:refinement, base, _, _}` stripped on either side;
  `:any` matches anything; `{:int, :float} → widening`; `{:named, a}` matches a
  `{:record, key, …}`/`{:adt, key, …}` when `downcase(a) == to_string(key)`.

## 3. Properties

### V2a — `Elab.Unify` (differential, oracle = `Conv`)

- **`unify/soundness` (the master property):** for **closed** `t1, t2` (no free
  `{:var,_}` — metavariables are fine, dangling de Bruijn references are not), if
  `unify(t1, t2, ctx, sig) = {:ok, ctx'}`, then `zonk(t1, ctx')` and
  `zonk(t2, ctx')` are `Conv`-convertible:
  `Conv.conv?(zonk(t1,ctx'), zonk(t2,ctx'), [], 0, sig) == true`. A `{:ok, …}`
  whose zonked sides are **not** convertible is `{:violation, {:unify_unsound,…}}`.
  This is the honest soundness question the δ-fallback's moduledoc waves at
  ("a wrong accept here is caught downstream") — V2a checks it *here*. The
  closedness precondition is not optional bookkeeping: `Conv.conv?(_,_,[],0,_)`
  compares under an **empty** value environment, so a free `{:var,i}` has no
  binding to resolve against and the comparison is meaningless (possibly
  crashing) rather than merely imprecise. The real code enforces exactly this
  before ever making this call — `delta_convertible?` (unify.ex:165-172) gates on
  `Cure.Core.Term.closed?(z1) and Cure.Core.Term.closed?(z2)`. The §5 catalog's
  `t1`/`t2` payloads for `unify/soundness` and `unify/intrinsic` MUST therefore be
  closed terms end-to-end (no catalog entry may contain a `{:var,_}` node) — a
  requirement the plan should state explicitly, not leave implicit.
- **`unify/intrinsic` (no oracle, same closedness precondition as above):**
  - *occurs-check:* no returned solution is cyclic — for every solved `?id`,
    `id` does not occur in `force`-resolved `solution(ctx', id)`. `Unify.occurs?/3`
    is **private** (`defp`), so — exactly as with meta-closed below and open item
    #5 — the assay needs its own independent occurs-check helper built on the
    op-map (`eu_solution`), not a call into `Elab.Unify`'s copy.
  - *idempotent zonk:* `zonk(zonk(t, ctx'), ctx') == zonk(t, ctx')` (checked for
    both `t1` and `t2`).
  - *well-scoped / meta-closed:* for catalog entries where every metavariable in
    `t1`/`t2` is unified against a genuinely different term — **never** a meta
    unified reflexively against an occurrence of itself, since
    `do_unify({:meta,id}, {:meta,id}, ctx, _sig, _depth)` returns `{:ok, ctx}`
    **unchanged** without ever calling `solve/4`, so such a meta legitimately
    stays unsolved and is not a counterexample — if `unify` succeeds, every such
    metavariable is solved: `zonk(t1, ctx')` and `zonk(t2, ctx')` contain no
    `{:meta,_}` node. (Scoping this to meta-**free** inputs, as an earlier draft
    did, makes the check vacuous instead: `solve`/`escapes?`/`strengthen` only
    ever run when a meta is actually being solved, so a meta-free-input version
    of this property never exercises that scope machinery at all. The catalog's
    proposed entries — bare metavar solve, structural ctor/data match, binder
    case — all unify a metavariable against a non-metavariable structure, so none
    of them hits the reflexive-meta exclusion above; no catalog change is needed,
    only this property-text caveat.)

    **Naming note vs. the umbrella sketch:** the umbrella
    (`2026-07-03-antigen-untrusted-machinery-design.md` §V2) describes
    "well-scoped" as *"a solution for `?m` mentions no variable out of `?m`'s
    context"* — a direct scoping check on the raw stored solution, distinct from
    the meta-elimination check above. That raw-scoping property is enforced
    internally by `solve/4`'s `escapes?` gate *before* a solution is ever stored
    (a successful store already implies it held), so a black-box assay can't
    observe a violation directly without re-implementing `escapes?`; a broken
    `escapes?` that let a mis-scoped solution through would instead surface as a
    `unify/soundness` (§3 first bullet) violation once the resulting term is
    zonked and compared — that master differential is what actually covers the
    umbrella's intent here. This bullet is the narrower, directly-observable
    meta-elimination check; it is not a restatement of the umbrella's wording.

### V2b — `Types.Unify` (intrinsic + fixpoint, no external oracle)

- **`unify_types/fixpoint` (self-consistency, the soundness proxy):** if
  `unify(t1, t2) = {:ok, s, _}`, then re-unifying the substituted sides needs no
  new work: `unify(apply_subst(t1, s), apply_subst(t2, s), s) = {:ok, s', _}` with
  `s' == s`. A solution that does not actually resolve its own constraint (new
  bindings appear, or the re-unification fails) is `{:violation, {:solution_unstable,…}}`.
- **`unify_types/intrinsic` (no oracle):**
  - *occurs-check:* a cyclic constraint (`{:type_var,"a"}` vs `{:list,{:type_var,"a"}}`)
    yields `{:error, …}`, never `{:ok, …}`.
  - *idempotent substitution:* `apply_subst(apply_subst(t, s), s) == apply_subst(t, s)`.
  - *solved-var elimination:* `apply_subst(t, s)` contains no `{:type_var, n}` for
    any `n ∈ Map.keys(s)`.

## 4. Assay & injectable seam

New module `Antigen.Assays.Unifier` with `run/1` → `run/2` (op-map seam), mirroring
`Antigen.Assays.{Elab,Normalizer}`. `@assay_fuel 500_000` wraps every `Conv` call
in `Cure.Core.Normalise.with_fuel/2` (defensive; these terms are first-order and
terminating). Four assay ids:

| id | engine | property | oracle |
|---|---|---|---|
| `unify/soundness` | `Elab.Unify` | zonked sides `Conv`-equal | `Conv` |
| `unify/intrinsic` | `Elab.Unify` | occurs / idempotent-zonk / meta-closed | none |
| `unify_types/fixpoint` | `Types.Unify` | re-unify substituted = no new bindings | none |
| `unify_types/intrinsic` | `Types.Unify` | occurs / idempotent-apply / var-elim | none |

**Op-map** (`@real`), injecting the **code-under-test** at the assay boundary (the
Run C sensitivity pattern; oracle ops stay real):

```elixir
%{
  # Elab.Unify (V2a)
  eu_unify: &Cure.Elab.Unify.unify/4,
  eu_zonk:  &Cure.Elab.Unify.zonk/2,
  eu_solution: &Cure.Elab.MetaCtx.solution/2,
  conv:     &Cure.Core.Conv.conv?/5,       # trusted oracle
  # Types.Unify (V2b)
  tu_unify: &Cure.Types.Unify.unify/3,
  tu_apply: &Cure.Types.Unify.apply_subst/2
}
```

Negative controls inject a broken code-under-test op and prove each assay is
load-bearing:
- `unify/soundness`: an `eu_unify` stub returning `{:ok, ctx}` **unchanged** on a
  problem whose sides only unify *after* a solve → zonked sides not `Conv`-equal →
  caught.
- `unify/intrinsic`: an `eu_solution` stub returning a **cyclic** term for a solved
  id → occurs violation.
- `unify_types/fixpoint`: a `tu_unify` stub returning `{:ok, s, []}` with a subst
  that leaves the constraint unsatisfied → re-unification produces a new binding /
  error → `{:solution_unstable,…}`.
- `unify_types/intrinsic`: a `tu_unify` stub accepting a cyclic constraint → occurs
  violation; a `tu_apply` stub that leaves a solved var in place → var-elim
  violation.

## 5. Generator

New module `Antigen.Generators.UnifyProblem` producing **fixed catalogs** (the
elab/normalizer reconciliation — no corpus/Coverage surgery; a new lightweight
`:unify_problem` challenge kind, typespec-only, wired via `assay_module/1` and a
dedicated test):

- `elab_soundness_challenges/0` / `elab_intrinsic_challenges/0` — payload
  `%{t1, t2, ctx, sig}` over Core terms. Every entry's `t1`/`t2` MUST be closed
  (no free `{:var,_}` — see §3's closedness precondition); in particular the
  binder case's domain/codomain terms must be picked closed (e.g. ctor/global
  terms), not variable references, or the entry falls outside what
  `Conv.conv?(_,_,[],0,_)` can validly compare. Catalog covers: a bare metavar
  solve (`{:meta,0}` vs `{:ctor, :S, [{:global, :z}]}`), a structural ctor/data
  match driving nested solves, a binder case (`{:pi, d, {:meta,0}}` vs
  `{:pi, d, c}`, `d`/`c` closed), and a no-metavar reflexive pair. `ctx` seeded
  via `MetaCtx.new/0` with literal `{:meta, N}` ids (see open item #2 — no
  `fresh/1` threading needed); `sig` is `nil` for the syntactic cases (a
  δ-fallback case may pass a small env).

  **Accepted scope limit on the binder case:** forcing `d`/`c` closed (required
  by the closedness precondition above) also forces `strengthen`'s shift to be
  the identity — for a closed whole term, any variable surviving `strengthen`
  would have to be free relative to the *entire* term, which a closed term
  cannot have. So this catalog entry exercises `do_unify`'s Π-codomain recursion
  and `escapes?`'s no-false-positive path, but **not** genuine free-variable
  re-leveling under a solved meta (the `{:var,4}` vs `{:var,5}` mis-levelling
  regression `test/cure/elab/higher_order_unify_test.exs` guards at the
  elaborator level) — that scenario needs an *open* term under an ambient
  context, which `Conv.conv?(_,_,[],0,_)` cannot validly compare (§3). This is
  an accepted first-cut gap of the closed-term differential, not something to
  work around by relaxing closedness — don't "improve" the binder case with an
  open codomain to chase that coverage; it would silently break the property
  (§3's closedness precondition), not extend it.
- `types_challenges/0` — payload `%{t1, t2}` over surface types. Catalog covers:
  `{:type_var,"T"}` vs `:int`; `{:list,{:type_var,"T"}}` vs `{:list, :int}`;
  `{:tuple,[{:type_var,"A"},{:type_var,"B"}]}` vs `{:tuple,[:int,:string]}`; a
  refinement-stripped case; an `:any`-widening case; an int/float-widening case
  (`unify(:int, :float, …)` — note the direction: `do_unify` only implements
  `(:int, :float)`, there is **no** `(:float, :int)` clause in
  `lib/cure/types/unify.ex`, so the reverse pair errors instead of widening); a
  named-vs-record/adt matching case (e.g. `{:named, "foo"}` vs
  `{:record, :foo, fields}`); and (for the occurs control) a hand-built cyclic
  pair used only in the negative test, never the clean catalog. The int/float and
  named/record-adt cases are not optional flourishes — §2 names both as reasons
  "no external structural oracle exists" for `Types.Unify`, so the fixpoint
  catalog must actually exercise them, not just the type-var-binding and
  refinement-stripping paths.

## 6. Invariants (what must never regress)

- No `Cure.Core.*`, `Cure.Elab.*`, or `Cure.Types.*` edits — both engines reached
  read-only through the op-map. No `:meck`, no new dependency.
- `Antigen.Assays.Unifier` contains no literal `StreamData` token (the
  `architecture_test` grep — a lesson banked from V1's Stage-5 trip; keep the word
  out of moduledoc/comments too).
- Assay `run/1,2` returns only `:ok | {:violation, term()}` (matches the `@spec`
  and both `Runner.replay_one/1` and `Runner.explore/1`'s no-catch-all dispatch —
  no third outcome kind). Incompleteness/reach-gaps are out of scope here (a
  `Conv`-equal pair `Elab.Unify` rejects is not a soundness violation).
- The whole clean catalog re-checks `:ok` under the real ops (a real infection
  ⟹ STOP and report; do not weaken a test).

## 7. Non-goals

- No fixes to either unifier (V2 *finds*; a surfaced infection is reported, not
  patched, without separate authorization).
- No higher-order / Miller-pattern unification coverage (a documented `Elab.Unify`
  extension point; out of first-order scope).
- No random unify-problem fuzzer — a curated fixed catalog (elab pattern). A
  generator-expansion follow-on could widen coverage.
- No surface-type external oracle invented for `Types.Unify` — V2b stays intrinsic
  + fixpoint by design (§1).
- No SMT (that is V6).
- No dedicated **determinism** property, despite the umbrella sketch
  (`2026-07-03-antigen-untrusted-machinery-design.md` §V2) listing it: both
  `Cure.Elab.Unify.unify/4` and `Cure.Types.Unify.unify/2,3` are pure functions
  over explicitly-threaded state (`MetaCtx`/`subst`) with no hidden
  non-deterministic source found on inspection (no `:rand`, no
  `System.unique_integer/system_time`, no `Process`/`:ets` reads) — a
  same-inputs-twice check would be a tautology for the current implementation
  and add no bug-catching value. Revisit only if either engine grows a genuine
  non-deterministic dependency.

## 8. Open items (for the plan / review to pin)

1. **`Conv.conv?` arg shape for zonked Core terms** — `conv?(z1, z2, [], 0, sig)`
   is the right call for closed first-order terms (the `Elab.Unify` δ-fallback
   itself calls exactly `Conv.conv?(z1, z2, [], 0, sig)`, so this is grounded —
   the plan should cite that call site — unify.ex:171). This is closedness-gated
   in the real code (`Term.closed?(z1) and Term.closed?(z2)`, unify.ex:170); §3
   now states that gate as a hard precondition on the property, not an
   implementation nicety, so the plan must enforce it on every `unify/soundness`
   and `unify/intrinsic` catalog entry (§5), not merely note it here.
2. **`MetaCtx` construction in the generator** — tracing `MetaCtx`/`Unify` shows
   `fresh/1` is never called internally by `unify`/`zonk`/`solve`/`occurs?` (they
   only read and write metavariables by the literal id already present in the
   term); nothing threads or allocates new ids during a run. So the simplest
   correct approach — and the one the plan should pin — is literal `{:meta, N}`
   terms in the catalog (`N` hand-picked distinct per multi-meta entry) paired
   with `ctx = MetaCtx.new()`; `fresh/1` threading is unnecessary machinery for a
   static catalog with no further meta allocation during the assay run.
3. **`tu_unify` arity** — resolved: `unify/2(t1, t2)` is exactly
   `do_unify(t1, t2, %{}, [])` and `unify/3(t1, t2, subst)` is exactly
   `do_unify(t1, t2, subst, [])` — identical when `subst = %{}`. So the assay
   uses `unify/3` uniformly via `tu_unify` in the op-map: the baseline call
   passes `%{}` explicitly, and the fixpoint re-unify call passes the real `s`.
   No separate call to `unify/2` is needed anywhere.
4. **Fixpoint equality of substitutions** — resolved by direct trace: `s' == s`
   (a plain map compare) holds across every non-syntactic accept clause —
   type-var bind, `:any` widening, `:int`/`:float` widening, refinement-strip,
   named-vs-record/adt match, and the list/tuple/fun/adt/map structural
   recursions — because `apply_subst` either leaves an already-ground/matched
   pair untouched or fully resolves a bound var to its (already-final) value
   before re-unify sees it, so the re-unify call retraces the identical clause
   and returns the same map. No spurious inequality risk found; no further plan
   pinning needed here.
5. **Meta-closed / occurs-check independence for V2a** — both the meta-closed
   check ("zonked sides meta-free") and the occurs-check use engine internals
   that are `defp`-private (`meta_free?/1` and `occurs?/3` respectively, both in
   `lib/cure/elab/unify.ex`); the plan supplies independent local
   implementations for **both**, not just meta-closed. The occurs-check helper
   must read solutions through the op-map's `eu_solution` (not
   `MetaCtx.solution/2` directly) so the negative control (a cyclic
   `eu_solution` stub) is actually observed by it.

## 9. Test catalog (for the plan — §5 of the plan will expand each)

1. V2a soundness baseline (`?0` vs `S z`, closed) → `:ok`.
2. V2a soundness structural (nested ctor solve, closed) → `:ok`.
3. V2a soundness negative control (identity `eu_unify` stub) → `{:unify_unsound,…}`.
4. V2a intrinsic baseline: occurs + idempotent zonk (both `t1`, `t2`) + meta-closed
   on a metavariable-**bearing** entry (not the no-metavar reflexive pair — that
   would leave meta-closed vacuous) → `:ok`.
5. V2a intrinsic occurs negative control (cyclic `eu_solution`, via the
   independent occurs-check helper reading through `eu_solution`) → `{:occurs,…}`.
6. V2b fixpoint baseline (`T` vs `int`; `list(T)` vs `list(int)`; `unify(:int,
   :float, …)` widening in that order; a named-vs-record/adt match) → `:ok`.
7. V2b fixpoint negative control (unstable `tu_unify` stub) → `{:solution_unstable,…}`.
8. V2b intrinsic baseline (occurs rejects cyclic; idempotent apply; var-elim) → `:ok`.
9. V2b intrinsic var-elim negative control (leaky `tu_apply` stub) → `{:var_not_eliminated,…}`.
10. Generator+wiring: each catalog non-empty & correctly tagged; `Runner.replay_one/1`
    dispatches every `unify*/…` id and the whole clean catalog is `:ok`.

## 10. Next (umbrella roadmap)

After V2: V5 totality-closure, V4 erasure/relevance, V6 SMT lint. **No auto-merge.**

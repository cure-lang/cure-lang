> **SUPERSEDED (2026-07-03)** by `2026-07-03-whnf-unification-design.md`. The
> Task-1 risk gate + a language cross-read showed the reachable gap is missing
> weak-head normalization before unification, not postponement (which flips no
> reachable verdict). Kept for history. Do not implement from this file.

# Postponed/Suspended Unification Constraints (#11) — Design Spec

**Date:** 2026-07-03
**Roadmap row:** #11 (Inference unification — postponed/suspended constraints)
**Layer:** E (untrusted elaborator) — `lib/cure/elab/unify.ex` + the elaborator's
per-definition kernel-handoff boundary. **No `lib/cure/core/*` change; no TCB.**
**Reference:** Abel & Pientka, "Extensions to Miller's Pattern Unification for
Dependent Types and Records," MSCS 2018 (`~/Downloads/unif_miller60.pdf`), plus a
cross-read of Idris2, Agda, and Lean4 constraint solvers (findings in §7).

---

## 1. Problem & goal

Cure's unifier (`Cure.Elab.Unify`) is **eager**: `unify/4` either solves a
metavariable now or fails (`{:ok, ctx} | {:error, reason}`). Two situations that
Idris/Agda *postpone and later solve* are today hard-rejected:

1. **Flex-flex** — both sides are metavariable-headed and neither is a Miller
   pattern (e.g. `?a x =? ?b y` where `x`/`y` are distinct bound variables that
   escape each other's pattern abstraction — verified today to fall through
   Miller solving on both sides and hard-fail; see §3.2's verification note on
   exactly how that failure currently arises). **Not** an example: two *bare*
   metavariables `?a =? ?b` already solve eagerly today (`do_unify_struct`'s
   `{:meta, id}, t` clause, unify.ex:240) — that case needs no postponement. The
   correct solution to a genuine flex-flex may become determined once some
   *other* constraint pins one side; eager failure loses that input.
2. **Weakly-rigid occurs** — a metavariable occurs in its own candidate solution,
   but only under another metavariable application or an eliminable position
   (`?a =? f(?a)` where `f` may cancel, `?a =? fst(?a, c)`). Such a constraint is
   *solvable* once the eliminable reduces away; only **strongly-rigid**
   occurrences (`?a =? S(?a)`, under a data constructor / type former) are truly
   cyclic. Cure's `Unify.occurs?` (unify.ex:382) rejects **any** occurrence — it
   is sound but over-rejects, costing reach.

**Goal.** Add a *constraint-postponement queue* with *retry-on-progress* so the
unifier can suspend a not-yet-solvable constraint, keep elaborating, retry the
queue to a fixpoint as metavariables get solved, and reject only if the queue
cannot be fully drained. Refine the occurs-check to postpone weakly-rigid
occurrences instead of failing them. This reaches inputs Idris accepts via
postponement.

**Non-goal for soundness.** All of this is E-layer. The trusted kernel re-checks
every elaborated term (`Unify.zonk/2` must produce a `{:meta,_}`-free term before
handoff), so optimistic postponement is a **completeness** concern only — a wrong
suspension/solve is caught downstream by the kernel. This mirrors the
conservative-fallthrough stance of the landed Miller solver (#10).

---

## 2. Success criterion & risk gate (FIRST task, gates everything)

The very first implementation task authors a **failing differential-oracle probe**:
a surface Cure program that `idris2 --check` **accepts** (via postponement) and
that Cure **currently rejects**. Concretely `postpone01_flex_flex` (§5).

- If such a probe is constructed and Cure rejects it while Idris accepts → the
  gap is real and oracle-measurable; proceed with the build.
- **If no surface Cure program can be made to trigger genuine flex-flex or
  weakly-rigid-occurs** that Idris accepts → the feature has **no
  oracle-measurable reach**. **HALT** and report (write `AUTOPILOT-STATE.md`),
  reconsidering scope, rather than building machinery no probe exercises.

This gate exists because earlier probing in this problem area was repeatedly
*confounded* (arity errors, general elaboration failures masquerading as the
target). The probe reason must be **verified** (dump the actual Cure rejection
reason via the throwaway-test pattern — `mix run` cannot be used because it
throws `unknown registry: Cure.Pipeline.Events.Registry`; a test-env module that
calls `Cure.Elab.Program.elaborate/1` and `IO.inspect`s the error works), and the
Idris verdict must come from the oracle, never hand-written.

---

## 3. Architecture — Option (A): MetaCtx queue + retry-all fixpoint drain

Chosen after cross-reading the three reference systems (§7). Rationale: Cure's
`MetaCtx` is **already an immutable threaded state** (a functional analogue of
Idris's global `UState`). Idris and Lean both store constraints in their threaded
state and drain at a definition boundary — Option (A). This needs **no 3-valued
`unify` result threaded through every caller** (Cure has many `unify` call sites);
callers stay `{:ok, ctx} | {:error, reason}`.

### 3.1 Storage — a queue field on `MetaCtx`

`MetaCtx` (unify.ex:12) today: `defstruct next: 0, solutions: %{}, types: %{}`.
Add a `constraints: []` field holding suspended equations:

```
constraints :: [ {a :: uterm(), b :: uterm(), depth :: non_neg_integer(),
                  sig :: term() | nil, reason :: atom()} ]
```

Each entry is a deferred `unify_d(a, b, ctx, sig, depth)` — the exact arguments
needed to retry it verbatim, plus a `reason` tag (`:flex_flex` |
`:weak_rigid_occurs`) for diagnostics. `depth` is captured because the two terms
were forced under `depth` binders; retry must re-enter at that depth (§3.4).

New `MetaCtx` helpers (all pure, alongside `put_solution/3`):
- `postpone(ctx, a, b, depth, sig, reason)` — append a constraint.
- `constraints(ctx)` — list them.
- `clear_constraints(ctx)` — return `{ctx_without, list}` for the drain loop.
- `put_constraints(ctx, list)` — replace the queue (drain writes back the
  still-unsolved remainder).

### 3.2 Postponement triggers (where `unify` suspends instead of failing)

Both live in `do_unify`/`do_unify_struct` (unify.ex:136–241) and in the two solve
paths. In every case the trigger **appends a constraint and returns `{:ok, ctx}`**
(Idris's optimistic model) rather than `{:error, …}`:

1. **Flex-flex.** In `do_unify_struct`, when both `t1` and `t2` are
   metavariable-headed (`{:meta,_}`-applied spines) and the Miller dispatch
   already fell through (neither side is a solvable pattern) → `postpone(…,
   :flex_flex)` instead of the structural mismatch error. Guard: at least one side
   must be genuinely a metavariable head (a solved meta is `force`d away first, so
   this only fires on *unsolved* metas).

   **Verification needed (plan task, same caveat as §3.3's shape mapping):**
   `do_unify_struct`'s existing `{:app, f1, x1}, {:app, f2, x2}` clause
   (unify.ex:253–255) recurses one argument layer at a time with **no spine-length
   reconciliation** — it does not first check "is the ultimate head of this whole
   spine a metavariable" before peeling an argument. For **equal-arity** spines
   (`?a x =? ?b y`) this recursion bottoms out at a bare-`{:meta,_}`-vs-bare-
   `{:meta,_}` sub-call, which `do_unify_struct`'s clause 2 (unify.ex:240–241)
   already solves eagerly and unconditionally (`?a := ?b`) — genuinely correct
   today, and **not** a flex-flex case needing postponement. For **unequal-arity**
   spines (the case that actually motivates this feature, e.g. a partial
   application on one side), the layer-by-layer recursion instead produces a
   sub-problem comparing a partially-applied meta against a shorter/bare one,
   which may spuriously solve or fail for reasons unrelated to the original
   two terms. The plan must locate (or add) a spine-head helper that walks the
   *whole* spine on both sides before this recursion begins, so the "both sides
   metavariable-headed" check in this bullet is a real, single decision point
   rather than an emergent side-effect of per-argument recursion; until verified,
   treat the exact trigger location as unconfirmed, and route Task 1's probe
   construction (§2) through the actually-implemented path.
2. **Weakly-rigid occurs.** `occurs?/3` (unify.ex:382) is refined into
   `occurs_rigidity/3 → :strong | :weak | :none` (§3.3). The two callers change:
   - `miller_solve` (unify.ex:159, occurs at :166): `:none` → solve as today;
     `:weak` → **fall through** to structural (which then postpones as flex-rigid,
     see below); `:strong` → `:fallthrough` (cyclic; ultimately unsolved).
   - `solve_strengthened` (unify.ex:334): `:none` → `put_solution`; `:weak` →
     `postpone(…, :weak_rigid_occurs)` returning `{:ok, ctx}`; `:strong` →
     `{:error, {:occurs_check, id, t}}` (unchanged hard failure).

   A **flex-rigid weak occurrence** (metavar vs rigid term where the metavar
   occurs weakly-rigidly in the rigid side) is postponed, not solved: it may
   become solvable after the interfering metavar resolves. **Same verification
   gap as bullet 1's note applies here too:** `solve_strengthened` (where the
   `:weak` → `postpone` branch actually lives, per the second sub-bullet above)
   is reached today only via `do_unify_struct`'s bare-`{:meta,id}`-vs-`t` clause
   (unify.ex:240–241) — i.e. when the metavariable side of the equation is
   *unapplied*. When `miller_solve` falls through on a genuine multi-argument
   Miller-pattern spine (`?a x1…xn`) whose *only* problem is a weak occurrence,
   the fallthrough lands in `do_unify_struct` with `t1` still spine-shaped, not
   bare — which, absent the same spine-head helper called for in bullet 1, will
   generally miss `solve_strengthened` entirely and hit the delta-convertible
   last-resort clause (unify.ex:282–288) instead, hard-failing rather than
   postponing. The plan's spine-head helper must route both this path and
   bullet 1's flex-flex path, or this paragraph's "postponed, not solved" claim
   only holds for **bare (unapplied)** metavariables, not for multi-argument
   patterns. This is narrower than bullet 1's gap, though: unlike flex-flex
   (which, per §1, is unreachable with bare metavariables — those already solve
   eagerly today), a genuine weakly-rigid occurrence is fully expressible with a
   **bare** metavariable (`?a =? f(?a)`, §1 example 2) and routes through the
   existing `{:meta,id}, t` → `solve` → `solve_strengthened` clauses without
   needing the spine-head helper at all. `postpone02_weak_rigid_occurs` (§5.2)
   should therefore be authored against the bare-metavariable case first; the
   multi-argument-pattern variant of weak-rigid occurs is real but not required
   for this probe, and can be deferred alongside pruning (§8) if it turns out to
   need the same spine-head work as bullet 1.

### 3.3 Occurs-check rigidity classification (`occurs_rigidity/3`)

Replaces the boolean `occurs?`. Walk `force(t, ctx)` tracking a rigidity mode
(`:strong` at entry, per Agda's `occursCheck` starting `StronglyRigid`):

- Hit `{:meta, ^id}` → return current mode (`:strong` or `:weak`).
- Hit `{:meta, _other}` → occurrences *inside its arguments* are `:weak`
  (metavar application is a flexible position — Agda `Flexible`/`WeaklyRigid`).
- Descend under a **data constructor** `{:ctor,_,args}` / **type former**
  `{:data,_,_,_}` / `{:pi,…}` / `{:sigma,…}` → arguments stay `:strong`
  (Agda `strongly`: under an inductive constructor stays StronglyRigid).
- Descend under an **eliminable / neutral** head — `{:app, f, x}` where `f` is
  **not** a constructor/data spine (application of a variable, global, or
  metavar), `{:fst,_}`, `{:snd,_}`, `{:prim,_,_}` → arguments become `:weak`
  (Agda `weakly`: args to variables/definitions are WeaklyRigid).
- Combine results by **strength**: `:strong` beats `:weak` beats `:none`
  (`:strong` if any strongly-rigid occurrence exists, else `:weak` if any weak
  occurrence, else `:none`).

The mapping to the Core term shapes must be verified against the actual
constructors used in `zonk`/`escapes?` (unify.ex:354–377 enumerates them:
`:var :meta :pi :lam :sigma :app :pair :fst :snd :eq :refl :prim :data :ctor`).
Classification of each shape as constructor/type-former (strong-preserving) vs
eliminable/neutral (weak-inducing) is fixed by that enumeration and pinned in the
plan; **no shape may be silently defaulted** — an unlisted shape is treated as
`:strong`-preserving (conservative: never under-reject into unsoundness, and the
kernel backstops regardless).

### 3.4 Retry driver — `drain_constraints/1` (retry-all fixpoint)

Idris/Lean style: **retry-all-while-progress**, no blocker-keying (Agda's
selective wakeup is deferred as premature at Cure's scale — §7, all three readers
concur). Signature `drain_constraints(ctx) :: {:ok, ctx} | {:error, reason}`:

```
drain(ctx):
  {ctx0, pending} = clear_constraints(ctx)
  if pending == []: return {:ok, ctx0}
  # retry each once; each may re-postpone (re-append) or solve or hard-fail
  ctx1 = ctx0
  for {a,b,depth,sig,_} in pending:
    case unify_d(a, b, ctx1, sig, depth):
      {:ok, ctx1'} -> ctx1 = ctx1'          # solved OR re-postponed (into queue)
      {:error, e}  -> return {:error, e}     # strong-rigid cycle / genuine mismatch
  {_, still} = clear_constraints(ctx1)  # peek remainder produced this round
  progress? = solved_count(ctx1) > solved_count(ctx0)   # ≥1 metavar newly solved
  cond:
    still == []          -> {:ok, ctx1}                  # fully drained
    progress?            -> drain(put_constraints(ctx1, still))  # loop
    true                 -> {:error, {:unsolved_constraints, still}}  # stalled
```

- **Progress metric.** A round makes progress iff the count of solved
  metavariables strictly increased (`map_size(solutions)`), i.e. a re-attempt
  pinned at least one meta. Re-postponing the same constraint with no new solution
  is *not* progress.
- **Termination.** Metavariables are finite and monotonically solved (a solution
  is never retracted). Each non-halting round solves ≥1, so the loop runs at most
  (number of metavariables) times. Guaranteed terminating — an explicit unit test
  asserts termination on a deliberately-stalled queue (`postpone04`).
- **Stall = reject.** A non-empty stalled queue is a clean `{:error,
  {:unsolved_constraints, …}}` (Lean's final strict no-postpone pass; Idris's
  `checkUserHolesAfter` → `CantSolveEq`). No optimistic acceptance of unsolved
  constraints.

### 3.5 Integration point — the per-definition boundary

**Verified prerequisite gap (must be resolved by the plan before this section's
call sites are actionable).** `MetaCtx` is **not currently threaded across a
whole top-level definition**. Every existing call site allocates its own
short-lived `MetaCtx.new()`, scoped to a single constructor/function
application's argument telescope, and discards it once that one application is
zonked/checked: `lib/cure/elab/elaborator.ex:3205,3321,3482,3575,3632` are the
five `MetaCtx.new()` sites, each consumed within one `Enum.reduce_while`/`reduce`
over one argument list and finalized by `finish_ctor_app`/`finish_global_app`
before returning plain Core terms (no `mctx` leaves that call). Neither
candidate call site below currently has an `mctx` in scope to drain:
- `lib/cure/elab/elaborator.ex:651` sits inside the private
  `elaborate_expr_checked_fallback/5` (defined at elaborator.ex:645, no `@spec`
  of its own), called from the public `elaborate_expr_checked/5`'s `@spec`
  (elaborator.ex:457: `term(), term(), [String.t()], Context.t(), Env.t()`) —
  no `MetaCtx.t()` parameter anywhere in that call chain. Confirmed by the
  codebase's own comment at elaborator.ex:3379: *"the general checking
  judgement (`elaborate_expr_checked`) does not thread `mctx`."*
- `lib/cure/elab/program.ex` and `lib/cure/elab/declarations.ex` never reference
  `MetaCtx` or `Unify` at all (zero hits) — `elaborate_function_body`
  (declarations.ex:45) calls `elaborate_body` then `Kernel.check` directly, with
  no `mctx` threaded through either.

Consequently, **"drain once per top-level definition" requires a new plumbing
step not yet accounted for**: threading a single `MetaCtx` through the whole
per-definition call graph (`elaborate_function_body` → `elaborate_body` →
`elaborate_expr_checked` → the argument-slot helpers that today call
`MetaCtx.new()` locally). This must be an explicit, early plan task (before
`drain_constraints/1` itself is wired in) — or, if that threading is judged too
large for this feature's scope, the plan must instead scope postponement/retry
to the granularity that's ALREADY threaded today (within one application's
argument telescope, i.e. inside a single `MetaCtx.new()` lifetime), and revise
the "later use" framing of `postpone01_flex_flex` (§5.1) and the
"solved by a unification arising later in the same definition" claim below to
match whichever granularity is actually implemented. Either resolution is
acceptable; leaving the mismatch unresolved is not — Task 1's probe (§2) should
be constructed to exercise whichever granularity the plan commits to, so the
risk gate measures the real, buildable design rather than the aspirational one.

Once that prerequisite is resolved, `drain_constraints/1` runs **once per
[definition | application-telescope — per the resolution above], after all its
unifications, immediately before the terminal `zonk`/`has_meta?` kernel-handoff
gate**. Candidate call sites (exact one pinned in the plan by tracing where the
chosen scope's elaborated term is finalized):
- `lib/cure/elab/elaborator.ex:651` (`if Unify.has_meta?(expected_core)` — the
  checked-expression gate) **only if** it is first given an `mctx` parameter, or
- the per-declaration finalize in `lib/cure/elab/program.ex` /
  `lib/cure/elab/declarations.ex` **only if** a definition-scoped `mctx` is
  first threaded into `elaborate_function_body`, or
- `finish_ctor_app`/`finish_global_app` (elaborator.ex, the existing
  `MetaCtx.new()` consumers) if the plan instead scopes to the
  already-threaded application-telescope granularity.

Requirement: after `drain_constraints/1` returns `{:ok, ctx}`, the existing
`has_meta?` gate still runs (a metavar with no constraint but never solved is
still an error, exactly as today). `drain` only converts "suspended constraints"
into either solutions (which `zonk` then substitutes) or a clean rejection. If
`drain` returns `{:error, …}`, that becomes the elaboration error for the chosen
scope.

**Idempotence/order:** draining before `zonk` guarantees `zonk` sees a queue-free
ctx; `zonk` itself is unchanged. Nested/local unify calls within the chosen scope
do **not** drain — only its boundary does — so a constraint suspended early can
be solved by a unification arising later **within that same scope** (whole
definition, once threaded — or, absent that threading, the same application's
argument telescope only; see the prerequisite above).

---

## 4. Data & control-flow summary

- `unify/4` public contract **unchanged**: `{:ok, ctx} | {:error, reason}`.
  Internally it may now enqueue constraints into `ctx` and still return `{:ok,
  ctx}`.
- New internal surface: `MetaCtx.{postpone,constraints,clear_constraints,
  put_constraints}` + `Unify.occurs_rigidity/3` (replacing `occurs?/3`) +
  `Unify.drain_constraints/1`.
- One (or, if the plan keeps today's per-application `MetaCtx` scoping rather
  than adding the threading prerequisite in §3.5, several) elaborator call
  site(s) gain a `drain_constraints/1` step before the relevant `has_meta?`
  gate. The exact count and location are pinned by the plan per §3.5's
  prerequisite resolution, not fixed here.

---

## 5. Oracle probes (`test/oracle/postpone/`)

Red-green plus soundness guards. Each is a faithful paired transliteration
(`.cure` + `.idr` with `%default total`, no `module` line); verdicts come from
`mix cure.oracle postpone`, never hand-written; the fixture is frozen into
`verdicts.json` and replayed by `test/oracle_replay_test.exs`.

1. **`postpone01_flex_flex`** — *the verdict-flip probe* (accept/accept). An
   implicit whose value is determined only by a later use, so the first constraint
   is flex-flex and gets pinned on retry. Before the feature: Cure **reject**,
   Idris **accept** (relation `cure_stricter` transiently → becomes `same` after
   the fix). The concrete program is authored in Task 1 and its pre-fix Cure
   rejection reason is verified; if it cannot be made to reject-for-the-right-reason,
   the risk gate (§2) fires.
2. **`postpone02_weak_rigid_occurs`** — (accept/accept). A metavar occurs
   weakly-rigidly in its candidate solution (under a metavar app / eliminable),
   solvable after another meta pins the eliminable away. Exercises §3.3 `:weak`.
3. **`postpone03_strong_rigid_cycle_neg`** — (reject/reject). Genuinely cyclic
   (`?a =? S(?a)` under a constructor). Guards against the occurs-refinement
   **over-accepting**: `:strong` must still hard-fail. Idris rejects
   (`OccursCheck`/cyclic); Cure rejects (`:occurs_check`).
4. **`postpone04_unsolved_neg`** — (reject/reject). Flex-flex that is **never**
   pinned by any later constraint. Both reject: Idris `UnsolvedMetas`, Cure
   `{:unsolved_constraints, …}`. Also serves as the driver **termination** witness
   (the stalled queue must terminate-then-reject, not loop).

If a probe's intended pre-fix verdict cannot be reproduced (e.g. Idris also
rejects `postpone01`, or Cure already accepts it), that probe is **not** frozen as
a divergence; the discrepancy is investigated first (skill's triage contract — a
general bug must be ruled out before labeling anything `cure_stricter`).

---

## 6. Testing discipline (strict red-green, immutable once green)

Per task, in order, one build at a time (never two `mix` suites concurrently):

- **Unit (ExUnit) tests** for the pure pieces, each written **failing first**:
  - `occurs_rigidity/3` classification table: strong/weak/none on hand-built Core
    terms (constructor-nested, meta-app-nested, projection-nested, none).
  - `MetaCtx` queue helpers (postpone/clear/put round-trips).
  - `drain_constraints/1`: solves a pinnable queue; **terminates and rejects** a
    stalled queue (asserts no infinite loop — bounded via the finite-metavar
    argument, tested with an explicit stalled fixture).
- **Oracle probes** (§5) as the behavioral red-green: author probe → run oracle →
  confirm pre-fix divergence → implement → confirm verdict flips → **no other
  probe regresses** → `mix test test/oracle_replay_test.exs` green before commit.
- Tests are behavioral (assert verdicts/classifications, not internal call
  shapes) and immutable once green.
- **Full suite** (`mix test`) run **once, alone**, at the Stage-5 gate.

---

## 7. Reference-system findings (design provenance)

Cross-read of the three mature dependent-type unifiers (Idris2 vendored-pinned;
Agda/Lean live clones, unpinned — inspiration, not oracle ground truth):

| | Idris2 | Agda | Lean4 |
|---|---|---|---|
| Store | global `UState.constraints` (IntMap) + `guesses` | awake/sleeping queues, blocker-keyed | `syntheticMVars`+`pendingMVars`+`dAssignment` |
| Retry | **retry-ALL fixpoint** while progress (`solveConstraints`, Unify.idr:1514) | **selective** blocker-keyed wakeup (`wakeupConstraints`, Constraints.hs:249) | **progress-flag fixpoint** + final strict pass (`synthesizeSyntheticMVars`, SyntheticMVars.lean:611) |
| Weak-rigid occurs | postpone (`failOnStrongRigid`, Unify.idr:387) | postpone (`abort` soft via `FlexRig'`, Occurs.hs:384) | **fail immediately** (`checkMVar`, ExprDefEq.lean:878) |
| Leftover | `checkUserHolesAfter`→`CantSolveEq` | `UnsolvedConstraints` | `reportStuckSyntheticMVars` |

**Adopted:** Idris/Lean retry-all-while-progress fixpoint; Agda/Idris
weak-vs-strong-rigid occurs split (Agda's `FlexRig'` is the canonical match to
Abel & Pientka); Idris/Lean threaded-state storage drained at a definition
boundary (→ Cure Option A). **Deferred:** Agda's blocker-keyed selective wakeup
(premature at Cure's scale — all three readers concur). Lean's occurs-fails-
immediately path was **not** adopted (it loses the reach we want; Idris/Agda
postpone, and the kernel backstops us either way).

---

## 8. Scope boundaries

**In scope:** techniques (A) postponement/constraint-queue + (B) weak-rigid
occurs refinement, together (they are coupled — §1: B flips no verdict without A).

**Out of scope (deferred, on-demand):**
- (C) Σ-flattening / projection elimination (`?m (fst y) (snd y)` → pattern form).
  Do when a projection-inference oracle probe actually fails.
- **Pruning** (Abel & Pientka §3.4, Fig 5; the roadmap's technique (B) bundles
  this with the occurs-check refinement — `docs/superpowers/specs/roadmap/2026-07-02-idris-parity-roadmap.md:56`:
  *"pruning … is what makes postponed/flex-rigid constraints actually solvable;
  and the occurs-check refinement fixes a latent completeness gap"*). This spec
  adopts only the occurs-check half of (B) and defers pruning: removing bound-variable
  dependencies from a metavariable's scope that provably cannot appear in any
  solution is a distinct mechanism from postponement/retry and from the
  weak/strong-rigid split, and none of the four probes in §5 require it (each is
  solved by retry-on-progress alone once the interfering metavariable is pinned).
  If Task 1 (§2) or later probing finds a postponed constraint that drains
  cleanly only with pruning (a bound variable that must be eliminated from a
  metavariable's dependency set, not just have its *value* pinned by another
  constraint), that is a **new oracle-measured gap**, not silently in scope here
  — add it as its own probe/task rather than folding it into this feature's
  "definition of done."
- Blocker-keyed selective wakeup (Agda). Add only if profiling shows O(n²)
  re-solving at realistic scale.
- Contextual-metavariable representation (`u[σ]` closures). Skipped per roadmap
  (a representation rewrite, not a capability).

## 9. Definition of done

- §3.5's `MetaCtx`-scoping prerequisite is resolved **in the plan, before Task
  1's probe is authored**: either the per-definition threading is added, or the
  feature is explicitly rescoped to the already-threaded per-application-
  telescope granularity — and `postpone01_flex_flex` (§5.1) is written to match
  whichever was chosen, not the aspirational "later use" framing verbatim.
- Risk gate (§2) passed: `postpone01` reproduced pre-fix divergence.
- All four oracle probes at intended verdicts; frozen; replay green.
- Unit tests (occurs_rigidity, queue helpers, drain incl. termination) green.
- Full `mix test` green (run once, alone).
- Roadmap §2 row #11 updated from open → landed, with the four probe names and the
  no-TCB / kernel-backstop note.
- No `lib/cure/core/*` diff (verified: `git diff --stat` touches only
  `lib/cure/elab/*`, `test/**`, `docs/**`).

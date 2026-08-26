# Antigen Tier A — harness + schema-directed assays (design)

**Status:** Draft (ready for review)
**Date:** 2026-07-01
**Author:** brainstormed with the operator.
**Umbrella:** `docs/superpowers/specs/antigen/2026-07-01-antigen-design.md` (vocabulary,
architecture, the totality vertical). **Research basis:**
`docs/research/pbt-dependent-types/synthesis.md` (11-paper synthesis).

This spec is the **first buildable slice** of Antigen. It inherits the umbrella's
vocabulary (antigen / assay / antibody / infection) and its swappable-backend
architecture, and pins down exactly what we build first and how.

---

## 1. Scope — what Tier A is and is not

The 11-paper research synthesis surfaced a hard fault line in Antigen. It has:

- a **schema-directed half** that rests on solid, published ground — the pipeline
  plus generators whose objects are built *by construction* with a known
  ground-truth label (totality/positivity), which is the "proven-good class" of
  the QuickChick derivation literature; and
- a **frontier half** — a general well-typed *dependent* term generator, which is
  genuinely open research (no turnkey solution exists in the corpus).

**Tier A builds the schema-directed half in full.** It delivers a working,
end-to-end engine that catches the *confirmed* mutual-recursion hole two
independent ways, with **zero dependence on the frontier generator**.

**In scope (Tier A):**
- The corpus subsystem — two committed, never-pruned, C2-serialized,
  generator-independent stores (antibodies + valid/seed bank).
- The `Antigen.Gen` DSL (reified, inspectable) + the StreamData backend.
- Known-label generators built directly as `Core`+`Env` (bypassing the elaborator).
- Four assays: `totality/terminating`, `totality/diverging`, `positivity`,
  `reflexivity-as-normalization`.
- Three run modes — explorer, generate, replayer — with the budget model of §8.
- Health-gate plumbing (discard-rate + coverage tracking).
- Reporting (`tmp/antigen/` + stdout breadcrumb).

**Deferred to Tier B (its own spec):** the hybrid bidirectional-inversion
dependent term generator and the differential assays it unlocks
(`subject_reduction`, `infer_check_agreement`, `normalization_stability`,
`conversion_termination`, `erasure_preservation`). Tier B's expensive-to-generate
terms will accrue into the *same* committed seed bank Tier A builds.

**Not in scope at all (separate specs):** *fixing* anything. Antigen **detects**.
The mutual-recursion checker fix, the `Vector`→`Std.Array` rename, and the emit
unused-var cleanup are their own specs that consume Antigen's findings.

## 2. Success criteria

Tier A is done when:

1. `mix antigen` (explorer) generates mutual-recursion definition groups, the
   kernel certifier wrongly certifies them (`totality/diverging` infection), the
   result is shrunk to a minimal cycle, written to `tmp/antigen/`, and appended
   to the antibody corpus — all in one self-terminating run.
2. `reflexivity-as-normalization` independently flags the *downstream* consequence
   of the same hole: a wrongly-certified diverging global, forced inside a pair
   of terms (§4.3), makes `conv(t, t')` exceed its fuel budget.
3. `totality/terminating` and `positivity` pass on known-good inputs and would
   fail on injected known-bad ones (both directions exercised).
4. `mix test` statically replays both corpora, reports **every** failing entry,
   and never mutates the corpus (git-clean for CI).
5. `mix antigen generate` harvests valid terms into the seed bank until killed,
   losing nothing on SIGINT.
6. The architecture test passes: nothing under `Antigen.Generators.*` /
   `Antigen.Assays.*` references `StreamData`.

**Sequencing note:** criteria 1–2 assume the mutual-recursion hole is still
live in the kernel when Tier A reaches completion. The actual fix is a
separate, out-of-scope spec (§1) that could land concurrently or first. If it
does, criteria 1–2 are satisfied instead by: `totality/diverging` correctly
reporting **no** violation post-fix, plus the generator self-tests of §12
(which check label-correctness against ground truth, independent of the
certifier's live behavior) standing as the enduring proof that the harness
*would* have caught the hole. Either outcome demonstrates the same thing — a
working detector — so this does not block Tier A; it only changes which
artifact (a live antibody vs. a passing self-test) is the evidence.

## 3. Component architecture

Modules, and which plan-phase builds them. (The spec is one document; the
*implementation plan* runs in two phases — see §11.)

```
Phase 1 — harness skeleton
  Antigen.Gen              # reified, inspectable generator AST (§6)
  Antigen.Backend          # behaviour: explore / replay
    └─ Backend.StreamData     # interprets Gen → StreamData; integrated shrinking
  Antigen.Corpus           # two stores: antibodies + seeds; decode/dedup/replay (§7)
  Antigen.Coverage         # the coverage key: dedup + health signal (§7.2, §9)
  Antigen.Report           # tmp/antigen/ + stdout breadcrumb (§10)
  Antigen.Runner           # explore / generate / replay orchestration (§8)
  Mix.Tasks.Antigen        # `mix antigen [generate]`

Phase 2 — schema-directed assays + generators
  Antigen.Generators.Totality   # known-label terminating/diverging defs (§5.1)
  Antigen.Generators.Positivity # ±strictly-positive families (§5.2)
  Antigen.Generators.Forcing    # schematic terms that force a global (§5.3)
  Antigen.Assays.Totality       # totality/{terminating,diverging} (§4.1)
  Antigen.Assays.Positivity     # positivity (§4.2)
  Antigen.Assays.Reflexivity    # reflexivity-as-normalization (§4.3)

Phase 2 also touches existing kernel modules (not new `Antigen.*` code):
  Cure.Core.Conv / Cure.Core.Eval  # add fuel instrumentation for the
                                    #   reflexivity assay's conv(t, t') (§8) —
                                    #   pure step-counting, no semantic change
```

Phase 1 is a runnable engine with a trivial stub assay; Phase 2 replaces the stub
with the real four and their generators. The harness is untestable without at
least one real assay, which is why they share a spec.

## 4. The four assays

Every assay is a pure function `antigen -> :ok | {:violation, detail}` (umbrella
§7). Tier A's four, in full:

### 4.1 `totality/terminating` and `totality/diverging`

The umbrella §6 details the totality vertical; this is its Tier-A realization.

- **Generator:** §5.1 (known-label defs built directly into `Core`+`Env`).
- **Oracle:** the **known label**. No fuel, no timeout — the certifier
  (`Kernel.validate_certificate` / `Certificate.terminating?`) is a *static
  structural analysis* that terminates on its own.
- **`totality/diverging` asserts:** the certifier **must NOT certify** a
  by-construction non-terminating def. Violation = a soundness infection. **This
  is the direct, cheap detector of the confirmed hole** — a mutual group
  `f→g→f` that the certifier wrongly accepts.
- **`totality/terminating` asserts:** the certifier **must certify** a
  by-construction total def (including well-founded mutual groups). Violation =
  an incompleteness bug (rejecting a genuinely-total function), and guards the
  eventual fix against over-correction.

### 4.2 `positivity`

- **Generator:** §5.2 (inductive families, labeled ±strictly-positive).
- **Oracle:** the **known label**. Static — run the positivity checker, compare.
- **Asserts:** the kernel accepts a family **iff** it is strictly positive. A
  labeled-negative family that is accepted, or a labeled-positive family that is
  rejected, is an infection. Guards the second classic unsoundness route (a
  negative occurrence lets you build a non-terminating loop and inhabit ⊥).

### 4.3 `reflexivity-as-normalization`

The independent, downstream probe for the hole. From *Certify a Conversion
Checker* (FSCD'25): **reflexivity of conversion is equivalent to deep
normalization** — `conv(t,t)` terminates iff `t` deeply normalizes. So a
budget-bounded conversion check is a non-normalization detector that does
**not** rely on trusting the checker's verdict (it relies only on whether it
*halts*).

- **Generator:** §5.3 — a known-label **diverging mutual** group registered in
  `Env` (certified for real, by calling the actual certifier — see §5.3), plus a
  pair of small **schematic terms** `t`, `t'` that force the group (built
  directly in `Core`, not the general term generator).
- **Oracle:** **fuel** (§8). Assert `conv(t, t')` halts within the fixed fuel
  budget. Fuel exhaustion = a (suspected non-termination) infection. **This is
  not literal syntactic self-comparison `conv(t,t)`:** `Cure.Core.Conv`'s
  `same_neutral_no_delta?` guard (`lib/cure/core/conv.ex`) deliberately
  short-circuits two *structurally identical* stuck neutrals as equal *before*
  attempting δ-unfolding — exactly the "same stuck recursive call on both sides"
  case a naive `conv(t,t)` would hit, which would make the assay pass
  immediately without ever forcing the diverging global, testing nothing. `t`
  and `t'` must therefore be two **structurally distinct** presentations that
  are only provably equal *through* δ-unfolding — e.g. `t = f(n)` (unsubstituted)
  vs. `t' =` one manual substitution step of `f`'s registered body applied to
  `n` (so `t'`'s head neutral is `g`, not `f`, for the `f→g→f` case), built
  directly in `Core` by the generator, not via a call to `conv` itself. Both
  sides must resolve to the *same* underlying value once genuinely normalized —
  the failure mode under test is that they never do, because the group never
  normalizes.
- **Why it complements §4.1:** δ-reduction only unfolds *certified-total*
  globals. So `conv(t, t')` can only loop here *because* the certifier already
  wrongly certified the diverging def (§4.1's hole). `totality/diverging` catches
  the hole at the certifier; `reflexivity-as-normalization` catches its
  conversion-level consequence — and remains a general non-normalization probe for
  any future source, not just this hole.

## 5. Known-label generators

All three build `Core` terms and the `Env` **directly**, bypassing the
elaborator. This is essential and load-bearing: the surface elaborator cannot even
express mutual recursion (the forward-reference gap that *masks* the hole), so
Antigen constructs the mutually-recursive `Env` itself and calls the certifier —
the exact move that confirmed the hole, now fuzzed. **These generators ARE the
oracle**, so their correctness is the depth of the vertical (umbrella §6).

### 5.1 Totality generator (`Antigen.Generators.Totality`)

Emits `(def_group, label)` where `label ∈ {:terminating, :diverging}` is
ground-truth by construction:

- **`:terminating`** — non-recursive defs; single defs where every self-call is on
  a strict structural subterm (guarded by destructors); **and well-founded mutual
  groups** (even/odd style, where the group's calls structurally decrease).
- **`:diverging`** — genuine non-termination: direct self-loops with
  non-decreasing arguments; **mutual groups `f→g→f` that are not structurally
  decreasing** (the confirmed hole); and non-structural / deep recursion.

Generation parameters (fed by `Antigen.Gen`): arity, number of mutual
participants, recursion-argument shape (decreasing vs. constant vs. increasing),
guard pattern. Shrinking respects the label — a `:diverging` counterexample
cannot shrink away its back-edge — via the same mitigations as umbrella §4.2
(shrink hints on the `Gen` DSL nodes that encode the back-edge / decreasing
argument, plus umbrella §4.2's type-preserving post-shrink pass before an
antibody is pinned), not an added Tier-A-specific mechanism.

### 5.2 Positivity generator (`Antigen.Generators.Positivity`)

Emits `(family, label)` where `label ∈ {:positive, :negative}`:

- **`:positive`** — every recursive occurrence in every constructor argument is
  strictly positive by construction.
- **`:negative`** — one injected negative occurrence (a recursive occurrence to
  the left of an arrow in a constructor argument type).

### 5.3 Forcing generator (`Antigen.Generators.Forcing`)

For `reflexivity-as-normalization`: takes a `:diverging` **mutual** def group
`f→g→f` from §5.1, registers it in `Env` by running the *actual* totality
certifier over the group (not a hardcoded flag) — the certifier's wrong verdict
is what marks the group certified-total and thus unfoldable, exactly reproducing
the confirmed hole's effect. It then builds two minimal schematic `Core` terms:
`t = f(n)` (an unsubstituted application forcing `f`) and `t' =` one manual
evaluation step of `f`'s registered body applied to `n` — β-substitution *and*,
where `f`'s guard pattern scrutinizes its argument (§5.1), the matching ι/`case`
step, not bare syntactic substitution — so `t'` is headed by `g`, `f`'s cycle
partner (the generator picks `n`'s shape itself, so it can guarantee this one
step actually lands on the branch that calls `g`) — **not** `t` compared
against a copy of itself. This asymmetry is required so conversion cannot resolve the pair via
`Cure.Core.Conv`'s same-neutral-without-δ shortcut (§4.3) and must instead
attempt genuine δ-unfolding, which is where the group's non-termination
surfaces. This is a fixed schematic construction, **not** the general term
generator — it stays schema-directed and Tier-A.

## 6. `Antigen.Gen` DSL + backend

Refines the umbrella §4.1. Two decisions from the research (synthesis §3.4, from
*Foundational PBT* ITP'15):

**Reified, inspectable AST — not opaque closures.** `Antigen.Gen` values are data
(`{:return, x}`, `{:one_of, gs}`, `{:frequency, weighted}`, `{:bind, g, f}`,
`{:member_of, list}`, `{:sized, f}`, `{:resize, n, g}`), so a static pass can
compute/over-approximate a generator's **support set** by structural recursion
(`support(bind g f) = ⋃_{a∈support g} support(f a)`) — which is what makes "what
can this assay generator actually produce?" answerable rather than assumed.
(`bind`'s continuation is a function, so its support is only *over-approximable* —
an accepted limit.) This reconciles with the umbrella §4 primitive list
(`int/bounded, one_of, frequency, constant, map, bind, sized, recurse`) as
follows: `:return` is the umbrella's `constant`; `:member_of` generalizes
`one_of` over a concrete enumerated list; `int/bounded` is expressed as
`member_of`/`bind` over a range, not a separate primitive; `map` is dropped as a
primitive since it is derivable from `bind` + `return`; `:resize` is new here,
for explicit depth/arity control. `recurse` is **not** needed in Tier A — all
three known-label generators (§5) produce finite, bounded-shape defs/families
(fixed arity, fixed mutual-participant count, fixed guard depth), never an
open-ended self-referential term; it is deferred to Tier B's general term
generator, which does need a distinguished fixed-point node for the static
support-set pass to terminate on.

**Size-hygiene tags.** Each generator is tagged `:unsized` (size-independent
support) or `:size_monotonic` (bigger size ⇒ superset). These license the clean
compositional support reasoning and prevent false-completeness claims across
sizes (ITP'15 §3.5: `bind` threads one size to both sides).

**No `filter` as a first-class primitive** — the generate-then-filter
anti-pattern every paper warns against. Available only as a marked escape hatch.

**Backend.** `Backend.StreamData` interprets one clause per primitive; because
`bind → bind`, integrated (Hedgehog-style) shrinking is inherited and stays valid.
Architecture rule (umbrella §4, enforced by test §11 there): only
`Backend.StreamData` may reference `StreamData`.

## 7. Corpus subsystem

Two committed stores, both **C2-serialized** (`Cure.Core.Serialize`),
**never-pruned**, and **generator-independent** — replay decodes a stored object
and runs the assay *through the kernel*; the generator is never on the read path.
This is why a full generator rewrite cannot cost us the accumulated library.

### 7.1 The two stores

- **`test/antigen/corpus.sexp` — antibodies** (counterexamples). Admission rule:
  **admit any** infection. One C2 record per line (umbrella §8.2 grammar). Static
  replay decodes each entry and re-runs its recorded assay, asserting the
  assay's own pass condition (e.g. `totality/diverging`'s "kernel must NOT
  certify") — **not** "this entry must still violate." While the underlying
  kernel bug is live, that assertion fails on replay, so a live infection turns
  `mix test` **red** and stays red until the kernel is fixed; once fixed, the
  same entry starts satisfying its invariant and replay goes green — the
  never-pruned corpus is a permanent regression guard, not a frozen "must stay
  broken" snapshot (matches umbrella §8.2: "every entry must satisfy its
  invariant"). Pure verdicts, no `open`/xfail.
- **`test/antigen/seeds.sexp` — the valid/seed bank.** Admission rule: **admit iff
  coverage-novel** (§7.2). Holds well-typed / well-formed generated antigens
  regardless of assay outcome. Serves three jobs at once: static regression
  replay, the coverage record, and (Tier B) generation seeding. An
  infection-triggering antigen is a *valid object that also violates an assay* — it
  is banked in **both** stores (valid here, counterexample in the antibody store);
  no contradiction.

Record grammar is shared; a `kind` distinguishes them where a reader needs it.
Dedup on append is idempotent, keyed on the canonical C2 serialization of the
`(assay, term)` for antibodies and on the **coverage key** for seeds.

**Append is atomic per record.** Each record is fully assembled in memory and
written with a single append syscall (not built up with multiple writes), so a
kill (SIGINT/SIGKILL) between records never leaves a torn/corrupted line —
required for both the interruptible run modes of §8 and for concurrent writers
(explorer and `generate` mode both append to the seed store; the same
single-write-per-record discipline makes concurrent appends safe to interleave
at the line level). The replayer (§8) treats a line that fails to decode as its
own reportable failure — distinct from an assay violation — and continues past
it rather than aborting the run, consistent with "reports every failing entry."

### 7.2 The coverage key

A **feature vector**, not a full-shape hash (a full hash makes every distinct term
"novel" and defeats the plateau — the store would grow without bound). The key:

```
{ set of Core constructors used
· depth bucket ∈ {0–2, 3–5, 6–9, 10+}
· binder-shape flags: has_shadowing, has_mutual_group, per-eliminator-kind present
· label kind (:terminating | :diverging | :positive | :negative | :none) }
```

**Admit a seed iff its key is new.** So "keep all valid terms" means "keep all
*coverage-novel* terms" — which plateaus (the feature-vector space is finite once
common shapes are covered) and stays committable and diff-friendly. Changing the
key later only affects whether *new* terms are judged novel; it never evicts an
already-committed term (never-pruned). The same key drives the health gate (§9).

## 8. Run modes and the budget model

Three modes on the runner. The budget model separates a **deterministic verdict**
from **wall-clock safety**, so the committed corpus replays identically everywhere.

- **Per-conversion fuel — the verdict, FIXED and committed.** The fuel bounding
  `reflexivity-as-normalization`'s `conv(t, t')` (§4.3) is a **fixed constant
  baked into the assay**, a count of reduction/normalization steps. It must not
  vary by run mode or machine: otherwise the same term could read diverging on
  one box and terminating on another, and a committed antibody could flip
  green↔red. Fuel exhaustion is the deterministic, replayable verdict. **No
  step-counting mechanism exists in `Cure.Core.Conv`/`Cure.Core.Eval` today**
  (δ-unfolding in `whnf_delta`/`unfold_head` recurses unconditionally) — Phase 2
  must add fuel instrumentation to the conversion/evaluation path the assay
  drives (a step counter threaded through, decremented per reduction, halting
  the call when exhausted). This is pure instrumentation, not a semantic
  change, but it does touch TCB modules and should be scoped accordingly.
- **Per-conversion killswitch — safety, a fixed decent constant.** A wall-clock
  cap on a single conversion so one pathological term can't wedge the runner.
  Reported as a distinct "killswitch tripped" event, **never** an assay verdict.
  Not configurable (a fixed sensible value).
- **Explorer — `mix antigen`** (generate + assay + bank). **Self-terminating** on
  a default number of generation rounds; optional `--count N` / `--budget Nm`
  override. **No** named fast/regular/thorough tiers. On each infection: shrink,
  write the tmp report, append to the antibody store (dedup), and **keep going**
  (harvests many infections per run). Every generated valid antigen is offered to
  the seed store (coverage-dedup). Owns corpus mutation; the operator commits the
  diff.
- **Generate — `mix antigen generate`** (harvest-only). Produces well-typed /
  well-formed antigens, coverage-dedups, appends to the seed store, and **skips
  the assays entirely** (no verdicts, no infection-hunting). **Runs until killed**
  (SIGINT). To make "losing nothing on SIGINT" (§2 criterion 5) actually hold,
  the runner **traps SIGINT and performs one final synchronous flush before
  exiting** — periodic flushing alone only bounds the loss window, it does not
  close it. This is the "leave it running for hours to stack up expensive terms"
  tool; those terms are assayed later by the replayer. (High-value mainly for
  Tier B's expensive terms; the machinery is built here so Tier B inherits it.)
- **Replayer — in `mix test`** (read-only, static). Decodes both stores and runs
  the assays over them, reporting **every** failing entry (non-fail-fast). Never
  generates, never mutates — `mix test` stays git-clean for CI. Bounded by corpus
  size, so no run budget.

## 9. Health gate

Coverage bounded by the generator is the field's dominant false-confidence trap
(synthesis §3.2, §3.4): a green assay from a generator that can't reach the
interesting shape is vacuous. Tier A builds the plumbing:

- **Discard rate** — fraction of generation attempts that fail to produce a
  well-formed candidate at all (a generator-quality failure). This is distinct
  from a coverage-duplicate rejection (§7.2's "admit iff coverage-novel"), which
  is expected to rise as the corpus matures and is *not* counted as a discard.
  For known-label generators the discard rate should be ≈0; a rising rate is a
  red flag.
- **Coverage** — which coverage-key buckets (§7.2) the run hit. Reported per run;
  a batch that never hits `has_mutual_group`, for instance, cannot have tested the
  hole.

Tier A **reports** these (per-run summary + into `tmp/antigen/`); it does not hard-
fail on them. Term-specific health metrics (binder-usage rate, reduction activity)
are added in Tier B. Tier A's own generated defs already have parameter binders,
but by construction they use them deterministically (a known-label recursive def
must reference its recursion argument to be labeled correctly) — so a
binder-*usage-rate* metric would be constant and uninformative here; it only
becomes meaningful once Tier B's general term generator can produce terms whose
binders go unused. The `Antigen.Coverage` module is structured to receive these
metrics without rework.

## 10. Reporting

Per umbrella §8.1, unchanged: on **every** infection or unexpected error, a full
report is written to `tmp/antigen/failure-<seed>-<assay>-<n>.txt` and flushed
**before** anything reaches stdout (a killed process or a `grep`-filtered pipe
cannot lose it), plus a stable `tmp/antigen/latest.txt`. One grep-surviving stdout
breadcrumb per infection. Reports also carry the run's health-gate summary (§9).

## 11. Plan phasing

One spec, two plan-phases (each an independently testable deliverable):

- **Phase 1 — harness skeleton.** `Antigen.Gen` + `Backend.StreamData`,
  `Antigen.Corpus` (both stores, decode/dedup/replay), `Antigen.Coverage`,
  `Antigen.Report`, `Antigen.Runner` (all three modes), `Mix.Tasks.Antigen`.
  Driven by a **trivial stub assay + stub generator** so the whole
  explore/generate/replay/report/corpus data flow is exercised end-to-end before
  any real assay exists.
- **Phase 2 — schema-directed assays + generators.** The three generators (§5)
  and the four assays (§4), plus the fuel instrumentation of
  `Cure.Core.Conv`/`Eval` that `Antigen.Assays.Reflexivity` needs (§3, §8).
  Replaces the stub. Phase 2's completion is success-criterion #1–#3 (§2): the
  engine catches the confirmed hole two ways.

## 12. Testing Antigen itself

Per umbrella §11, plus Tier-A specifics:

- **Architecture test** — no `Antigen.Generators.*` / `Antigen.Assays.*` module
  references `StreamData`.
- **Generator self-tests** — the totality generator's `:terminating` / `:diverging`
  outputs are validated against a fixed known-good/known-bad set, *including* the
  confirmed mutual cycle Antigen must flag; the positivity generator likewise.
  The forcing generator (§5.3) gets its own self-test: verify its two schematic
  terms actually reach/force the registered global under plain (non-δ)
  evaluation, and verify they are *not* structurally identical (guarding against
  a regression to literal `t` vs. `t` — see §4.3), since a construction that
  never forces the global, or that collapses to self-comparison, would make
  `reflexivity-as-normalization` pass vacuously.
- **Support-set characterization** — for each generator, a runnable soundness
  meta-test (`check all x <- gen: assert well_formed?(x)`) and a documented note on
  what its support set can/can't produce (synthesis §3.4). Soundness is tested;
  completeness is the coverage/corpus argument, not a proof.
- **Corpus round-trip** — every record encodes → decodes → re-checks identically
  (C2 stability), for both stores.
- **Replay determinism** — replaying any stored term yields the same verdict every
  run (this is what the fixed fuel of §8 guarantees).
- **Fuel determinism** — `reflexivity-as-normalization` returns the same verdict
  regardless of machine speed (fuel, not wall-clock, decides).

## 13. Deferred to Tier B (for continuity, not built here)

The hybrid dependent term generator: bidirectional-rule inversion + INDIR
(head-first saturated elimination) + a retained plain-elimination rule (so redexes
remain reachable) + interleaved generation-and-checking + direct normal-form
generation + deliberate shadowing contexts; conversion and index constraints
discharged via the kernel conv-checker under the same fuel budget. It unlocks the
differential assays and feeds the seed bank built here. Its yield and coverage are
engineering unknowns to be *measured against this harness* — which is the reason
Tier A is built first.

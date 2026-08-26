# Antigen — a property-based metatheory-testing engine for the Cure kernel

**Status:** Draft (open items tracked in §12)
**Date:** 2026-07-01
**Author:** brainstormed with the operator; see the dependent-types initiative memory.

---

## 1. Motivation

Cure's dependent type system rests on a small **trusted kernel** (`Cure.Core.*`,
the TCB): NbE conversion, universe checking, indexed-family well-formedness,
positivity, and the totality/termination certifier that gates δ-reduction. If
any of these is unsound, the whole language silently accepts wrong programs.

A manual review already found **one confirmed soundness hole**: the termination
checker (`Cure.Core.Certificate.terminating?`) certifies **mutually-recursive**
definitions as total. Verified directly on hand-built Core terms —
`terminating?(:f, f)` and `terminating?(:g, g)` both return `true` for the
non-terminating cycle `f (S y) = g y ; g y = f (S y)` — because `calls?/2` only
detects a function's *own* name, not a cycle through a sibling. It is currently
unreachable from surface syntax only because the elaborator lacks forward
references; the TCB must not depend on that accident.

One hole found by hand implies others unfound. Rather than probe case-by-case
forever, we build a **durable engine** that generates candidate kernel inputs
and checks metatheoretic invariants against them — continuously, and as a
regression harness that grows with the language. That engine is **Antigen**.

Antigen is *falsification, not proof*: passing runs are strong evidence, a
failing run is a proof of a bug. Mechanized metatheory (Agda/Coq) is explicitly
out of scope (a later phase). Antigen is the pragmatic middle: cheap, continuous,
decisive on failure.

## 2. Goals / non-goals

**Goals**
- Continuously search for soundness/completeness violations in the TCB.
- Go **deep on totality soundness** first (it has a confirmed hole), and stay
  **broad** across the other kernel invariants (T-shaped v1).
- Every discovered counterexample is preserved: never lost to a filtered pipe,
  and permanently re-run as a regression.
- Be a durable, extensible foundation — new language capabilities extend the
  generators; the invariants stay fixed and immediately exercise them.
- Keep the PBT backend swappable (StreamData now, Hypothesis-style later).

**Non-goals**
- Not a proof system; does not replace mechanized metatheory.
- Not the *fixes* — Antigen finds and pins holes; fixing the mutual-recursion
  checker, the `Vector`/`Std.Array` rename, etc. are separate specs.
- Coverage is bounded by the generators: Antigen catches the *kinds* of inputs
  it can generate. This is stated openly, not hidden.

## 3. Name & vocabulary

**Antigen** — the engine, and each generated challenge term injected into the
kernel. The immune metaphor names the parts:

| Term | Meaning |
|---|---|
| **Antigen** | the engine / a generated challenge (term, family, def, or context) |
| **Assay** | one property check: an invariant run against an antigen |
| **Antibody** | a counterexample preserved as a permanent regression (a corpus entry) |
| **Infection** | an assay violation (a real or suspected soundness/completeness bug) |

## 4. Architecture

Layers, from bottom up. The dependency rule is strict: **nothing under
`Antigen.Generators.*` or `Antigen.Assays.*` may reference `StreamData`** — only
`Antigen.Backend.StreamData` may. This is what keeps the PBT engine swappable;
it is enforced by an architecture test (§11).

```
Antigen.Gen              # backend-neutral generator DSL: int/bounded, one_of,
                         #   frequency, constant, map, bind, sized, recurse
Antigen.Backend          # behaviour: interpret a Gen program; explore; replay
  ├─ Backend.StreamData     # NOW: interprets Gen → StreamData; integrated shrinking
  └─ Backend.ChoiceSeq      # LATER: Hypothesis-style choice-sequence shrinking
Antigen.Generators.*     # typed generators (contexts, families, defs, terms) in Gen
Antigen.Assays.*         # invariants: antigen -> :ok | {:violation, detail} — pure
Antigen.Corpus           # read/append/dedup the committed corpus (C2 records)
Antigen.Report           # write tmp/antigen/ failure files + stdout breadcrumb
Antigen.Runner           # ties (backend, generators, assays) into explore/replay
Mix.Tasks.Antigen        # `mix antigen` — the non-halting explorer
```

### 4.1 Swappable backend (tagless interpreter)

Generators are `Antigen.Gen` programs describing primitive random draws. Each
backend interprets them:

```
interp(Gen.int(lo,hi))    = StreamData.integer(lo..hi)
interp(Gen.bind(g, f))    = StreamData.bind(interp(g), &interp(f.(&1)))
interp(Gen.frequency(fs)) = StreamData.frequency(...)
```

Because `bind` maps to `bind`, StreamData builds its integrated (Hedgehog-style)
shrink tree over our generators — so shrinks stay well-typed automatically and we
get shrinking for free today. `Backend.ChoiceSeq` will interpret the *same* `Gen`
programs by recording primitive draws into a sequence and shrinking that sequence
(Hypothesis-style, better through the deep `bind` chains that dependent-term
generation produces). Swapping backends is one new interpreter; **no generator or
assay changes.**

Backend behaviour (the two operations the runner needs):
- `explore(gen, assay, budget) -> [shrunk_failure]` — non-halting; runs the whole
  budget and returns *every* distinct shrunk counterexample.
- `replay(term, assay) -> verdict` — static; decode a stored term, run one assay,
  no generation.

### 4.2 Shrinking note

StreamData shrinking is *integrated* (Hedgehog family): correct (every shrink is
a value the generator could produce, so invariants hold) but not Hypothesis-grade
through deep dependent `bind`. Mitigations: known-label generation keeps the
shrink space small and valid; the `Gen` DSL can carry shrink hints; a small
type-preserving post-shrink pass runs before an antibody is pinned. The
`ChoiceSeq` backend is the long-term answer.

## 5. Generator layer

Four antigen kinds, in increasing difficulty. All are `Antigen.Gen` programs.

1. **Contexts (Γ)** — telescopes of typed binders; terms are generated relative
   to one.
2. **Inductive families** — random indexed families + constructors, with a
   **positivity knob**: strictly-positive by construction, or a *labeled*
   injected negative occurrence.
3. **Definitions / recursive functions** — the totality flagship (§6).
4. **Well-typed Core terms at a type** — `gen_term(Γ, T)`: build a term of type
   `T` in `Γ` bottom-up by inverting the bidirectional rules (the "typing rules
   as generation rules" technique; see §10). This is the *broad* axis and the
   frontier-hard part; start deliberately small (var/app/λ/Σ/data/`case` at low
   universes) and grow. Feeds the broad invariants in §7.

## 6. The totality vertical (deep, the flagship)

The oracle problem: we cannot ask the kernel "does this terminate?" (circular).
Antigen sidesteps it with **generate-with-known-label** — every definition is
produced *together with its ground-truth termination status*, because we built
it. Two classes:

- **`:terminating` by construction** — non-recursive defs; structural recursion
  where every self-call is provably on a strict subterm; **and terminating
  mutual groups** (even/odd style). *Assay:* the kernel **must certify**.
  Failures are *incompleteness* (rejecting genuinely-total functions) — real
  bugs, not soundness holes. Including terminating mutual groups guards the
  eventual mutual-recursion fix against **over-correction**.
- **`:diverging` by construction** — a genuine non-terminating cycle: direct
  self-loops with non-decreasing arguments, **mutual-recursion groups**
  (`f→g→f`), and non-structural / deep recursion. *Assay:* the kernel **must not
  certify**. This is the **soundness-critical** direction and the one that flags
  the confirmed hole.

Two properties make this work:

- **Antigen builds Core + `Env` directly, bypassing the elaborator.** The
  certifier operates on registered definitions, and the surface elaborator cannot
  even express mutual recursion (the forward-reference limitation that *masks*
  the hole). Antigen constructs the `Env` with the mutually-recursive defs itself
  and calls the certifier — the exact move that confirmed the hole, now fuzzed.
- **The two generators *are* the oracle, so their correctness is load-bearing.**
  A `:diverging` def mislabeled (actually terminating) is a false soundness
  alarm; a `:terminating` def mislabeled is a false completeness alarm. The depth
  of this vertical is in making the two generators emit *only* genuinely-diverging
  / genuinely-terminating definitions. Shrinking respects the label (a
  `:diverging` counterexample cannot shrink away its back-edge).

The payoff: Antigen's first end-to-end act is to generate mutual-recursion
groups, watch the kernel wrongly certify them, shrink to a minimal cycle, and
mint the first antibody — a live demonstration on a *known* bug before we trust
it on unknown ones. Both directions are covered: it **catches non-terminating**
(soundness) *and* **verifies terminating** (completeness), and the terminating
mutual groups keep the eventual fix honest on both sides.

## 7. The assay suite (broad)

Each assay is a pure `antigen -> :ok | {:violation, detail}`. Two are detailed
(the totality vertical, §6). The rest are listed with their intent and are
**OPEN** for full detail (§12):

| Assay | Asserts | Fed by | Oracle |
|---|---|---|---|
| `totality/diverging` | kernel must NOT certify | §6 diverging gen | known label |
| `totality/terminating` | kernel MUST certify | §6 terminating gen | known label |
| `subject_reduction` | `infer(t)=A ⟹ nf(t)` still checks at `A` | term gen | self (differential) — **OPEN** |
| `conversion_termination` | `conv(a,b)` always halts | term-pair gen | timeout — **OPEN** |
| `infer_check_agreement` | `infer(t)=A ⟹ check(t,A)=:ok` | term gen | differential — **OPEN** |
| `positivity` | negative occurrence ⟹ rejected | family gen (labeled) | known label — **OPEN** |
| `normalization_stability` | `nf(nf(t))=nf(t)`; `nf(t)` re-checks; C2 round-trips | term gen | differential — **OPEN** |
| `erasure_preservation` | erased args don't change typing/runtime value | def/term gen | differential — **OPEN** |

## 8. Capture, corpus, and runner

Two tiers of preservation.

### 8.1 `tmp/antigen/` — ephemeral full reports (never lose a failure in a run)

Repo-local, already gitignored, created on demand. On **every** infection or
unexpected error, written and flushed **before** anything reaches stdout, so a
killed process or a `grep`-filtered pipe cannot lose it. Each file holds:

- the **seed**;
- **assay identity** — invariant + direction (e.g. `totality/diverging → kernel
  must NOT certify`);
- the **antigen**, C2-serialized (the exact failing Core term/def/Env) *plus* a
  human-readable pretty-print — reproduction is generator-version-independent;
- **ground truth vs actual** — the label and what the kernel actually did;
- the **shrunk minimal form** (C2);
- **two repro paths** — `mix test … --seed <seed>`, and a decode-and-run-one-assay
  snippet (no generator needed);
- a timestamp.

Filenames: `tmp/antigen/failure-<seed>-<assay>-<n>.txt`, plus a stable
`tmp/antigen/latest.txt` pointing at the most recent. **Stdout breadcrumb** — one
grep-surviving line:

```
ANTIGEN INFECTION [totality/diverging] seed=12345 → tmp/antigen/failure-12345-totality-1.txt
```

### 8.2 `test/antigen/corpus.sexp` — committed, permanent regression corpus

(A non-`.exs` extension deliberately: it is data, not an ExUnit script, so
`mix test` does not try to run it directly — a dedicated `*_test.exs` replayer
reads and iterates it.)

Append-only, **never pruned**. One C2 record per line — machine-readable with the
parser we already have, diff-friendly:

```
(case (assay totality/diverging) (seed 12345) (note "mutual cycle f→g→f") (term <sexpr>))
```

- **Static replay every run:** decode each `term`, run its `assay`, assert the
  invariant holds. No generation cost — a large corpus stays cheap.
- **Pure verdicts:** every entry must satisfy its invariant. A real infection
  turns the suite **red** and stays red until fixed — a soundness harness must
  not be green while the kernel is unsound. No `open`/xfail status.
- **Dedup on append:** idempotent, keyed on the canonical C2 serialization of the
  `(assay, shrunk term)`. Re-runs accumulate only genuinely new shapes.

### 8.3 Runner: explorer vs replayer

- **Explorer — `mix antigen`** (non-halting *fuzzing loop*, not `check all`).
  Runs its full budget; for each generated antigen, runs the assay; on failure,
  shrinks, writes the tmp report, appends to the corpus (dedup), and **keeps
  going**. One run harvests *many* distinct infections. Owns corpus mutation; the
  operator commits the resulting diff.
- **Replayer — in `mix test`** (read-only). Replays the whole corpus statically
  and reports **every** failing entry (non-fail-fast — full blast radius in one
  run). Never mutates the corpus, so `mix test` stays git-clean for CI.

## 9. Reused infrastructure

- **`Cure.Core.Serialize` (C2)** — antigen serialization in tmp and corpus,
  canonical dedup, and generator-independent replay. Already built.
- **The kernel certifier** — `Kernel.validate_certificate` /
  `Certificate.terminating?` is the unit under test for the totality vertical.
- **StreamData** — added as a test dependency; quarantined behind
  `Backend.StreamData`.

## 10. Prior art (structure to copy)

See `docs/research/pbt-dependent-types/` (PDFs + README). The generator copies
the "typing rules as generation rules" technique:

- **Making Random Judgments** (ESOP'15) — derive the generator from the typing
  rules. The closest blueprint.
- **Pałka et al.** (AST'11) — the base technique.
- **Generating Good Generators for Inductive Relations** (POPL'18) — the
  QuickChick derivation theory (sound+complete generators from a relation).
- **Generic Bidirectional Typing for Dependent Type Theories** (2023) — the rule
  structure to invert; our kernel is already bidirectional (`infer`/`check`).
- **What does it take to certify a conversion checker?** (2025) — directly about
  a `conv.ex`-style checker.

No turnkey *dependent* term generator exists (open research problem), so we start
**schema-directed** (§6 is schema-directed) and grow toward general type-directed
generation (§5, kind 4).

## 11. Testing Antigen itself

Antigen's own correctness matters (its generators are oracles):

- **Architecture test:** assert no module under `Antigen.Generators.*` /
  `Antigen.Assays.*` references `StreamData` (grep-based or AST-based).
- **Generator self-tests:** the `:terminating` and `:diverging` generators are
  validated against a fixed set of known-good / known-bad definitions — including
  the confirmed mutual-recursion cycle, which Antigen must flag.
- **Corpus round-trip:** every corpus record encodes → decodes → re-checks
  identically (C2 stability).
- **Replay determinism:** replaying a corpus term yields the same verdict every
  run.

## 12. Open items — status

**Research complete.** All 11 prior-art papers are read and synthesized in
`docs/research/pbt-dependent-types/synthesis.md`. **Slicing decided:** the engine
is split into two tiers, each its own spec → plan → build cycle.

- **Tier A** — the harness + the schema-directed (known-label) assays — is fully
  designed in `docs/superpowers/specs/antigen/2026-07-01-antigen-tier-a-design.md`. It
  resolves items 3–7 below and builds the pipeline end-to-end against the *known*
  mutual-recursion hole with no dependence on the frontier generator.
- **Tier B** — the general term generator + the differential assays (items 1–2) —
  is deferred to its own later spec; it feeds the seed bank Tier A builds.

**Locked decisions this session** (see the Tier-A spec + synthesis for detail):
- Generator = bidirectional-rule inversion + INDIR (head-first elimination) + a
  retained plain-elimination rule (redexes stay reachable) + interleaved
  generation-and-checking + direct normal-form generation + deliberate shadowing;
  conversion / index constraints discharged via the kernel conv-checker under a
  fixed fuel budget (a hybrid: generate the structural skeleton, *check* the
  semantic constraints — yield is the engineering unknown, not correctness).
- Oracle strategy (the kernel-as-its-own-checker problem, which no paper faces):
  differential/self-consistency assays, independent invariants (esp.
  **reflexivity `conv(t,t)` ⟺ deep normalization** — the sharp cheap probe for the
  hole), and known-label generation. Never trust the kernel against itself.
- **Two committed, never-pruned, C2-serialized, generator-independent corpora:**
  antibodies (counterexamples, admit-any) and a valid/seed bank (coverage-deduped
  via a feature-vector key). Seeds folded into the bank; generator-independence
  means a generator rewrite cannot cost the accumulated library.
- **Budget model:** a fixed committed **fuel** budget decides the verdict
  (deterministic replay); a fixed wall-clock **killswitch** is a safety net,
  reported separately, never a verdict. Explorer self-terminates (default +
  override); a dedicated **generate mode** harvests terms until killed without
  running assays.
- **Health gate:** discard-rate + coverage tracking (binder-usage / reduction
  activity added in Tier B) — reported, guarding against vacuous green runs.

**Remaining open (Tier B spec):**
1. **General term generator** (§5, kind 4) — the hybrid design above, its small
   starting fragment, and its yield/coverage measured against the Tier-A harness.
2. **Differential assay detail** (§7) — for `subject_reduction`,
   `infer_check_agreement`, `normalization_stability`, `conversion_termination`,
   `erasure_preservation`: exact assertion, feeding generator, oracle strategy.

## 13. Relationship to the broader initiative

Antigen is the **audit engine** of the "soundness audit first" decision. Its
findings feed a separate fix-scoping step. The known fixes already on the table —
the mutual-recursion checker, the `Vector` → `Std.Array` rename plus the new
length-indexed `Vector`, the emit unused-var cleanup — are their own specs;
Antigen's job is to catch them and keep them caught.

# Antigen pre-port banking — the antibody work to do now

**Status:** implementation-scoped design for a single Antigen run. Banks, *before*
any transliteration port lands, every antibody that today's surface/Core forms
can already express — plus the roadmap's port-independent coverage fills. The
ordering rationale (why before) comes from the transliteration program's TDD
discipline; this spec is its "bank-now" half. Challenges that **cannot** be
expressed until a port's new surface forms exist are explicitly *not* here —
they are folded into the transliteration program spec's per-cluster gates.

Related:
[`2026-07-02-idris-transliteration-program-design.md`](2026-07-02-idris-transliteration-program-design.md)
(the ports these antibodies precede; §8 gate 4 carries the syntax-gated half),
[`2026-07-02-idris-parity-roadmap.md`](2026-07-02-idris-parity-roadmap.md)
(rows A1–A4, A9, #19, #23 executed or corrected here),
[`2026-07-01-antigen-tier-a-design.md`](2026-07-01-antigen-tier-a-design.md)
(the apparatus itself: challenges, assays, corpus, replay).

## 1. Goal and non-goals

**Goal.** Two kinds of banking, split by verdict polarity:

- **Soundness antibodies (must-reject).** Programs that are ill-founded /
  ill-typed *by construction* and must stay rejected. They replay `:ok` under
  today's conservative checker and their only failure window opens at the
  moment a port makes the checker more permissive — so the net must exist
  before that transition. Authoring them now, from the reference literature's
  counterexamples rather than from the port's own case analysis, decorrelates
  them from the code they will guard. Load-bearing for P1 (size-change
  termination), the one port cluster with **no kernel backstop**.
- **Reach pins (must-eventually-accept).** Programs that are well-founded by
  construction but conservatively rejected today. Their ground-truth label is
  recorded now; their *current* rejection is pinned so drift in either
  direction is loud; the port run that achieves them migrates them into the
  main corpus (§3 D2). These are the port's red tests, written early.

**Non-goals:** the A8 term-generator engine (designed separately); A5/A6
verticals (own track, roadmap §3.2); E-layer unit tests for the P5 unifier
(Antigen assays run the kernel — Miller-pattern guards are ordinary elab tests
at P5 time); any challenge gated on not-yet-existing surface syntax (P2 nested
patterns, P3 dot/forced patterns, P4 `with` — transliteration spec §8).

## 2. Verified findings that shape the design

1. **The replay harness requires `:ok` from every committed entry.**
   `test/antigen/corpus_replay_test.exs` replays `corpus.sexp` + `seeds.sexp`
   and asserts no entry violates its assay invariant. A reach challenge
   (ground truth `:terminating`, currently rejected → `{:violation,
   {:wrongly_rejected, …}}`) therefore cannot enter those stores yet — hence
   the separate reach store (D2).
2. **The Totality assay's labels are two-sided.** `:diverging` → *no* focus
   def may certify (violation = soundness infection); `:terminating` → *all*
   must certify (violation = incompleteness). Both polarities of this spec map
   onto existing assay semantics; no new assay logic is needed for W1/W2.
3. **Stale artifacts from the mutual-recursion fix.**
   `Antigen.Generators.Totality.diverging_mutual_pair/0`'s @doc and `note:`
   still describe the hole as live ("`Certificate.calls?/2` misses the cycle
   … wrongly certified"), and roadmap A1/§3.1 still show 🔴 — but the fix
   landed (`d13d718`) and the assay test asserts the sound behavior. Hygiene
   is W6.
4. **The atom table is a closed, load-time-interned set.**
   `Antigen.Challenge.@known_atoms` must list every kind, label, and
   generator-produced name or `:safe` corpus decode fails in processes that
   never loaded a generator. Every work item that mints names extends it.
5. **Known-label discipline is the oracle rule.** A challenge's label must be
   correct *by construction* (the generator is the oracle), cross-checked
   against the real checker in tests. Every challenge below states its
   ground-truth argument in its @doc.

## 3. Design decisions

- **D1 — Bank must-reject antibodies before the port that could break them.**
  For W1 specifically: draw the adversarial set from the size-change
  literature (Lee–Jones–Ben-Amram's counterexamples) and Agda's termination
  regression suite, not from intuition about the future port — independence
  from the implementation is the point.
- **D2 — Reach pins live in a third store, `test/antigen/reach.sexp`,** same
  record format, ground-truth labels; records are never edited, only
  migrated (the one sanctioned move, below). A dedicated
  replay test asserts each entry currently replays to its *documented*
  violation (e.g. `{:violation, {:wrongly_rejected, [:even, :odd]}}`) — so an
  accidental acceptance (verdict flips to `:ok`; possible unsoundness
  elsewhere) and an accidental change to the violation's own shape (still
  rejected, but for a different reason or a different affected-name set
  than documented) are both loud. The port run that closes the gap (P1 for all
  initial entries) migrates the record to `corpus.sexp`, where the ordinary
  `:ok` replay and its never-pruned rule take over. Migration is
  append-there + remove-here in the port's commit; the record's content is
  byte-identical before and after.
- **D3 — Labels state mathematical truth, never checker behavior.** A
  well-founded mutual pair is `:terminating` even while the checker rejects
  it; *where it is banked* (reach vs. corpus) encodes the checker's current
  reach. This keeps the corpus meaningful across checker generations.
- **D4 — Audit-first per work item.** Each item starts by running its
  challenges against the current kernel. A must-reject challenge the kernel
  *accepts* is a live soundness hole discovered early: stop banking, report
  it, fix it red-green per the house testing rule, then bank the antibody as
  the regression guard. Symmetrically, a must-*accept*-today challenge (W3's
  deletion-rule case; W5's cumulativity / two-universe cases — not W2, whose
  reach pins are *expected* rejected) that the kernel wrongly rejects is an
  incompleteness surprise, not a soundness hole: per D3 its ground truth
  doesn't change, so it reroutes to `reach.sexp` under D2 instead of
  blocking the work item — it is not banked in `corpus.sexp` until the
  kernel actually accepts it. This is exactly how roadmap #19's "verify"
  half (W4) resolves either way.

## 4. Work items

### W1 — adversarial diverging set (pre-P1 soundness net; subsumes roadmap A9)

Extend `Antigen.Generators.Totality` with by-construction diverging
`:def_group` challenges, each banked as an antibody in `corpus.sexp` with an
assay test:

- **3-cycle:** `f → g → h → f`, no self-reference in any body (generalizes
  the banked 2-cycle).
- **Indirect cycle through a genuinely total mediator:** `f` calls `total_id`
  applied to a `g`-call, `g` calls `f` — the cycle exists but every direct
  callee looks innocent.
- **Argument-permuting mutual pair:** `f x y = g y x`, `g x y = f x y` —
  size-preserving swaps; every argument is "≤", none is "<". The classic
  size-change discriminator: a naive "some argument shrinks somewhere"
  checker wrongly certifies it.
- **Constructor-regrowing self-call:** `f` recurses on a value it first
  re-wraps (`f (S (pred n))`-shaped) — descent claimed by shape, refuted by
  size.
- **One-leg-decreasing mutual pair:** `f (S n) = g n`, `g n = f (S n)` — one
  call strictly decreases, the composed cycle does not. LJB's motivating
  case: certification must consider cycle *composition*, not individual
  calls.

All five must replay `:ok` today (the conservative checker rejects every
mutual group and W1's self-calls are non-structural) and forever after P1.
Ground-truth divergence argument goes in each @doc.

### W2 — reach pins for P1 (the port's red tests, banked early)

Well-founded-by-construction `:def_group` challenges, label `:terminating`,
banked in `reach.sexp` (D2):

- **Structural mutual pair:** `even`/`odd` over `Nat`, each recursing on the
  predecessor through the other.
- **Lexicographic two-argument descent:** an Ackermann-shaped definition —
  first argument decreases, or stays while the second decreases.
- **Permuted well-founded pair:** descent visible only after tracking
  arguments across a swap (the accept-side twin of W1's permuting rejecter).

The reach replay test pins today's `{:violation, {:wrongly_rejected, …}}` for
each. P1's acceptance gate flips these by migration, not by editing tests
ad hoc.

### W3 — occurs-check + deletion-rule antibodies (roadmap A2, ledger #23)

The kernel case unifier implements both rules; neither has a named antibody.
Extend `Antigen.Generators.Indexed` with `:indexed_case` challenges: a
cyclic-index equation the occurs-check must refuse to solve (`:ill_typed` /
must-reject path), and a syntactically-identical-index equation the deletion
rule must discharge (`:well_typed` acceptance path). Bank both; name them in
the assay tests alongside the existing `inject`/`discharge` probes.

### W4 — positivity escape-hatch antibodies (roadmap A3, ledger #19)

Three classic escapes, each first *audited* (D4) then banked via
`Antigen.Generators.Positivity` as `:family` challenges, label `:negative`:

- **Negative position, arrow-left:** `MkBad : (Bad -> Nat) -> Bad`.
- **Nested/through-constructor:** the family under a previously declared
  wrapper (`MkBad : Box(Bad -> Nat) -> Bad`) — recursion hidden one type
  layer down.
- **Double negation:** `MkBad : ((Bad -> Nat) -> Nat) -> Bad` — positive by
  naive polarity-flip counting once, negative in fact for strict positivity.

If the kernel accepts any of them, D4's stop-and-fix path applies and #19's
status becomes a confirmed-then-closed hole rather than a verification.

### W5 — universes vertical (roadmap A4; first coverage of an entire kernel subsystem)

New assay + generator + tests for the rules ledger row #20 says the kernel
enforces but nothing exercises: `Type l : Type l` self-membership must
reject; cumulativity (`t : Type 0` usable at `Type 2`) must accept; the
two-universe constructor-field rule violation must reject; the fixed 0–2
ceiling must reject `Type 3`-shaped inputs at the representation boundary.
Challenge shape: these are plain typing judgments, so either reuse the
def-shaped `:indexed_case` kind with `well_typed`/`ill_typed` labels or add
a minimal `:universe` kind — the run decides; either way `@known_atoms`
grows and the replay registry gains `"universes" => Assays.Universes`.

### W6 — hygiene: retire the stale hole narrative

Fix `diverging_mutual_pair/0`'s @doc and `note:` to the post-fix truth
(mirror `corpus_replay_test.exs`'s moduledoc, which already has it right);
flip roadmap A1 to done and §3.1's `totality/diverging` strength cell from
"🔴 checker fails it" to its regression-guard status; note rows #13's 🔴
correction (also assigned to the transliteration program's P0 — whichever
runs first does it, the other verifies).

## 5. Acceptance gates

1. Full suite + corpus replay green; the new reach replay green (pinning
   violations, not `:ok`).
2. Every new generator name interned in `Challenge.@known_atoms`; a decode
   round-trip test per new record shape.
3. Every challenge @doc states its by-construction ground-truth argument.
4. Any W3/W4/W5 audit surprise where the kernel wrongly accepts a
   must-reject challenge is reported as a soundness finding and fixed
   red-green before its antibody banks; the K diff, if any, is called out
   as a TCB change. A symmetric surprise where the kernel wrongly rejects a
   must-accept-today challenge (W3, W5) reroutes that entry to
   `reach.sexp` per D4 instead.
5. Roadmap ledger updated: A1 ✅ (stale-closed) with parity-ledger `#13` and
   §3.1's `totality/diverging` strength cell corrected to match (W6); A2/#23,
   A3/#19, and A4 each resolved per audit outcome (✅ if every challenge
   banks as designed; left open if D4's incompleteness reroute sends an
   entry to `reach.sexp` instead); A9 ✅ (subsumed).

## 6. Sequencing

One autopilot run, items ordered **W6 → W1 → W2 → W3 → W4 → W5** (hygiene
first so every later @doc is written against the corrected narrative; W1/W2
next because the transliteration program's P1 blocks on them; W5 last as the
only item introducing a new vertical). The run precedes P1 by construction —
that ordering is the entire point of this spec.

## 7. Out of scope

A5 (conversion vertical), A6 (ctor-formation vertical), A8/A10 (term
generator + wiring), A7/#25 (④ surface corpus — post-④), all syntax-gated
port challenges (transliteration spec §8 gate 4), and any kernel change
except one forced by a W3/W4/W5 audit surprise under gate 4.

# Antigen elab-tier dot-forcing vertical — design

**Date:** 2026-07-08
**Initiative:** F (task #16), queued behind #12 (dot-syntax tail) for execution.
**Layer:** A (Antigen) only — no elaborator, kernel, or parser changes. Pure test-side addition.

## 0. Why: the oracle-boundary blind spot

The existing `forcing/dot` vertical (`Antigen.Assays.DotForcing`, ledger row #24) is a
**value-level known-label oracle**: it builds a kernel context from the v1 sig menu,
computes the branch-unify substitution, and calls the named-implicit check directly
through the `Cure.Elab.Elaborator.forced_check_probe/7` shim. Its entry point is *below*
the check's call sites.

The C-a defect (ledger row #5 tail, fixed by #12's Task 2) was a **call-site omission
one level up**: `elaborate_matched_branch` routed carried-eq branches to
`elaborate_carried_eq_branch`, which never invoked `check_named_implicits` at all. The
value oracle is structurally blind to this class:

1. Every challenge it generates calls the check *by construction* — it can never
   observe a caller that forgets to.
2. The condition selecting the carried path (a sibling whose type mentions the
   scrutinee's stuck index, detected by `detect_carried_index`) is not representable
   in its payload space (family, ctor, indices, name, written term). No payload makes
   the shim take or skip a dispatch path the shim does not have.

The fix is not to bend that assay but to add challenges **one tier up**, entering at
`Cure.Elab.Program.elaborate/1` — and that tier already exists: `Antigen.Assays.Elab`
consumes `:elab_program` challenges carrying raw surface source (`elab/completeness`,
`elab/metamorphic`, `elab/erasure`, `elab/soundness`). This design adds a dot-forcing
generator family to it. The `elab/erasure` family is the direct precedent: a two-sided
`expect:` catalog plus a metamorphic `:same`/`:flip` relation form.

**Rejected alternative** (recorded for the endgame): raising `forced_check_probe`'s
entry point to `elaborate_matched_branch/10`. That function carries 10 arguments of
elaborator-internal state; a shim reconstructing that state drifts from the real caller
— exactly the failure mode the #12 plan review caught (the plan wrongly assumed the
probe called `check_named_implicits`; it reimplements it inline and had already
diverged once). The value oracle stays as the unit tier for the check function itself;
this vertical is the integration tier for its call-site wiring.

## 1. Design overview

Two small additions, mirroring the `ElabErasure` shape verbatim:

- **`lib/antigen/generators/elab_dot_forcing.ex`** (`Antigen.Generators.ElabDotForcing`)
  — a deterministic fixed catalog (no corpus banking, like `ElabComplete`/`ElabErasure`)
  of self-contained surface modules with two-sided expected verdicts, plus metamorphic
  `:same`/`:flip` variants.
- **Two new `run/1` clauses in `lib/antigen/assays/elab.ex`** for assay
  `"elab/dot_forcing"` — a catalog clause (verdict must equal `expect`) and a relation
  clause (`:same` / `:flip`), mirroring the two `elab/erasure` clauses, with distinct
  violation tags.

The known-label discipline survives the move up the stack because the **generator
writes both the forced solution and the written dot value itself**: matching `hmk`
against `H(S(j), …)` pins `m := j`, so a catalog entry that writes `{m = .j}` is
accept-by-construction and one that writes `{m = .(S(j))}` is reject-by-construction.
No reference oracle (Idris) is consulted at assay time.

## 2. The catalog

### 2.1 Axes

The catalog is the product of the two axes the C-a class demands, plus the C-c
quantity axis:

- **Dispatch path**: `plain` (ordinary solved-verdict branch) × `carried` (a sibling
  `w : G(app(p, q))` forces `detect_carried_index` to fire — the mixed forced+carried
  `H`/`app`/`G` shape from #12's Task 2).
- **Dot outcome**: `right` (written value = forced solution → accept) × `wrong`
  (written value ≠ forced solution → reject, error head `:forced_pattern_mismatch`).
- **Unforced quantity (C-c)**: `bind_erased` (unforced named implicit bound and used
  only erasedly → accept) × `bind_relevant` (bound and used in a computationally
  relevant position → reject, error head from the Relevance check).

Six cells total: {plain, carried} × {right, wrong} = 4 cells for the forced axis,
plus {bind_erased, bind_relevant} = 2 cells for the unforced axis. The unforced axis
is **not** crossed with dispatch path — it is tested on the plain/existential shape
only (§2.2's Pack/Vec reuse), for two reasons: (1) no fixture combining a carried
sibling (which needs a stuck computed index, as in `H`/`app`/`G`) with an existential
unforced ctor param (as in `Pack`'s `m`) exists in #12's landed or planned work, and
inventing one would violate §2.2's reuse principle; (2) #12 Task 4 computes the
named-implicit split and the renamed `branch_names` **once, before** the plain/carried
dispatch fork, specifically so the binding decision is dispatch-invariant — a carried
variant of `bind_erased`/`bind_relevant` would consume the identical upstream split
result and exercise no code path the plain variant doesn't already cover. Every cell's
label is correct-by-construction; the carried column of the forced axis is precisely
what no existing Antigen challenge could reach.

### 2.2 Sources

Catalog surface programs **reuse the shapes landed by #12** — rather than inventing
new ones — but the two source tiers are NOT interchangeable, verified post-landing
(#12 is now merged, commits 1d75ecf…bb077c5):

- **Forced-axis carried cells** (`carried × right`/`carried × wrong`) MUST source
  from the **Task-2 unit-test fixtures** in `test/cure/elab/named_implicit_tail_test.exs`
  (the "wrong dot on a carried-eq branch rejects" / "right dot ... accepts" tests) —
  these are the only landed programs that actually reach `elaborate_carried_eq_branch`.
  **They do NOT come from `nidot` ni03/ni07.** ni03/ni07 landed as a *simplified
  two-index directly-invertible* family instead (Idris cannot express the genuine
  stuck-function-application differential — `app(as, bs)` unifying against
  `app(p, q)` — without a `with` block, so the #12 plan's own contingency substituted
  `type H indices (n: Nat, k: Nat) / hmk : H(S(m), m)`, where **both** indices solve
  directly and the branch never reaches the carried dispatch at all). Treating
  ni03/ni07 as carried-shape sources (as an earlier draft of this spec did) is a
  factual error — verified against the landed fixture text.
- **Forced-axis plain cells** and **unforced-axis cells** may still use ni01/ni02
  (a `Vec`-family plain right/wrong precedent) or ni05/ni06 (confirmed verbatim
  matches of Task 4's Pack/Vec bind-erased/bind-relevant shapes) respectively, or the
  H/app/G family with the sibling omitted — whichever the implementer finds cleanest;
  **the landed fixture wins** on any divergence from this spec's sketch.

The real carried preamble (verified in `named_implicit_tail_test.exs`, not `nidot`) is
the `H`/`app`/`G` menu:

```
type SList = SNil | SCons(Nat, SList)
fn app(xs: SList, ys: SList) -> SList = match xs
  SNil() -> ys
  SCons(h, t) -> SCons(h, app(t, ys))
type H indices (n: Nat, xs: SList)
  hmk : H(S(m), app(as, bs))
type G indices (xs: SList)
  gwrap : G(cs)
```

with probe fns of the #12 Task-2 shape (`v: H(S(j), app(p, q))` scrutinee; the
carried variant adds the sibling `w: G(app(p, q))`, the plain variant omits it) and
branch bodies of the landed `-> Z()` form — **not** `-> j`: `j` is an erased implicit
(`{j: Nat}`), so a body returning it directly trips `{:erased_used_relevantly, …}`
(the unforced-axis's own error), which would confound the dot-outcome axis (right/wrong)
with the C-c quantity axis this catalog keeps deliberately separate. The unforced
cells reuse the ni05/ni06 `Vec`/`P`-style shape (confirmed verbatim match). The plan
copies the exact landed fixture text at implementation time; if a landed fixture
differs from this spec's sketch, **the landed fixture wins**.

**Structural note for §2.4's reused transforms:** the catalog needs **two** fixed
preambles, not one — the `H`/`app`/`G` block above for the forced axis's 4 cells, and
a separate Vec/Pack preamble (Task 4's `@exist_preamble`) for the unforced axis's 2
cells — so `ElabDotForcing.module/2` should mirror `ElabComplete`'s two-preamble
`module(pre, body)` form (an atom selecting which preamble), not `ElabErasure`'s
single-preamble `module/1`. Either way, each catalog cell's `body` passed to `module/2`
is *only* its small probe-`fn` text, never the preamble. This split matters because
`ElabComplete`'s regex-based `alpha_rename`/`prepend_unused_param` transforms are
reused, and they operate on `body` alone, never on `preamble <> body` — that is what
already lets `ElabComplete`'s own `:slist_f` preamble (which also defines a helper
`fn app` ahead of the probe fn, in its `computed_idx/rebuild` catalog entry) avoid
corruption: `prepend_unused_param`'s brace-anchored regex (`fn \w+\(\{`) only ever
matches a probe fn's own `{…}`-leading implicit param list, never `app`'s
`(xs: SList, …)` signature, and this holds regardless of preamble content precisely
*because* the preamble is never in the string the transform sees. Implementation must
preserve this split — pass only the probe-fn body to the transform functions, never
the concatenated module text — or the transform's first-match semantics are no longer
guaranteed collision-free.

### 2.3 Payload and expected-error hardening

Catalog challenge payload: `%{id, src, expect}` with `label: expect`
(`:accept | :reject`), matching `ElabErasure`. Reject cells additionally carry
`expect_error:` — the expected error head atom for the two reject cells this
catalog actually has (per §2.1's six cells): `:forced_pattern_mismatch` for the
forced-axis `wrong` cells, and `:erased_used_relevantly` for the unforced-axis
`bind_relevant` cell (the Relevance check's error head, per #12 Task 3/4 — not a
named-implicit error at all, since by the time Relevance runs the binding has
already succeeded). `:named_implicit_unforced` is NOT one of this catalog's error
heads — that atom is the pre-existing dot-on-unforced-position reject (Task 4's
third, guard-only test; unaffected by C-c since it uses dot notation, not the
bare-variable form C-c binds), already pinned by #12's own unit tests and by
`dot_forcing.ex`'s value-level oracle. It is out of scope for this catalog (neither
a wiring-omission concern like C-a nor a quantity-gate concern like C-c), so its
2-tuple shape is noted here only as a cross-codebase invariant this work must not
disturb, not as a cell this catalog tests. The assay checks the head when present,
so a fixture that rots into rejecting for an unrelated reason (parse error, arity
error) is a violation (`{:dot_forcing_wrong_reject_reason, id, got}`), not a silent
pass. Both of this catalog's genuine reject errors arrive at `Program.elaborate/1`
unwrapped — `{:error, {:forced_pattern_mismatch, _, _}}`, `{:error,
{:erased_used_relevantly, _}}` — with no intermediate `{:def, name, …}` or similar
wrapping anywhere in the `elaborate_matched_branch` / `elaborate_branches` /
`Declarations` / `Program` chain (every `with` in that chain has no `else`, so the
tuple check_named_implicits or Relevance produces propagates verbatim); the assay's
head check is therefore a plain `elem(e, 0)` against `e` from `{:error, e}` for
every genuine elaboration-stage reject.

**Non-tuple hardening.** `e` is not always a tuple: `Program.elaborate/1` propagates
lexer/parser front-end errors unwrapped too, and those two stages disagree in shape —
a lexer failure is a tuple (e.g. `{:unexpected_character, ?$, line, col}`), but a
parser (grammar) failure is a **list** (`Parser.parse/2`'s `{:error,
Enum.reverse(errors)}`, `lib/cure/compiler/parser.ex:95-98`). A bare `elem(e, 0)`
would crash with `ArgumentError` on the list case rather than reporting
`{:dot_forcing_wrong_reject_reason, …}`. The assay's head check must therefore guard
the shape: `if is_tuple(e), do: elem(e, 0), else: :non_tuple_error` (or equivalent) —
a non-tuple `e` never matches any `expect_error` atom, so it always correctly falls
into the wrong-reject-reason violation instead of crashing. §6's "reject-for-the-
wrong-reason" test fixture (a syntax error) must specifically be a source that fails
at the elaboration stage (or, if it deliberately exercises the parser front-end, one
whose brokenness is a lexer-stage error — an illegal character reliably lexes to a
tuple; an ill-formed-but-lexable grammar construct reliably returns the parser's list
— so a grammar-stage typo without the guard above would crash the test itself, not
merely fail an assertion).

### 2.4 Metamorphic forms

- **`:flip` — the C-a detector.** Each accepting base is paired with a
  verdict-flipping mutation that must turn accept into reject:
  - `corrupt_dot`: rewrite the written dot value (`{m = .j}` → `{m = .(S(j))}`) on
    both the plain and the carried base. On pre-#12 code the carried instance of this
    relation FAILS (the variant still accepts because the carried path skipped the
    check). Note this is not the *only* cell that would have caught C-a pre-#12 — the
    plain catalog cell (§2.1's `carried × wrong`, `expect: :reject`) independently
    reports `{:dot_forcing_verdict_wrong, …}` on the same pre-fix behavior (actual
    `:accept` vs. expected `:reject`), no relation needed. What the `:flip` form adds
    beyond the catalog cell is not detection-uniqueness but a *causal* pin: it holds
    the base program fixed and varies only the dot value, so a failure of this
    specific challenge locates the defect as "the check doesn't run/doesn't compare"
    rather than "this program happens to mis-elaborate" — the same accept/flip
    contrast `promote_use` (below) uses to prove the C-c gate load-bearing, and the
    same reasoning `ElabErasure`'s own `relevance_injection` uses for its check.
  - `promote_use`: on the `bind_erased` base, rewrite the body to use the bound name
    in a relevant position — proves the C-c quantity gate is load-bearing. (Only one
    base exists for this cell — per §2.1 the unforced axis isn't crossed with dispatch
    path — so there is no second "carried path" instance of this mutation to run.)
- **`:same`.** Typing-preserving perturbations must not change the verdict:
  α-rename and prepend-unused-implicit-param, following `ElabComplete.variants/1`
  (arm reorder is inapplicable — the menu families are single-constructor). Applied
  to each catalog base.

Relation payload: `%{id, transform, relation, base_src, variant_src}` — same shape as
`elab/erasure`'s relation form.

## 3. Assay clauses

Added to `Antigen.Assays.Elab` (they mirror the `elab/erasure` clauses; the
duplication is deliberate — one clause per assay family with distinct violation tags
is the file's existing style):

- Catalog: elaborate `p.src`, collapse to the accept/reject bit; violation
  `{:dot_forcing_verdict_wrong, id, %{expected, actual}}` on mismatch. When
  `expect_error` is present and the verdict is a reject, the error head must match —
  extracted via the non-tuple-safe guard in §2.3 (a non-tuple error is never a match,
  so it falls into the wrong-reject-reason violation rather than crashing).
- Relation: elaborate base and variant; `:same` requires equal bits, `:flip` requires
  `base == :accept and variant == :reject`; violation
  `{:dot_forcing_relation_wrong, id, transform, %{relation, base, variant}}`.

A raised exception inside `elaborate/1` is already normalized by the existing
`elaborate/1` helper in the assay module and counts as reject for the bit — consistent
with `elab/erasure`.

## 4. What does not change

- `lib/antigen/assays/dot_forcing.ex` + `lib/antigen/generators/dot_forcing.ex` (the
  value-level unit tier) — untouched by this work. **Resolved post-#12-landing:**
  Task 6 already rewrote the moduledoc's stale "does NOT cover the carried-eq motive
  branch" note (verified in the tree — it now cites "spec 2026-07-08" and the `nidot`
  ni03/ni07 differential directly). The conditional pointer this section originally
  described is therefore moot: no edit to that moduledoc is a spec obligation. (Note,
  not itself part of this spec's scope to fix: the landed moduledoc's claim that
  ni03/ni07 exercise the carried-eq branch "end-to-end" repeats the same ni03/ni07
  misattribution §2.2 corrects above — ni03/ni07 are the simplified non-carried
  family, so that sentence is arguably now stale in a different way. Flagged for the
  operator; out of scope for this design doc to patch already-landed code.)
- No changes under `lib/cure/` at all. If implementation discovers an elaborator
  behavior contradicting a catalog label, that is a STOP-and-report (it means either
  #12 landed differently than planned or a genuine infection) — not a license to
  patch the elaborator in this chain.
- The existing `elab/*` families, their generators, and their tests.

## 5. Wiring and execution points

Challenges execute wherever `ElabErasure`'s do: a dedicated deterministic test file
(`test/antigen/elab_dot_forcing_test.exs` — directly under `test/antigen/`, NOT
`test/antigen/generators/`, which is a different family of kernel-primitive generator
unit tests, e.g. `dot_forcing_test.exs`, `branch_unify_test.exs`; `elab_erasure_test.exs`
and `elab_completeness_test.exs` both live directly under `test/antigen/`, confirmed by
directory listing — mirroring `test/antigen/elab_erasure_test.exs`'s structure) that
runs every catalog and relation
challenge through `Antigen.Assays.Elab.run/1` and asserts `:ok`, plus
assay-discrimination tests (see §6). At plan time, grep for every execution/registration
point that references `ElabErasure` (runner, e2e, corpus, health gates) and mirror each
one; the spec requirement is **parity of wiring with `elab/erasure`**, whatever that
set turns out to be. **Verified at spec-review time:** that set is currently just
`ElabErasure`'s own test file — `grep -rn ElabErasure` outside
`lib/antigen/generators/elab_erasure.ex` and `test/antigen/elab_erasure_test.exs`
finds no runner script, e2e test, corpus-banking entry, or health-gate config
referencing it (`test/antigen/corpus.sexp` has zero `elab_program`-kind records, and
`Mix.Tasks.Antigen.default_gen/0` does not include the elab generators — the whole
`elab/*` family runs off each generator's own dedicated test file, not corpus
banking or the default random-generation runner). So parity of wiring is satisfied by
the single dedicated test file above; a re-grep at plan/implementation time is still
required (this could change), but finding nothing beyond the test file is the
*expected* outcome, not a sign the search was incomplete.

## 6. Testing the vertical itself (red-green discipline)

The deliverable is test infrastructure, so the red-green cycle targets the vertical's
own discrimination (mirroring `elab_completeness_test.exs`):

1. **Generator unit tests** (red first: module absent): catalog size and cell coverage
   (all six cells present per §2.1 — the 2×2 forced axis and the 2-cell unforced axis
   — each axis value represented), every `src` elaborates to its `expect` bit — this is
   also the end-to-end proof the fixtures are live post-#12.
2. **Assay discrimination**: a hand-built challenge with a deliberately wrong `expect`
   must yield the catalog violation; a relation challenge with `variant_src ==
   base_src` under `:flip` must yield the relation violation; a reject-for-the-wrong-
   reason source with `expect_error` set must yield `{:dot_forcing_wrong_reject_reason,
   …}` — use a source that is well-formed enough to reach elaboration and reject there
   for an unrelated reason (e.g. an undefined variable/constructor), or, if
   deliberately probing the front-end, a single illegal character (a lexer-stage
   reject, whose error is tuple-shaped). Do NOT use a grammar-level typo as this test's
   fixture: per §2.3's non-tuple hardening, a parser-stage failure returns a *list*,
   which is exactly the shape the guard is for — a fixture chosen without reading that
   guard risks silently testing only the tuple path.
3. **No new full-suite gate semantics**: the new test file joins the ordinary
   `mix test` set; the Antigen campaign gate covers it via the wiring-parity of §5.

Tests are behavioral and immutable once green.

## 7. Sequencing and constraints

- **Execution gate: satisfied.** #12 has completed and merged (commits
  1d75ecf, 7a2febe, b4c1267, 8568d4b, 9046bb4, 44b68eb, bb077c5 are on-branch,
  stable, no further concurrent churn on the files this spec touches) — this work
  is unblocked. (Historical note, kept for record: the gate existed because the
  catalog labels assume post-Task-2 behavior — pre-Task-2 code would have made the
  `carried × wrong` cell's label wrong by design.)
- File-collision audit vs #12: this work creates `elab_dot_forcing.ex` (new),
  `elab_dot_forcing_test.exs` (new) and appends clauses to `assays/elab.ex` — none of
  which #12 touched, confirmed retrospectively clean now that #12's diff is final.
  The §4 moduledoc question is likewise resolved (Task 6 already rewrote it; no
  pointer edit is owed by this work).
- Standard batch constraints apply: ghost commits, explicit-pathspec staging, one
  `mix` invocation at a time, two-pipeline steer in any subagent brief (the dependent
  machinery is `lib/cure/elab/*` + `lib/cure/core/*`; `lib/cure/compiler/*` and
  `lib/cure/types/*` are decoys).

## 8. Generality

This establishes the reusable pattern for **call-site-wiring properties** that value
shims structurally cannot probe: enter at `Program.elaborate/1` with
correct-by-construction labels, and encode "the check is actually invoked on path P"
as a `:flip` relation whose mutation targets exactly the checked property. Future
candidates (not in scope): splice-site reconstruction (C-b class), dispatch
inheritance for future branch kinds, guard-check wiring once match-embedded guards
land.

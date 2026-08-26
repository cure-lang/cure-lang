# Antigen deep cut: indexed-family `case` soundness — design spec

**Status:** approved design, spec drafted for self-review.
**Branch:** `autopilot/cure-dependent-types-frp` (worktree `.claude/worktrees/cure-dependent-types-frp`).
**Depends on:** [[antigen-metatheory-engine]] Tier A (totality + positivity + reflexivity), already implemented and merged into this branch. Reuses its harness plumbing (see §3 for the one required extension: a new `Antigen.Challenge` kind).
**Vertical name:** `indexed`. Assay key: `indexed/case`.

## 1. Why

Antigen's Tier A went deep on **totality** (the confirmed mutual-recursion hole, now fixed) and touched **positivity**. A manual read of `Cure.Core.Kernel`'s dependent-`case` typing (`infer/2` on `{:case,...}`, `check_coverage/3`, `check_case_branches/5`, `branch_index_subst/4`, `specialize_branch_context/2`, `check_motive_wf/3`) surfaced four concrete target hypotheses where a soundness hole could live — the same "found one hole by hand, build an engine to find more" motivation that started Antigen:

1. **Branch-family discipline.** `check_coverage/3` only checks `declared ⊆ covered` (`MapSet.subset?`). It never checks the reverse: a branch naming a constructor of an *unrelated* family is not rejected at that point. It flows into `check_case_branches/5`, which looks the constructor up in the *global* constructor namespace (not scoped to the scrutinee's family) and checks its body against the motive at that foreign constructor's own computed indices. Possible category-confusion route into the type checker.
2. **Coverage exactness.** Untested in the other direction: an omitted required branch must produce `{:error, :coverage}`.
3. **Index-refinement soundness — the crown jewel: compound-index refinement gap.** `branch_index_subst/4` only records a substitution when a constructor's declared result index is a bare `{:var, i}` (line ~548); the `{_other, _}` clause silently **drops** any compound (or ground, non-variable) result index (e.g. `S k`, `and(d1, d2)`, or a nullary literal like `Z`). Refinement is incomplete for computed-index families — the open question is whether a dropped equation ever lets a branch body typecheck under an assumption that doesn't actually hold at that branch.
4. **Motive well-formedness.** `check_motive_wf/3` — untested in the negative direction: a malformed motive (not a valid type family over the index telescope + scrutinee) must be rejected as `{:error, :bad_motive}`.

These four obligations are the entire non-trivial surface of dependent `case` typing. Unlike totality (which needed only two known labels, terminating/diverging), this vertical has **four independent obligations**, each bidirectional (accept the good case, reject the bad case) — hence "deep cut."

**Considered and ruled out: "impossible-branch inhabitation."** An earlier draft of this spec additionally hypothesized that requiring an *ordinary* (non-absurd) body for a branch whose declared result index provably conflicts with the scrutinee's actual index — e.g. a `succ`-branch body when the scrutinee is statically known to have index `Z` — was itself "a direct, first-class route to inhabiting `⊥`." Tracing `infer/2`'s `{:case, ...}` clause shows this is **not** a real, independent hole: the case expression's *overall* inferred type is `apply_motive(motive_value, scrut_indices ++ [scrut_value])` (line ~192), computed solely from the scrutinee's own honest indices/value — it never depends on any branch's body, reachable or not. Each branch (reachable or not) is independently required to produce a genuine term of `motive` applied to *that constructor's own* naturally-computed indices (line ~526-529), which is exactly the standard, sound (if conservative) typing rule for non-refining pattern matches — this is neither laxer for "impossible" branches (they get no free pass; `check_case_branches` always checks every branch's body, with no impossibility-driven shortcut) nor does an easy/ordinary proof for one branch leak into another branch's or the overall expression's type. The only way an unreachable branch's body could be *exploitable* is if it were accepted under a **false premise injected into its context** — which is exactly the compound-index-drop mechanism already covered by hypothesis 3 above, not an independent one. (A residual, genuinely different mechanism — a term whose *ascribed* static index doesn't match the constructor it was actually built with — would be a constructor-injectivity/no-confusion hole, already out of scope per §2.) No obligation is built for this in §4.

## 2. Scope

**In scope:** all four obligations above, delivered **one at a time**, each with its own generator self-test + assay test + real-kernel run + (if it catches a real infection) a kernel fix + permanent antibody, before starting the next.

**Out of scope (explicitly deferred, Tier B or never):**
- The general dependent-term generator (bidirectional-inversion + INDIR). Not needed: every challenge here is built directly as Core (family declarations + constructors + a `case` def), the same way `Generators.Positivity` already hand-builds `SF`/`SVDesc`. See §7 for the YAGNI argument in full.
- Differential assays (subject-reduction, infer/check agreement) over arbitrary generated programs.
- Universe/cumulativity and constructor-injectivity/no-confusion verticals — candidate future deep cuts, not this one.
- Elaborator-level index unification (`lib/cure/elab/unify.ex`) — this vertical targets the **trusted kernel's** `case` checker only, matching Antigen's TCB-first mandate. A hole here is a hole in `Cure.Core.*`; a gap in the elaborator's `unify.ex` would only cause spurious elaboration failures (still safe), never unsoundness.

## 3. Architecture

Reuses the Tier-A harness's plumbing: `Antigen.Gen`, `Antigen.Backend.StreamData`, `Antigen.Corpus`, `Antigen.Report`, `Antigen.Runner`, `Cure.Core.Serialize` (C2), the two-tier capture (`tmp/antigen/` ephemeral, `test/antigen/corpus.sexp` + `seeds.sexp` committed/never-pruned), the static replayer (`test/antigen/corpus_replay_test.exs`), and the architecture test forbidding `StreamData` under `Antigen.Generators.*`/`Antigen.Assays.*`. This is **not** 100% reuse, though: `Antigen.Challenge`'s data model is closed over its existing four `kind`s (`:stub | :def_group | :family | :forcing_pair`) and must be **extended** — see "Required `Antigen.Challenge` extension" below.

**New modules:**

- **`lib/antigen/generators/indexed.ex`** (`Antigen.Generators.Indexed`) — builds each challenge as raw Core: one or two family declarations (`Inductive` family + constructor records), plus a global def whose body is a `{:case, scrut, motive, branches}`, registered directly into a `Cure.Core.Env`/signature — bypassing the elaborator entirely, identical in spirit to `Generators.Positivity` (which already hand-builds non-indexed families this way; genuinely-indexed families with computed result indices built the same way are already proven feasible by `test/cure/core/case_typing_test.exs`'s `Box`/`mk` fixture, which this vertical's generator can follow as a template). One builder function per obligation (see §4), each returning a `Challenge.t()` with `payload: %{families: [...], ctors_by_family: %{...}, def_name: ..., def_type: ..., def_body: ...}` (concrete shape decided at generator-implementation time; whatever it is, it must round-trip through the extension below) and a `label` of `:well_typed` or `:ill_typed`.
- **Required `Antigen.Challenge` extension** — add a new `kind` (e.g. `:indexed_case`) to `Antigen.Challenge.@type kind` and `@known_atoms`, plus:
  - a `to_pieces/1` clause decomposing the payload's family/ctor declarations and the def's type+body into named `Term` pieces (mirroring the existing `:family` clause, extended to a *list* of families and a trailing def), and a matching `from_pieces/7` clause to rebuild it;
  - a `terms_of/1` clause in `Antigen.Coverage` covering the same payload (that module's dispatch is also exhaustive on `kind` and has no fallback);
  - without these, `Antigen.Corpus.encode_record/2` and `decode_record/1` (which call `Challenge.to_pieces/from_pieces` directly) and `Antigen.Runner`'s discard check (which calls `Coverage.terms_of/1`) cannot round-trip or evaluate this vertical's challenges at all — this is a prerequisite for any of §4's generator work, not an incidental detail.
- **`lib/antigen/assays/indexed.ex`** (`Antigen.Assays.Indexed`) — runs `Cure.Core.Kernel.check_def(env, def_name)` and asserts the accept-iff-well-typed invariant:
  - `label: :well_typed` ⟹ expect `:ok` (completeness direction — a real hole here is "the kernel wrongly rejects legal code," annoying but not a soundness bug).
  - `label: :ill_typed` ⟹ expect `{:error, _}` (soundness direction — the kernel accepting this is an **infection**, exactly like `Assays.Totality`'s `:wrongly_certified`).
  - Verdict shape mirrors the existing assays: `:ok` | `{:violation, {:wrongly_accepted, reason}}` | `{:violation, {:wrongly_rejected, reason}}`.

**Unchanged:** `Antigen.Challenge.@known_atoms` gets one addition per PR — the new family/ctor/label atoms this vertical introduces (e.g. `:indexed_case`, `:well_typed`, `:ill_typed`, plus whatever family/ctor names each obligation invents), so a fresh process can decode committed records without having run a generator (the same fix the replayer needed for Tier A).

## 4. The obligation battery (build order)

Each obligation below contributes at least one `:well_typed` and one `:ill_typed` challenge, built by direct Core construction (ground truth is known by *how* the term was assembled — see §7). Built and verified **one at a time**, per the loop in §5.

### 4.1 Branch-family discipline
Two unrelated indexed families, `D` and `E`, each with ≥1 constructor. A `case` on a scrutinee of family `D`, covering **every** constructor of `D` correctly, **plus one additional branch** naming a constructor of `E`.
- `:ill_typed` — the branches are exactly: a correct branch for every declared constructor of `D`, plus the extra foreign-constructor (`E`) branch. This precise shape is load-bearing: `check_coverage/3` only tests `MapSet.subset?(declared, covered)` (`declared` = `D`'s constructor names, `covered` = the branches' constructor names) — it never rejects `covered` having *extra* names beyond `declared`. So `declared ⊆ covered` still holds and `check_coverage` returns `:ok`, letting the challenge reach `check_case_branches/5` (the function under test) with the foreign branch intact. If instead the foreign branch *replaced* one of `D`'s required branches, `declared ⊄ covered` and `check_coverage` would reject it first with `{:error, :coverage}` — a real rejection, but for the wrong, uninteresting reason, and the assay (which only asserts a generic `{:error, _}`) would report a false "confirmed sound" verdict without ever exercising the hypothesized unscoped-lookup hole. The construction must be the additive form to actually test this obligation.
- `:well_typed` — the same `case` with all branches correctly drawn from `D` (the foreign branch omitted), expected accepted.

### 4.2 Coverage exactness
A family with ≥3 constructors.
- `:ill_typed` — a `case` covering only some of them, expected `{:error, :coverage}`.
- `:well_typed` — the same `case` with every constructor covered, expected accepted.

### 4.3 Index-refinement soundness (the crown jewel)
Against a family with a **computed** (non-variable) result index on at least one constructor (e.g. an indexed-`Nat`-like family with a `succ`-shaped constructor whose result index is `S k`, not a bare variable): a branch for the computed-index constructor whose body's typing only succeeds if the (dropped) equation `index = S k` were substituted in; construct the body so that dropping the substitution changes whether it should typecheck.
- `:ill_typed` — a body that is only well-typed *under the false assumption* that the index equation was never applied (i.e., it exploits the gap), expected rejected.
- `:well_typed` — the analogous body that is correctly well-typed with or without the refinement, expected accepted (regression guard that the fix, if any, doesn't over-reject).

### 4.4 Motive well-formedness
- `:ill_typed` — a motive term that is not a valid type family over the index telescope + scrutinee, constructed as **either** (a) an *over*-applied motive (more `lam` layers than `length(index_tele) + 1`, so `apply_motive` leaves a residual `{:vlam, ...}` value) **or** (b) a motive whose fully-applied body is a value that isn't a sort (e.g. an `{:int_lit, _}`-typed body). Either construction is caught by `infer_type_value_sort/2`'s catch-all clause (line ~502) and correctly returns `{:error, :bad_motive}`.
  - **Do not** construct this case as an *under*-applied motive (fewer `lam` layers than `length(index_tele) + 1`). Traced through `check_motive_wf/3` → `apply_motive/2` → `Eval.apply/2` (`lib/cure/core/eval.ex`, clauses only for `{:vlam, _, _}` and `{:vneutral, _}`): applying a non-function, non-neutral value (e.g. the motive resolves to `{:vtype, _}` or `{:vdata, ...}` before all required arguments are consumed) raises an unhandled `FunctionClauseError` rather than returning `{:error, :bad_motive}`. This is a real robustness gap in the trusted kernel (an unhandled crash on malformed input, not a soundness hole — the term is still correctly rejected in the sense that `check_def` never returns `:ok`, but the assay's `{:error, _}` pattern-match would itself raise instead of matching), separate from this obligation's soundness question. Track it as a follow-up hardening item (wrap `check_motive_wf`'s call in a guard, or give `Eval.apply` a catch-all `{:error, :not_applicable}` clause) rather than folding it into this challenge's construction.
- `:well_typed` — a correct motive, expected accepted.

## 5. Per-obligation loop

For each of 4.1–4.4, in order:

1. **Generator self-test** — assert the label is real **by construction**, independent of the kernel's verdict (e.g. "this branch's constructor genuinely belongs to family `E`, not `D`" checked via `Inductive.get_ctor`/family lookup, not via `check_def`). This is the enduring detection proof, mirroring the Tier-A totality self-tests (`refute Certificate.terminating?(mutual)`).
2. **Assay test** — both directions (`:well_typed` → `:ok`, `:ill_typed` → violation), run against the assay module.
3. **Real-kernel run** — `mix test` scoped to this obligation's test file only (one build/test process at a time, per the standing constraint — never run concurrently with another full-suite invocation).
4. **Triage the result:**
   - If the `:ill_typed` case is correctly rejected and `:well_typed` is correctly accepted: obligation confirmed sound, no kernel change, move on.
   - If the `:ill_typed` case is **wrongly accepted** (a real infection): reproduce minimally, fix `Cure.Core.Kernel` (or `Cure.Core.Inductive` as appropriate — e.g. if the fix is scoping a constructor lookup to its family) with its own red→green kernel test, bank the exact reproducing term as a permanent antibody in `test/antigen/corpus.sexp`, and re-run this obligation's assay to confirm it now reports `:ok` (no violation).
   - If the `:well_typed` case is **wrongly rejected** (incompleteness, not unsoundness): do **not** silently change kernel behavior. Log the finding and surface the fix-or-accept decision to the operator before touching kernel code.
5. **Full suite once**, commit, proceed to the next obligation.

This mirrors exactly how the totality vertical caught and fixed the mutual-recursion hole (spec `2026-07-01-antigen-tier-a-design.md` + `AUTOPILOT-REPORT.md`), generalized to four obligations instead of one.

## 6. Regression and corpus

Identical mechanics to Tier A: every confirmed infection's reproducing term becomes a permanent, never-pruned antibody in `test/antigen/corpus.sexp`, replayed statically (no generation) by `test/antigen/corpus_replay_test.exs` on every `mix test`. Known-good challenges (the `:well_typed` side of each obligation) seed `test/antigen/seeds.sexp` via the existing coverage-deduped seed bank. Both stores use the existing tab-delimited, C2-serialized (`Cure.Core.Serialize`) record envelope — no format changes.

## 7. Why no term generator is needed here (YAGNI)

The general dependent-term generator (Tier B, bidirectional-inversion + INDIR, per the research synthesis in [[antigen-metatheory-engine]]) solves a different problem: generating an arbitrary well-typed term when the ground truth ("is this legal?") is *not already known* — which forces the oracle problem (checking the kernel's homework with the kernel itself).

Every obligation in §4 avoids that problem by construction: the label is fixed by *how the challenge is assembled*, not inferred by running the checker. "A branch naming a foreign-family constructor" is ill-typed because we picked two families and wired the mismatch in by hand — no generator or oracle needed to know that. This is exactly the technique `Antigen.Generators.Positivity` and `Antigen.Generators.Totality` already use, and it is what let Tier A catch the real mutual-recursion hole without any general term generator existing. Building the general generator now, because this work is "in the area," would be premature generality for a problem this deep cut does not have — the general generator remains a distinct, later initiative (Tier B) that this spec does not touch.

## 8. Testing

- `test/antigen/challenge_test.exs` and `test/antigen/coverage_test.exs` — extend with cases for the new `:indexed_case` kind (§3's required `Antigen.Challenge` extension): a `to_pieces/1` → `from_pieces/7` round trip that recovers an equivalent challenge (families, ctors, and def all intact), and a `Coverage.terms_of/1` case that returns every embedded `Term`. This is prerequisite infrastructure — write and green it before any of §4's generators, mirroring how the existing `:family` kind is covered in these same files.
- `test/antigen/generators/indexed_test.exs` — one self-test per obligation (§5 step 1), 8 tests total (2 per obligation × 4 obligations: 4.1, 4.2, 4.3, 4.4).
- `test/antigen/assays/indexed_test.exs` — one accept + one reject test per obligation, 8 tests total (same breakdown).
- Any kernel fixes get their own red→green tests under `test/cure/core/kernel_test.exs` (or a new `test/cure/core/case_soundness_test.exs` if the fixes are substantial enough to warrant a dedicated file — decided at fix time, not speculatively now).
- `test/antigen/corpus_replay_test.exs` requires no changes — it already replays whatever is in `corpus.sexp`/`seeds.sexp` generically via the assay registry; this vertical only adds `"indexed/case" => Assays.Indexed` to that registry.

## 9. Success criteria

1. All four obligations (§4) have generator self-tests, assay tests, and have been run against the real kernel — one at a time, with a full suite run between each.
2. Every confirmed infection (an `:ill_typed` challenge the kernel wrongly accepts) is fixed in the trusted kernel with its own red→green test, and its reproducing term is a permanent antibody in `corpus.sexp`.
3. Every `:well_typed` challenge is accepted by the (possibly now-fixed) kernel — no obligation's fix over-rejects legitimate code.
4. `mix test` is fully green at the end: the new tests pass, the existing 2100 tests are unaffected, and the corpus replayer covers the new `indexed/case` entries.
5. Any incompleteness finding (a `:well_typed` case wrongly rejected) is reported to the operator rather than silently patched.

## 10. Non-negotiable constraints carried over

- Serialize each committed record with `Cure.Core.Serialize` (C2); force-intern new atoms in `Antigen.Challenge.@known_atoms`.
- One `mix test`/`mix compile` process at a time — never concurrent (past concurrent runs caused a kernel panic).
- Ghost-written commits; no co-author trailers.
- Antibodies are never pruned once committed.
- **Tests are immutable once green.** Every generator self-test, assay test, Challenge/Coverage round-trip test (§8), and kernel red→green test (§5 step 4) is fixed by changing the *implementation* (kernel, `Antigen.Challenge`/`Antigen.Coverage`, or the generator/assay module) to make it pass — never by weakening, skipping, or deleting the test itself. The sole exception is a test later proven to encode incorrect behavior; that requires first stating in the commit/PR why the test itself was wrong before changing it.

# Dot-syntax tail — close ledger row #5's named-implicit caveats

**Date:** 2026-07-08
**Status:** Approved (operator batch authorization: parity-queue initiative C,
item 1 of 3 — "dp01/dp02 dot syntax (#5 tail)"; match-embedded ctor guards and
Nat→Int erasure follow as their own chains)
**Topic:** dotsyntax-tail

## 1. Problem — three documented caveats keep row #5 at 🟡

The explicit dot-pattern / named-implicit machinery itself landed on
2026-07-04 (`5409184`; ledger row #5): `{k = .e}` on a constructor pattern
asserts the forced erased index `k` is convertible to `e`, wrong dots reject
with `{:forced_pattern_mismatch,…}`, oracle `dotpat` (dp01/dp01b/dp02/dp03
accept + dp06 reject) and `nidot` (ni01 accept + ni02 reject) all `same`. The
row stays 🟡 because of three caveats written into it, all re-verified against
the current worktree (branch `autopilot/kernel-parity-batch`):

- **C-a (missed check on the carried-eq path).** `elaborate_matched_branch/10`
  dispatches `_solved_or_trivial when carried != nil` to
  `elaborate_carried_eq_branch/10` (`lib/cure/elab/elaborator.ex:3181`,
  `:3357`), which receives neither the surface pattern nor the verdict
  substitution and never calls `check_named_implicits/7`. A named-implicit
  annotation on such a branch is **silently discarded** — a *wrong* dot is
  accepted where Idris rejects. Not a soundness hole (the annotation binds
  nothing; the kernel still checks the branch), but a faithfulness bug and a
  false sense of a checked assertion.
- **C-b (spurious error when the body references the scrutinee).**
  `refine_scrutinee_in_body/5` (`elaborator.ex:3533`) substitutes the raw
  surface pattern into the branch body via `subst_surface_var`. If the pattern
  carries a `{:named_implicit_pat,…}` argument, that non-expression node lands
  in expression position and elaboration fails with
  `{:named_implicit_not_in_pattern,…}` (`elaborator.ex:82`) — a spurious
  reject of a program Idris accepts. Re-verification for this spec found a
  second, independent site with the identical failure mode
  (`desugar_as_patterns`, an as-pattern over a named-implicit ctor pattern —
  see §2.2); both are treated as the one C-b caveat, fixed together.
- **C-c (unforced named implicit: reject vs bind).** Cure rejects any named
  implicit whose telescope position was not pinned by index inversion
  (`{:named_implicit_unforced, name}`, `elaborator.ex:3269`). Idris **binds**
  it as a quantity-0 pattern variable. Probe evidence (idris2 `--check`,
  2026-07-08, scratchpad `nidot-probe/`): existential
  `MkP : {0 k : Nat2} -> Vec k -> P` — `f (MkP {k = kk} v) = Z` **accepts**
  (binding, erased-only use); `g (MkP {k = kk} v) = kk` **rejects** ("kk is
  not accessible in this context"). Cure rejecting the *binding itself* is a
  genuine cure-stricter divergence with no soundness rationale.

## 2. Design — three scoped fixes, E-layer only

No kernel change anywhere in this chain. The named-implicit machinery is
check-and-discard (C-a, C-b) or a naming-of-an-existing-binder concern (C-c);
`{:case}` terms, motives, and the index unifier are untouched.

### 2.1 C-a: run the forced check on the carried-eq path

Thread the surface `pattern` and the verdict's solved substitution into
`elaborate_carried_eq_branch` and call the existing `check_named_implicits/7`
with the same inputs the plain path uses, in the pre-proof branch frame
(`branch_ctx0 = extend_context(ctx, telescope, scrut_param_vals)`
specialized by the same subst — exactly the frame `forced_check_probe/7`
documents). The verdict is already in scope at the dispatch site
(`{:solved, s}` / `:trivial` → `%{}`); today it is simply not passed down.
Failure propagates identically to the plain path
(`{:forced_pattern_mismatch,…}` rejects the branch).

### 2.2 C-b: strip annotations before body substitution

Named-implicit arguments are annotations, not expression material — this
bug's root cause is any site that substitutes a raw surface pattern into an
expression position via `subst_surface_var` without first stripping
`{:named_implicit_pat,…}` args. There are TWO such sites, not one:

- `refine_scrutinee_in_body` (`elaborator.ex:3533`) — the caveat as
  originally documented (§1 C-b): the branch's own scrutinee name referenced
  in the body.
- `desugar_as_patterns`/`strip_as_patterns` (`elaborator.ex:2130-2171`),
  which runs FIRST in the desugar pipeline (`elaborator.ex:1319`, before
  `refine_scrutinee_in_body` is ever reached). `strip_as_patterns`'s
  `:function_call` clause (`:2161-2169`) recurses into every argument, but
  its catch-all (`:2171`) returns a `{:named_implicit_pat,…}` argument
  unchanged — so `p @ MkP({k = kk}, v)` with `p` referenced in the body hits
  the identical failure the moment `desugar_as_patterns` substitutes `p`'s
  reconstruction (`subst_surface_var` at `:2145`) into the body, entirely
  independent of `refine_scrutinee_in_body` and before C-a/C-b's other fixes
  even run. Confirmed reachable: `maybe_wrap_as`/`@` (`parser.ex:2001-2012`)
  wraps any bare-variable-then-`@` pattern, and `parse_named_implicit_pat`
  (`parser.ex:448`) is a valid constructor-argument sub-parse, so
  `p @ MkP({k = kk}, v)` parses today.

Both sites get the same fix: rewrite the pattern to its positional-only form
(drop `{:named_implicit_pat,…}` args — the same filter `constructor_pattern`
already applies via `named_implicit_arg?/1` at `elaborator.ex:3609`) at the
point each captures its reconstruction (`refine_scrutinee_in_body`'s
`pattern` argument, and `strip_as_patterns`'s `clean_sub`/`recon`) so the
substituted body sees the constructor expression Idris/Lean would substitute.
The annotation is still checked by `check_named_implicits` on its own path
(which runs against the ORIGINAL, un-stripped pattern); nothing is lost.

### 2.3 C-c: bind unforced variable-form named implicits at quantity 0

For `{k = <inner>}` where `named_implicit_forced_value/4` reports unforced:

- **`inner` is a bare variable** (surface `{:variable,…,name}`; not a dot
  form): bind it. The erased telescope slot already exists in `branch_ctx` —
  it is anonymized in `branch_names` today (`branch_scope(quantities,
  pattern_vars)` names only present positions). The fix names that slot with
  the written variable. Quantity stays `0`, but the relevance layer does NOT
  already police this for free: `Cure.Elab.Relevance.check/4`
  (`relevance.ex:62-76`) is only ever called as `Relevance.check(env,
  sig.name, sig.quantities, body_term)` (`declarations.ex:59,82`) — its
  tracked erased-set is fixed to the *enclosing definition's own* top-level
  parameter quantities. Its `:case` clause (`relevance.ex:143-151`) walks each
  branch body at `depth + arity` but never folds that branch's *constructor's
  own* `quantities` into the tracked erased set — today that's moot because
  an anonymized erased ctor field has no name to reference at all
  (`erasure_relevance_test.exs:147-155` pins today's "referencing it is
  simply unbound" behavior). Once this fix names the slot, a relevant use of
  the newly-bound variable would NOT trip `{:erased_used_relevantly,…}` under
  the unmodified check — it would elaborate, then be silently dropped by
  `Erase.erase`, reopening the M8.3-class hole `erasure_relevance_test.exs`
  exists to close, one level down (inside a match arm rather than at a
  definition's own parameters). **This fix therefore must also extend
  `Relevance.check`'s `:case` clause** to fold the matched constructor's own
  `Inductive.ctor_quantities/2` into the tracked erased set for that branch's
  frame, keyed by branch depth exactly as `sig.quantities` is keyed by the
  outer definition's depth — still E-layer/untrusted (`relevance.ex`, not the
  kernel), but a real extension, not reuse-unchanged. Shadowing an existing
  name follows the ordinary innermost-wins rule the branch scope already
  implements.
- **`inner` is a dot form `.e` or any non-variable**: keep the
  `{:named_implicit_unforced, name}` error. A dot asserts agreement with a
  unification-pinned value; when nothing was pinned there is nothing to check
  (and Idris's equivalent — a non-variable pattern for an unforced erased
  implicit — is first-class matching Cure does not do on erased positions).
  The error text gains a hint distinguishing "use a variable to bind" from
  the old blanket message.
- On a **forced** position, a bare-variable inner keeps today's semantics
  (convertibility check against the pinned value — Idris's `{w = a}` with
  `a` in scope behaves the same way there).

## 3. What is NOT changed

- **Kernel/TCB untouched** — no new Core forms, no conv/normalise change.
- Erasure/emit untouched: C-c names an existing erased binder; it never
  becomes present (`quantities` unchanged), so `emit.ex` anonymization and
  the zero-footprint guarantee hold.
- `Relevance.check` (§2.3) gains one new rule — folding a matched
  constructor's own quantities into the tracked erased set for its branch —
  which IS a real code change, just still E-layer/untrusted (`relevance.ex`),
  never the kernel. It changes what surface code is *allowed to write*, not
  what gets erased.
- Bare positional `.e` stays parse-level-guarded groundwork (ledger: proven
  structurally inexpressible for Cure's erased-implicit indices; no dead
  syntax gets elaboration).
- The classic pipeline (`lib/cure/compiler/*`, `lib/cure/types/*`) is not
  touched — this is all dependent-elaborator work.

## 4. Oracle probes (differential, cluster `nidot`)

New paired fixtures, each run through `mix cure.oracle nidot` (destructive —
restore `verdicts.json` via `git checkout` before investigating any drift):

| Fixture | Shape | Expected |
|---|---|---|
| `ni03_carried_wrong_dot_neg` | carried-eq branch (sibling arg's type mentions the carried index, per `detect_carried_index`) + wrong dot `{k = .(S(m))}` | reject/reject `same` (today: Cure accepts — the C-a red) |
| `ni04_body_scrutinee_ref` | named implicit + branch body referencing the scrutinee name | accept/accept `same` (today: Cure rejects — the C-b red) |
| `ni05_unforced_bind_erased` | existential ctor, `{k = kk}` bound, `kk` used only in an erased position (e.g. a type annotation / erased implicit argument) | accept/accept `same` (today: Cure rejects — the C-c red) |
| `ni06_unforced_bind_relevant_neg` | same binding, `kk` returned relevantly | reject/reject `same` (guards the quantity-0 discipline both sides) |
| `ni07_carried_right_dot` | carried-eq branch + correct dot | accept/accept `same` (guards C-a against over-rejection) |
| `ni08_as_pattern_body_ref` | as-pattern over a named-implicit ctor pattern (`p @ MkP({k = kk}, v)`) + branch body referencing `p` | accept/accept `same` (today: Cure rejects — the `desugar_as_patterns` C-b variant, §2.2) |

Idris sides mirror the probe programs from §1's evidence. If Idris rejects
`ni07`'s carried shape for an unrelated reason, simplify the shape until both
sides express the same program — never hand-write a verdict.

## 5. Testing (TDD; red first, immutable once green)

1. **Red unit tests** per caveat in `test/cure/elab/` (new
   `named_implicit_tail_test.exs`): C-a wrong-dot-on-carried rejects; C-b
   scrutinee-in-body accepts AND as-pattern-body-ref accepts (both sites in
   §2.2 — `refine_scrutinee_in_body` and `desugar_as_patterns`, each needs
   its own red case since they are independent code paths); C-c bind-erased
   accepts / bind-relevant rejects with `{:erased_used_relevantly,…}` /
   dot-on-unforced still errors. The bind-relevant-rejects case is exercising
   the new `Relevance.check` `:case` rule (§2.3) specifically — write it (and
   confirm it fails red before the `:case`-clause extension lands) rather
   than relying solely on the end-to-end `ni06` oracle probe to surface that
   gap.
2. Existing pins stay green untouched: `dotpat`/`nidot` current fixtures,
   `dot_pattern_parse_test.exs`, `carried_index_sibling_test`,
   forced-check Antigen vertical (#24, `forced_check_probe` shim — extend
   with a carried-frame case mirroring C-a).
3. Oracle: add §4 fixtures, run `mix cure.oracle nidot` (and `dotpat`
   untouched byte-identical), replay test green.
4. Gate (sequential, one at a time): full Antigen → full `mix test` →
   `mix cure.check.examples` → oracle replay.
5. Ledger row #5 graduates 🟡 → ✅ (all three caveats closed; the row's
   remaining text records C-c's variable-bind semantics and the kept
   dot-on-unforced error).

## 6. Out of scope

- Match-embedded constructor guards and Nat→Int erasure (next chains in
  initiative C).
- First-class matching on erased positions (non-variable patterns for
  unforced implicits) — Idris feature with no Cure counterpart; recorded, not
  built.
- `{:named_implicit_pat,…}` in nested (non-outermost) pattern positions:
  whatever the current parser/`desugar_nested_arms` support is, it is
  preserved, not extended.

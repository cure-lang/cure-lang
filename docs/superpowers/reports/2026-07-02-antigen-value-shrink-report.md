# Autopilot completion report — Antigen value-level post-shrink

**Branch:** `autopilot/antigen-tier-b` (worktree `.claude/worktrees/antigen-tier-b`) — stayed on this branch per operator instruction (no separate worktree; `autopilot-worktree-preference` memory).
**Status:** complete. Full suite green — **2311 passed, 0 failures** (3 doctests, 2308 tests; +12 over the post-B 2299). **Not merged** — operator merges when ready.

Delivers Tier-1 of the shrinking work: when an assay fires, the Runner minimizes the reified `Challenge` artifact into a minimal witness before banking it. This is the cheaper minimizer the `ChoiceSeq` reference spec gates itself behind — `ChoiceSeq` stays shelved unless a real deep antibody proves visibly non-minimal after this.

## Stage outcomes

| Stage | Outcome | Key commit(s) |
|---|---|---|
| 0 — Brainstorm + spec | Interactive design gate (4 decisions: Tier-1 now / both test polarities / generic type-preserving rewriter / auto-shrink-before-bank bounded). Self-reviewed + committed | `13743fe` |
| 1 — Spec review (Sonnet, recursive-skeptical-review) | Converged 9 passes (2 clean); 7 findings — biggest: the "predicate is the only validity gate" core was **subtly unsound** (`Assays.Term` returns `{:violation, {:infer_failed, e}}`, so a loose `{:violation,_}` pred lets a typed_term shrink wander into ill-typed nonsense → pred must pin the violation **tag**) | `0c7c483` |
| 2 — Plan (writing-plans, inline) | 5-task TDD plan; probed every signature (`Term.shift/3` positional cutoff, ctx entries as bare terms) and wrote the exact rule-3 de Bruijn arithmetic | `7737469` |
| 3 — Plan review (Sonnet) | Converged 5 passes (2 clean); 9 findings — biggest: `0..(n-1)` at `n=0` enumerates `[0,-1]` (Elixir implicit-step footgun) → phantom candidate burns the budget; also missing challenge-kind guard, the `challenges:` seam genuinely absent, untested pred-crash-rescue | `5d60298` |
| 4 — Execute (Opus, strict TDD) | 4 tasks, red→green→commit; one execution finding (budget-test semantics) fixed with justification | `670e1e3`…`7d0b50e` |
| 5 — Verify + report | Full suite green; sanity explore (shrink dormant, 0 infections); this report | — |

## The design in one line

The rewriter is **purely structural and untyped**; the caller's **same-violation-shape** predicate is the sole validity gate. A candidate edit is accepted iff it stays shape-well-formed and the same assay still returns a violation *of the same tag*. So no per-edit re-typecheck, no bidirectional walk — well-typedness is preserved for free (an edit that breaks it makes the assay stop firing the original shape → rejected).

## What was built

- **`Antigen.Shrink.minimize/3`** — deterministic greedy sweep of single-edit candidates to a fixpoint or step budget (pred-call cost cap). Four rules: **(1)** subterm→minimal-atom (`Z`/`vnil`/`T`/`Type₀`, guarded to `>1`-node positions for strict size-decrease), **(2)** numeral shrink, **(3)** context drop with full de Bruijn shift (term/type `shift -1 cutoff d+1`; sibling entries `pos<d` `shift -1 cutoff d-pos`; `pos>d` unchanged), **(4)** structural unwrap (incl. `:lam`-body shift-and-reject-on-`{:var,0}` and arity-0 `:case`-branch bodies). Fixed enumeration `ctx → type → term`, pre-order, rules 1→2→4. Reseeds the minimized payload; reimplements `occurs?`/`well_formed?` locally to avoid a Runner↔Shrink cycle.
- **`Runner.explore/1`** — infection branch builds a same-shape predicate (`same_shape?/2` pins the violation tag, with a bare-atom fallback for `Assays.Stub`'s `:boom`), minimizes `:typed_term`/`:mutant_term` infections (kind-guarded — other kinds bank as-is), banks the minimized artifact. `@shrink_budget 2000`, `shrink_budget/1`, and a new `challenges:` opt seam.

## Test evidence (12 new tests, all green)

- **Determinism / monotone / idempotent**; **budget as a cost cap** (rewritten from the plan's accepted-edit assumption to spec §3's pred-call semantics — an execution finding, justified by the spec).
- **Per-rule de Bruijn closedness**, incl. a genuinely *dependent* context where `pos0` references both `pos1` and `pos3` straddling the dropped `pos2` — exact sibling-shift indices hand- and probe-verified.
- **pred-crash-rescue** (a raising predicate is safely treated as reject).
- **Synthetic §7.4** — a generated deep well-typed term shrinks to the exact global minimum `vcons Z Z vnil : Vec (S Z)` (size 4, probe-verified stable across seeds).
- **Buggy-infer end-to-end §7.5** — a planted `infer` that wrongly accepts `head_swap` makes a deep mutant a real survivor; the full `explore/1` infection→shrink→bank path banks a strictly-smaller artifact that still trips the assay.

## Acceptance (`mix antigen --count 300`)

```
antigen health[typed_term]:  binder_usage=0.94 reduction_activity=0.69 fuel_exhausted=0 discard=0.0 → healthy
antigen health[mutant_term]: reason_diversity=9 max_depth=8 wrap_diversity=5 survivors=0 → healthy
antigen health[conversion]:  carriers=2 both_polarities=true reject=22 accept=83 → healthy
antigen: 0 infection(s), 47 seed(s) banked
```

**0 infections** — the shrink path stays dormant (no organic counterexamples to minimize), and every existing health line is unchanged. The Runner change is inert on the normal path, exactly as designed for infrastructure that only activates when a real bug surfaces.

## The `ChoiceSeq` decision gate

`ChoiceSeq` (Hypothesis-style internal buffer shrinking) remains shelved per its own §9. Reassess only if a real deep antibody stays visibly non-minimal after this value-level pass. For terms, greedy value-level shrinking reaching the exact minimum (as the §7.4 test shows) is expected to suffice — so `ChoiceSeq` likely stays on the shelf.

## Follow-ons still queued (unrelated)

- **Human-readable corpus terms + fault provenance** (operator-requested; its own spec/plan).
- **`ChoiceSeq` backend** — gated as above.

## Next

Operator review + merge of `autopilot/antigen-tier-b` (now carries: Tier B + lazy generator + ChoiceSeq reference spec + mutation corpus + deep-propagation (A) + conversion-at-depth (B) + value-level post-shrink).

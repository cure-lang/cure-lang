# Autopilot completion report — Antigen human-readable corpus

**Branch:** `autopilot/antigen-tier-b` (worktree `.claude/worktrees/antigen-tier-b`) — stayed on this branch per operator preference (`autopilot-worktree-preference` memory).
**Status:** complete. Full suite green — **2321 passed, 0 failures** (3 doctests, 2318 tests; +10 over the post-value-shrink 2311). **Not merged** — operator merges when ready.

Banked Antigen corpus records are now human-readable on disk: terms are tagged s-expressions, notes are plaintext, and a mutant's `fault` provenance is a readable inline field — while every existing Base64 record still decodes (dual-read) and replay is byte-for-byte identity-preserving.

## Stage outcomes

| Stage | Outcome | Key commit(s) |
|---|---|---|
| 0 — Brainstorm + spec | Design gate: 2 decisions — **tagged s-expr** term format + **dual-read + migrate** transition. Spec written + self-reviewed | `9fa50be` |
| — Planning discovery | `Cure.Core.Serialize` **already is** the exact tagged s-expr codec (the C2 re-validation format). Spec amended to reuse it — no new module, atom-safety/`:boom` finding mooted | `43f0bb1` |
| 1 — Spec review (Sonnet, recursive-skeptical-review) | 6 passes (2 clean); **3 live-verified findings** by decoding the real corpus: fault values aren't uniformly atom/int/nil (`:out_of_scope_var` → `scope:{lo,hi}`; `:universe` → `expected/injected_head:{:type,n}` — migration would have crashed on record 1); `Stub`'s `:boom` not in `@known_atoms`; **three** committed corpora, not one | `c793ac8` |
| 2 — Plan (writing-plans, inline) | 5-task TDD plan; probed the full Core-former set + every fault-producer + `Serialize` internals; fixed a `(term …)` reader double-wrap bug pre-commit | `cf66463` |
| 3 — Plan review (Sonnet) | 6 passes (2 clean); reviewer **ran the plan's code+tests verbatim** on scratch copies + real migration + full antigen suite. 3 fixes: Task-5 marker-line `Map.new` crash, Task-4 `Files:` omission, spec-deviation record + test-immutability rule | `ca04878` |
| 4 — Execute (Opus, strict TDD) | 5 tasks, red→green→commit | `1beac1a`…`88c0d72` |
| 5 — Verify + report | Full suite green (2321); static-replay + quarantine green; this report | — |

## The design in one line

`Cure.Core.Serialize` is the readable term format — so the whole feature is **dropping a Base64 wrapper** (pieces), **plaintext-escaping** (note), and a **small readable codec** (fault), all inside `lib/antigen/corpus.ex`; `Antigen.Challenge` is untouched because the mutant `fault` is relocated purely at the Corpus layer (pop out of the scaffold on encode, merge back on decode).

## What was built

- **Readable term pieces** — `id::Serialize.encode(t)` instead of `id::Base64(…)`. Decode is per-piece dual-read: a `(`-prefix → `Serialize.decode`; else legacy `Serialize.decode(Base64…)`. Unambiguous because every `Serialize.encode` output starts with `(` and Base64 never does.
- **Plaintext note** — percent-escaped (`%`→`%25` first, then tab/newline; `-`=nil, literal `"-"`→`%2D`). Decode is **format-gated**: a record is wholly-legacy or wholly-new, inferred from its pieces (`legacy_record?/1`), so a legacy Base64 note decodes to its original text and migration recovers the real human note rather than freezing gibberish.
- **Readable fault field** — a dedicated `fault=((key val)…)` assoc-sexpr (keys sorted), pulled out of the Base64 scaffold. Values: atom/int/`nil` bare; `(pair i i)` for `:out_of_scope_var`'s int-pair `scope`; `(list …)` for `wrap_path`; `(term <serialize>)` for `:universe`'s `{:type,n}` head values — the latter re-uses `Serialize` and round-trips exactly. A ~20-line self-contained s-expr reader backs decode.
- **`mix antigen.migrate`** — rewrites any `.sexp` file in place to the readable format, preserving the byte-exact stored dedup key and record order; idempotent (new-format input → byte-identical output). Ran once over `seeds.sexp` (77), `corpus.sexp` (17), `reach.sexp` (3).

## Test evidence (15 corpus tests + migration of 3 corpora)

- **Record round-trip (new format)** for `typed_term`, all fault shapes (`:head_swap` atoms+list, `:out_of_scope_var` int-pair, `:universe` term-valued heads, conversion carrier ints), and a non-term kind (no `fault=`).
- **Dual-read legacy** — hand-written Base64 pieces + fault-in-scaffold + Base64 note still decode, incl. the original note text.
- **Migration lossless + idempotent** — dedup-key multiset identical pre/post; decoded challenges equal; already-new-format file migrates **byte-identically**.
- **Readability smoke** — a real migrated `mutant_term` line has plaintext note, `(ctor …)` pieces, readable `fault=`, and none of those three fields matches a Base64 pattern.
- **Static-replay meta-tests** (`corpus_replay`, `indexed/positivity/totality/universes/rewrite/typed_term_seed`, `reach_pin`) — all green against the migrated corpora, proving dual-read + dedup-key stability held.

Sample migrated mutant line (fault now legible):
```
… note=- scaffold=<base64> fault=((expected_head Nat) (injected_head Vec) (kind app_domain) (scope nil) (witness head)) key=<base64> pieces=ctx0::(data Vec () ((var 0)));;…;;term::(app (lam (data Nat () ()) (var 0)) (ctor vnil))
```

## Deviation from spec (recorded)

The spec's original §3 (a new `Antigen.SExpr` module with `to_existing_atom`) is superseded by §3.0: reuse `Cure.Core.Serialize`, which mints atoms via `String.to_atom`. This is not a regression — the corpus term path already went through `Serialize.decode` on the Base64 path, so the atom posture is unchanged. It also mooted the Stage-1 `:boom`/`@known_atoms` finding (that only bit a *new* safe decoder). **Known limitation:** a hand-edited corpus typo like `(global pluss)` mints `:pluss` rather than erroring — identical to today's behavior. A safe (`to_existing_atom`) decode is a trivial future follow-up if hand-edit typo-catching is ever wanted (out of scope, YAGNI).

## Follow-ons still queued

- **Mutation-generator flaky-fixture fix** (operator handoff, next): `mutation_test.exs:32`/`:36` intermittently fail because `Mutation.build` can draw an injected head/index equal to the expected one (a no-op mutation), breaking the "heads differ" invariant. Fix direction: draw the injected head from the complement of `expected_head` so distinctness holds by construction. Operator asked to **merge the lean-match worktree first** (where the flakiness was found) before fixing. To be handled as its own spec.
- **Safe (`to_existing_atom`) corpus decode** — trivial follow-up if hand-edit typo-catching is wanted.
- **ChoiceSeq backend** — still shelved.

## Next

Operator review + merge of `autopilot/antigen-tier-b` (now carries: Tier B + lazy generator + ChoiceSeq reference spec + mutation corpus + deep-propagation (A) + conversion-at-depth (B) + value-level post-shrink + human-readable corpus).

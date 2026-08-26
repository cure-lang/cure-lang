# Migration Facility + `cure migrate` — Design Capture (PARKED for release 0.34)

> **STATUS: PARKED until after the dependent-pipeline parity work is complete** (operator-ordered 2026-07-09: "wait on executing this plan until after the dependent pipeline has been fixed up"). *Spec and park* — NOT to build now. This is a design capture, not an implementation-ready spec: the lossless-AST strategy (§4) has genuine open questions needing a brainstorm before a plan. Target: exist before the **0.34** release cut (alongside the Signal/Flow 0.34 hardening).
>
> **Near-term unblock is decoupled from this facility:** the Std library's uppercase type vars are being renamed to lowercase **by hand now** (a plain source edit, NOT via this unbuilt facility) so the dependent-pipeline parity program can proceed; see [[uppercase-typevar-bad-motive-finding]]. No compiler-side tolerance is built ahead of this facility.
>
> **Operator-DECIDED constraints (no longer open):** (1) migration MUST be lossless — no lossy-but-warned v0. (2) The migration corpus (the set of rules `cure migrate` applies) is EXACTLY the set the compiler warns on — one rule registry, two consumers. (3) `--strict` promotes the migration warnings to errors (the warn-now→error-later knob).

## 1. Goal

A general, extensible **source-migration facility** for Cure: a registry of migration rules that (a) during normal compilation emit deprecation **warnings** and, where safe, auto-tolerate the legacy form; and (b) via a `cure migrate` command, **rewrite source files in place** to the canonical form. Warn-now → error-later. The uppercase-type-var → lowercase rule is the first *new* client; the existing `if`/`elif` → `pickup` rewrite is the first *existing* client to fold in.

## 2. Pipeline (operator-specified)

`cure migrate` runs the compiler pipeline **up to the migration step only**, then formats and writes back:

```
source → lex (preserve_comments) → parse → [migration-rewrite pass] → canonical formatter → write to disk
```

The migration pass sits **between the parser and the elaborator**. It does NOT type-check. Rules that need to distinguish (e.g.) a free type variable from a resolved type constructor consult a light **name-resolution** set (declared + imported type names) built from the AST — this is far short of full elaboration and belongs in the pass. During normal `cure build`, the same pass runs in **warn-and-tolerate** mode (normalize in-memory + emit W-warning; do NOT touch the file); `cure migrate` runs it in **rewrite-and-write** mode.

## 3. What already exists (AUDIT — reuse, do not rebuild)

Verified in-tree 2026-07-09:

- **Canonical formatter: `Cure.Compiler.Printer`** — already renders AST to canonical source; documented block rules (PICKUP §8 / MATCH §9). No new formatter needed.
- **In-place AST migrator prototype: `mix cure.rewrite`** (`lib/mix/tasks/cure.rewrite.ex`) — rewrites legacy `if`/`elif` → `pickup`, renders via `Cure.Compiler.Printer`, writes files in place by default, has `--check` (CI, non-zero exit on pending rewrites) and `--print`. This is the `cure migrate` pipeline already working for one rule. `mix antigen.migrate` is a second in-place-rewrite precedent.
- **CLI: `cure fmt`** exists (`cli.ex` `cmd_fmt`) — sibling command; `cure migrate` slots beside it.
- **Comment tokens: lexer `preserve_comments`** (opt-in, v0.20.0+; `lexer.ex:73,92-103`) emits `:line_comment`; doc comments (`##`/`###`) always preserved as `:doc_comment`.

## 4. The three real gaps (the actual work)

1. **Rule registry (the anti-ad-hoc ask).** Generalize `cure.rewrite`'s single hardcoded rule into a registry: a rule = `{id: W-code, description, phase (syntactic | needs-resolution), detect+rewrite fn, warning-message template}`. Register the existing if/elif→pickup rule and the new uppercase-type-var→lowercase rule as the first two entries. Shared: warning emission (W-code channel — W086 exists), the warn/error policy knob, an optional migration report.
2. **Lossless round-trip (the real engineering rock).** `cure.rewrite`'s own doc states round-trip is preserved only *"up to position metadata"* — i.e. comments are **not** guaranteed to survive a rewrite. For migration to be non-lossy (operator requirement), the AST must carry comments/trivia and the Printer must re-emit them positionally. The lexer already produces comment tokens (`preserve_comments`); the gap is **threading them through the parser AST and back out through `Cure.Compiler.Printer`**. OPEN QUESTION for the brainstorm: full concrete-syntax-tree/trivia model (Roslyn/rowan style) vs. comment-attachment heuristics on the existing AST — the former is more faithful, the latter far less invasive. Assess round-trip fidelity of `Printer` on a comment-heavy corpus first to size this.
3. **`cure migrate` command + policy.** A CLI subcommand (mirror `cure fmt`/`cure.rewrite` ergonomics: in-place default, `--check`, `--print`), plus the warn-now→error-later **policy** on the W-code channel (a rule's warning becomes an error under `--strict`/a future edition flag once its compat window closes).

## 5. First rules

- **`if`/`elif` → `pickup`** (existing `cure.rewrite` logic — fold into the registry unchanged; purely syntactic).
- **uppercase type var → lowercase** (needs-resolution phase; see [[uppercase-typevar-bad-motive-finding]]). Detection: a *free* (would-be-auto-generalized) uppercase identifier in a type-parameter position that does NOT resolve to a known type constructor. Apply the lowercased binder consistently across the signature; handle the `T`+`t` collision (freshen/warn, never silently merge). NOTE the parity decouple (§6).

## 6. Relationship to the value-surface parity program (decouple)

The parity program needs `Std.List`'s uppercase type vars to stop producing `:bad_motive` (to trigger the 20+-dependent cascade) *before* 0.34. Decouple: the type-var wave (after `@extern`) does the **compiler-side** half only — auto-generalize free uppercase type vars during elaboration + emit the W-warning — unblocking std with no source rewrite. The **source-rewrite** half (the `cure migrate` rule that lowercases files to clear the warning) ships with this parked facility. Same rule concept, two consumers. (Pending operator confirmation of the decouple vs. gating the cascade entirely on the facility.)

## 7. Open questions for the pre-implementation brainstorm

- Lossless model: full trivia-CST vs. comment-attachment on the current AST (§4.2) — the decisive design fork; assess `Printer` fidelity first. **Lossless is REQUIRED (operator-decided); a lossy v0 is NOT an option** — so this fork is about *how* to be lossless, not *whether*.
- Is the migration pass a new module (`Cure.Migrate`?) wrapping the registry, or an evolution of `cure.rewrite`'s internals?
- Per-rule maturity levels under `--strict` (a rule graduates warn→error independently), vs. one global switch.

**RESOLVED (operator, no longer open):** migration MUST be lossless (no lossy v0); the `cure migrate` corpus === the compiler's warning set (one registry, two consumers); `--strict` turns those warnings into errors. Scope of first release: at least the two named rules (if/elif→pickup, uppercase-type-var→lowercase), all lossless.

## 8. Out of scope for this capture

- Any implementation (parked).
- The kernel/elaborator dependent-type machinery (unrelated).
- Deciding the lossless model — that is the brainstorm's job.

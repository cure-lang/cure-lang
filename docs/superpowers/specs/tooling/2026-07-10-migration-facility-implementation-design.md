# Migration Facility + `cure migrate` — Implementation Design (Approach A)

> **STATUS: IMPLEMENTATION-READY.** Supersedes the parked design capture
> [`2026-07-09-migration-facility-design.md`](2026-07-09-migration-facility-design.md),
> which explicitly deferred the lossless-model fork to a pre-implementation
> brainstorm. That brainstorm is complete (2026-07-10); this document records
> the resolved decisions and is the source of truth for the plan.
>
> **Branch:** `autopilot/migration-facility`, based on `autopilot/kernel-parity-batch`.

## 1. Goal

A general, extensible **source-migration facility** for Cure: a registry of
migration rules that (a) during normal `cure build` emit deprecation
**warnings** and tolerate the legacy form in-memory, and (b) via a new
`cure migrate` command, **rewrite source files in place** to the canonical
form — **losslessly**, preserving every comment. Warn-now → error-later.

The uppercase-type-var → lowercase rule is the first *new* client; the existing
`if`/`elif` → `pickup` rewrite (today in `mix cure.rewrite`) is the first
*existing* client to fold into the registry. A third seed, the `@group` hoist
(§5.5), is the first *relocation* rule — it moves a decorator rather than
transforming a node in place, exercising the trivia model's carry path.

## 2. Operator-decided constraints (locked, not open)

1. **Migration MUST be lossless** — no lossy-but-warned v0. Every comment
   survives a rewrite.
2. **One rule registry, two consumers.** The set of rules `cure migrate`
   applies is EXACTLY the set the compiler warns on.
3. **`--strict` promotes migration warnings to errors** (the warn-now→error-later
   knob).
4. **Approach A — whole-file canonical reprint.** `cure migrate` reprints the
   entire file in canonical form (gofmt/elm-format style), carrying comments and
   blank-lines as trivia. It is *also* the engine behind `cure fmt`. (Chosen over
   the minimal-diff/surgical-splice alternative — see §4.)
5. **Keep the hand-rolled Pratt parser.** No NimbleParsec rewrite (see §4.2).
6. **`cure migrate` refuses to run unless its target files are git-tracked and
   clean** (read-only modes exempt) — scoped to the resolved target set
   (§5.6), not a whole-repository cleanliness requirement; see §5.7 for the
   precise definition of "clean."

## 3. Empirical grounding (measured 2026-07-10, this worktree)

This data was decided on measured round-trip fidelity, not inference. It
grounds the claim that a **total Printer + a lossless trivia model are
required work**, full stop — independent of the Approach A vs. B choice (see
§4.1, which is a separate, preference-driven argument; the two bugs below
afflict a surgical-splice printer just as much as a whole-file one, since B
still has to reprint arbitrary changed subtrees and still needs comments
outside the touched region preserved). On a comment-heavy corpus,
`lex(preserve_comments) → parse → Printer.quoted_to_string`:

| File | `#`-comment lines in → out | Output reparses? |
|---|---|---|
| `lib/std/access.cure` | 142 → **11** | yes |
| `lib/std/core.cure` | 111 → **9** | yes |
| `lib/std/iter.cure` | 108 → **4** | yes |
| `examples/cure_moneta/.../moneta.cure` | 110 → 49 | yes |
| `examples/match_showcase.cure` | 83 → 81 | **no** |

Two root causes, both confirmed by direct probe:

- **Bug 1 — the Printer is non-total over the AST.** `match_showcase` output
  line 127 was a raw `inspect`-ed tuple
  `{:pin, [line: 205, col: 7], [{:variable, …, "target"}]} -> true` — the Printer
  has **no clause for the `:pin` pattern node**, so it fell through to `inspect`,
  which does not reparse. Whole-file reprint (Approach A) requires the Printer to
  handle *every* node the parser can emit.
- **Bug 2 — comment capture is positional and partial.** The parser only turns
  `:line_comment` tokens into `{:comment, meta, text}` nodes at a few
  statement-list boundaries it explicitly scans. `access.cure` has 142 full-line
  comments, **0 trailing**, yet only 11 survived — the rest live *inside*
  constructs (type bodies, between fields, mid-clause) where no comment
  collection runs, so they are dropped. Losslessness requires trivia capture that
  is independent of AST position.

## 4. Design decision: Approach A over minimal-diff

### 4.1 Why whole-file canonical reprint (A), not surgical splice (B)

The minimal-diff alternative (recast/rust-analyzer style: keep original bytes,
reprint only changed subtrees) is lossless "for free" outside changed regions,
but it makes `cure migrate` a migrator only — never a canonical formatter. The
operator chose A: migration also canonicalizes formatting, and the same engine
powers `cure fmt`. **This A-vs-B choice is a goal/preference decision, not one
that follows from §3's measured bugs** — B would need the identical
total-Printer-and-complete-trivia-model fix to preserve comments outside its
touched subtrees, so §3 doesn't discriminate between A and B; it only
establishes that the fix is mandatory either way. A's marginal cost over B is
that the Printer must reprint *every* node (not just touched ones) and the
blank-line policy (§5.4) must be fully specified, not just applied to changed
regions; both are addressed below and are one-time costs that also retire the
standing Printer/`cure fmt` fidelity debt.

### 4.2 Why keep the Pratt parser (no NimbleParsec)

Measured: `parser.ex` is 4,537 non-blank lines (≈3,663 code + 874 comment) plus
a 117-line precedence table, atop a 1,393-line indentation-aware lexer. A
NimbleParsec rewrite would be a wash-to-larger on LOC and would fight this
project's goal:

- **Operator precedence** lives in a compact 117-line Pratt table; NimbleParsec
  has no precedence mechanism and would re-encode it as a longer rule tower.
- **Indentation** is solved in the lexer (indent/dedent tokens); NimbleParsec is
  context-free PEG and bad at the offside rule — the lexer stays either way.
- **Backtracking + recovery give good diagnostics NimbleParsec cannot match** —
  e.g. the record-update rewind probe (save/restore `pos`+`errors`, then fall
  back to plain-construction parsing on a non-update literal) and the
  `synchronize_to_statement` error-recovery helper (resumes parsing after a
  broken top-level or expression statement). *(An earlier draft cited "31
  sites" for this category; that count does not re-derive from the current
  parser and is dropped rather than repeated unverified — the qualitative
  argument stands on its own.)*
- **This does NOT rest on a trivia-specific argument.** The trivia model
  (§5.2) is a *separate* post-parse pass over `(tokens, ast)`; it does not
  depend on the parser's internal traversal strategy and would work unchanged
  atop a NimbleParsec-produced AST + token stream too. The three bullets above
  (precedence, indentation, backtracking/recovery) are the actual reasons to
  keep the Pratt parser.

The AST is Metastatic 3-tuples `{type, meta, children_or_value}` where `meta` is
a keyword list already carrying `line`/`col`/`subtype`. Trivia goes in `meta`
under new keys with **no tuple-shape change and no impact on any consumer that
ignores `meta`.**

## 5. Architecture

### 5.1 Pipeline

```
cure migrate:  source → lex(lossless) → parse → attach-trivia → migration-rewrite
                       → canonical Printer(trivia-aware) → git-guard → write
cure build:    source → lex(lossless) → parse → attach-trivia → migration-rewrite(warn-only)
                       → … normal elaboration/codegen …
cure fmt:      source → lex(lossless) → parse → attach-trivia
                       → canonical Printer(trivia-aware) → write
```

The migration-rewrite pass sits **between the parser and the elaborator** and
does NOT type-check. Rules needing name context consult a light declared+imported
**type-name set** built from the AST (far short of elaboration).

### 5.2 Trivia model (the core)

Modeled on Go's `go/printer`/`ast.CommentMap`: comments and blank-lines are
**trivia owned by AST nodes**, populated by a single post-parse attachment pass.

- **Lexer (lossless mode):** collect every comment and blank-run as a *positioned
  trivia item*: `{:comment, text, line, col}`, `{:doc_comment, text, line, col}`,
  `{:blank, count, line}`. (Reuses the existing `preserve_comments` lexer path;
  the new requirement is that nothing is emitted into the significant-token stream
  for the parser to special-case — trivia is collected to a side list keyed by
  position.)
- **`Cure.Compiler.Trivia` (new module):** a single pass over `(tokens, ast)`
  that attaches each trivia item to exactly one owning node as `meta[:leading]`
  (items whose source position precedes the node and are not same-line-trailing
  on a prior node) or `meta[:trailing]` (a comment on the same line, after the
  node's last token). Items after the last node land in a **trailer bucket on
  the innermost enclosing container node** — every AST node kind that owns a
  statement/clause list (program, block, `if`/`pickup` branch bodies, `fsm`
  states, etc.) gets its own `meta[:trailer]`, not just the top-level program
  node; a comment after the last statement inside a nested block belongs to
  that block's trailer, not the file's. (Without a per-container bucket, such a
  comment has no defined home — it is neither leading on a later sibling in the
  same block nor caught by a file-level-only bucket — so this is load-bearing
  for the "total by construction" claim below, not just a nicety for the
  top-level case.) The pass is **total by construction**: it asserts every
  collected trivia item is placed exactly once (an unplaced item is a hard
  error, not a silent drop — this is the anti-Bug-2 invariant).
- **Attachment on nodes, not a line-keyed side map:** migration rules
  *restructure* subtrees (`if/elif`→`pickup`). Trivia attached to a node
  **travels with the node** through a rewrite; a pure line-keyed map would
  detach. Restructuring rules get a registry helper (`Trivia.carry/2`) to move
  attached trivia onto the surviving/replacement node.

### 5.3 Printer totality

- Make `Cure.Compiler.Printer` **total** over the AST: add the missing `:pin`
  clause and any siblings surfaced by the totality gate. No node kind may fall
  through to `inspect`.
- Teach the Printer to emit trivia: `meta[:leading]` before a node (each on its
  own line at the node's indent), `meta[:trailing]` as an end-of-line `# …`,
  and each container's `meta[:trailer]` bucket (§5.2) at the end of that
  container's own body — the program node's trailer prints at EOF, a block's
  trailer prints just before that block closes/dedents.
- **"Total" is asserted by a corpus test below, which proves totality over the
  corpus, not over the AST in general — a whole-in-repo-corpus pass cannot
  prove every node kind the parser can ever emit is handled, only that the
  ones actually present in today's corpus are.** To close that gap without
  requiring a full static exhaustiveness proof (Elixir's `case`/`cond` has no
  compile-time exhaustiveness check over atoms), two things are required, not
  just the corpus test:
  1. **The catch-all clause must `raise`, not `inspect`.** Bug 1 was silent
     precisely because the old catch-all degraded to `inspect(node)` and kept
     going. The new catch-all for an unrecognized node kind must raise
     immediately with the node kind and position, converting any future gap
     from a silent reparse failure (discovered later, if ever) into an
     immediate, loud crash the first time that node kind is printed — corpus
     or not.
  2. **A static cross-check test** enumerates every AST node-kind atom the
     parser's grammar can construct (grep/AST-walk `parser.ex` for tuple
     literals in first position, or maintain an explicit list alongside the
     parser) and asserts the Printer has a matching clause for each. This is
     the actual falsifiable "total" claim; the corpus test alone is not.
- **Totality gate (test):** for the whole in-repo `.cure` corpus,
  `parse → print` (a) never emits a string containing an `inspect`-shaped tuple
  literal, and (b) reparses; and `parse→print→reparse→print` is a byte-fixpoint.

### 5.4 Blank-line normalization (fully opinionated, elm-format style)

1. **Top of file:** 0 blank lines — strip all leading blanks.
2. **Bottom of file:** exactly 1 blank line — inject if absent, collapse if
   multiple. (Byte form: content ends with the terminating newline followed by a
   single empty line.)
3. **Between top-level definitions:** exactly 1 blank line — inject if missing,
   collapse if multiple.
4. **Inside a block body:** cap runs at 1; trim blank lines immediately adjacent
   to a block's open/close; otherwise preserve the author's 0-or-1.
5. **Scope note:** rules 1–4 govern blank lines between *statements/clauses in
   a statement list* (top-level defs, block bodies). They do **not** apply
   inside a single multi-line *expression* — e.g. a call-argument list, record
   literal, or list literal spanning several lines has no "block" for rule 4
   to reference. Blank-line trivia collected inside such a span is attached
   (per §5.2) to whichever sub-expression node precedes/follows it like any
   other trivia, and the Printer emits it unchanged (not capped, not
   collapsed) — normalization is deliberately scoped to statement lists only,
   not arbitrary expression spans, so this is not a gap in rules 1–4, but it
   is worth stating explicitly rather than leaving "inside a block body" to be
   misread as "anywhere inside any pair of brackets."

   **Implementation note (2026-07-10): rule 5 is VACUOUS for Cure as it stands.**
   Cure has no multi-line collection-literal syntax at all — a `%{`, `[`, or `(`
   that spans a newline fails to reparse (`expected :rbrace/:rbracket, got
   :dedent`; verified against `Parser.parse/2`). There is therefore no
   in-language source that can place blank-line trivia "inside a multi-line
   expression span," so no rule-5 case can arise. The Printer accordingly does
   not special-case it (blank trivia that the classifier attaches below
   statement level, deep inside an expression, is simply dropped — it can never
   be re-emitted where it landed without a grammar that allows a newline there,
   which Cure does not have). Rule 5 remains documented as the *intended*
   behavior should Cure ever gain multi-line collection literals; until then it
   is a no-op. Rules 1, 3, and 4 (statement-list normalization) are fully
   implemented and gated by `lossless_roundtrip_test.exs`.

### 5.5 Rule registry (the anti-ad-hoc ask)

A rule is a struct:

```
%Cure.Migrate.Rule{
  id:                atom(),        # the W-code, e.g. :W087
  description:       String.t(),
  phase:             :syntactic | :needs_resolution,
  detect_and_rewrite: (ast, ctx -> {:rewrite, ast} | :no_change),
  warning_template:  String.t()     # rendered with match context
}
```

- **`ctx`** carries the declared+imported type-name set for `:needs_resolution`
  rules; `:syntactic` rules ignore it. **`ctx` is built identically by both
  consumers, from that file's own AST alone** (declared type/ctor names in the
  file plus names brought in by its own `import`/`use` list) — never from a
  project-wide or cross-file type registry. This is what makes the §7
  "warn-and-tolerate parity" claim actually true: both consumers see the same
  per-file-scoped `ctx`, so a `:needs_resolution` rule cannot fire in one
  consumer and not the other because one had a wider or narrower view of
  declared type names.
- **Two consumers, one registry:**
  - `cure build` runs each rule in **warn-and-tolerate** mode: apply the rewrite
    in-memory (so compilation proceeds on the canonical form) and emit the
    W-warning; never touch the file.
  - `cure migrate` runs each rule in **rewrite-and-write** mode.
- **Rule application order:** rules run **once each, in registry-declaration
  order, threaded as an ordered fold** — rule *N*'s `detect_and_rewrite` sees
  the AST as left by rules `1..N-1`, not the original parse tree in isolation
  (ordinary function composition, one pass through the registry). What this
  does **not** do is iterate the whole registry to a fixpoint: there is no
  repeated re-scan looking for matches newly exposed by a later rule's
  rewrite, which bounds a `cure migrate` run to one pass per file regardless
  of registry size. This is a real constraint worth naming even though the two
  seed rules don't interact: a rule ordered *before* another rule whose
  rewrite would expose its trigger will not see that trigger in the same run
  (it would need a second `cure migrate` invocation to catch it, or the
  registry would need reordering). Any future rule with such an ordering
  dependency must document it explicitly (§8 already scopes "new rules" out of
  v1; this is part of why a new rule isn't just a drop-in).
- **Seed rules:**
  - `if`/`elif` → `pickup` (`:syntactic`) — fold in the existing
    `cure.rewrite` logic unchanged; it already produces `{:pickup, …}` from
    `{:conditional, …}` chains with a populated `else`. **Known pre-existing
    limitation, not newly introduced by this design:** `cure.rewrite`'s own
    moduledoc documents that the layout-sensitive parser disables
    `:indent`/`:dedent` emission inside parenthesised contexts, so a
    conditional embedded as a call argument can be rewritten into a multi-line
    `pickup` block that fails to reparse. This directly conflicts with §7's
    "Lossless round-trip gate" and "Rule tests" reparse requirements, which
    this rule must now satisfy as a registry member (it did not have to before,
    as a standalone opt-in `mix` task). Folding it in "unchanged" is only
    correct if paired with one of: (a) detect the parenthesised-argument
    context and skip the rewrite there (emit the warning but leave the source
    untouched, same as an unmatched rule), or (b) fix the underlying
    indent/dedent-in-parens restriction. Phase 3 (§6) must pick one and land it
    as part of porting this rule — "unchanged" cannot mean "including the
    known reparse failure," or the rule fails its own gate on day one.
  - uppercase-type-var → lowercase (`:needs_resolution`) — detect a *free*
    (would-be-auto-generalized) uppercase identifier in a type-parameter position
    that does NOT resolve to a known type constructor; lowercase the binder
    consistently across the signature; on a `T`+`t` collision, freshen (append
    the smallest numeric suffix not already in use in that signature's scope,
    e.g. `t` → `t1` → `t2`, recursively checked so a freshened name cannot
    collide with an existing or previously-freshened binder) and warn —
    **never silently merge.**
  - `@group(:x)` hoist (`:syntactic`) — relocate an in-body `@group(...)`
    decorator to directly above the module's `mod` declaration; idempotent
    (a file already in the above-`mod` form is left unchanged). This
    supersedes the fragile line-regex codemod at
    `787a9745…/scratchpad/migrate_group.exs`, which manually collapses a
    trailing blank line and would mangle or drop any comment on/around the
    `@group` line. **This is the first rule that is a *relocation* (detach a
    node + reinsert it elsewhere), not an in-place transform**, so it is the
    load-bearing exercise of two facility properties: (1) `Trivia.carry/2`
    (§5.2) — comments attached to the `@group` node must travel with it to
    its new position, and the trivia at its old slot must re-home to the
    following sibling; (2) the §5.4 blank-line policy — the blank the
    line-regex script hand-collapses is normalized automatically. It also
    confirms the registry's `detect_and_rewrite: (ast, ctx) -> {:rewrite,
    ast} | :no_change` signature is general enough for a move with **no
    signature change** (it returns a whole rewritten AST). Implementation
    prerequisite: confirm how module-level vs body-level decorator
    attachment is represented in the AST (`{:decorator, …}` nodes exist and
    the Printer already renders them) before writing the rewrite.

### 5.6 `cure migrate` CLI + policy

- New subcommand beside `cure fmt` in `cli.ex`, mirroring `cure.rewrite`
  ergonomics: **in-place by default**, `--check` (CI; lists pending files,
  non-zero exit), `--print` (stdout, no write).
- **Target selection (spelled out explicitly here — the "mirrors `cure.rewrite`
  ergonomics" language in the constraint above refers only to the
  in-place/`--check`/`--print` *mode* trio, not to default file discovery;
  `cure.rewrite` is a `mix` task scoped to this compiler repo's own dev corpus
  and is not the right convention for a general CLI subcommand end users run
  against their own projects):** explicit file/directory/glob arguments when
  given (directories wildcard-expand to `**/*.cure` beneath them, same helper
  `cure fmt` already uses). When no paths are given, `cure migrate` mirrors
  its actual sibling **`cure fmt`** (the bullet above already places it
  "beside `cure fmt` in `cli.ex`") rather than `cure.rewrite`: scan
  `lib/**/*.cure` and `test/**/*.cure` relative to the current project — see
  `cmd_fmt/2` in `lib/cure/cli.ex`. (`cure build`/`cure compile` take a third,
  stricter stance — no implicit scan, an explicit path is mandatory — which
  was considered and rejected for `migrate`/`fmt` specifically because both are
  whole-project maintenance commands, not a single-file compile invocation;
  requiring one explicit path per invocation would make a project-wide
  `cure migrate` unnecessarily tedious.) This determines the "target files"
  the git-guard (§5.7) checks — the guard runs over whatever this resolves to,
  whether that is one explicit path or the full default-scan set.
- **Warn-now → error-later:** `--strict` promotes every migration W-warning to an
  error. Per-rule maturity (a rule graduating warn→error independently of a global
  switch) is **out of scope for v1** — one global `--strict` switch; per-rule
  maturity is a documented future extension.

### 5.7 Git-safety guard

- Before any write, `cure migrate` verifies, for each target file: it is
  **git-tracked** AND **clean**, defined precisely as: `git status --porcelain
  -- <path>` produces **zero output** for that path. This is deliberately
  specified as the full porcelain check rather than a narrower one: a
  worktree-only check (e.g. `git diff --name-only`) would miss a file with
  *only* staged changes and no working-tree diff, incorrectly treating it as
  clean; `git status --porcelain` reports staged, unstaged, and
  staged+unstaged combinations alike (all produce non-empty output for that
  path), so specifying it precisely closes that gap. A conflicted (`UU`) path
  from a mid-merge/mid-rebase state also produces non-empty porcelain output
  and is correctly treated as dirty.
- The check runs as a **preflight over the whole target set before any file is
  written** (see §5.8 for why: it must not be possible to write file 2 of N and
  then abort on file 3's dirty tree, leaving a partial rewrite).
- If any target fails, abort the whole run with a message instructing the user to
  commit or stash first. `--check` and `--print` (read-only) are exempt.
- Implementation: shell out to `git` (`git ls-files --error-unmatch`,
  `git status --porcelain`) with a clear non-git-repo error. Out of scope for
  v1: submodule-boundary targets (a `.cure` file inside a nested git
  submodule) and detached-HEAD warnings — neither is an expected shape for
  this project's `.cure` corpus today; if it arises, treat it as a new finding
  rather than silently assuming the guard handles it.

### 5.8 Batch write semantics (atomicity)

`cure migrate` (default in-place mode) processes a run of possibly-many target
files (§5.6). The git-guard (§5.7) preflights git-cleanliness for the whole
set, but git-cleanliness alone does not protect against a **mid-run failure in
the rewrite/print/reparse pipeline itself** (a rule bug, or a corpus file this
design didn't anticipate hitting a Printer/trivia gap despite the gates in
§5.3/§7). To avoid leaving a batch half-rewritten on disk:

1. For every target file, run the full `lex → parse → attach-trivia →
   migration-rewrite → print → reparse-and-diff-check` pipeline **in memory
   first**, without writing anything.
2. **Reparse-and-diff-check is a runtime guard, not only a dev-time test-suite
   gate:** re-lex and re-parse the freshly printed output and confirm it
   reparses and its collected comment text/count matches the input's before
   that file is considered ready to write. (§7's lossless round-trip gate
   covers the checked-in corpus at test time; this is the same check running
   defensively against whatever file is actually handed to the tool at
   runtime, since the corpus can't anticipate every future `.cure` file.)
3. Only if **every** target file passes step 2 does `cure migrate` write any
   file to disk. If any file fails, abort with no writes at all and report
   which file(s) failed and why.
4. `--check` and `--print` naturally satisfy the *no-partial-write* concern
   already (they never write). They still run the same in-memory pipeline
   (they must, to know what's pending / to print it) and so can still hit a
   step-2 reparse failure for a given file — that must surface as a **visible
   error attributed to that file**, not be silently folded into "pending
   changes" (`--check`) or silently printed as possibly-broken output
   (`--print`). Both must distinguish "file has pending migrations" from "file
   failed to migrate cleanly" in their exit code / output.

## 6. Build order (phases)

1. **Printer totality** — add missing node clauses (`:pin`, …), make the
   catch-all raise instead of `inspect`; land both the corpus totality gate
   and the static-exhaustiveness gate (§5.3/§7). Independent, immediately
   valuable (fixes `cure fmt`/`cure.rewrite` reparse breakage).
2. **Trivia model** — lossless lexer collection + `Cure.Compiler.Trivia`
   attachment pass + trivia-aware Printer + blank-line policy; land the lossless
   round-trip gate.
3. **Rule registry** — `Cure.Migrate.Rule` + registry; port `if/elif→pickup`
   (including resolving its known parenthesised-context reparse limitation,
   §5.5), uppercase-type-var→lowercase, and the `@group` hoist (the first
   relocation rule — exercises `Trivia.carry/2`); wire the `cure build`
   warn-and-tolerate consumer.
4. **`cure migrate` CLI + policy + git guard** — subcommand, `--check`/`--print`/
   `--strict`, git-safety guard, batch-atomicity preflight (§5.8).

Each phase ends green on the full suite; phases 1–2 are prerequisites for a
faithful whole-file reprint and must not be skipped.

## 7. Testing strategy (gates)

- **Printer-totality gate** (§5.3): corpus parse→print never inspects a tuple and
  always reparses; print is a fixpoint.
- **Printer static-exhaustiveness gate** (§5.3): every AST node-kind atom the
  parser can construct has a matching Printer clause; the catch-all raises
  (not `inspect`s) for anything else. This is the gate that actually backs the
  "total" claim, independent of what happens to be in today's corpus.
- **Lossless round-trip gate** (§5.2): corpus `lex→parse→attach→print` preserves
  every comment (count, text, attachment order) and reparses. This is the
  operator's "lossless" acceptance criterion, mechanized.
- **Trivia attachment totality:** the attachment pass errors (not drops) on any
  unplaced trivia item; a unit test asserts this on a constructed input,
  including a comment trailing the last statement of a *nested* block (not
  just the file-level case) to exercise the per-container trailer bucket
  (§5.2).
- **Rule tests:** each seed rule has red-green cases — legacy form in →
  canonical out, comments preserved across a *restructuring* rewrite
  (`if/elif→pickup` with comments on the branches), the `T`+`t` collision
  freshen-and-warn case (including a freshen that must skip past an
  already-used `t1` to `t2`), and `if/elif→pickup` on a conditional embedded in
  a call-argument list (the known parenthesised-context case, §5.5) reparsing
  successfully post-fix. The `@group` hoist additionally has a
  **comment-carry-across-move** red case: a `#`-comment attached to the in-body
  `@group(...)` line must appear attached to the hoisted decorator above `mod`
  (never dropped, never left orphaned at the old slot), and an idempotence case
  (a file already in above-`mod` form is unchanged).
- **`cure migrate` CLI tests:** in-place, `--check` exit code, `--print`,
  `--strict` error promotion, the git-guard refusal (dirty tree / untracked
  file, and a staged-only case — changes in the index but no working-tree
  diff — per the tightened §5.7 definition) via a temporary git repo fixture,
  and the batch-atomicity guarantee (§5.8: a multi-file run where one file
  fails leaves zero files written).
- **Warn-and-tolerate parity:** a rule warns under `cure build` on exactly the
  inputs `cure migrate` rewrites (one registry, two consumers, identical
  per-file `ctx` per §5.5 — asserted).

## 8. Out of scope (v1)

- Per-rule warn→error maturity levels (one global `--strict` for now).
- Any new migration rules beyond the **three** seeds (if/elif→pickup,
  uppercase-type-var→lowercase, `@group` hoist).
- A full concrete-syntax-tree replacing the AST (the trivia-on-`meta` model is
  sufficient for lossless reprint; a CST is not needed and not built).
- Migrating the kernel/elaborator or the classic-pipeline rip-out (unrelated;
  tracked elsewhere).
- Repointing `cure fmt` onto the trivia Printer (see §9 — the trivia Printer
  built here is Layer 1 of that future change, but the change itself is not v1).

## 9. Future work — `cure fmt` / `cure migrate` convergence (post-v1)

Operator direction (2026-07-10): later, repoint `cure fmt` off its current
Algebra formatter (`Cure.Compiler.Formatter.format_algebra`) onto the lossless
trivia Printer built here, and give the Printer a conservative Algebra layout
layer, so `cure fmt` can format **without** the git-clean guard.

**Why the git guard is a migration-only concern, not a formatting one.**
`cure migrate` runs rewrite *rules* that **restructure** the AST, so the guard
exists to make a possibly-buggy rule trivially revertable — a safety net against
*rule* errors. Pure formatting does not change the tree; it re-lays-out the same
AST. A formatter that is both **lossless** (trivia model) and **round-trip
verified** (reparse → compare → bail to original on any mismatch) cannot lose
information — worst case is "no change," never a corrupted file — exactly why
`gofmt`/`prettier`/`mix format` run freely on a dirty tree. So `cure fmt` needs
no guard.

**Layering.**

```
L1  total, trivia-aware Printer          ← built in this v1 (Phases 1–2), shared
L2  + conservative Algebra layout        ← width-aware breaking (future; reuse algebra.ex)
L3a cure fmt   = L2 + comment-aware verify + bail-to-original, NO rules, NO guard
L3b cure migrate = L2 + rule pass + git guard + batch atomicity  (this v1 minus L2)
```

**The one required semantic flip.** Today's `verify_algebra`
(`formatter.ex:146-166`) **strips `{:comment}` nodes before comparing**, so its
"safe" means structurally-safe, comments be damned. For a lossless `cure fmt`
the verify must become **comment-aware** — compare the attached trivia too and
bail if any comment would move or vanish. Without that flip, "conservative" does
not imply "lossless." Building the migration engine now delivers ~80% of this
future repoint; what remains later is the Algebra-layer reuse plus this verify
change.

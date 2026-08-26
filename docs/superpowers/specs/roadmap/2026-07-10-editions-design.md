# Cure Editions — Design

**Status:** design approved (brainstorm 2026-07-10), buildable; hands to
`writing-plans` for a phased implementation plan.

**Relationship to prior specs:** extends the migration facility
(`2026-07-09-migration-facility-design.md` and
`2026-07-10-migration-facility-implementation-design.md`, both landed). Those
built the *rule engine* (ordered fold, one registry / two consumers, lossless
Trivia + Printer, git-guard, `cure migrate`). This spec adds the *edition* layer
on top: a coarse, declared compatibility line that a file/project is read
against, so the language surface can evolve without breaking already-written
code. It reverses exactly one locked facility decision — the §5.5 single-pass
constraint — and only for the edition-crossing migrate path (see §6).

---

## 1. Goal

Give Cure a Rust-style **edition** system: a small, declared, calendar-named
compatibility checkpoint (`edition = "2026"`) that (a) lets the *parser* keep
reading old syntax after a keyword is retired, (b) gives every migration rule a
principled "since / enforced-in" provenance, and (c) lets `cure migrate` carry a
file or project across an edition boundary safely — apply the mechanical
rewrites to a fixpoint, verify the result still parses with every comment
intact, then bump the declared edition.

Editions are **rare and coarse**. The fine-grained unit of change is the
migration *rule*; an edition is just the line you cross. You batch a season of
breaking changes behind one boundary rather than minting an edition per rename.

## 2. Locked decisions (from the brainstorm)

1. **Scope = "C": syntax editions + rewrite-only stdlib.** An edition gates the
   *parser keyword set* (compat-parse retired keywords) and carries rule
   provenance. `cure migrate` **rewrites both** keyword changes and stdlib
   renames. It does **not** build an edition-conditional stdlib *resolver*: a
   renamed/removed stdlib name does not silently keep resolving under an old
   edition — it errors with a "run `cure migrate`" hint. (Full transparent
   stdlib compatibility — option B — was rejected as ongoing resolver weight for
   a problem the lossless one-pass rewrite already solves.)
2. **Edition identity = calendar year string**, e.g. `"2026"`. Coarse,
   ordered, deliberately not per-change.
3. **Declaration precedence: file pragma > `Cure.toml` > compiler default.** A
   `@edition("2026")` pragma at the top of a `.cure` file wins; else the
   project's `[project].edition`; else the compiler's built-in current edition.
4. **Default when undeclared = latest** (the compiler's current edition). Cure
   has no pre-edition install base to protect (pre-1.0). This default **freezes**
   post-1.0 so it never silently reinterprets code once real legacy exists.
5. **Applicability tier replaces `tolerate_safe?`.** A static `:machine |
   :review | :manual` field on each rule is the single source of truth for
   warn-vs-rewrite and safe-to-normalize.
6. **Error-later = the edition boundary itself.** A deprecation introduced in
   edition N warns under N and is a hard rejection under its `enforced_in`
   edition. `--strict` is an opt-in early preview of that strictness, and
   promotes only the fixable tiers (`:machine`/`:review`), never `:manual`.
7. **Verify = reparse + comment-preservation only** (no elaboration coupling),
   with **bounded fixpoint iteration** and a **monotone-rewrite law** +
   max-pass cap as the termination guarantee.
8. **Editions start at `"2026"`** = this branch's surface. Pre-2026 (main-era)
   code has no compat guarantee; crossing into 2026 is a one-time port aided by
   the existing rules. `proto`→`interface` is the first *forward* deprecation
   exercising the full warn→enforce cadence.

## 3. Edition identity & resolution

### 3.1 The `Cure.Edition` module

A new module `Cure.Edition` owns the edition type and its total order.

- **Representation:** an edition is a 4-digit calendar year string, validated
  against a closed allow-list `@known ["2026"]` (grows by one entry per real
  edition). An unknown string is an error at resolution time, never a silent
  pass-through — a typo'd `edition = "2062"` must fail loudly.
- **Ordering:** `compare/2` on the integer year. `current/0` returns the newest
  known edition (today `"2026"`); `all/0` returns them oldest-first.
- **No open-ended parsing:** editions are not semver and carry no minor/patch.
  `"2026"` is the whole identity.

### 3.2 `Cure.Edition.resolve/1`

`resolve(%{source: src, file: path, project_dir: dir}) -> {:ok, edition} |
{:error, reason}` applies precedence:

1. **File pragma.** If `src` begins (after leading trivia) with
   `@edition("YYYY")`, that wins. The pragma reuses `@group`'s decorator-node
   syntax but is **stricter on placement**: `@group` misplacement is only a
   soft deprecation (`emit_group_placement_deprecation/3` in `parser.ex`, still
   parses, later hoisted by `cure migrate`'s `@group`-hoist rule), whereas
   `@edition(...)` elsewhere than file-leading is a **hard parse error**, not a
   deprecation — it must be the first non-comment item. This is deliberately
   not "like `@group`" on placement: edition resolution must be decidable
   before any migration rule can run, so there is no analogous rewrite rule
   that could relocate a misplaced pragma the way `@group`-hoist relocates a
   misplaced `@group`. A pragma elsewhere failing to parse is what makes its
   scope unambiguously whole-file.
2. **`Cure.toml`.** Else `Cure.Project.load(dir)` and read `[project].edition`.
   A project with a `Cure.toml` but no `edition` key resolves to the default
   (4) **and emits a one-time advisory** to add one (so projects converge on
   explicit editions without hard-failing).
3. **Compiler default.** Else `Cure.Edition.current/0` (latest). Standalone
   `cure run hello.cure` with no manifest and no pragma lands here.

Resolution is **per-file** (the pragma can override the project on any single
file), which is what enables incremental one-file-at-a-time migration.

### 3.3 `Cure.toml` and pragma surface

- `Cure.toml` `[project]` table gains an optional `edition = "2026"` string.
  `Cure.Project` (`lib/cure/project.ex`) gains an `:edition` field, parsed and
  validated through `Cure.Edition`. Absent ⇒ `nil` ⇒ default path.
- The `@edition("2026")` pragma is a new recognized top-of-file decorator. It is
  **not** a keyword (so it needs no edition gating itself) — it is a decorator
  node the parser already represents, special-cased only in that it must be
  file-leading and its argument is validated as an edition.

## 4. Edition-parameterized lexing

The one thing that genuinely *requires* editions: keeping an old file parseable
after a keyword is retired.

### 4.1 Keyword set as a function of edition

Today `lib/cure/compiler/lexer.ex` has a compile-time `@keywords` (line 47) and
`@keyword_strings`, consulted at `word in @keyword_strings` (line 718).

- `Cure.Lexer.tokenize/2` gains an `:edition` option (default
  `Cure.Edition.current/0`). It computes the **effective keyword set** for that
  edition instead of using the static constant.
- The effective set = **base keywords** minus every keyword *retired at or
  before* this edition. "Retired at edition R" means: present for editions
  `< R`, absent for editions `>= R`. A retired keyword lexes as an ordinary
  identifier once it's out of the set, so old code that used the *new* spelling
  is unaffected and code that used the retired word as an identifier keeps
  working at the newer edition.
- **Single source of truth:** the retirement schedule is **not** duplicated in
  the lexer. It is derived from the migration registry: a rule may declare
  `retires_keywords: ["proto", "impl"]` alongside its `enforced_in:` edition
  (§5). `Cure.Edition.keyword_set(edition)` folds the registry to compute the
  removed set. This keeps the lexer and `cure migrate` from disagreeing about
  when `proto` stops being a keyword.
- `interface`/`implementation` were *added* in 2026 (the floor edition), so they
  are present in every edition and need no gating. Only *retiring* keywords are
  edition-conditional; `proto`/`impl` with `enforced_in: nil` stay present in
  all editions (perpetual soft-deprecation until scheduled).

### 4.2 Parser

`Cure.Parser.parse/2` already threads options; it gains `:edition` and passes it
wherever a token's keyword-ness is (re)checked. The Pratt structure is unchanged
(no NimbleParsec — facility §4.2 holds). The parser also enforces the
`@edition(...)` pragma placement rule (file-leading only).

## 5. Rule model: tiers + edition provenance

`Cure.Migrate.Rule` (`lib/cure/migrate/rule.ex`) is extended.

### 5.1 New/changed fields

```
%Cure.Migrate.Rule{
  id:                 atom(),                       # unchanged (the W-code)
  description:        String.t(),                   # unchanged
  phase:              :syntactic | :needs_resolution,# unchanged
  detect_and_rewrite: (ast, ctx -> result()),       # unchanged shape
  warning_template:   String.t(),                   # unchanged
  # --- new ---
  tier:               :machine | :review | :manual, # REPLACES tolerate_safe?
  since:              Cure.Edition.t(),             # edition it starts warning
  enforced_in:        Cure.Edition.t() | nil,       # edition it becomes a hard error (nil = unscheduled)
  retires_keywords:   [String.t()]                  # default []; drives §4.1 lexer gating
}
```

- **`tier`** is the single warn/rewrite/normalize authority:
  - `:machine` — rewrite proven semantics-preserving. `cure migrate` applies;
    `cure build` may normalize in-memory. Returns `{:rewrite, ast[, lines]}`.
  - `:review` — a candidate rewrite exists but may shift meaning / is
    context-dependent. `cure migrate` applies **and lists it in the run report
    as needing review**; `cure build` warns and does *not* normalize. Returns
    `{:rewrite, …}`. Has one member at launch: `uppercase-type-var →
    lowercase` (§5.3) — its rewrite is unsafe to fold into `cure build`'s
    in-memory AST because lowering a dependently-typed signature's binder can
    break metavar solving (the exact reason `Cure.Migrate.Rule`'s moduledoc
    gives today for shipping it `tolerate_safe?: false`); `:review` is what
    preserves that non-normalizing behavior under the new tier scheme.
  - `:manual` — no rewrite possible; warn-only with a porting hint. Returns
    `{:warn, lines}`.
- `tolerate_safe?` is removed; `commit/4` in `Cure.Migrate` keys off `tier`
  (`:machine` normalizes in `:safe_only`/build mode; `:review`/`:manual` do
  not). **This is not a pure rename of the old flag.** Every rule in today's
  registry ships `tolerate_safe?: false` (`cure build` never normalizes any of
  them). Retagging `if/elif→pickup`, `@group` hoist, and module rename to
  `:machine` (§5.3) is a **deliberate capability upgrade**, not a like-for-like
  translation: `cure build` will now normalize those three in-memory where it
  never did before. That upgrade is safe to grant them specifically because
  each is independently semantics-preserving per its own moduledoc (a pure
  spelling rename, a no-op-when-already-canonical relocation, and a mechanical
  rename respectively) — it is not true of every currently-`tolerate_safe?:
  false` rule, which is why `uppercase-type-var→lowercase` is retagged
  `:review`, not `:machine` (above), rather than swept into `:machine` along
  with the other four.
- **`retires_keywords`** is the bridge to §4.1: only keyword-class deprecations
  set it. Its `enforced_in` is what the lexer reads.

### 5.2 Provenance semantics

- `since` — the edition in which this deprecation begins **warning**. Every rule
  in the shipped registry today is `since: "2026"`.
- `enforced_in` — the edition in which the old form becomes a **hard error**:
  for a `retires_keywords` rule, the edition the lexer drops the keyword;
  for a stdlib rule, effectively "already enforced" (the name is already gone —
  see §8) so these carry `enforced_in: "2026"`. `nil` = warns but is never
  auto-enforced until scheduled (`proto`→`interface` ships `nil`).

### 5.3 The existing rules, re-tagged

| rule | tier | since | enforced_in | retires_keywords |
|---|---|---|---|---|
| if/elif → pickup | `:machine` | 2026 | nil | — |
| uppercase type var → lowercase | `:review` | 2026 | nil | — |
| `@group` hoist | `:machine` | 2026 | nil | — |
| module rename (`Std.Eq`→`Equatable`) | `:machine` | 2026 | 2026 | — |
| removed module (`Refine`/`Equal`) | `:manual` | 2026 | 2026 | — |
| **new:** `proto`/`impl` → `interface`/`implementation` | `:machine` | 2026 | **nil** | `["proto","impl"]` |

The `proto`→`interface` rule is authored as part of this spec (it's the
exemplar), rewriting `proto Name(t)` → `interface Name(t)` and `impl C for T`
→ `implementation C for T`, preserving the body. `enforced_in: nil` means it
warns and rewrites but the keyword stays live until a future edition schedules
it.

## 6. Migration engine: fixpoint + verify

Reverses facility §5.5 single-pass **only here**.

### 6.1 `Cure.Migrate.run_to_fixpoint/2`

New driver wrapping the existing `run/2` ordered fold:

1. Run the registry fold once (`run/2`), collecting warnings and the new AST.
2. If the pass changed nothing, stop — converged.
3. Else reprint → reparse the output; **verify** it parses and every source
   comment survives (reuse the facility's lossless check). If verify fails, the
   whole migration **aborts** with the offending file/rule (never writes a
   half-migrated file).
4. Else loop from (1) with the new AST, up to `@max_passes` (e.g. 8).
5. If still changing at `@max_passes`, **error** "migration did not converge"
   naming the rules that were still firing — a bug in the rule set, not the
   user's file.

### 6.2 Monotone-rewrite law

Every rule's rewrite must move *toward* the canonical/new form and never back.
Formally: for the whole registry, a second full pass over the fixpoint output
produces no change (idempotence at the reprint level). This is a **design law on
rule authors**, enforced by a property test (§9): pick any corpus, migrate to
fixpoint, migrate again, assert byte-identical. It makes the `@max_passes` cap a
backstop against an authoring mistake rather than a load-bearing limit, and it
rules out A:x→y / B:y→x ping-pong by construction.

### 6.3 Warn-and-tolerate parity is preserved

`cure build` still runs the registry once (warn mode) — it does **not** iterate
to a fixpoint (build must not silently apply chained rewrites; it warns on what
it sees in one pass, same as today). Fixpoint iteration is exclusive to
`cure migrate`, whose job is to *reach* the canonical form. The parity claim
(the set of rules that warn == the set that rewrite) holds per-pass.

## 7. `cure migrate` — edition crossing

`cure migrate` (`lib/cure/cli.ex` cmd at line 139) gains an edition-aware,
two-phase behavior modeled on `cargo fix --edition`.

### 7.1 Target selection

- `cure migrate` (no `--edition`) — migrate to `Cure.Edition.current/0` (latest).
- `cure migrate --edition 2026` — migrate to the named edition (must be known
  and `>=` the file's current edition; downgrades are refused).
- File/dir/glob target selection and the git-guard are unchanged from facility
  §5.6/§5.7 (whole-project scan when no paths given).

### 7.2 Which rules run for a crossing X → Y

Apply every rule that is **relevant to reaching Y**:

- rules with `enforced_in != nil and enforced_in <= Y` — **mandatory** (their
  old form is illegal at Y);
- plus all `:machine`/`:review` rules with `since <= Y` — proactively applied.
  This must include `:review`, not just `:machine`: §5.1 already says
  "`:review` — … `cure migrate` applies" — a rule-selection formula that only
  named `:machine` here would silently drop `:review`-tier rewrites (currently
  `uppercase-type-var → lowercase`, §5.3) from every `cure migrate` invocation,
  contradicting §5.1 and regressing today's `cure migrate`, which applies that
  rewrite unconditionally. `:machine` and `:review` differ only in whether
  `cure build` may also normalize (§5.1) and in the run-report annotation
  (§5.1's "needing review" flag carries through here) — not in whether
  `cure migrate` applies them.

`:manual` rules never rewrite; if any `:manual` item with `enforced_in <= Y`
remains after phase 1, the bump (phase 2) is **refused** with the list of
hand-port sites — bumping would produce code that errors at Y.

### 7.3 Two phases

- **Phase 1 — make edition-idempotent.** Run `run_to_fixpoint/2` with the
  X→Y rule set. Result parses under both the current and target edition (the
  rewrites remove exactly the forms that differ). Write the reprinted files
  (respecting the git-guard and atomic batch write, facility §5.8).
- **Phase 2 — bump the declared edition.** Update the edition marker to Y:
  - whole-project migrate ⇒ set `[project].edition = "Y"` in `Cure.toml`
    (via `Cure.Project`, lossless TOML edit);
  - single standalone file ⇒ insert/update its `@edition("Y")` pragma.
  Phase 2 runs only if phase 1 fully succeeded and no blocking `:manual` item
  remains.

### 7.4 Modes

`--check` (CI: list files that would change, non-zero exit, no write) and
`--print` (stdout) behave as facility §5.6, now including the pending edition
bump in their report.

## 8. `--strict` and the error-later boundary

- **The edition boundary is the real "error-later."** Under edition N a
  `since: N` deprecation warns; under its `enforced_in` edition the old form is
  rejected — for keywords by the lexer (§4.1), for stdlib by ordinary
  resolution failure (the C decision: the name is simply gone). No separate
  per-rule maturity switch is needed; the edition *is* the maturity axis.
- **Already-removed stdlib (`enforced_in: "2026"`).** `Std.Eq`/`Refine`/`Equal`
  are already absent on this branch, so a reference to them already hard-errors
  at resolution. Their migration rules exist purely as **porting aids** for
  crossing the pre-2026 → 2026 gap; the "warning" is advisory on top of a real
  resolution error.
- **`--strict`** promotes fixable-tier (`:machine`/`:review`) migration warnings
  to build errors — an opt-in preview of the next edition's strictness. It does
  **not** promote `:manual` (no button to clear it; its real breakage surfaces
  as a resolution error at the boundary anyway).

## 9. Testing strategy (gates)

- **Edition resolution:** pragma > `Cure.toml` > default precedence; unknown
  edition string errors; missing-`edition` project advisory; standalone-file
  default = latest.
- **Edition-parameterized lexer:** a retiring keyword (use a fixture rule with
  `retires_keywords` + `enforced_in`) lexes as a keyword below `enforced_in` and
  as an identifier at/above it; `proto`/`impl` stay keywords in all editions
  (`enforced_in: nil`); the removed set is derived from the registry, not
  hardcoded (change the fixture rule's `enforced_in`, the keyword set follows).
- **Tier refactor:** `:machine` normalizes in build mode, `:review`/`:manual` do
  not; `{:warn}`/`{:rewrite}` result kinds follow tier. The regression pin
  covers each rule's warning text and `cure migrate` rewrite output
  (unchanged by the refactor) and, separately, `cure build`'s normalization
  decision for the two rules whose tier keeps it non-normalizing
  (`uppercase-type-var→lowercase` at `:review`, `removed-module` at
  `:manual` — both pin to their prior `tolerate_safe?: false` behavior
  exactly). It does **not** claim `cure build`'s normalization decision is
  unchanged for the three rules retagged `:machine`
  (`if/elif→pickup`, `@group` hoist, module rename): that is a deliberate,
  disclosed upgrade from `tolerate_safe?: false` (§5.1) — assert instead that
  `cure build` normalizes those three post-refactor and did not pre-refactor.
- **Fixpoint + verify:** a two-rule chain (rule B's trigger exposed only by rule
  A) converges in one `run_to_fixpoint`; a deliberately non-monotone fixture
  rule set hits `@max_passes` and errors with the offending rules; verify
  failure (a rule that drops a comment / breaks reparse) aborts without writing.
- **Monotone property test:** migrate the stdlib corpus to fixpoint, migrate
  again, assert byte-identical.
- **Two-phase migrate:** X→Y rewrites then bumps `Cure.toml`/pragma; a blocking
  `:manual` item refuses phase 2 and reports the hand-port sites; `--check`/
  `--print` report the pending edition bump; git-guard still refuses dirty
  targets.
- **`proto`→`interface` exemplar:** an old `proto`/`impl` file warns under 2026,
  `cure migrate` rewrites it to `interface`/`implementation` losslessly and the
  output reparses; the keyword remains live (`enforced_in: nil`).
- **`--strict`:** promotes `:machine`/`:review`, not `:manual`.
- **Antigen:** the edition-parameterized lexer path and the fixpoint driver get
  coverage probes so the coverage-floor gate protects them.

## 10. Build order (phases)

1. **`Cure.Edition` + resolution.** The module, ordering, allow-list, `resolve/1`
   precedence, `Cure.Project`/`Cure.toml` `edition` field, `@edition` pragma
   parse. (No behavior change yet — nothing consumes the edition.)
2. **Rule model refactor.** Add `tier`/`since`/`enforced_in`/`retires_keywords`;
   remove `tolerate_safe?`; re-tag the five existing rules; repoint
   `commit/4`. Existing test suite stays green, but this is **not** behavior-neutral
   for `cure build`: retagging `if/elif→pickup`, `@group` hoist, and module
   rename to `:machine` (§5.1) turns on in-memory normalization for those three
   that was off under `tolerate_safe?: false` — add a regression test per rule
   asserting the new normalized-in-build behavior before merging this phase, not
   just "suite stays green" on the pre-existing tests (which never exercised
   this path in the first place, since nothing was normalized before it).
3. **Edition-parameterized lexer/parser.** `:edition` option, registry-derived
   keyword set, pragma placement enforcement.
4. **Fixpoint + verify engine.** `run_to_fixpoint/2`, monotone property test,
   `@max_passes`. `cure build` stays single-pass.
5. **`proto`→`interface` rule.** The first `retires_keywords` rule; exercises 3
   and 4 end to end.
6. **Edition-crossing `cure migrate`.** Two-phase target selection, edition bump
   of `Cure.toml`/pragma, `:manual`-blocks-bump interlock, `--check`/`--print`
   reporting, `--strict` tier promotion.

Each phase ends green and independently testable.

## 11. Out of scope (v1)

- **Transparent stdlib compat resolution** (option B) — explicitly rejected in §2.
- **Per-rule maturity switches** beyond the edition boundary + `--strict` — the
  edition is the maturity axis.
- **Minting a second edition ("2027").** This spec builds the machinery and ships
  `2026` as the floor plus `proto`→`interface` as an unscheduled (`enforced_in:
  nil`) forward deprecation. Scheduling it (choosing the enforcing edition and
  adding "2027" to the allow-list) is a later, trivial follow-up once the
  machinery exists.
- **Elaboration-level migrate verification** — rejected in §2 (kernel coupling);
  "does it still typecheck" stays with `cure build` after migration.
- **Cross-edition dependency interop policy** (a `Cure.toml` dep on a differently-
  editioned package). Cure compiles from source into one BEAM target; deps are
  resolved and compiled under their own declared edition already via per-file
  resolution (§3.2), so no separate ABI-stability story is needed at v1. Named
  here only to record it was considered.

## 12. Future work

- Schedule `proto`→`interface` enforcement by minting the next edition.
- `cure fmt`/`cure migrate` convergence (facility §9) is unaffected and still
  applies — the fixpoint driver is a natural shared core.
- A per-edition idiom-lint group (Rust's "idioms" — style, not correctness),
  distinct from the compatibility rules here.

# Cure 0.34 — Launch Checklist

**Status:** open
**Target version:** 0.34.0 (`mix.exs` currently pins `@version "0.33.1"`)

What 0.34 *is* lives in [`../ROADMAP-0.34.md`](../ROADMAP-0.34.md) — the feature
narrative for the dependent-pipeline release. This document is the complementary
list: the work that must be finished before the tag goes out. Roadmap answers
"what shipped"; this answers "what's blocking".

Items are grouped by kind, not priority. Anything marked **breaking** must land
before the tag, because it cannot land after one without a 0.35.

---

## 1. Surface changes that must land pre-tag

- [x] **Rename the anonymous hole `??` → `?_`.** (breaking)
  `?_` is now the sole authored anonymous spelling. Exact `??` produces the
  targeted “Anonymous hole spelling changed” diagnostic with a `?_` repair;
  bare `?` remains valid and compiler-generated `???` placeholders retain their
  existing token and span behaviour. Lexer regressions cover `?_`, `??`, `???`,
  and predicate identifiers ending in `?`. Current language/type/proof docs,
  the holes demo, printer, doctor, registry, and the retained holes utility use
  the new spelling.

- [x] Sweep for any other locked-surface spellings still in flux, so the whole
      breaking set lands in one tag. Current website pages, Vim/Neovim syntax
      and examples, the VS Code README, and Highlight.js source/distribution
      now teach `?_`; no live actor/FSM/supervisor/application example authors
      a BEAM-only `Cure.` module prefix. Historical release/design archives keep
      their original spellings intentionally.

---

## 2. Documentation

- [x] **Write `docs/MACROS.md`.** Done — 14 sections covering the `macro`
      container and its members, rule grammar (dispatch keyword, holes,
      repetition, `is`/`open`, `where`, `contextual`), `literal`, `becomes`,
      `computed by`, `syntax family`/`accepts`/`expands with`, the `Std.Syntax`
      quoted-AST API, the self-proving obligations, scope/staging, termination
      and purity, diagnostics, and known sharp edges. Registered in `mix.exs`
      `extras` and the README doc list. Every ` ```cure ` fence in it is checked
      by `mix cure.check.docs`; one is tagged ` ```cure W000 ` because
      `lift_module` cannot emit a warning-free module. Grammar fragments — rule
      shapes, quoted-AST type excerpts, a deliberately non-parsing template —
      are ` ```text `, since they are not Cure source and there is no tag that
      opts a `cure` fence out of the gate. Diagnostic transcripts quoted in the
      doc were reproduced, not paraphrased.

      Written against the implementation rather than the specs, which corrected
      three points the design docs get wrong:
      - `explain` clauses use `=>`, not the `->` in
        `2026-07-08-macro-facility-design.md`.
      - Only `Name`, `ModuleName`, `Type`, `Parameters`, `Int`/`Float`/`Atom`/
        `Bool` and `Code` have dedicated matching behaviour in a `syntax` rule
        (`parser.ex:987-1039`). Every other hole kind — `Number`, `Expression`,
        `Statement`, `Pattern`, `Token` — falls through to the same
        `parse_expr` clause at `parser.ex:1087`, so those names are labels, not
        constraints. The richer shape vocabulary is only meaningful as a
        `syntax family` field shape.
      - Writing an `explain` block is what opts a macro into the *full*
        self-proving contract (exhaustive failure-point coverage **and** a
        mandatory worked example on every `syntax`/`computed` rule). Without it,
        examples are optional. This is the doc's main narrative and it is not
        stated in any one spec.

- [x] **Expand `docs/PROOFS.md` to cover the new proof vocabulary.** It now
      gives worked authoring guidance for the implemented constructs, while
      the authoritative design
      (`superpowers/specs/2026-07-21-proof-language-ergonomics-design.md`) is 786
      lines and marked *implemented*. Each of the ten features needs a worked,
      compiling example:
      `proof chain`/`because` · `have` · `rewrite using` ·
      `rewrite backwards using` (incl. `in <hypothesis>` and `at <n>`) ·
      `simplify` / `simplify using [rules]` / `simplify using <proof>` ·
      `induction` with `case C(field, ih) =>` · automatic congruence ·
      generated defining equations · dependent-pattern refinement and named
      implicit patterns · named arguments.
      Best existing exemplar to lift from:
      `lib/std/proof_linear_arithmetic_semantics.cure:45-150`.

- [x] Document the proof diagnostics **E109–E114** and **E115** (named
      arguments) at the same level as the rest of the catalog — the design gates
      each feature on its diagnostics, so the docs should show them.

- [x] Reconcile `docs/PROOFS.md` "Proof authoring surface" with
      `LANGUAGE_SPEC.md` §"Proof authoring" so the two don't drift.

- [ ] Finalise `CHANGELOG.md`: promote `[Unreleased]` to `[0.34.0]` with a date,
      and confirm the "Breaking changes" list in `ROADMAP-0.34.md` is fully
      mirrored there.

- [ ] ~~Decide the fate of the root-level `AUTOPILOT-*.md` reports (10 files).~~
      No longer applicable: `ls AUTOPILOT-*.md` at the repo root now returns no
      matches, so those files have already been removed (or their conclusions
      folded elsewhere). Confirm nothing they recorded still needs to land in
      the changelog/roadmap before closing this item.

---

## 3. Website (`site/`)

- [ ] **Finish the redesign.** Last touched by `7db54c80` ("Improve
      source-driven documentation and landing page"), which reworked
      `site/lib/cure_site_web/controllers/page_html/home.html.heex` and
      `components/layouts.ex`. *(Fill in the remaining scope — I couldn't infer
      what "done" means for the redesign from the repo alone.)*

- [x] Make sure the source-driven stdlib docs pipeline covers the 0.34 surface.
      `stdlib_controller.ex` renders from `lib/std/*.cure` docstrings, and
      `test/cure/doc/stdlib_source_docs_test.exs` gates it — verify the new
      proof modules (`Std.Proof.LinearArithmetic`, `Std.Decision`,
      `Std.Equivalent`) render correctly. The renderer test now asserts all
      three generated pages and their source-owned module documentation.

- [x] Landing page reflects 0.34's actual pitch: one dependent pipeline from
      elaboration through independent kernel checking and quantitative erasure
      to BEAM emission, with indexed types and OTP on the same surface. The
      machine-facing `llms.txt` summary was updated from the retired
      refinement/Z3 framing at the same time and links the macro and proof
      references directly.

- [ ] Check `llms_controller.ex` / `sitemap_controller.ex` output includes the
      new docs (`MACROS.md`, expanded `PROOFS.md`) once written.

---

## 4. Known bugs blocking advertised features

- [x] **Generated defining equations can be applied at their friendly names.**
      `f.Ctor` resolves and reports a correct Pi type, but applying it panics.
      Minimal reproduction:

      ```cure
      mod Probe3
        use Std.Equivalent
        type Nat3 = Z3 | S3(Nat3)
        fn add3(x: Nat3, y: Nat3) -> Nat3 = match x
          Z3()  -> y
          S3(k) -> S3(add3(k, y))
        fn add3_succ_eq(k: Nat3, y: Nat3) -> Equivalent(Nat3, add3(S3(k), y), S3(add3(k, y))) = add3.S3(k, y)
      end
      ```

      The parser's flattened `add3.S3(...)` call now resolves to the certified
      theorem, reconstructs the scrutinised `S3(k)` argument, and supplies the
      complete theorem telescope. Reachable equations enter the emission
      closure; unused equations remain compile-time-only. The reproducer is
      covered through actual BEAM compilation in `defining_equation_test.exs`.

- [x] Re-audit the proof-ergonomics acceptance criteria (§11 of the design, 12
      items). The implementation ledger records criterion-by-criterion parser,
      printer, elaborator, kernel, erasure, diagnostic/LSP, restored affine-LIA,
      and Cure/Idris evidence. The post-dependent-core release gate re-ran the
      complete suite (6,178 tests, 0 failures, 6 excluded), canonical stdlib,
      documentation (332/332), and Antigen (318/318); the repaired friendly
      defining-equation application has its own real-BEAM regression.

- [x] **Bad `lift_module` names are ordinary validation errors, never E101.**
      Authored `Books`/`Demo.Books` captures are qualified under their defining
      module by the parser. A computed macro that manufactures an invalid name
      is now rejected immediately after declaration expansion: `compile` returns
      `invalid_module_name` before entering codegen, and `check` runs the same
      lifted-request validation before printing OK. Compiler and CLI regressions
      cover both public paths.

- [x] **`<fresh …>` works in lambda parameter position.**
      `parse_explicit_param/2` now consumes the complete marker as a binder,
      preserves its source span and explicit-fresh metadata, and the scoped
      hygiene pass gives the parameter and matching body references the same
      gensym. `macro_hygiene_test.exs` covers the original
      `(fn(<fresh tmp>) -> <fresh tmp>)(n)` reproducer end to end through macro
      parsing and expansion.

- [x] **`cure.check.docs`'s own tests never ran — the fixture had no artifact
      set.** Fixed. The fixture in `test/mix/tasks/cure.check.docs_test.exs` is
      a bare temporary directory; the task resolves `stdlib_ebin` as
      `_build/cure/ebin` relative to that root, found nothing, and
      `Cure.Compiler.Artifacts` rejected every compile with `E100 INVALID BUILD
      ARTIFACT` before any snippet was judged. All eleven tests failed for a
      reason none of them was testing. The setup now symlinks the project's own
      compiled stdlib into the fixture root; the file is green.

      (If `mix compile` aborts with `(UndefinedFunctionError) function
      Cure.Compiler.Artifacts.Writer.transact/2 is undefined` via
      `cure.compile_stdlib.ex:57`, the seven files under
      `lib/cure/compiler/artifacts*` are missing from the working tree. They
      are tracked — `git checkout HEAD -- lib/cure/compiler/artifacts.ex
      lib/cure/compiler/artifacts/` restores them.)

- [x] **The repository-wide documentation gate is green.** All historical
      backlog was ported or correctly classified, and `mix cure.check.docs`
      now reports **332 passed, 0 failed**. The final failures exposed and fixed
      general compiler/macro gaps rather than being hidden: let-bound tuple
      matrices used by generated FSMs, lexical lifted-module resolution, and a
      complete `handle_call/3` callback floor for cast-only actors.

---

## 5. Warning diagnostics reach parity with errors

Warnings currently render as a bare title and message — no file, no quoted
source, no carets — while errors get the full treatment (heading with path,
`at path:line:col`, quoted source lines, `^^^^` primary and `----` secondary
labels). Compare the two from a single stdlib build:

```
-- MIGRATION WARNING [W001] ----------------------------------------------------

uppercase type variable will be lowercased
```

```
-- PROOF DOES NOT JUSTIFY CHAIN STEP 1 [E110] -- /path/to/probe.cure

The evidence after `because` does not prove the equality required by step 1.

at /path/to/probe.cure:41:17
40 |         add2(S2(k), y) == S2(add2(y, k))
   >                        -----------------
41 |         because rewrite using ih
   > -------------------------------- step 1 requires this equality
   >                 ^^^^^^^^^^^^^^^^ this evidence proves a different proposition
```

- [x] **Give warnings a primary `Label` with a real `Span`.** This was the
      actual blocker upstream of the renderer.
      `Cure.Diagnostic.Renderer.evidence_doc/3` already draws the snippet for
      *any* diagnostic that has both a `%SourceRegistry{}` and a `primary`
      `%Label{span: %Span{}}`. Migration producers now recover source lines from
      canonical `SourceInfo`, the compiler resolves those lines against its
      registered source buffer, and W001 carries a primary label through plain,
      ANSI, JSON, and LSP renderers.

- [x] **Widen the migrate-rule contract from lines to spans.**
      `Cure.Migrate.Rule.warning_loc` now accepts authored `%Span{}` locations,
      `Cure.Migrate.Warning` carries the span while retaining its derived `line`
      compatibility field, and the compiler consumes the producer's span
      directly. All six rules point at the token they diagnose: the uppercase
      binder, `if`, `proto`/`impl`, module name or qualified callee, removed
      reference, and `group` decorator name. Standalone decorators now retain
      canonical `SourceInfo` so the group rule does not have to reconstruct a
      range. The complete migration plus parser suite covers the contract
      (146 tests, 0 failures).

- [x] **Show the post-migration preview.** Migration warnings now carry the
      canonical printed proposal produced by the rule's rewritten AST. The
      compiler turns it into a whole-file structured `TextEdit`, so the existing
      terminal, JSON, and LSP projections expose the same proposal (including an
      LSP code action). Preview generation uses a trivia-attached diagnostic copy
      of the compile AST; comments are therefore retained even though the AST
      used for code generation deliberately omits trivia.

- [x] **Respect `tier` in how the preview is worded.** `Rule.tier` is the
      warn/rewrite/normalize authority and is no longer flattened:
      `:machine` is certified semantics-preserving (safe to phrase as "will
      become" and to offer as an auto-fix); `:review` warns only and must not be
      auto-normalized by `cure build` (phrase as advisory); `:manual` has no
      auto-migration at all. Warnings now retain the tier: machine proposals are
      `:machine_applicable`, review proposals are `:maybe_incorrect` and worded
      as review-required, and manual warnings have a manual hint with no edit or
      fake preview. Tier and comment-preservation regressions are covered by the
      migration tier suite and the public compiler diagnostic path.

- [x] **Cover the whole warning family, not just W001.** `W000`
      (`compiler_warning`) resolves its authored line to a primary range in the
      host adapter and is covered in terminal, JSON, and LSP projections. W001
      now uses exact producer spans. W002 is process/configuration-level and W003
      is an explicit whole-operation confirmation; neither has an authored
      source token, so both intentionally remain global diagnostics rather than
      carrying fabricated locations.

- [x] Add terminal (plain + ANSI), JSON, and LSP snapshots for warnings at the
      catalog widths, matching what §7 of the proof-ergonomics design already
      requires of errors. `warning_snapshot_test.exs` pins W000/W001 with exact
      source-bearing terminal output and machine ranges, and W002/W003 as
      deliberately global diagnostics with no invented LSP range.

- [x] Fix the emission point that interleaves W001 with Mix's progress output.
      Compiler entrypoints now accept an optional migration-diagnostic collector;
      the default still renders immediately, while the incremental stdlib driver
      collects complete diagnostics with their source registries and flushes them
      after module progress. A public compiler-path regression proves collection
      leaves stderr empty and preserves source evidence for later rendering.

---

## 6. The REPL still works after everything we changed

Verified by running `mix cure.repl` against the current tree. Basic evaluation
is fine (`1 + 1` → `2`, `type Nat3 = ...` → `defined type Nat3`), but **no
multi-line definition survives the input loop**, which means none of the new
proof vocabulary is reachable from the REPL at all.

- [x] **Teach `incomplete?/2` about indentation-structured blocks.** This is the
      blocker everything else in this section sat behind. Fixed with recursive
      open-AST detection plus indentation-aware buffering. The REPL suite now
      installs a real multi-clause function entered line by line.
- [x] **Blank lines must not force-submit inside a block.** `proof chain`
      separates its steps with blank lines (see
      `lib/std/proof_linear_arithmetic_semantics.cure:45-150`). Blank lines are
      now retained while an indented block is open; `;;` explicitly submits it.
- [x] **Add the new proof keywords as continuation cues** once the indentation
      rule is in: `induction`, `have`, `because`, `rewrite`, `simplify`, and the
      two-word `proof chain`. `case C(field, ih) =>` is covered as well.
- [x] **Make `:holes` actually work.**
      Session definitions are elaborated before emission and retain the typed
      `%{function:, goal:, context:}` reports from `Program.hole_goals/1`.
      Replacing the incomplete definition clears the retained goals.
- [x] **REPL diagnostics retain source evidence.** Expression evaluation now
      gives each synthesized module a stable `repl/Repl.M<n>.cure` identity and
      passes that exact wrapper source to the diagnostic registry on failure.
      The terminal renderer therefore prints the failing input and caret rather
      than an empty numbered line; an eval-path regression asserts this.
- [x] **Session-def inlining survives proof definitions and defining equations.**
      A REPL regression installs a recursive ADT function, then an
      `@lemma`-decorated theorem whose body is its generated `f.Ctor` equation,
      and finally evaluates the function through the next synthesized module.
      This also exposed and fixed multi-declaration submissions: each entry now
      slices its own parser span instead of storing/re-emitting the entire input
      once per sibling declaration.
- [ ] **Version banner.** The REPL prints `Cure REPL v0.33.1`; covered by the
      `mix.exs` bump in §7 but worth confirming it reads the bumped version.
- [x] **First launch pays a silent multi-minute stdlib build.** A cold
      `mix cure.repl` took ~6 minutes here (74-module stdlib compile + 7.5 MB
      escript). The delay belongs to the project's `compile` alias, not REPL
      preload, and release artifacts already bundle the generated stdlib BEAMs.
      The incremental compiler now accepts a safe progress callback and
      `cure.compile_stdlib` reports `[n/74] Module` for each distinct dirty
      module, plus an honest `[recheck] Module` when interface-cycle
      stabilization revisits one; warm builds emit no fake per-module progress.
      A forced 74-module rebuild and a focused fresh/no-change regression verify
      both paths. W001 batches are collected until progress completes (§5).
- [x] **Add eval-path test coverage.** `repl_test.exs` now drives real line-by-line
      multiline input through buffering and session compilation, covers nested
      match arms, indentation-preserved blank lines, explicit `;;` submission,
      proof continuation cues, and live hole reporting/clearing. The complete
      REPL/session gate is 71 tests green.
- [x] Update `docs/REPL.md`: submission semantics, indentation-owned blank
      lines, proof cues, `:holes`, and the Idris-style inspection commands now
      describe the implemented behaviour.

---

## 7. Release mechanics

- [ ] Bump `@version` in `mix.exs` to `0.34.0` (also drives `source_ref:
      "v#{@version}"` for docs links).
- [x] `cure migrate` rule coverage for every 0.34 rename. Strict check mode is
      clean with zero output over both `lib/std/` and `examples/`. The final
      pass also fixed source-path propagation, canonical resolution of
      underscored stdlib modules such as `Std.ExitReason`, optional syntax-family
      printing, and grammar-alternative selection so the gate cannot silently
      corrupt nominal types or payload-free FSM productions.
- [ ] Full gate pass: suite, canonical stdlib compilation, TCB/termination
      checks, Antigen, Dialyzer, `mix cure.diagnostics --coverage`.
- [ ] `mix cure.compile` clean on the downstream consumers — at minimum the
      `cure-otp` package (`lib/` + `metatheory/src`, 59 proof modules) and the
      `esp32-beam` phase dirs on generic-unix AtomVM. `cure-otp` has now been
      run against this exact checkout: 252 tests pass. Its only two migration
      warnings were real uppercase implicit binders in
      `otp_branch_merge.cure`; those were ported, strict migration is clean over
      `lib` + `metatheory/src`, and a fresh metatheory preload completes without
      warnings. The AtomVM phase-dir gate remains.
- [x] Resolve the stdlib's spurious `W001` migration warning. The uppercase
      type-variable rule was descending into qualified type paths and treating
      the `Std` in `Std.Bool.Bool` as a free type variable. Qualified
      `attribute_access` types are now atomic to detection and rewriting. The
      migration suite is green and a clean 74-module stdlib build emits no W001.
- [ ] Tag v0.34.0 after the remaining gates. `RELEASE.md` has been replaced
      with an operational 0.34 procedure covering metadata, repository and
      downstream gates, package inspection, CLI/REPL smoke checks, signed tag,
      Hex/HexDocs/site publication, and the post-publication rollback boundary.

---

## Notes

- The `?_` rename, the E101 bug, the doc gaps in §2, and every §6 REPL finding
  were verified against the tree at the time of writing — the REPL items come
  from actually running `mix cure.repl`, not from reading it. Items marked
  *(Fill in)* are placeholders where I had no evidence to draw on.
- Downstream consumers of the new proof vocabulary should not start migrating
  until §1 is settled, or they'll migrate twice.

### REPL verification — what was actually run

Evidence behind §6, recorded so the next person doesn't have to re-derive it.

**Headline: the REPL cannot accept any multi-line definition, so none of the
0.34 proof vocabulary is reachable from it at all.** Every new proof form
(`induction` + `case … =>`, `proof chain`, indented `because`) is multi-line by
construction.

Basic evaluation is healthy — `1 + 1` → `2`, `type Nat3 = Z3 | S3(Nat3)` →
`defined type Nat3`. The failure starts the moment a definition spans lines:

```
cure(1)> fn add3(x: Nat3, y: Nat3) -> Nat3 = match x
-- PATTERN MATCH IS MISSING `Z3` [E118] --------------------- repl/session
This match can receive `Z3`, but no branch handles that constructor.
cure(2)>   Z3()  -> y
-- I GOT STUCK WHILE PARSING THIS [E094] ------------------------- nofile
'->' cannot appear at this point in the construct.
cure(3)>   S3(k) -> S3(add3(k, y))
-- I GOT STUCK WHILE PARSING THIS [E094] ------------------------- nofile
```

Root-cause chain, all in `lib/cure/repl.ex`:

1. `incomplete?/2` (`:1562`) is the whole decision. It ORs four signals:
   `classify_input/1`, bracket balance, `parse_indicates_continuation?/1`,
   `ast_is_open_block?/1`.
2. `classify_input/1` (`:1491`) only continues on a line *ending with*
   `do -> = | then else , (`, or a lone `@opening_keywords` word (`:1511`:
   `match if case cond try fn do let mod rec type proto impl proof actor fsm`).
   `… = match x` ends in `x`. No match.
3. `parse_indicates_continuation?/1` (`:1569`) needs a parse error rooted at
   `:eof` / `:dedent` / `:newline`. But `fn add3(…) -> Nat3 = match x` is a
   *syntactically complete* function — it parses. No error, no continuation.
4. `ast_is_open_block?/1` (`:1601`) only recognises a **top-level** stub, e.g. a
   bare `match` with no arms. Here the top-level node is a function definition,
   so `open_ast?` never sees the empty match nested inside it. No match.

Result: submit. The indented arms that follow are each parsed as their own
top-level input, hence the `E094`s. `;;` cannot rescue this — by the time you
type it the buffer has already been submitted and cleared. Verified with an
explicit `;;`-terminated multi-line `fn`; it failed identically, and the
follow-up call then failed with `E091 UNKNOWN VALUE` because the definition was
never registered.

So the fix has to be a real indentation rule (a line indented deeper than the
submission's first line continues it), not more suffix cases in
`classify_input/1`. Adding proof keywords to `@opening_keywords` is necessary
but nowhere near sufficient — and note `proof chain` is two words while
`lone_opening_keyword?/1` (`:1513`) requires a single token, so `proof chain`
does not trigger continuation today even though bare `proof` does.

Compounding it: `proof chain` separates its steps with **blank lines** (see
`lib/std/proof_linear_arithmetic_semantics.cure:45-150`), and a blank line is an
unconditional submit — the documented behaviour at `docs/REPL.md:74`. Even after
the indentation fix, chains stay untypeable until blank-line submit is scoped to
indent level 0.

**`:holes` is dead code.** `state.holes` is initialised to `[]` at `:55` and
`:742` and is never assigned anywhere in the file, so `:holes` unconditionally
prints `(no holes recorded)` (`:760-766`). The data already exists —
`Cure.Elab.Program.hole_goals/1` (`lib/cure/elab/program.ex:1862`) returns
`[%{function:, goal:, context:}]`, which is exactly the `{label, goal, ctx}`
shape the renderer at `:766` destructures. Two gaps to bridge: the REPL compiles
with `emit_events: false` at all four call sites (`:663`, `:780`, `:856`,
`:1222`), and nothing threads the elaborated env back out of
`Cure.Compiler.compile_and_load/2`. Separately, a bare `??` errors with
`E014 HOLE NEEDS A TYPE ANNOTATION` because the synthesized wrapper is
`fn main() =` with no declared result type (`evaluate/2`, `:657-661`).

**REPL diagnostics quote an empty line and point the caret at nothing.** Every
error above rendered as `at nofile:3:7`, then `3 | ` with no source text, then a
bare `^`. The spans are coordinates in the synthesized `mod Repl.M<n>` wrapper,
and the REPL registers no `%SourceRegistry{}` for it — so
`Renderer.evidence_doc/3` has a span but no text to underline. This directly
undercuts §5: the caret work will land as blank output in the REPL unless the
wrapper source is registered and spans are offset back to the user's input
line/column.

Incidental observations from the same session:

- Cold `mix cure.repl` took **~6 minutes** (74-module stdlib compile + a 7.5 MB
  escript build) behind the single line `Compiling Cure standard library
  (74 modules)`, and emitted the §5 `W001` warning mid-build. Warm launch is
  ~9 s.
- Banner reads `Cure REPL v0.33.1` — will follow the `mix.exs` bump in §7, but
  confirm it reads the bumped value rather than a hardcoded string.
- `test/cure/repl/` holds eleven test files (completer, config, docs, highlight,
  history, line_editor, markdown, options, render, session, terminal) and none
  of them exercises `incomplete?/2` against real multi-line source or the
  evaluate/compile path — which is why this regressed unnoticed.
- `lib/cure/repl.ex` was last touched 2026-07-21 (`1b600962 fix(diagnostics):
  locate macro use mismatches`), i.e. the diagnostics work reached it but the
  proof-ergonomics work did not.

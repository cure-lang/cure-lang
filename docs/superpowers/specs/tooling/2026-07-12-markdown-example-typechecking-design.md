# Type-checking Cure examples in Markdown — Design

**Status:** approved design, pre-plan.
**Date:** 2026-07-12.
**Topic:** make ` ```cure ` fenced code blocks in `.md` documents verifiable by the
Cure compiler, so documentation examples cannot silently drift from the language.

---

## 1. Goal

Scan every ` ```cure ` fenced block in a Markdown file, assemble each block into a
compilable unit, and **type-check** it. A block is expected to type-check by
default; fence directives mark the exceptions (skip, or expect-rejection). The
first consumer is `docs/GLOSSARY.md`, whose 100 examples are made self-contained
as part of this work so the checker passes and stays a regression guard.

This feature **type-checks**; it does not evaluate examples or assert `# =>`
output values. Those comments remain illustrative. Evaluation-style doctests are
already handled separately (see §2).

## 2. Background — what already exists

- **`Cure.Compiler.compile_string/2`** (`lib/cure/compiler.ex:84`) compiles a
  source string end to end: `lex → parse → migrate_warn → maybe_check → optimize →
  codegen`. Relevant options: `check_types` (default `true`), `emit_events`
  (set `false` to silence), `output_dir`, `file`. This is the mechanism the new
  checker drives.
- **`Cure.Doc.Doctests`** (`lib/cure/doc/doctests.ex`) is a *separate, existing*
  facility: it harvests `cure> EXPR` / `=> EXPECTED` pairs from `##` doc-comments,
  wraps each expression in a synthetic module, **evaluates** it, and compares the
  result via `inspect/1`. It is wired into `cure test --doctests` and
  `mix cure.check.examples`. It does **not** touch ` ```cure ` fenced blocks. The
  new feature is a sibling to this, not a replacement: doctests *evaluate*
  expressions; this feature *type-checks* fenced blocks.
- There are **433 ` ```cure ` fenced blocks** in the tree — 16 `.md` files and 36
  stdlib `.cure` doc-comment files — none currently checked by anything.
- **`cure check <file>`** (`cmd_check` in `lib/cure/cli.ex`) type-checks a `.cure`
  file today. **`mix cure.check.examples`** compiles every `examples/*.cure` and
  checks output; **`mix cure.check`** aggregates the check tasks.
- Cure modules use the **offside rule**: `mod Name` opens a module and its
  indented declarations run to end-of-file; there is no `end` terminator. Top-level
  declaration keywords are `mod`, `use`, `fn`, `type`, `interface`,
  `implementation`, the concurrency containers (`fsm`, `actor`, `sup`, `app`), and
  attributes (`@extern`, `@group`, `@builtin`, `@derive`, `@record`).

## 3. Scope

**In scope**
- Extract and type-check ` ```cure ` fenced blocks from `.md` files.
- Fence-directive grammar: default (must check), `ignore` (skip), `fail` /
  `fail=<reason>` (must be rejected).
- Hybrid block assembly (declarations compiled as-is; bare expressions wrapped).
- A single-file entry (`cure check <file>.md`) and a suite entry
  (`mix cure.check.docs`).
- Making `docs/GLOSSARY.md`'s examples self-contained so it passes.

**Out of scope (future work, noted in §12)**
- Checking ` ```cure ` blocks inside `.cure` doc-comments (the 36 stdlib files).
  The extractor is written to make this a small later addition.
- Evaluating examples or asserting `# =>` output (that is the doctest facility).
- Inner-line error mapping finer than block granularity.

## 4. Directive grammar

The fence info-string is `cure` optionally followed by one directive token:

| Fence | Meaning |
|-------|---------|
| ` ```cure ` or ` ```cure check ` | **Must type-check.** The default. |
| ` ```cure ignore ` | **Not checked.** For conceptual / comment-only blocks. |
| ` ```cure fail ` | **Must be rejected** — the checker asserts the block does *not* type-check. |
| ` ```cure fail=<reason> ` | Must be rejected, and the compiler error must match `<reason>`. |

- `<reason>` is a bare identifier (e.g. `positivity`, `coverage`, `conversion`).
  It matches if it appears, case-insensitively, in the compiler's error text or
  error kind for the block (substring match, documented as such).
- `check` is an explicit synonym for the bare default.
- Any other info-string suffix after `cure` is a **hard extraction error**
  (`unknown cure fence directive: <token>`) — this guards against typos silently
  turning into unchecked blocks.
- Markdown renderers ignore the suffix, so ` ```cure ignore ` still syntax-
  highlights as Cure on GitHub and elsewhere.

## 5. Block extraction — `Cure.Doc.MdExamples`

New module `lib/cure/doc/md_examples.ex`.

```
@type block :: %{directive: :check | :ignore | :fail | {:fail, String.t()},
                 code: String.t(), line: pos_integer()}

@spec extract(path :: String.t()) :: {:ok, [block()]} | {:error, term()}
@spec extract_from_source(source :: String.t()) :: {:ok, [block()]} | {:error, term()}
```

- Splits on lines; tracks fenced-block state. A block opens on a line whose trimmed
  content is ` ```cure ` (optionally followed by a directive) and closes on the
  next line whose trimmed content is ` ``` `.
- `line` is the 1-based line number of the **opening fence** in the `.md` source,
  used for reporting.
- Non-`cure` fenced blocks (` ```elixir `, ` ``` `, etc.) are skipped entirely,
  including any ` ```cure ` text that appears inside them.
- An unterminated ` ```cure ` fence at end of file is an `{:error, …}` (malformed
  document), not a silently dropped block.
- Unknown directive → `{:error, {:unknown_directive, token, line}}`.

## 6. Assembly — hybrid (option C)

New module `lib/cure/doc/example_runner.ex` owns assembly + running. Assembly turns
a block's `code` into a compilable source string.

**Classification.** A block *has declarations* if, ignoring blank lines and `#`
comment lines, any line begins (after optional leading whitespace) with a top-level
keyword from §2 (`mod`, `use`, `fn`, `type`, `interface`, `implementation`, `fsm`,
`actor`, `sup`, `app`, or `@`).

**Three cases:**
1. **Has own `mod`.** Compile the block *verbatim*. The author is fully in control;
   no prelude is injected.
2. **Has declarations but no `mod`.** Wrap in a synthetic module: emit
   `mod <SyntheticName>`, then the configured default-prelude `use` lines and the
   block's lines, each indented two spaces (offside rule; no `end`).
3. **Expression / statement only** (no declarations). Wrap the block's lines as the
   body of a synthetic zero-argument function inside a synthetic module, injecting
   the default prelude — mirroring the technique `Cure.Doc.Doctests.run_one/2`
   already uses for `cure>` expressions. Multi-line statement blocks (e.g. a `let`
   followed by an expression) become the function's block body.

- `<SyntheticName>` is unique per block (e.g. `Doc.Example.N` via
  `:erlang.unique_integer([:positive])`) so independently-compiled blocks never
  collide in the throwaway output dir.
- **Default prelude** is configurable (§9); it is injected only in cases 2 and 3,
  never over a block that declares its own `mod`.
- A block containing only `#` comments and blank lines falls into case 3 with an
  empty synthetic body; that fails to compile. This is intended — a comment-only
  block carries no checkable code and must be marked ` ```cure ignore `. The
  failure is the nudge to do so, not a bug.

## 7. Running & result classification

```
@spec run_block(block(), opts :: keyword()) ::
        {:ok, :checked | :skipped | :expected_failure}
        | {:error, {:reason, String.t()}}
```

- Assemble the block, then call `Cure.Compiler.compile_string(assembled,
  check_types: true, emit_events: false, output_dir: <tmp>, file: <"path:line">)`.
- **Full compile path is used deliberately** (not a type-check-only shortcut):
  `fsm`/`actor`/`sup`/`app` containers are validated during codegen, so only a
  full `compile_string` actually checks those block kinds.
- Classification by directive:
  - `:ignore` → `{:ok, :skipped}` (not compiled).
  - `:check` → `{:ok, :checked}` if `compile_string` returns `{:ok, …}`; else
    `{:error, {:reason, <compiler error text>}}`.
  - `:fail` → `{:ok, :expected_failure}` if `compile_string` returns `{:error, …}`;
    else `{:error, {:reason, "expected rejection, but the block type-checked"}}`.
  - `{:fail, reason}` → like `:fail`, and additionally the error text/kind must
    contain `reason` (case-insensitive substring); on mismatch,
    `{:error, {:reason, "rejected, but not for <reason>: <actual error>"}}`.
- The throwaway `output_dir` is a temp directory removed after the run; emitted
  BEAM (if any) is discarded.

## 8. Delivery / UX

- **`cure check <file>`** — `cmd_check` inspects the argument's extension. A `.md`
  file dispatches to the doc checker; a `.cure` file keeps today's behavior. This
  overloads the verb the user already reaches for.
- **`mix cure.check.docs`** — new task `lib/mix/tasks/cure.check.docs.ex`, mirroring
  `cure.check.examples`. Checks a configured doc set (default glob `docs/**/*.md`).
  Added to the `mix cure.check` aggregator so CI runs it with the rest.
- **Output** (both entries): one line per non-skipped block
  (`docs/GLOSSARY.md:214  ✓ checked` / `✗ failed — <reason>`), then a summary
  (`N checked, M skipped, K expected-failures, F failed`).
- **Exit status:** `0` when every non-skipped block is classified as expected; `1`
  if any block fails (compile error on a `check` block, an unexpected pass on a
  `fail` block, a `fail=reason` mismatch, an unknown directive, or a malformed
  document).

## 9. Configuration

- **Default prelude** — a list of `Std` modules injected as `use` lines in
  assembly cases 2 and 3. Default set: `Std.Show`, `Std.Option`, `Std.Result`,
  `Std.List`, `Std.String`, `Std.Semigroup`, `Std.Comparable`, `Std.Map`,
  `Std.Set`. Rationale: lets terse one-liners (`show(42)`, `"ab" <> "cd"`) check
  without ceremony while remaining a small, non-conflicting set. `Std.Semigroup`
  is included so `<>`/non-numeric-`+` resolve. Overridable via a task option
  (`--prelude Mod,Mod`) and a module attribute default so it lives in one place.
- **Doc set** — `mix cure.check.docs` default glob is `docs/**/*.md`; overridable
  with positional path arguments.

## 10. Testing strategy

Unit tests (fixture strings, no filesystem):
- **Extractor:** directive parsing (each of bare/`check`/`ignore`/`fail`/
  `fail=x`); correct opening-fence line numbers; adjacent fenced blocks; a
  ` ```cure ` string sitting *inside* a non-cure fence is ignored; unknown
  directive → error; unterminated fence → error.
- **Assembly:** expression-only block wraps in a synthetic `fn`; declaration block
  without `mod` gets a synthetic `mod` + prelude at correct indentation; a block
  with its own `mod` is emitted verbatim with **no** prelude injected.
- **Runner:** a valid block → `:checked`; a type-error block → `{:error, …}`; an
  `ignore` block → `:skipped`; a `fail` block that errors → `:expected_failure`; a
  `fail` block that compiles → error; `fail=positivity` matching and mismatching.

Integration test:
- A fixture `.md` with one block of each directive runs through the full pipeline
  and yields the expected per-block classification and overall exit status.

Acceptance test:
- After the §11 doc-fixing pass, `cure check docs/GLOSSARY.md` exits `0`, and this
  is asserted by a test so the glossary stays honest.

## 11. The doc-fixing pass (`docs/GLOSSARY.md`)

Part of this work, because the feature is worthless if its first target fails.
Per-block, make each of the 100 examples honest:
- **Fragment blocks** that call undefined helpers (`int_to_string`, `map`, …) —
  either switch to a builtin/stdlib function or define the helper inside the block.
- **Expression one-liners** (`show(42)`, `combine([1,2],[3,4])`) — left terse;
  they type-check via case-3 wrapping plus the default prelude.
- **Purely conceptual / comment-only blocks** (erasure, canonicity, transport,
  `believe_me`, "at run time a Vector is just its spine", the `?goal` hole
  placeholder) — marked ` ```cure ignore `.
- **Counterexamples** — `type Bad = Mk(Bad -> Bad)` marked ` ```cure fail=positivity `;
  the non-exhaustive `match` marked ` ```cure fail=coverage `.

The `docs/check_glossary_telescope.py` guard (ordering) and this type-check guard
are independent and both run over the file.

## 12. Future work (explicitly deferred)

- Extend `Cure.Doc.MdExamples` (or a shared extractor) to harvest ` ```cure `
  blocks from `.cure` doc-comments so the 36 stdlib files are covered too.
- Optional evaluation mode that also checks `# =>` results, unifying with the
  existing `cure>`/`=>` doctest facility.
- Inner-line error mapping (report the offending line *within* a block, not just
  the block's fence line).

## 13. Acceptance criteria

1. `Cure.Doc.MdExamples.extract/1` returns correctly-classified blocks with fence
   line numbers, and errors on unknown directives and unterminated fences.
2. Assembly implements the three hybrid cases with prelude injection only in the
   synthetic-wrapper cases.
3. `run_block/2` classifies `check` / `ignore` / `fail` / `fail=reason` exactly as
   in §7, driving the full `compile_string` path.
4. `cure check <file>.md` and `mix cure.check.docs` work, print per-block +
   summary output, and exit `0`/`1` per §8.
5. `docs/GLOSSARY.md` is made self-contained and `cure check docs/GLOSSARY.md`
   exits `0`, asserted by a test.
6. All new modules have the unit + integration tests of §10, and the full suite is
   green.

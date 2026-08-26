# SP1 §2 — Default Error-Machinery Floor for Macro Uses — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4). Steps use `- [ ]`. Strict red-green TDD; commit per task. This is the LAST gate-critical SP1 piece.

**Goal:** Meet the SP1 gate clause "wrong-shape macro uses produce a (default-machinery) **diagnostic**, not a raw parser error." Today a mismatched macro use emits `{:macro_use_mismatch, …}` and a malformed hole emits `{:malformed_hole, …}`, both of which fall through `Cure.Compiler.Errors.format_error/2`'s catch-all and render RAW (a tuple inspection). Give them friendly, Elm-spirited default diagnostics routed through the central renderer.

**Architecture:** The default floor (design §2). `explain`/author-defined `Diagnosis` is SP2; this is the DEFAULT message shown when the author wrote no `explain`. Two moves: (1) **enrich** the `:macro_use_mismatch` tuple at its single emit site (`parse_macro_use/1`, `parser.ex:232`, where `rule` is in scope) to carry *what the macro expected* and *what it got*, so a message can name them; (2) add `format_error/2` clauses in `lib/cure/compiler/errors.ex` for `:macro_use_mismatch` and `:malformed_hole` that build friendly messages via the existing `format_diagnostic/5`. (`suggest/2` near-miss hints are NOT wired into either clause below — the floor's messages name what was expected/got directly, which is sufficient for the SP1 §2 gate; a `suggest`-based "did you mean" is optional future polish, not part of these two tasks.) **Forward-compatible with the parked Elm-rendering initiative** (`docs/superpowers/specs/diagnostics/2026-07-12-elm-style-error-rendering-PARKED.md`): message CONTENT lives in the `format_error` clause and routes through `format_diagnostic`, so a future snippet/caret rewrite upgrades it for free. **TCB delta zero** (parser + error rendering only).

**Tech Stack:** Elixir; `lib/cure/compiler/parser.ex`, `lib/cure/compiler/errors.ex`; ExUnit.

## Global Constraints

- **TCB delta ZERO.** Only `lib/cure/compiler/parser.ex`, `lib/cure/compiler/errors.ex` (+ tests). No `lib/cure/core/*`.
- **Ghost commits** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. `git add -- <path>`, never `-A`.
- **One build at a time.** Scoped `mix test test/cure/compiler/macro_error_floor_test.exs`; `mix test test/cure/compiler/` for regression.
- **Run mix from the worktree root** (`.claude/worktrees/core-let-binder`), NEVER the parent clone.
- **Forward-compat contract (parked spec §"Forward-compatibility"):** route through `format_error`/`format_diagnostic`; do NOT hand-format macro error strings at the parser call site; keep `line, col` in the tuple.

## Verified grounding (probed live)

- Raw macro tuples with NO `format_error` clause (fall to catch-all `errors.ex:374`, render raw): `{:macro_use_mismatch, keyword, :at_segment, progress, line, col}` (emitted ONLY at `parser.ex:232` in `parse_macro_use/1`); `{:malformed_hole, line, col}` (`parser.ex:4358`). — `{:expected, :syntax_rule/:becomes, :got, …}` ALREADY renders via the generic `errors.ex:86` clause, so it is not raw (out of scope; optional polish).
- `parse_macro_use/1` (`parser.ex:218`): `rule` (with `rule.segments`) is in scope at the `{:error, progress, state}` arm; `progress` = count of segments matched before the miss, so the failed segment is `Enum.at(rule.segments, progress)`.
- `errors.ex`: `format_error/2` dispatch (many clauses) + catch-all `format_error(error, file)` at `:374`; renderer `format_diagnostic(severity, category, file, line, message)` at `:1730` → `severity: category\n --> file:line\n  | message`; `suggest(name, candidates)` at `:1678` + `levenshtein/2` at `:1759` exist for "did you mean" but are NOT used by either Task below (out of scope for this floor).
- Existing test coupling: `test/cure/compiler/macro_use_test.exs` asserts `match?({:macro_use_mismatch, "say", :at_segment, 0, _, _}, &1)` — this SHAPE assertion must update when the tuple is enriched (Task 1 Step 5). The behavioral intent (a mismatch is recorded) is preserved and strengthened.

---

### Task 1: Enrich `:macro_use_mismatch` + render a friendly default diagnostic

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_macro_use/1` error arm `:232`; add `macro_expected_at/2`, `macro_got_desc/1`)
- Modify: `lib/cure/compiler/errors.ex` (add a `format_error` clause for `:macro_use_mismatch`, before the catch-all `:374`)
- Modify: `test/cure/compiler/macro_use_test.exs` (update the shape assertion to the enriched tuple)
- Test: `test/cure/compiler/macro_error_floor_test.exs` (create)

**Interfaces:**
- New tuple shape: `{:macro_use_mismatch, keyword :: String.t(), expected, got :: String.t(), line, col}` where `expected` is `{:literal, String.t()} | {:hole_kind, String.t()} | :nothing_more`.
- `Errors.format_error({:macro_use_mismatch, …}, file)` → a multi-line diagnostic STRING.

- [ ] **Step 1: Write the failing test** (renderer-level — the floor is about the message)

```elixir
# test/cure/compiler/macro_error_floor_test.exs
defmodule Cure.Compiler.MacroErrorFloorTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Errors}

  # Parse a source expected to fail, return its error list.
  defp errors_of(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:error, errors} = Parser.parse(tokens, emit_events: false)
    errors
  end

  test "a macro-use literal mismatch renders a friendly diagnostic naming the macro + what it expected" do
    # `say hello` is the rule; `say goodbye` mismatches on the literal segment.
    errors =
      errors_of(
        "mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say goodbye\n"
      )

    mismatch = Enum.find(errors, &match?({:macro_use_mismatch, "say", _, _, _, _}, &1))
    assert mismatch, "expected a :macro_use_mismatch error"

    rendered = Errors.format_error(mismatch, "f.cure")
    # A DIAGNOSTIC, not a raw tuple: names the macro, what it expected, what it got.
    assert rendered =~ "say"
    assert rendered =~ "hello"
    assert rendered =~ "goodbye"
    refute rendered =~ ":macro_use_mismatch"   # not the raw tuple
    refute rendered =~ ":at_segment"
  end
end
```

- [ ] **Step 2: Run it — expect FAIL** (the current tuple is `{:macro_use_mismatch, "say", :at_segment, 0, _, _}`, so the `match?` finds it but the render — via the catch-all — inspects the raw tuple, so `rendered =~ ":macro_use_mismatch"` is TRUE and the `refute` fails; also `=~ "hello"` fails since the raw tuple has no "hello").

Run: `mix test test/cure/compiler/macro_error_floor_test.exs` → FAIL.

- [ ] **Step 3: Enrich the emit site** (`parser.ex` `parse_macro_use/1` error arm)

Replace the `add_error` call:

```elixir
        state =
          add_error(
            state,
            {:macro_use_mismatch, keyword, macro_expected_at(rule, progress),
             macro_got_desc(t), t.line, t.col}
          )
```

Add helpers near `parse_macro_use/1`:

```elixir
  # Describe the segment a macro rule expected at the failed position, for the
  # default mismatch diagnostic (SP1 §2 floor). A literal segment names the exact
  # word; a hole names its declared kind; past the end means the use supplied
  # tokens the rule did not call for.
  defp macro_expected_at(rule, progress) do
    case Enum.at(rule.segments, progress) do
      {:lit, w} -> {:literal, w}
      {:hole, %{kind: k}} -> {:hole_kind, k}
      _ -> :nothing_more
    end
  end

  # NOTE (reviewed): under today's `match_segments/4`, a `{:hole, _}` segment
  # NEVER fails to match (it unconditionally parses an expr and binds it), so
  # the only way `parse_macro_use`'s single call site reaches this function is
  # via a `{:lit, w}` mismatch — `Enum.at(rule.segments, progress)` will always
  # be a `{:lit, w}` in practice today. The `{:hole_kind, k}` and `:nothing_more`
  # arms are deliberately-defensive/forward-looking (for when `match_segments`
  # gains hole-content validation, or T9's multi-rule maximal-progress
  # selection makes a hole-position failure possible) and are NOT reachable by
  # any input today. Step 1's red test exercises ONLY the `{:literal, w}` arm —
  # do not expect (or demand) a red test for the other two arms; there is no
  # input that reaches them yet.

  # A short human description of the token actually found at the mismatch.
  defp macro_got_desc(%Token{type: :eof}), do: "end of input"
  defp macro_got_desc(%Token{value: v}) when not is_nil(v), do: to_string(v)
  defp macro_got_desc(%Token{type: t}), do: to_string(t)
```

- [ ] **Step 4: Add the render clause** (`errors.ex`, before the catch-all `:374`)

```elixir
  def format_error({:macro_use_mismatch, keyword, expected, got, line, col}, file) do
    detail =
      case expected do
        {:literal, w} -> "the `#{keyword}` macro expected `#{w}` here, but found `#{got}`"
        {:hole_kind, k} -> "the `#{keyword}` macro expected #{article(k)} #{k} here, but found `#{got}`"
        :nothing_more -> "the `#{keyword}` macro has no more to match here, but found `#{got}`"
      end

    format_diagnostic(
      "error",
      "macro syntax",
      file,
      line,
      "#{detail} (at column #{col})"
    )
  end
```

Add a tiny `article/1` helper next to it (grammatical "a"/"an" for the hole-kind message):

```elixir
  defp article(<<c, _::binary>>) when c in ~c"AEIOUaeiou", do: "an"
  defp article(_), do: "a"
```

- [ ] **Step 5: Update the milestone-2 shape assertion** (`macro_use_test.exs`)

The T6b test asserted the OLD tuple shape. Update it to the enriched shape (intent preserved — a mismatch is still recorded — and the assertion is now stronger):

```elixir
    assert Enum.any?(errors, &match?({:macro_use_mismatch, "say", {:literal, "hello"}, "goodbye", _, _}, &1))
```

(This is a legitimate shape evolution, not weakening a passing test: the behavioral claim "a literal mismatch records a macro_use_mismatch error" is unchanged; the tuple's payload got richer.)

- [ ] **Step 6: Run both test files — expect PASS**

Run: `mix test test/cure/compiler/macro_error_floor_test.exs test/cure/compiler/macro_use_test.exs` → PASS.

- [ ] **Step 7: Full parser suite — no regression**

Run: `mix test test/cure/compiler/` → all pass.

- [ ] **Step 8: Commit**

```bash
git add -- lib/cure/compiler/parser.ex lib/cure/compiler/errors.ex test/cure/compiler/macro_error_floor_test.exs test/cure/compiler/macro_use_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(errors): default diagnostic for macro-use mismatch (SP1 §2 floor)"
```

---

### Task 2: Friendly diagnostic for a malformed hole in a macro definition

**Files:**
- Modify: `lib/cure/compiler/errors.ex` (add a `format_error` clause for `:malformed_hole`, before the catch-all)
- Test: `test/cure/compiler/macro_error_floor_test.exs` (extend)

**Interfaces:**
- `Errors.format_error({:malformed_hole, line, col}, file)` → a diagnostic string explaining the `<name: Kind>` hole syntax.

- [ ] **Step 1: Write the failing test**

```elixir
  test "a malformed hole in a macro definition renders a diagnostic explaining the hole syntax" do
    # Missing the closing `>` — the milestone-1 :malformed_hole path.
    errors =
      errors_of("macro Bad\n  syntax every <t: Duration becomes x\n")

    mh = Enum.find(errors, &match?({:malformed_hole, _, _}, &1))
    assert mh, "expected a :malformed_hole error"

    rendered = Errors.format_error(mh, "bad.cure")
    assert rendered =~ "hole"
    assert rendered =~ "<name: Kind>"          # tells the author the correct form
    refute rendered =~ ":malformed_hole"       # not the raw tuple
  end
```

- [ ] **Step 2: Run it — expect FAIL** (`:malformed_hole` has no clause → catch-all renders the raw tuple, so `=~ ":malformed_hole"` is true and the `refute` fails).

Run: `mix test test/cure/compiler/macro_error_floor_test.exs` → the new test FAILs.

- [ ] **Step 3: Add the render clause** (`errors.ex`, before the catch-all)

```elixir
  def format_error({:malformed_hole, line, col}, file) do
    format_diagnostic(
      "error",
      "macro syntax",
      file,
      line,
      "malformed hole at column #{col} — a macro hole is written `<name: Kind>` " <>
        "(e.g. `<period: Duration>`); check for a missing `:` or closing `>`"
    )
  end
```

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_error_floor_test.exs` → PASS (both floor tests).

- [ ] **Step 5: Full parser suite — no regression**

Run: `mix test test/cure/compiler/` → all pass.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/errors.ex test/cure/compiler/macro_error_floor_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(errors): default diagnostic for malformed macro hole (SP1 §2 floor)"
```

---

## Task boundary — SP1 GATE MET

With Task 1 + 2, a wrong-shape macro use and a malformed hole both render friendly
default diagnostics through the central renderer (not raw tuples) — the last SP1 gate
clause. **The SP1 gate is now met:** Tier-1 (T4) ✓ + Tier-2 (`syntax`) ✓ + expansions
kernel-check (T8) ✓ + default-machinery diagnostics ✓. Next: SP1 **Stage 6** — one full
`mix test` — then SP1 is COMPLETE and **SP2** (Tier-3 + type-enforced `Diagnosis` +
required examples) begins.

**Deferred SP1 "Includes" (NOT in the gate's pass criteria; post-gate or folded later):**
T9 (import scoping §7 + two-pass name resolution §6 — cross-module macros, the hard
parser/import-resolution lift), T7b (automatic full hygiene + the fresh∩hole and
backtick-spoof gaps + `<capture>`). The **parked** Elm-style error rendering
(`…-elm-style-error-rendering-PARKED.md`) upgrades these diagnostics' chrome later,
for free, since they route through `format_diagnostic`.

# SP2 slice 1 — Mechanism 1: Exhaustive `explain` over the structural `Diagnosis` — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4). Steps use `- [ ]`. Strict red-green TDD; commit per task. First slice of SP2 (the self-proving headline); SP1 is COMPLETE.

**Goal:** Deliver the operator's headline — *the type system requires a macro author to describe every way a use can fail* — for the **structural** failure points (each typed hole, each literal/keyword token in a rule). A macro whose `explain` block does not cover every derived failure point is a compile error `missing_diagnosis`. This slice builds (a) parsing of `explain` blocks and (b) a standalone exhaustiveness-check function. Author-declared `fail C(args)` (§3.4), Tier-3 `computed by`, and wiring the check into the compile pipeline are LATER SP2 slices.

**Architecture:** Self-proving design §3.1–§3.2. The `Diagnosis` is *derived* from a macro's closed grammar — one structural failure point per typed hole (`{:hole_kind, Category}`) and per literal segment (`{:keyword, word}`) across all `syntax`/`literal` rules. An `explain` block lists clauses `<point> => <message>`; exhaustiveness = every derived point is covered by some clause. Parsing attaches the `explain` clauses to the existing `{:macro_def, meta, rules}` node as a `%{kind: :explain, …}` entry in the rules list (locked AST shape preserved; harvest ignores non-`:syntax`/`:literal` entries). The check is a new frontend module `Cure.Compiler.MacroValidate` — **TCB delta zero** (frontend validation only; no `lib/cure/core/*`). This slice does NOT wire the check into `Program.elaborate`/`compile_string` (that would break SP1's explain-less test macros); wiring + pinning SP1 macros is a subsequent slice.

**Tech Stack:** Elixir; `lib/cure/compiler/parser.ex`, `lib/cure/compiler/macro_validate.ex` (new), `lib/cure/compiler/errors.ex`; ExUnit.

## Global Constraints

- **TCB delta ZERO.** `lib/cure/compiler/*` only (+ tests). No `lib/cure/core/*`, no `lib/cure/elab/*`.
- **Ghost commits** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. `git add -- <path>`, never `-A`.
- **One build at a time.** Scoped `mix test test/cure/compiler/macro_explain_test.exs`; `mix test test/cure/compiler/` for regression.
- **Run mix from the worktree root** (`.claude/worktrees/core-let-binder`), NEVER the parent clone.
- **Locked AST:** keep `{:macro_def, meta, rules}` — `explain` is a `rules`-list entry, not a new node arity.
- **Tests immutable once green.** Once a step's red test passes, make later changes go green by editing implementation code only — never by deleting, skipping, loosening, or rewriting a passing test. The sole exception is a test that is itself provably wrong (wrong expected shape, typo, etc.); if you believe a test is wrong, state exactly why before touching it. (Matches the convention in every sibling SP1 plan in this series.)

## Verified grounding (probed live)

- Tokenization: `explain` → `:identifier "explain"` (a soft keyword like `syntax`/`literal`); `Duration =>` → `:identifier "Duration"`, `:fat_arrow`; `keyword "every"` → `:identifier "keyword"`, `:string "every"`; `=>` → `:fat_arrow`.
- `parse_macro_rules/2` (`parser.ex:4184`) is the macro-body loop: dispatches `%Token{type: :identifier, value: "syntax"}` → `parse_macro_rule/1` and `value: "literal"` → `parse_literal_rule/1`, else `{:expected, :syntax_rule, …}`. Add an `"explain"` clause.
- A `syntax` rule map is `%{kind: :syntax, keyword: kw, segments: [{:lit,w}|{:hole,%{name,kind,line}}], template, …}`; a `literal` rule is `%{kind: :literal, keyword: nil, segments: [{:hole,_}, {:lit, suffix}], suffix: s, …}`. `harvest_active_macros/1`/`harvest_literal_macros/1` filter by `kind: :syntax`/`:literal` — an `%{kind: :explain, …}` entry is ignored by both (no use-site dispatch), exactly right.
- **A `syntax` rule's own dispatch keyword lives OUTSIDE `segments`, in the separate `keyword` field — `segments` is only what follows it.** Probed live (`Cure.Compiler.Parser.parse/2` on `"macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n"`): the parsed rule is `%{kind: :syntax, keyword: "every", segments: [hole: %{line: 2, name: "t", kind: "Duration"}], ...}` — **zero `{:lit, _}` entries in `segments`** even though `every` is a literal token the use-site must match. Probed a second rule with a trailing literal word (`syntax every <t: Duration> minutes becomes …`) to confirm `segments` DOES carry literal words that come *after* the leading keyword: `segments: [hole: %{...}, lit: "minutes"]`. So a naive `derive_points` that only walks `rule.segments` silently drops the rule's own dispatch keyword as a failure point — see Task 2 Step 3 below, which special-cases it.
- `errors.ex` `format_error/2` dispatch + `format_diagnostic/5` renderer (SP1 §2 floor established the pattern); place a `:missing_diagnosis` clause before the catch-all (`errors.ex:398`) and `describe_point/1` after it, matching the existing `article/1` helper's placement/comment at the same spot — confirmed by reading the file.

## Failure-point derivation (the structural `Diagnosis`)

From a macro's `:syntax`/`:literal` rules, the set of structural points (deduped) is:
- for each `{:hole, %{kind: k}}` segment → `{:hole_kind, k}` ("this position expected a `k`");
- for each `{:lit, w}` segment → `{:keyword, w}` ("expected `w` here");
- **for a `:syntax` rule, its own dispatch keyword `rule.keyword` → `{:keyword, kw}` too** — it is not a `segments` entry (see the probed rule shape in "Verified grounding" above), so it must be derived separately or it silently escapes the exhaustiveness check entirely. This is the common case: a bare `syntax every <t: Duration> becomes …` rule has ONE literal token (`every`) and it lives only in `rule.keyword`.

An `explain` clause covers a point iff: a `Category =>` clause (point form `{:category, c}`) covers every `{:hole_kind, c}`; a `keyword "w" =>` clause (point form `{:keyword, w}`) covers `{:keyword, w}`. Exhaustive ⇔ every derived point is covered. Uncovered → `{:missing_diagnosis, [point, …]}`.

---

### Task 1: Parse an `explain` block and attach it to the macro_def

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_macro_rules/2` `:4184`; add `parse_explain_block/1`, `parse_explain_clauses/2`, `parse_explain_point/1`)
- Test: `test/cure/compiler/macro_explain_test.exs` (create)

**Interfaces:**
- Produces a rules-list entry `%{kind: :explain, clauses: [%{point: point, body: ast, line: n}], line: n}` where `point` is `{:category, String.t()}` or `{:keyword, String.t()}`. Consumed by Task 2.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/macro_explain_test.exs
defmodule Cure.Compiler.MacroExplainTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp explain_entry({:macro_def, _, rules}), do: Enum.find(rules, &(&1[:kind] == :explain))
  defp explain_entry({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &explain_entry/1)
  defp explain_entry(_), do: nil

  test "an explain block parses its clauses (category + keyword points) onto the macro_def" do
    node =
      parse!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n  explain\n    Duration =>\n      \"needs a duration\"\n    keyword \"every\" =>\n      \"a repeat rule starts with every\"\n"
      )

    ex = explain_entry(node)
    assert ex, "expected an :explain entry in the macro_def rules"
    points = Enum.map(ex.clauses, & &1.point)
    assert {:category, "Duration"} in points
    assert {:keyword, "every"} in points
  end

  test "a malformed explain point (stray '=>' with no preceding point) is a recorded parse error, not a crash" do
    {:ok, tokens} =
      Lexer.tokenize(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n  explain\n    => \"oops\"\n",
        emit_events: false
      )

    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    assert Enum.any?(errors, &match?({:expected, :explain_point, :got, _, _, _}, &1))
  end
end
```

- [ ] **Step 2: Run it — expect FAIL** (`parse_macro_rules` records `{:expected, :syntax_rule, …}` on the `explain` line → `Parser.parse` returns `{:error, …}`, `{:ok, ast} =` raises for the first test. Probed live: WITHOUT the `parse_explain_point/1` fallback added in Step 3 below, the second test doesn't merely fail an assertion — it CRASHES the whole run with an uncaught `** (CaseClauseError) no case clause matching: %Cure.Compiler.Token{type: :fat_arrow, ...}` raised from `parse_explain_point/1`, propagating up through `parse_explain_clauses/2` → `parse_explain_block/1` → `parse_macro_rules/2` → `Parser.parse/2`. Both are expected-red for this step; Step 3's fallback clause is what turns the crash into a clean `{:error, [...]}`.).

Run: `mix test test/cure/compiler/macro_explain_test.exs` → FAIL (first test fails an assertion; second test's own process crashes with `CaseClauseError` until Step 3 lands the fallback).

- [ ] **Step 3: Add the `explain` dispatch + parsers**

In `parse_macro_rules/2` (`:4184`), add before the `other ->` fallback:

```elixir
      %Token{type: :identifier, value: "explain"} ->
        {entry, state} = parse_explain_block(state)
        parse_macro_rules(state, [entry | acc])
```

Add near `parse_literal_rule/1` (uses `expect/2`, `expect_dedent/1`, `skip_macro_trivia/1`, `parse_expr/2`, all verified in SP1):

```elixir
  # `explain` <INDENT> (<point> => <message>)+ <DEDENT> — the author's failure
  # descriptions (self-proving §3.2). Attached to the macro_def as one entry;
  # exhaustiveness over the derived Diagnosis is checked separately (MacroValidate).
  defp parse_explain_block(state) do
    kw = peek(state)
    state = advance(state)
    state = skip_macro_trivia(state)

    {clauses, state} =
      case peek(state) do
        %Token{type: :indent} ->
          state = advance(state)
          {cs, state} = parse_explain_clauses(state, [])
          state = expect_dedent(state)
          {cs, state}

        _ ->
          {[], state}
      end

    {%{kind: :explain, clauses: clauses, line: kw.line}, state}
  end

  defp parse_explain_clauses(state, acc) do
    state = skip_macro_trivia(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      _ ->
        {point, state} = parse_explain_point(state)
        state = expect(state, :fat_arrow)
        state = skip_macro_trivia(state)
        {body, state} = parse_expr(state, 0)
        clause = %{point: point, body: body, line: peek(state).line}
        parse_explain_clauses(state, [clause | acc])
    end
  end

  # A point is `keyword "w"` (a literal-token failure) or a bare `Category`
  # identifier (a typed-hole failure). Backticked/qualified categories are out
  # of scope for this slice.
  #
  # A total fallback is REQUIRED here, not optional polish: probed live, a
  # malformed point (e.g. `explain\n    => "oops"`, a stray `=>` with no
  # preceding point) reaches this function with `peek(state)` a `:fat_arrow`
  # token, and the two-clause `case` above (without this fallback) raises
  # `** (CaseClauseError) no case clause matching: %Cure.Compiler.Token{type: :fat_arrow, ...}`
  # UNCAUGHT all the way up through `Parser.parse/2` — crashing the whole parse
  # instead of recording a recoverable diagnostic the way every other malformed
  # construct in this parser does (e.g. `parse_macro_rules/2`'s `other ->`
  # clause, which calls `add_error` and skips a token). Record the error and
  # recover by treating the point as unnamed and NOT advancing past the
  # offending token (so `expect(state, :fat_arrow)` in the caller either
  # matches it directly or reports its own clean `:expected` error next).
  defp parse_explain_point(state) do
    case peek(state) do
      %Token{type: :identifier, value: "keyword"} ->
        state = advance(state)
        w = peek(state)
        state = advance(state)
        {{:keyword, to_string(w.value)}, state}

      %Token{type: :identifier, value: cat} ->
        {{:category, cat}, advance(state)}

      other ->
        error = {:expected, :explain_point, :got, other.type, other.line, other.col}
        state = add_error(state, error)
        {{:category, "?"}, state}
    end
  end
```

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_explain_test.exs` → PASS.

- [ ] **Step 5: Full parser suite — no regression** (existing macros without `explain` are unaffected; the harvesters ignore `kind: :explain` entries — confirm milestone-1/2 + literal + hygiene macro tests pass).

Run: `mix test test/cure/compiler/` → all pass.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_explain_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): parse macro explain blocks (SP2 M1)"
```

---

### Task 2: Exhaustiveness check — `missing_diagnosis` for uncovered failure points

**Files:**
- Create: `lib/cure/compiler/macro_validate.ex`
- Modify: `lib/cure/compiler/errors.ex` (add `format_error` clause for `:missing_diagnosis`)
- Test: `test/cure/compiler/macro_explain_test.exs` (extend)

**Interfaces:**
- `Cure.Compiler.MacroValidate.check_explain_exhaustive(macro_def :: tuple()) :: :ok | {:error, {:missing_diagnosis, [point]}}` — `point` is `{:hole_kind, String.t()}` or `{:keyword, String.t()}`.
- `Errors.format_error({:missing_diagnosis, points}, file)` → a diagnostic string.

- [ ] **Step 1: Write the failing test**

```elixir
  alias Cure.Compiler.{MacroValidate, Errors}

  defp macro_def!(src) do
    node = parse!(src)
    find = fn find, n ->
      case n do
        {:macro_def, _, _} = m -> m
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end
    find.(find, node)
  end

  test "a macro whose explain omits a hole's category is missing_diagnosis" do
    # `every` has a <t: Duration> hole and a `every` keyword; explain covers only
    # the keyword → the Duration hole point is uncovered.
    md =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n  explain\n    keyword \"every\" =>\n      \"starts with every\"\n"
      )

    assert {:error, {:missing_diagnosis, points}} = MacroValidate.check_explain_exhaustive(md)
    assert {:hole_kind, "Duration"} in points

    rendered = Errors.format_error({:missing_diagnosis, points}, "m.cure")
    assert rendered =~ "Duration"
    refute rendered =~ ":missing_diagnosis"
  end

  test "a macro whose explain covers every structural point checks clean" do
    md =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n  explain\n    Duration =>\n      \"needs a duration\"\n    keyword \"every\" =>\n      \"starts with every\"\n"
      )

    assert :ok = MacroValidate.check_explain_exhaustive(md)
  end

  test "a macro with NO explain block reports every structural point as missing" do
    md = macro_def!("macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n")
    assert {:error, {:missing_diagnosis, points}} = MacroValidate.check_explain_exhaustive(md)
    assert {:hole_kind, "Duration"} in points
    assert {:keyword, "every"} in points
  end
```

- [ ] **Step 2: Run it — expect FAIL** (`Cure.Compiler.MacroValidate` does not exist → `UndefinedFunctionError`).

Run: `mix test test/cure/compiler/macro_explain_test.exs` → the three new tests FAIL.

- [ ] **Step 3: Create `MacroValidate`**

```elixir
# lib/cure/compiler/macro_validate.ex
defmodule Cure.Compiler.MacroValidate do
  @moduledoc """
  Frontend validation of `macro` definitions against the self-proving
  obligations (design 2026-07-11 §3). TCB delta zero — pure analysis over the
  parsed `{:macro_def, …}` AST, upstream of the elaborator.
  """

  @type point :: {:hole_kind, String.t()} | {:keyword, String.t()}

  @doc """
  Check a macro's `explain` block covers every structural failure point derived
  from its `syntax`/`literal` rules (design §3.2). Returns `:ok` or
  `{:error, {:missing_diagnosis, uncovered_points}}`.
  """
  @spec check_explain_exhaustive(tuple()) :: :ok | {:error, {:missing_diagnosis, [point]}}
  def check_explain_exhaustive({:macro_def, _meta, rules}) do
    points = derive_points(rules)
    covered = covered_points(rules)

    case Enum.reject(points, &covered?(&1, covered)) do
      [] -> :ok
      uncovered -> {:error, {:missing_diagnosis, uncovered}}
    end
  end

  # Structural Diagnosis: one point per typed hole, per literal segment, AND
  # (for `:syntax` rules) the rule's own dispatch keyword — across all
  # syntax/literal rules, deduped and order-stable.
  #
  # NOTE: a `:syntax` rule's dispatch keyword lives in `rule.keyword`, NOT in
  # `rule.segments` (`segments` is only what follows it — verified live, see
  # "Verified grounding"). Omitting this would mean the single most common
  # macro-use failure (typing the wrong keyword) could never be required to
  # have an `explain` clause, defeating the exhaustiveness guarantee for the
  # plan's own headline example (`syntax every <t: Duration> becomes …` has
  # NO literal `segments` entries at all).
  defp derive_points(rules) do
    rules
    |> Enum.filter(&(&1[:kind] in [:syntax, :literal]))
    |> Enum.flat_map(fn rule ->
      keyword_points =
        case rule do
          %{kind: :syntax, keyword: kw} when is_binary(kw) -> [{:keyword, kw}]
          _ -> []
        end

      keyword_points ++ Enum.map(rule.segments, &segment_point/1)
    end)
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq()
  end

  defp segment_point({:hole, %{kind: k}}), do: {:hole_kind, k}
  defp segment_point({:lit, w}), do: {:keyword, w}
  defp segment_point(_), do: nil

  # What the explain block covers, as a set of clause points.
  defp covered_points(rules) do
    rules
    |> Enum.filter(&(&1[:kind] == :explain))
    |> Enum.flat_map(& &1.clauses)
    |> Enum.map(& &1.point)
    |> MapSet.new()
  end

  # A `{:category, c}` clause covers a `{:hole_kind, c}` point; a `{:keyword, w}`
  # clause covers a `{:keyword, w}` point.
  defp covered?({:hole_kind, k}, covered), do: MapSet.member?(covered, {:category, k})
  defp covered?({:keyword, w}, covered), do: MapSet.member?(covered, {:keyword, w})
end
```

- [ ] **Step 4: Add the `:missing_diagnosis` render clause** (`errors.ex`, before the catch-all)

```elixir
  def format_error({:missing_diagnosis, points}, file) do
    listed = points |> Enum.map(&describe_point/1) |> Enum.join(", ")

    format_diagnostic(
      "error",
      "macro is missing a failure description",
      file,
      0,
      "this macro can fail in ways it does not describe: #{listed}. Add an `explain` " <>
        "clause for each (a `Category =>` covers a typed hole, `keyword \"w\" =>` a literal)."
    )
  end
```

Add `describe_point/1` after the catch-all (keep `format_error/2` clauses contiguous — an SP1 §2 lesson):

```elixir
  defp describe_point({:hole_kind, k}), do: "a `#{k}` hole"
  defp describe_point({:keyword, w}), do: "the keyword `#{w}`"
```

- [ ] **Step 5: Run the tests — expect PASS**

Run: `mix test test/cure/compiler/macro_explain_test.exs` → PASS (all: parse + the three check tests).

- [ ] **Step 6: Full suite + warnings**

Run: `mix test test/cure/compiler/` → all pass. Then `mix compile --warnings-as-errors --force` → clean (confirm `format_error/2` clauses stay grouped; `describe_point/1` placed after the catch-all).

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/compiler/macro_validate.ex lib/cure/compiler/errors.ex test/cure/compiler/macro_explain_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(macros): exhaustive-explain check emits missing_diagnosis (SP2 M1)"
```

---

## Slice boundary — what SP2 still needs

This slice delivers Mechanism 1's **structural** core as a testable unit: parse `explain`,
derive the structural `Diagnosis`, and enforce exhaustiveness via `missing_diagnosis` — the
operator's headline for grammar failures. Not yet:

- **Wire the check into the compile pipeline** (so a real macro-using program is rejected when
  a macro's `explain` is non-exhaustive) — deferred because SP1's own test macros have no
  `explain` and would break; that slice adds the wiring AND pins SP1 macros with `explain`
  blocks (or scopes enforcement to macros that opt in / declare an `explain`).
- **§3.4 author `fail C(args)`** — extends `Diagnosis` with author points; the exhaustiveness
  check then covers them too (same `missing_diagnosis`).
- **§3.3 interception** — route a live use-site parse failure through the macro's `explain`
  instead of the default diagnostic (needs the check wired + the `here`/`got` binding).
- **Tier-3 `computed by`** elaborators + `check … else fail`.
- **Mechanism 3** — required per-rule `example … expands …` (`rule_unpinned`).

Each is a subsequent SP2 slice (own plan). When all SP2 mechanisms are executed + reviewed, run
SP2's Stage 6 (full `mix test`) → SP2 complete → SP3 (generative expansion proof).

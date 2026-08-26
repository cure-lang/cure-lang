# SP2 slice 2a — Mechanism 3: Required per-rule examples (`rule_unpinned`) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4). Steps use `- [ ]`. Strict red-green TDD; commit per task. Second SP2 slice; SP1 + SP2 slice 1 (M1) COMPLETE.

**Goal:** Deliver the *presence* half of the self-proving Mechanism 3 (design §5): every `syntax` rule must carry at least one worked `example … expands …`. A `syntax` rule with no example is a compile error `rule_unpinned`. This slice (a) parses `example`/`expands` sub-blocks onto `syntax` rules and (b) adds a standalone `check_rules_pinned/1`. The *expansion-equality* half — parse the example through the rule, expand, compare to `expands` up to α-renaming, and type-check (`example_mismatch`) — is **slice 2b** (its own plan; it reuses the tokens this slice captures).

**Architecture:** Self-proving design §5.1–§5.2. An `example` line is *indented under* a `syntax` rule: `example <filled-use-site> expands <expected-expansion>` (or `expands : <Type>` for a type-only pin, §5.2). Parsing captures the filled use-site as **raw tokens** (it names the macro's own keyword — it cannot be expanded at macro-def parse time) and the expected expansion as an AST, attaching `examples: [...]` to the rule map. The check is `Cure.Compiler.MacroValidate.check_rules_pinned/1` (extends the SP2-slice-1 module) — **TCB delta zero** (frontend analysis; not wired into the compile pipeline this slice). Consistent with M1: standalone + tested; the SP1-macro-breaking wiring is deferred to one later slice.

**Tech Stack:** Elixir; `lib/cure/compiler/parser.ex`, `lib/cure/compiler/macro_validate.ex`, `lib/cure/compiler/errors.ex`; ExUnit.

## Global Constraints

- **TCB delta ZERO.** `lib/cure/compiler/*` only (+ tests). No `lib/cure/core/*`, no `lib/cure/elab/*`.
- **Ghost commits** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. `git add -- <path>`, never `-A`.
- **One build at a time.** Scoped `mix test test/cure/compiler/macro_example_test.exs`; `mix test test/cure/compiler/` for regression.
- **Run mix from the worktree root** (`.claude/worktrees/core-let-binder`), NEVER the parent clone.
- **Locked AST:** `{:macro_def, meta, rules}` unchanged; `examples` is a new key on the `:syntax` rule map.
- **Tests immutable once green.** Go green by fixing implementation only; touch a passing test only if it is provably wrong (state why first).

## Verified grounding (probed live)

- Tokenization: `example` → `:identifier "example"`; `expands` → `:identifier "expands"`; `expands : Effect(Unit)` → `:identifier`, `:colon`, `:identifier`, `:lparen`, … ; the filled use-site `every 500ms` is ordinary tokens (`:identifier`, `:integer`, `:identifier`).
- `parse_macro_rule/1` builds the `:syntax` rule map right after `{template, state} = parse_expr(state, 0)` — the attach point for an indented `example` sub-block. The example line is indented DEEPER than the `syntax` keyword (design §5.1 shows `syntax` at 2 spaces, `example` at 4), so after the template's newline the next token is an `:indent` when an example follows, or the next rule / a `:dedent` when not.
- Helpers verified in SP1: `peek/1`, `peek_at/2`, `advance/1`, `expect/2`, `expect_dedent/1`, `skip_macro_trivia/1` (skips `:newline`/`:doc_comment`/`:line_comment`), `parse_expr/2`, `add_error/2`. `%Cure.Compiler.Token{}` fields: `type`, `value`, `line`, `col`.
- `MacroValidate` (SP2 slice 1) already has `check_explain_exhaustive/1`; add `check_rules_pinned/1` alongside. `errors.ex` renders via `format_error/2` → `format_diagnostic/5`; place the `:rule_unpinned` clause before the catch-all (the `# -- Catch-all --` marker + `def format_error(error, file) do` fallback, currently ~line 409-411 — mirror the existing `:missing_diagnosis` clause immediately above it), any private helper AFTER it (clause-grouping lesson from SP1 §2).
- **Scope:** `rule_unpinned` applies to `:syntax` rules only (design §5.1 "every syntax rule"). Tier-1 `:literal` rules are exempt this slice (their example semantics are not specified) — note it, do not silently enforce.

---

### Task 1: Parse `example … expands …` sub-blocks onto a `syntax` rule

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_macro_rule/1`; add `parse_rule_examples/1`, `parse_example_lines/2`, `parse_one_example/1`)
- Test: `test/cure/compiler/macro_example_test.exs` (create)

**Interfaces:**
- Adds `examples: [example]` to the `:syntax` rule map (empty list when none). Each `example` is `%{use_site: [%Token{}], expected: expected, line: n}` where `expected` is `{:expansion, ast}` or `{:type, ast}`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/macro_example_test.exs
defmodule Cure.Compiler.MacroExampleTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp syntax_rule({:macro_def, _, rules}), do: Enum.find(rules, &(&1[:kind] == :syntax))
  defp syntax_rule({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &syntax_rule/1)
  defp syntax_rule(_), do: nil

  test "an example expands sub-block attaches to its syntax rule" do
    node =
      parse!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(500)\n"
      )

    rule = syntax_rule(node)
    assert [ex] = rule.examples
    # use_site captured as raw tokens: every 500
    assert Enum.map(ex.use_site, & &1.value) == ["every", 500]
    # expected expansion captured as AST
    assert {:expansion, {:function_call, _, _}} = ex.expected
  end

  test "a type-only example pin (`expands : Type`) is captured as {:type, _}" do
    node =
      parse!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands : Int\n"
      )

    rule = syntax_rule(node)
    assert [%{expected: {:type, _}}] = rule.examples
  end

  test "a syntax rule with no example has an empty examples list (non-breaking)" do
    node = parse!("macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n")
    assert syntax_rule(node).examples == []
  end
end
```

- [ ] **Step 2: Run it — expect FAIL** (`parse_macro_rule` produces no `:examples` key → `rule.examples` raises `KeyError`, and the indented `example` line makes `parse_macro_rules` record `{:expected, :syntax_rule, …}` so `parse!` raises).

Run: `mix test test/cure/compiler/macro_example_test.exs` → FAIL.

- [ ] **Step 3: Attach example parsing to `parse_macro_rule/1`**

In `parse_macro_rule/1`, after `{template, state} = parse_expr(state, 0)` and before building `rule`, add:

```elixir
    {examples, state} = parse_rule_examples(state)
```

and add `examples: examples` to the `rule` map:

```elixir
    rule = %{
      kind: :syntax,
      keyword: keyword,
      segments: segments,
      template: template,
      examples: examples,
      progress: nil,
      line: kw_token.line
    }
```

Add the example parsers near `parse_macro_rule/1`:

```elixir
  # After a syntax rule's template, an OPTIONAL indented block of `example …`
  # lines (self-proving §5). Consumes the nested indent/dedent so the macro-body
  # loop stays at the rule level. Returns [] when no example block follows.
  defp parse_rule_examples(state) do
    state = skip_macro_trivia(state)

    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {examples, state} = parse_example_lines(state, [])
        state = expect_dedent(state)
        {examples, state}

      _ ->
        {[], state}
    end
  end

  defp parse_example_lines(state, acc) do
    state = skip_macro_trivia(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :identifier, value: "example"} ->
        {ex, state} = parse_one_example(state)
        parse_example_lines(state, [ex | acc])

      other ->
        state = add_error(state, {:expected, :example, :got, other.type, other.line, other.col})
        # Recover: skip one token so a bad line does not eat the block.
        parse_example_lines(advance(state), acc)
    end
  end

  # `example <use-site tokens…> expands <expected>` where <expected> is either
  # `: <Type>` (a type-only pin, §5.2) or an expansion expression. The use-site
  # is captured as raw tokens — it names the macro's own keyword and cannot be
  # expanded at macro-def parse time; slice 2b feeds these tokens through the
  # rule to check the expansion.
  defp parse_one_example(state) do
    kw = peek(state)
    state = advance(state)
    {use_site, state} = collect_until_expands(state, [])

    state =
      case peek(state) do
        %Token{type: :identifier, value: "expands"} -> advance(state)
        t -> add_error(state, {:expected, :expands, :got, t.type, t.line, t.col})
      end

    {expected, state} =
      case peek(state) do
        %Token{type: :colon} ->
          {ty, state} = parse_expr(advance(state), 0)
          {{:type, ty}, state}

        _ ->
          {ast, state} = parse_expr(state, 0)
          {{:expansion, ast}, state}
      end

    {%{use_site: Enum.reverse(use_site), expected: expected, line: kw.line}, state}
  end

  # Collect the filled use-site tokens up to the `expands` keyword (or end of
  # line). Guards on :newline/:dedent/:eof so a missing `expands` cannot run off
  # the block.
  defp collect_until_expands(state, acc) do
    case peek(state) do
      %Token{type: :identifier, value: "expands"} -> {acc, state}
      %Token{type: type} when type in [:newline, :dedent, :eof] -> {acc, state}
      tok -> collect_until_expands(advance(state), [tok | acc])
    end
  end
```

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_example_test.exs` → PASS.

- [ ] **Step 5: Full parser suite — no regression** (all existing macro tests: `parse_macro_rule` now emits an `examples: []` key; confirm milestone-1/2, literal, hygiene, explain tests still pass — the new key is additive).

Run: `mix test test/cure/compiler/` → all pass.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_example_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): parse per-rule example/expands sub-blocks (SP2 M3)"
```

---

### Task 2: `rule_unpinned` — a syntax rule with no example is a compile error

**Files:**
- Modify: `lib/cure/compiler/macro_validate.ex` (add `check_rules_pinned/1`)
- Modify: `lib/cure/compiler/errors.ex` (add `format_error` clause for `:rule_unpinned`)
- Test: `test/cure/compiler/macro_example_test.exs` (extend)

**Interfaces:**
- `MacroValidate.check_rules_pinned(macro_def) :: :ok | {:error, {:rule_unpinned, [keyword :: String.t()]}}` — the keywords of `:syntax` rules that carry no example.
- `Errors.format_error({:rule_unpinned, keywords}, file)` → a diagnostic string.

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

  test "a syntax rule with no example is rule_unpinned" do
    md = macro_def!("macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n")
    assert {:error, {:rule_unpinned, ["every"]}} = MacroValidate.check_rules_pinned(md)

    rendered = Errors.format_error({:rule_unpinned, ["every"]}, "m.cure")
    assert rendered =~ "every"
    assert rendered =~ "example"
    refute rendered =~ ":rule_unpinned"
  end

  test "a syntax rule WITH an example checks clean" do
    md =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(500)\n"
      )

    assert :ok = MacroValidate.check_rules_pinned(md)
  end

  test "only unpinned syntax rules are reported (mixed macro)" do
    md =
      macro_def!(
        "macro M\n  syntax a becomes X\n    example a expands X\n  syntax b becomes Y\n"
      )

    assert {:error, {:rule_unpinned, ["b"]}} = MacroValidate.check_rules_pinned(md)
  end
```

- [ ] **Step 2: Run it — expect FAIL** (`check_rules_pinned/1` undefined → `UndefinedFunctionError`).

Run: `mix test test/cure/compiler/macro_example_test.exs` → the three new tests FAIL.

- [ ] **Step 3: Add `check_rules_pinned/1`** (in `macro_validate.ex`, alongside `check_explain_exhaustive/1`)

```elixir
  @doc """
  Check every `syntax` rule carries at least one worked example (design §5.1).
  Returns `:ok` or `{:error, {:rule_unpinned, unpinned_keywords}}`.
  """
  @spec check_rules_pinned(tuple()) :: :ok | {:error, {:rule_unpinned, [String.t()]}}
  def check_rules_pinned({:macro_def, _meta, rules}) do
    unpinned =
      rules
      |> Enum.filter(&(&1[:kind] == :syntax))
      |> Enum.filter(&(Map.get(&1, :examples, []) == []))
      |> Enum.map(& &1.keyword)

    case unpinned do
      [] -> :ok
      kws -> {:error, {:rule_unpinned, kws}}
    end
  end
```

- [ ] **Step 4: Add the `:rule_unpinned` render clause** (`errors.ex`, before the catch-all)

```elixir
  def format_error({:rule_unpinned, keywords}, file) do
    listed = keywords |> Enum.map(&"`#{&1}`") |> Enum.join(", ")

    format_diagnostic(
      "error",
      "macro rule has no worked example",
      file,
      0,
      "these rules are not pinned by an example: #{listed}. Add an indented " <>
        "`example <use> expands <result>` under each rule so its intent is checked, not just its type."
    )
  end
```

- [ ] **Step 5: Run the tests — expect PASS**

Run: `mix test test/cure/compiler/macro_example_test.exs` → PASS (all: parse + the three check tests).

- [ ] **Step 6: Full suite + warnings**

Run: `mix test test/cure/compiler/` → all pass. Then `mix compile --warnings-as-errors --force` → clean (confirm `format_error/2` clauses stay grouped).

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/compiler/macro_validate.ex lib/cure/compiler/errors.ex test/cure/compiler/macro_example_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(macros): rule_unpinned check for syntax rules with no example (SP2 M3)"
```

---

## Slice boundary — what M3 still needs

This slice delivers M3's **presence** obligation: `rule_unpinned` fires for an unexampled
`syntax` rule; examples parse and are captured (use-site tokens + expected AST) for the next
slice. Not yet:

- **Slice 2b — the expansion-equality check (`example_mismatch`):** feed an example's captured
  `use_site` tokens through the rule (reuse the two-phase parse so nested literal/`<fresh>`
  expansion runs), and check the result **equals** `expected` **up to α-renaming** (gensym
  normalisation) for `{:expansion, _}`, or **has** the pinned type for `{:type, _}` (reuse
  `Program.elaborate`, T8-style). The α-equality comparator is the one genuinely new piece.
- **§3.4 author `fail C(args)`** (extends `Diagnosis`; needs Tier-3 `check … else fail`).
- **Tier-3 `computed by`** elaborators.
- **The wiring slice** — invoke `check_explain_exhaustive` + `check_rules_pinned` (+ later
  checks) in the compile pipeline, and pin SP1's own macros with `explain`/`example` blocks.

When all SP2 mechanisms are executed + reviewed, run SP2 Stage 6 (full `mix test`) → SP2
complete → SP3 (generative expansion proof).

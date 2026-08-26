# SP1 — Minimal Macro Facility — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4) to implement task-by-task. Steps use checkbox (`- [ ]`) syntax. Strict red-green TDD; commit per task.

**Goal:** A `macro` container parses into a structured `{:macro_def, meta, rules}` AST — the front end the rest of SP1 (use-site matching, hygienic expansion) builds on.

**Architecture:** `macro` is a **soft keyword** (identifier-dispatched at prefix position, like `sup`/`app`), parsed by a new `parse_macro_def/1` that mirrors `parse_fsm/1` (`parser.ex:3894`). Its indented body is a list of `syntax`/`literal` **rules**; each rule captures its leading **keyword**, an ordered list of **segments** (literal tokens + typed **holes** `<name: Kind>`), and a template, in a shape that carries a **progress** slot from the start (per the syntax-parse comparison — retrofitting progress later is painful). No elaborator wiring yet; a `{:macro_def, …}` is inert data this milestone.

**Tech Stack:** Elixir; `lib/cure/compiler/{lexer,parser,token}.ex` (shared frontend, P layer); ExUnit.

## Global Constraints

- **TCB delta ZERO.** No `lib/cure/core/*` change. This milestone touches only `lib/cure/compiler/parser.ex` (+ tests). If a task seems to need a kernel or lexer change beyond what a task names, STOP — it is mis-scoped.
- **Ghost commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. Explicit pathspec `git add -- <path>`, never `-A`.
- **One build at a time.** Never run concurrent `mix test`. Prefer scoped `mix test <file>`; full suite once at the end.
- **Tests are immutable once green.** Once a step's red test passes, make later changes go green by editing implementation code only — never by deleting, skipping, loosening, or rewriting a passing test. The sole exception is a test that is itself provably wrong (wrong expected shape, typo, etc.); if you believe a test is wrong, state exactly why before touching it.
- **User-facing syntax is DEFERRED** — the spellings here (`macro`, `syntax`, `becomes`, `<name: Kind>`) are the design's current notation, used as placeholders; the AST shape is what matters, not the surface words.
- **Token/state/helpers (verified anchors):** `%Cure.Compiler.Token{type, value, line, col}` (`token.ex:16`); parser state `%{tokens, file, pos, errors, emit_events}` (`parser.ex:45`); helpers `peek/1` (`:5562`, eof-safe), `peek_at/2` (`:5568`), `advance/1` (`:5573`), `skip_newlines/1` (`:5581`), `expect/2` (`:5588`), `expect_dedent/1` (`:5610`), `add_error/2` (`:5617`); `variable/1` builds `{:variable, meta, name}`. Soft-keyword dispatch site: `parse_prefix/1`'s `:identifier` case (`parser.ex:292-340`). Container template: `parse_fsm/1` (`:3894`) + `parse_fsm_block/1` (`:3933`).

---

### Task 1: Recognize `macro Name` as a soft keyword and parse the container skeleton (dedent-closed, no `end`)

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (the `:identifier` prefix case at `:292-340`; add `parse_macro_def/1` + `parse_macro_block/1` near `parse_fsm/1` `:3894`)
- Test: `test/cure/compiler/macro_def_parse_test.exs` (create)

**Interfaces:**
- Produces: `{:macro_def, meta, rules}` where `meta` is a keyword list `[name: String.t(), line: integer, col: integer]` and `rules` is a list (empty this task). Consumed by Task 2+ (which fills `rules`) and, later, the elaborator's grammar-registration pass.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/macro_def_parse_test.exs
defmodule Cure.Compiler.MacroDefParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # NOTE on both sources below: Cure's containers (fsm/sup/app, confirmed at
  # parse_fsm_block/parse_sup_block/parse_app_block, all via expect_dedent/1)
  # close purely by DEDENT — no literal `end` is ever consumed by a container
  # parser. `end` IS a reserved keyword (`Token{type: :keyword, value: :end}`),
  # so writing a trailing `end` line here would lex as a real token that no
  # macro-container code consumes, and it would be re-parsed as a second,
  # stray top-level `{:variable, _, :end}` node. Real fixtures (e.g.
  # examples/traffic_light.cure, examples/cure_colony/.../colony.cure) confirm
  # containers never write `end`. So there is no trailing `end` below.
  #
  # NOTE on `parse!/1`'s return shape: `Parser.parse/2` (parser.ex:99-103)
  # returns the bare AST node directly when there is exactly one top-level
  # form (`case exprs do [single] -> single; many -> {:block, ...} end`) —
  # NEVER a list. So each test below binds `node = parse!(...)` directly
  # (matching the idiom already used elsewhere, e.g.
  # test/cure/compiler/dot_pattern_parse_test.exs's `ast = parse!(source)`),
  # not `[node] = parse!(...)`.

  test "an empty macro container parses to a {:macro_def, meta, []} node" do
    # A macro with no rules yet — just the container shell.
    node = parse!("macro Every\n")
    assert {:macro_def, meta, []} = node
    assert meta[:name] == "Every"
  end

  test "`macro` NOT followed by an identifier stays a plain variable (non-breaking)" do
    # `macro` used as an ordinary local must keep parsing as a variable: the
    # dispatch clause added in Step 3 falls through to `{variable(token),
    # advance(state)}` whenever `macro` isn't followed by an identifier, so
    # `macro + 1` still parses as the binary `+` over a `macro` variable and
    # an integer literal — confirmed against the real parser's output shape
    # (`{:binary_op, [category: :arithmetic, operator: :+, ...], [left, right]}`).
    node = parse!("macro + 1\n")
    assert {:binary_op, _, [{:variable, _, "macro"}, _rhs]} = node
  end
end
```

- [ ] **Step 2: Run it and watch it fail**

Run: `mix test test/cure/compiler/macro_def_parse_test.exs`
Expected: the first test FAILs — `macro Every` currently parses as two bare `{:variable, ...}` nodes (`"macro"` then `"Every"`), never a `{:macro_def, …}` node. The second test (`macro` as a plain variable) already PASSes before this task's implementation — it's a non-regression pin on today's existing fallback behavior, not a new red test.

- [ ] **Step 3: Add the soft-keyword dispatch clause**

In `parse_prefix/1`'s `:identifier` `case token.value do` (`parser.ex:293`), add a clause beside `"sup"`/`"app"` (mirror their `peek_at(state, 1)` guard exactly):

```elixir
          # Soft keyword: `macro Name …` at statement-prefix position is the
          # macro container. `macro` followed by anything other than an
          # identifier stays a plain variable (non-breaking, like sup/app).
          "macro" ->
            case peek_at(state, 1) do
              %Token{type: :identifier} ->
                parse_macro_def(state)

              _ ->
                {variable(token), advance(state)}
            end
```

- [ ] **Step 4: Add `parse_macro_def/1` and `parse_macro_block/1`**

Near `parse_fsm/1` (`parser.ex:3894`), add (mirrors `parse_fsm`/`parse_fsm_block`, but emits `:macro_def` and collects `rules` — empty until Task 2):

```elixir
  defp parse_macro_def(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    state = skip_newlines(state)
    {rules, state} = parse_macro_block(state)

    meta = [name: name, line: token.line, col: token.col]
    {{:macro_def, meta, rules}, state}
  end

  defp parse_macro_block(state) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {rules, state} = parse_macro_rules(state, [])
        state = expect_dedent(state)
        {rules, state}

      _ ->
        # No body (e.g. `macro Name` immediately followed by newline/eof,
        # nothing indented underneath) — empty rule set. Containers close
        # purely by dedent; there is no `end` keyword to consume here.
        {[], state}
    end
  end

  # Filled in Task 2; for now, consume to the block's end producing no rules.
  defp parse_macro_rules(state, acc) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      _ ->
        # Task 2 replaces this with real rule parsing; for now skip the token.
        parse_macro_rules(advance(state), acc)
    end
  end
```

- [ ] **Step 5: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_def_parse_test.exs`
Expected: PASS (both tests).

- [ ] **Step 6: Run the neighbouring parser suite for no regression**

Run: `mix test test/cure/compiler/`
Expected: PASS (soft-keyword addition is non-breaking; `macro` as a variable still works).

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_def_parse_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): parse macro container skeleton (SP1 task 1)"
```

---

### Task 2: Parse a bare-keyword `syntax … becomes …` rule (no holes yet)

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_macro_rules/2`; add `parse_macro_rule/1`)
- Test: `test/cure/compiler/macro_def_parse_test.exs` (extend)

**Interfaces:**
- Produces: a **rule** map `%{kind: :syntax, keyword: String.t(), segments: [segment], template: ast, progress: nil, line: integer}` where a `segment` is `{:lit, String.t()}` (a literal token) this task. `progress: nil` is the slot Task 3+ / SP2 fills. Consumed by SP1's use-site matcher.

- [ ] **Step 1: Write the failing test**

```elixir
  test "a bare-keyword syntax rule captures its keyword and template" do
    # No trailing `end` (see the note on Task 1's tests — containers close by
    # dedent only); `node` is the bare top-level node, not a 1-list.
    node = parse!("macro Now\n  syntax now becomes Clock.now()\n")
    assert {:macro_def, _meta, [rule]} = node
    assert rule.kind == :syntax
    assert rule.keyword == "now"
    assert rule.segments == []          # `now` is the keyword; nothing after it before `becomes`
    assert {:function_call, _, _} = rule.template   # Clock.now()
    assert Map.has_key?(rule, :progress)            # progress slot present from the start
  end

  test "a body line that isn't a recognized rule keyword records a parse error" do
    # New behaviour introduced by this task's `parse_macro_rules` recovery
    # clause: a macro-body statement that isn't `syntax ...` must record an
    # `{:expected, :syntax_rule, ...}` error rather than silently vanishing.
    # Any recorded error makes the overall parse `{:error, _}` (parser.ex:109-112:
    # `case state.errors do [] -> {:ok, ast}; errors -> {:error, ...} end`), so
    # this can't be observed via `parse!/1` — it must assert on the raw result.
    {:ok, tokens} = Lexer.tokenize("macro Bad\n  oops\n", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    assert Enum.any?(errors, &match?({:expected, :syntax_rule, :got, _, _, _}, &1))
  end
```

- [ ] **Step 2: Run it — expect FAIL**

Run: `mix test test/cure/compiler/macro_def_parse_test.exs`
Expected: both new tests FAIL — the first because `parse_macro_rules` (Task 1's placeholder) skips tokens and yields `rules = []`, no rule map; the second because nothing yet calls `add_error/2` for an unrecognized body statement, so `Parser.parse` returns `{:ok, ast}` and the test's `{:error, errors} = ...` match raises.

- [ ] **Step 3: Implement rule parsing**

Replace the placeholder branch in `parse_macro_rules/2` and add `parse_macro_rule/1`:

```elixir
  defp parse_macro_rules(state, acc) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :identifier, value: "syntax"} ->
        {rule, state} = parse_macro_rule(state)
        parse_macro_rules(state, [rule | acc])

      other ->
        state = add_error(state, {:expected, :syntax_rule, :got, other.type, other.line, other.col})
        # Recover: skip to the next line so one bad rule does not eat the block.
        parse_macro_rules(advance(state), acc)
    end
  end

  defp parse_macro_rule(state) do
    kw_token = peek(state)      # `syntax`
    state = advance(state)

    keyword_token = peek(state) # the rule's leading keyword, e.g. `now`
    keyword = to_string(keyword_token.value)
    state = advance(state)

    # Segments between the keyword and `becomes` (holes added in Task 3;
    # bare-keyword rules have none). Stop at the `becomes` identifier.
    {segments, state} = parse_rule_segments(state, [])

    # Expect `becomes`, then the template expression.
    state =
      case peek(state) do
        %Token{type: :identifier, value: "becomes"} -> advance(state)
        t -> add_error(state, {:expected, :becomes, :got, t.type, t.line, t.col})
      end

    {template, state} = parse_expr(state, 0)

    rule = %{
      kind: :syntax,
      keyword: keyword,
      segments: segments,
      template: template,
      progress: nil,
      line: kw_token.line
    }

    {rule, state}
  end

  # Task 3 replaces this to recognize `<name: Kind>` holes. For now a
  # bare-keyword rule has no segments: the next token is `becomes`.
  defp parse_rule_segments(state, acc) do
    case peek(state) do
      %Token{type: :identifier, value: "becomes"} -> {Enum.reverse(acc), state}
      %Token{type: type} when type in [:newline, :dedent, :eof] -> {Enum.reverse(acc), state}
      _ -> {Enum.reverse(acc), state}   # Task 3: collect literal-token + hole segments here
    end
  end
```

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_def_parse_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_def_parse_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): parse bare-keyword `syntax … becomes …` macro rules (SP1 task 2)"
```

---

### Task 3: Parse typed holes `<name: Kind>` inside a syntax rule

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_rule_segments/2`)
- Test: `test/cure/compiler/macro_def_parse_test.exs` (extend)

**Interfaces:**
- Extends a `segment` to also be `{:hole, %{name: String.t(), kind: String.t(), line: integer}}`. The rule's `segments` becomes an ordered mix of `{:lit, word}` and `{:hole, …}` — the ordered shape the use-site matcher walks (recording progress as it consumes each segment).

**Design decision pinned (grounding doc):** a hole is lexed at PARSE time by shape — the token stream for `every <t: Duration>` is `[identifier "every", lt, identifier "t", colon, identifier "Duration", gt]`. `parse_rule_segments` recognizes the `:lt identifier :colon identifier :gt` window as a hole. (The `<`-opens-a-hole lexer subtlety of design §2 is deferred to the use-site milestone; inside a rule the window is unambiguous because a rule body is not an expression.)

- [ ] **Step 1: Write the failing test**

```elixir
  test "a syntax rule with a typed hole captures name + kind in order" do
    # No trailing `end` (dedent-only closing, per Task 1's note); `node` is
    # the bare top-level node, not a 1-list.
    node = parse!("macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n")
    assert {:macro_def, _m, [rule]} = node
    assert rule.keyword == "every"
    assert [{:hole, hole}] = rule.segments
    assert hole.name == "t"
    assert hole.kind == "Duration"
  end

  test "a malformed hole (missing closing `>`) records a :malformed_hole error" do
    # New behaviour introduced by this task's :lt branch's `else`: a `<...`
    # window that doesn't close with `identifier :colon identifier :gt` must
    # record `{:malformed_hole, line, col}`. Same reasoning as Task 2's error
    # test: any recorded error flips the whole parse to `{:error, _}`
    # (parser.ex:109-112), so assert on the raw result, not `parse!/1`.
    {:ok, tokens} =
      Lexer.tokenize("macro Bad\n  syntax every <t: Duration becomes x\n", emit_events: false)

    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    assert Enum.any?(errors, &match?({:malformed_hole, _, _}, &1))
  end
```

- [ ] **Step 2: Run it — expect FAIL**

Run: `mix test test/cure/compiler/macro_def_parse_test.exs`
Expected: both new tests FAIL — the first because `parse_rule_segments`'s catch-all branch (Task 2) treats `<` as an ordinary literal token, so `rule.segments` comes back as `[{:lit, "<"}, ...]` instead of a `{:hole, ...}`; the second because nothing yet calls `add_error/2` for a malformed hole, so `Parser.parse` returns `{:ok, ast}` and the test's `{:error, errors} = ...` match raises.

- [ ] **Step 3: Implement hole recognition in `parse_rule_segments/2`**

```elixir
  defp parse_rule_segments(state, acc) do
    case peek(state) do
      %Token{type: :identifier, value: "becomes"} ->
        {Enum.reverse(acc), state}

      %Token{type: type} when type in [:newline, :dedent, :eof] ->
        {Enum.reverse(acc), state}

      # A hole `<name: Kind>` — window: :lt identifier :colon identifier :gt
      %Token{type: :lt} ->
        with %Token{type: :identifier, value: name} <- peek_at(state, 1),
             %Token{type: :colon} <- peek_at(state, 2),
             %Token{type: :identifier, value: kind} <- peek_at(state, 3),
             %Token{type: :gt} <- peek_at(state, 4) do
          hole = {:hole, %{name: name, kind: kind, line: peek(state).line}}
          state = state |> advance() |> advance() |> advance() |> advance() |> advance()
          parse_rule_segments(state, [hole | acc])
        else
          _ ->
            t = peek(state)
            state = add_error(state, {:malformed_hole, t.line, t.col})
            {Enum.reverse(acc), advance(state)}
        end

      # A literal token in the rule (e.g. the `ms` in `every <n> ms`).
      %Token{value: v} ->
        seg = {:lit, to_string(v)}
        parse_rule_segments(advance(state), [seg | acc])
    end
  end
```

Note: confirm the lexer emits `:lt`/`:gt`/`:colon` token types for `<`/`>`/`:` (grep `lexer.ex` for `:lt`/`:gt`; if `<` is `:lt`-vs-`:less_than`, use the actual atom). If the tokens differ, adjust the pattern to the real atoms — do NOT invent token types.

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_def_parse_test.exs`
Expected: PASS.

- [ ] **Step 5: Full parser suite for no regression**

Run: `mix test test/cure/compiler/`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_def_parse_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): parse typed holes `<name: Kind>` in macro rules (SP1 task 3)"
```

---

## Milestone boundary

Tasks 1–3 deliver the **macro-definition front-end**: a `macro` container with `syntax`
rules (literal segments + typed holes) parses to a structured, progress-slotted
`{:macro_def, meta, rules}` AST, non-breakingly, with the full parser suite green. That
is this plan's independently-testable deliverable.

The **remaining SP1 tasks** (their own plan increment, written next by the autopilot
Stage-2 loop against this same grounding) are:
- **T4 — `literal` rules + numeric-suffix lexer** (`500ms`): new lexer machinery
  (`lex_decimal`), the one non-parser change SP1 needs.
- **T5 — two-phase parse:** parser-state `active_macros`; a pre-pass seeding it from
  `use` + local `macro` defs (the architectural core, grounding doc).
- **T6 — use-site matching:** at a keyword/identifier prefix in `active_macros`, walk the
  rule's `segments`, bind holes, **recording progress** (port syntax-parse's
  maximal-by-progress selection when several rules could apply).
- **T7 — hygienic `becomes` expansion** (`<fresh Name>` gensym) → surface AST.
- **T8 — feed expansion back through parse→elaborate; assert it kernel-checks** (green +
  a red fixture whose expansion is ill-typed → rejected-not-unsound).
- **T9 — import scoping + same-keyword conflict; two-pass name resolution.**

Each is a task with a named red test, following the pattern above.

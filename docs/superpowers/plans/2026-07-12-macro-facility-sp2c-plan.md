# SP2 slice 2b — Mechanism 3: Example expansion-equality (`example_mismatch`) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4). Steps use `- [ ]`. Strict red-green TDD; commit per task. Third SP2 slice; SP1 + SP2 M1 + SP2 M3-presence (2a) COMPLETE.

**Goal:** Complete Mechanism 3 (design §5): an example doesn't just have to *exist* (2a's `rule_unpinned`), it must be *correct* — the rule with its holes filled must actually **expand to** the `expands …` the author wrote. A `syntax` rule whose example's real expansion differs from its pinned expansion (up to hygiene/α-renaming) is a compile error `example_mismatch`. This is the intent oracle: the example is the checked documentation.

**Architecture:** Self-proving design §5.1. Slice 2a captured each example as `%{use_site: [tokens], expected: {:expansion, ast} | {:type, ast}}`. This slice adds (1) `Parser.expand_example/2` — a driver that runs an example's captured `use_site` tokens through the macro's own rules (seeds `active_macros`/`literal_macros` from the rules and calls `parse_expr`, so nested literal/`<fresh>` expansion happens exactly as at a real use-site), and (2) `MacroValidate.check_examples/1` comparing the driven expansion to the pinned `expected` **up to α-renaming** (strip `:line`/`:col`; canonicalise `<fresh>` gensym `$N` suffixes). **Scope:** `{:expansion, ast}` pins only. `{:type, ast}` type-only pins (§5.2) need `Program.elaborate` and are deferred to a follow-on. **TCB delta zero** (frontend parse + analysis; unwired).

**Tech Stack:** Elixir; `lib/cure/compiler/parser.ex`, `lib/cure/compiler/macro_validate.ex`, `lib/cure/compiler/errors.ex`; ExUnit.

## Global Constraints

- **TCB delta ZERO.** `lib/cure/compiler/*` only (+ tests). No `lib/cure/core/*`, no `lib/cure/elab/*`.
- **Ghost commits** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. `git add -- <path>`, never `-A`.
- **One build at a time.** Scoped `mix test test/cure/compiler/macro_example_check_test.exs`; `mix test test/cure/compiler/` for regression.
- **Run mix from the worktree root** (`.claude/worktrees/core-let-binder`), NEVER the parent clone. (A background formatter re-touches `parser.ex` timestamps → the Edit tool may report "file modified"; `git status` shows it clean vs HEAD — re-read the exact region and re-apply.)
- **Tests immutable once green.** Go green by fixing implementation only; touch a passing test only if it is provably wrong (state why first).

## Verified grounding (probed live)

- The expansion of `every 500` (through rule `syntax every <t: Duration> becomes Timer.repeat(t)`) is `{:function_call, [name: "Timer.repeat", line: 2, col: 50], [{:literal, [subtype: :integer, line: 3, col: 16], 500}]}`. The author's standalone `Timer.repeat(500)` parses to the SAME shape modulo `:line`/`:col` (semantic meta `name: "Timer.repeat"` and `subtype: :integer` are identical). So α-equality = **strip `:line`/`:col` from every meta keyword list, then compare** (plus gensym canonicalisation for `<fresh>` templates).
- Parser state `defstruct` (`parser.ex:45`): `[:tokens, :file, pos: 0, errors: [], emit_events: false, active_macros: %{}, fresh_counter: 0, literal_macros: %{}]`. `harvest_active_macros/1`/`harvest_literal_macros/1` (private, same module) index a `[{:macro_def, meta, rules}]` list by keyword/suffix. `parse_expr(state, 0)` (private) parses one expression from a state — the entry that triggers `parse_prefix` → `parse_macro_use` expansion. `%Cure.Compiler.Token{}` = `type, value, line, col`.
- `MacroValidate` (SP2) has `check_explain_exhaustive/1` + `check_rules_pinned/1`; add `check_examples/1`. `errors.ex`: `:example_mismatch` clause before the catch-all, helper after (clause-grouping lesson).
- Example capture (2a): `rule.examples = [%{use_site: [%Token{}], expected: {:expansion, ast} | {:type, ast}, line}]`.

## The α-comparator (design's "up to hygiene/α-renaming")

`normalize(ast)` = (1) recursively drop `:line`/`:col` from every meta keyword list; (2) rewrite any `{:variable, meta, name}` whose `name` matches `~r/^(.+)\$\d+$/` (a `<fresh>` gensym like `x$0`) to its base name (`x`). Then `normalize(actual) == normalize(expected)`. For non-`<fresh>` templates (the common case) step 2 is a no-op and this is structural-equality-modulo-position. **Honest limit:** the gensym-suffix rewrite is a *first-cut* α-approximation, not capture-aware de Bruijn α — two distinct fresh names both stripping to the same base could theoretically mis-compare; a fully capture-aware comparator is a noted follow-on. All tests here use a single fresh name or none.

> **CRITICAL — caught by recursive-skeptical-review, fixed in Task 2 Step 3 below.** The two-clause `normalize/1` originally drafted here (recurse-with-list-children, else pass through unchanged) only strips `:line`/`:col` from a node whose **third element is a list** (real AST children). `Parser`'s own `literal/2` (`parser.ex:924-926`) builds every `:literal` node as `{:literal, [subtype: s, line:, col:], token.value}` — the third element is the **scalar** `token.value` (an integer/string/bool/atom/char), never a list. Such nodes fell through to the catch-all `normalize(other), do: other`, which returns them **completely unchanged** — their `:line`/`:col` never gets stripped. Verified live: patching the original two-clause `normalize/1` into the tree and running exactly the three Task-2 Step-1 tests below gives `mix test` → `2/4 passed` — the very tests the plan asserts should pass (`"an example whose expansion matches its pin checks clean"` and `"a matching example modulo source position still checks clean"`) both FAIL, because the driven expansion's `:literal` sits at the rule-template's column while the captured pin's `:literal` sits at the `expands` clause's column, and neither gets stripped. Since virtually every real macro example's expansion contains at least one literal argument (numbers, strings, atoms, bools — the design's own headline `every 500ms` example included), the unpatched comparator would reject essentially every correct macro rule as `example_mismatch`. The fix is a third `normalize/1` clause for scalar-valued nodes, added to Task 2 Step 3's code below; verified green (`4/4` on the scoped file, `672 passed, 1 skipped` — no regression — on the full `test/cure/compiler/` suite) with the fix in place, and confirmed to fail exactly the same two tests when the fix is removed again.

---

### Task 1: `Parser.expand_example/2` — drive an example's use-site through the macro's rules

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (add public `expand_example/2`)
- Test: `test/cure/compiler/macro_example_check_test.exs` (create)

**Interfaces:**
- `Parser.expand_example(rules :: [map()], use_site_tokens :: [Token.t()]) :: ast()` — seeds a parser state's `active_macros`/`literal_macros` from `rules`, parses `use_site_tokens` as one expression, returns the expanded AST.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/macro_example_check_test.exs
defmodule Cure.Compiler.MacroExampleCheckTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp macro_def!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    find = fn find, n ->
      case n do
        {:macro_def, _, _} = m -> m
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end
    find.(find, ast)
  end

  test "expand_example runs an example's captured use-site through the rule" do
    {:macro_def, _, rules} =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(500)\n"
      )

    rule = Enum.find(rules, &(&1[:kind] == :syntax))
    [ex] = rule.examples

    result = Parser.expand_example(rules, ex.use_site)
    # every 500  ==>  Timer.repeat(500)
    assert {:function_call, meta, [{:literal, _, 500}]} = result
    assert Keyword.get(meta, :name) == "Timer.repeat"
  end
end
```

- [ ] **Step 2: Run it — expect FAIL** (`Parser.expand_example/2` undefined → `UndefinedFunctionError`).

Run: `mix test test/cure/compiler/macro_example_check_test.exs` → FAIL.

- [ ] **Step 3: Add `expand_example/2`** (public, near `parse/2` or the macro helpers)

```elixir
  @doc """
  Expand a macro example's captured use-site tokens through the macro's own
  rules — the same expansion a real use-site gets (nested literal/`<fresh>`
  expansion included). Used by MacroValidate to check `example … expands …`
  pins (self-proving §5). Returns the expanded surface AST.
  """
  @spec expand_example([map()], [Token.t()]) :: ast()
  def expand_example(rules, use_site_tokens) do
    synthetic = [{:macro_def, [], rules}]
    active = harvest_active_macros(synthetic)
    literal = harvest_literal_macros(synthetic)

    eof = %Token{type: :eof, value: nil, line: 0, col: 0}

    state = %__MODULE__{
      tokens: use_site_tokens ++ [eof],
      file: "example",
      emit_events: false,
      active_macros: active,
      literal_macros: literal
    }

    {ast, _state} = parse_expr(state, 0)
    ast
  end
```

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_example_check_test.exs` → PASS.

- [ ] **Step 5: Full parser suite — no regression** (a new public function; existing behaviour untouched).

Run: `mix test test/cure/compiler/` → all pass.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_example_check_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): expand_example drives an example use-site through the macro rules (SP2 M3)"
```

---

### Task 2: `check_examples` — `example_mismatch` when the expansion ≠ the pin

**Files:**
- Modify: `lib/cure/compiler/macro_validate.ex` (add `check_examples/1` + `normalize/1` + helpers)
- Modify: `lib/cure/compiler/errors.ex` (add `format_error` clause for `:example_mismatch`)
- Test: `test/cure/compiler/macro_example_check_test.exs` (extend)

**Interfaces:**
- `MacroValidate.check_examples(macro_def) :: :ok | {:error, {:example_mismatch, [%{keyword, expected, actual}]}}` — for each `{:expansion, _}` example whose driven expansion differs from its pin (up to α). `{:type, _}` examples are skipped this slice.
- `Errors.format_error({:example_mismatch, mismatches}, file)` → a diagnostic string.

- [ ] **Step 1: Write the failing test**

```elixir
  alias Cure.Compiler.{MacroValidate, Errors}

  test "an example whose expansion matches its pin checks clean" do
    md =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(500)\n"
      )

    assert :ok = MacroValidate.check_examples(md)
  end

  test "an example whose pin is WRONG is example_mismatch" do
    # Rule expands to Timer.repeat(t); the example claims Timer.repeat(999) for
    # `every 500` — a wrong pin.
    md =
      macro_def!(
        "macro Every\n  syntax every <t: Duration> becomes Timer.repeat(t)\n    example every 500 expands Timer.repeat(999)\n"
      )

    assert {:error, {:example_mismatch, [m]}} = MacroValidate.check_examples(md)
    assert m.keyword == "every"

    rendered = Errors.format_error({:example_mismatch, [m]}, "m.cure")
    assert rendered =~ "every"
    refute rendered =~ ":example_mismatch"
  end

  test "a matching example modulo source position still checks clean (α: positions ignored)" do
    # The pin is written on a different line/column than the expansion carries;
    # normalisation must ignore :line/:col.
    md =
      macro_def!(
        "macro M\n  syntax m <x: Code> becomes f(x)\n    example m 1 expands f(1)\n"
      )

    assert :ok = MacroValidate.check_examples(md)
  end
```

- [ ] **Step 2: Run it — expect FAIL** (`check_examples/1` undefined).

Run: `mix test test/cure/compiler/macro_example_check_test.exs` → the three new tests FAIL.

- [ ] **Step 3: Add `check_examples/1` + `normalize/1`** (in `macro_validate.ex`)

```elixir
  alias Cure.Compiler.Parser

  @doc """
  Check every `syntax` rule's `{:expansion, _}` example actually expands to its
  pinned result, up to α-renaming (design §5.1). `{:type, _}` pins are skipped
  (deferred). Returns `:ok` or `{:error, {:example_mismatch, mismatches}}`.
  """
  @spec check_examples(tuple()) :: :ok | {:error, {:example_mismatch, [map()]}}
  def check_examples({:macro_def, _meta, rules}) do
    mismatches =
      rules
      |> Enum.filter(&(&1[:kind] == :syntax))
      |> Enum.flat_map(fn rule ->
        for %{use_site: use_site, expected: {:expansion, expected}} <- Map.get(rule, :examples, []),
            actual = Parser.expand_example(rules, use_site),
            normalize(actual) != normalize(expected) do
          %{keyword: rule.keyword, expected: expected, actual: actual}
        end
      end)

    case mismatches do
      [] -> :ok
      ms -> {:error, {:example_mismatch, ms}}
    end
  end

  # α-normalise for example comparison: drop source positions, then collapse
  # `<fresh>` gensym suffixes (`x$0` → `x`) so a template binder and its pin
  # compare equal. See the plan's "α-comparator" note on the honest limit.
  defp normalize({:variable, meta, name}) when is_binary(name) do
    {:variable, strip_pos(meta), degensym(name)}
  end

  defp normalize({t, meta, children}) when is_list(children) do
    {t, strip_pos(meta), Enum.map(children, &normalize/1)}
  end

  # A scalar-valued node (`:literal`'s {subtype, value} shape — `value` is a
  # raw integer/float/string/bool/atom/char, NOT a list of children) still
  # carries `:line`/`:col` in its meta that must be stripped, exactly like any
  # other node. Without this clause every `:literal` falls through to the
  # catch-all below UNCHANGED, so its source position never gets stripped and
  # `check_examples` rejects almost every real macro example (see the CRITICAL
  # note above "The α-comparator").
  defp normalize({t, meta, value}) when is_list(meta) do
    {t, strip_pos(meta), value}
  end

  defp normalize(other), do: other

  defp strip_pos(meta) when is_list(meta) do
    meta
    |> Enum.reject(fn
      {k, _} when k in [:line, :col] -> true
      _ -> false
    end)
    |> Enum.map(fn
      {k, v} -> {k, normalize_meta_value(v)}
      other -> other
    end)
  end

  defp strip_pos(meta), do: meta

  defp normalize_meta_value(v) when is_tuple(v), do: normalize(v)
  defp normalize_meta_value(v) when is_list(v), do: Enum.map(v, &normalize_meta_value/1)
  defp normalize_meta_value(v), do: v

  defp degensym(name) do
    case Regex.run(~r/^(.+)\$\d+$/, name) do
      [_, base] -> base
      _ -> name
    end
  end
```

- [ ] **Step 4: Add the `:example_mismatch` render clause** (`errors.ex`, before the catch-all)

```elixir
  def format_error({:example_mismatch, mismatches}, file) do
    listed = mismatches |> Enum.map(&"`#{&1.keyword}`") |> Enum.join(", ")

    format_diagnostic(
      "error",
      "macro example does not match its expansion",
      file,
      0,
      "these rules have an `example … expands …` whose stated result is not what the rule " <>
        "actually produces: #{listed}. Fix the `expands` side to the real expansion (or the rule)."
    )
  end
```

- [ ] **Step 5: Run the tests — expect PASS**

Run: `mix test test/cure/compiler/macro_example_check_test.exs` → PASS (driver + the three check tests). This requires the third `normalize/1` scalar-node clause above — verified live (recursive-skeptical-review): with only the first two clauses, this run is `2/4 passed` (the "checks clean" and "checks clean modulo position" tests fail); with all three clauses, `4/4`.

- [ ] **Step 6: Full suite + warnings**

Run: `mix test test/cure/compiler/` → all pass. Then `mix compile --warnings-as-errors --force` → clean (confirm `format_error/2` clauses stay grouped; the `normalize` walk mirrors `subst_holes`'s meta handling).

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/compiler/macro_validate.ex lib/cure/compiler/errors.ex test/cure/compiler/macro_example_check_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(macros): example_mismatch check — an example must expand to its pin (SP2 M3)"
```

---

## Slice boundary — M3 complete, what SP2 still needs

With 2a (`rule_unpinned`) + 2b (`example_mismatch`), **Mechanism 3 is functionally complete** (the
`{:type, _}` type-only pin check is the one deferred piece — it reuses `Program.elaborate` and is small).
SP2 now has live (unwired) checks for **all three** of its gate errors: `missing_diagnosis` (M1),
`rule_unpinned` + `example_mismatch` (M3). Still remaining in SP2:

- **`{:type, _}` type-only pin check** (§5.2) — small follow-on (elaborate the expansion, check its type).
- **§3.4 author `fail C(args)`** — extends `Diagnosis`; needs Tier-3 `check … else fail`.
- **Tier-3 `computed by`** total compile-time elaborators.
- **The WIRING slice** — invoke `check_explain_exhaustive` + `check_rules_pinned` + `check_examples` (+ later
  checks) in the compile pipeline, and pin SP1's own macros with `explain`/`example` blocks so they still
  compile.

When all SP2 mechanisms are executed + reviewed, run SP2 Stage 6 (full `mix test`) → SP2 complete → SP3.

# SP1 milestone 2 — Two-Phase Parse + Use-Site Expansion — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4). Steps use `- [ ]`. Strict red-green TDD; commit per task. Builds on milestone 1 (the `{:macro_def, meta, rules}` front-end, commits c381e7a/8f07931/77cbd6d/4295479).

**Goal:** A **locally-defined** macro's use-site expands. `macro Now` + `syntax now becomes Clock.now()`, then a `now` use-site, parses to `Clock.now()` — the first point a macro actually *does something*.

**Architecture:** **Two-phase parse.** `Parser.parse/2` runs a *harvest* pass (parse once; keep only the `{:macro_def, …}` nodes) to build `active_macros :: %{keyword => [rule]}`, then an *authoritative* pass with `active_macros` seeded on parser state. At a use-site, `parse_prefix/1`'s `:identifier` clause consults `active_macros`; a hit walks the rule's `segments` (binding holes), then **substitutes** the bound holes into the rule's `template` (an ordinary surface AST), yielding expanded surface AST that the elaborator later re-checks like hand-written code. Progress is recorded during segment matching (per the syntax-parse comparison). **TCB delta zero** — expansion is surface-AST-to-surface-AST, upstream of the elaborator.

**Tech Stack:** Elixir; `lib/cure/compiler/parser.ex` (shared frontend); ExUnit.

## Global Constraints

- **TCB delta ZERO.** No `lib/cure/core/*`. Only `lib/cure/compiler/parser.ex` (+ tests) this milestone.
- **Ghost commits** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. `git add -- <path>`, never `-A`.
- **One build at a time.** Scoped `mix test <file>`; `mix test test/cure/compiler/` for regression.
- **Tests immutable once green** — go green by fixing implementation, never by weakening a passing test (unless the test is provably wrong; state why first).
- **Scope of milestone 2:** LOCAL macros only (defined and used in the same module). Imported macros (cross-module `use SomeMacro`) are T9's concern — the harvest here scans only the module's own top-level `{:macro_def}` nodes.
- **Verified anchors (milestone-1 + new reads):** `Parser.parse/2` (parser.ex:92) returns `{:ok, bare_node}` / `{:error, errors}`; `parse_program/1` (parser.ex:117) is a flat forward loop over top-level forms; parser state `%{tokens, file, pos, errors, emit_events}` (parser.ex:45); the `:identifier` soft-keyword dispatch in `parse_prefix/1` (parser.ex ~292, where `macro`/`sup`/`app` live); the milestone-1 rule shape `%{kind: :syntax, keyword, segments: [{:lit,String}|{:hole,%{name,kind,line}}], template, progress, line}`; helpers `peek/1`, `peek_at/2`, `advance/1`, `expect/2` (`:5588`, records `{:expected, type, :got, …}`), `add_error/2`; `variable/1` → `{:variable, meta, name}`; `parse_expr/2`.

---

### Task 1: Two-phase parse — harvest local macro grammars into `active_macros` state

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (the `defstruct` at `:45`; `parse/2` at `:92`; add `harvest_active_macros/1`)
- Test: `test/cure/compiler/macro_use_test.exs` (create)

**Interfaces:**
- Adds `active_macros: %{}` to parser state — `%{keyword :: String.t() => [rule]}`, each `rule` the milestone-1 map. Consumed by Task 2's use-site dispatch. `parse/2`'s external contract (`{:ok, ast}` / `{:error, errors}`) is unchanged.

- [ ] **Step 1: Write the failing test** (asserts the harvest is wired — a program with a macro def parses, and the def is still present; the observable expansion lands in Task 2, so this task's test pins the two-phase parse does not *regress* single-pass output).

```elixir
# test/cure/compiler/macro_use_test.exs
defmodule Cure.Compiler.MacroUseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "two-phase parse still returns the macro def unchanged (no regression from single-pass)" do
    # A module with only a macro def: the harvest pass must not alter the
    # authoritative parse's output for the def itself.
    node = parse!("mod M\n  macro Now\n    syntax now becomes Clock.now()\n")
    # The macro def survives inside the module container.
    assert has_macro_def?(node)
  end

  defp has_macro_def?({:macro_def, _, _}), do: true
  defp has_macro_def?({_t, _m, children}) when is_list(children), do: Enum.any?(children, &has_macro_def?/1)
  defp has_macro_def?(_), do: false
end
```

- [ ] **Step 2: Run it — expect PASS already** (the current single-pass parse returns the macro def; this test is a *pin* that the Step-3 two-phase refactor keeps it). Run: `mix test test/cure/compiler/macro_use_test.exs` → PASS.

- [ ] **Step 3: Add the `active_macros` field and the two-phase `parse/2`**

Change the defstruct (parser.ex:45):

```elixir
  defstruct [:tokens, :file, pos: 0, errors: [], emit_events: false, active_macros: %{}]
```

Refactor `parse/2` (parser.ex:92) to run a harvest pass then an authoritative pass:

```elixir
  def parse(tokens, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    emit? = Keyword.get(opts, :emit_events, true)

    # Phase 1 (harvest): parse once with NO active macros, keep only the local
    # macro grammars. Use-sites may mis-parse here; we discard everything but
    # the {:macro_def, …} nodes and their (recovered) errors.
    harvest_state = %__MODULE__{tokens: tokens, file: file, emit_events: false}
    {harvest_exprs, _harvest_state} = parse_program(harvest_state)
    active = harvest_active_macros(harvest_exprs)

    # Phase 2 (authoritative): parse with active_macros seeded so use-sites expand.
    state = %__MODULE__{tokens: tokens, file: file, emit_events: emit?, active_macros: active}
    {exprs, state} = parse_program(state)

    ast =
      case exprs do
        [single] -> single
        many -> {:block, [line: 1, col: 1], many}
      end

    if emit?, do: Events.emit(:parser, :parse_complete, ast, Events.meta(file, 1))

    case state.errors do
      [] -> {:ok, ast}
      errors -> {:error, Enum.reverse(errors)}
    end
  end

  # Collect every local macro rule, indexed by the rule's leading keyword, from
  # a parsed top-level expr list. Descends into containers (a `macro` inside a
  # `mod` is still a local macro of that module).
  defp harvest_active_macros(exprs) do
    exprs
    |> collect_macro_defs()
    |> Enum.reduce(%{}, fn {:macro_def, _meta, rules}, acc ->
      Enum.reduce(rules, acc, fn rule, acc2 ->
        Map.update(acc2, rule.keyword, [rule], &(&1 ++ [rule]))
      end)
    end)
  end

  defp collect_macro_defs(node) when is_list(node), do: Enum.flat_map(node, &collect_macro_defs/1)
  defp collect_macro_defs({:macro_def, _, _} = m), do: [m]
  defp collect_macro_defs({_t, _m, children}) when is_list(children), do: collect_macro_defs(children)
  defp collect_macro_defs(_), do: []
```

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_use_test.exs` → PASS.

- [ ] **Step 5: Full parser suite — no regression**

Run: `mix test test/cure/compiler/` → all pass (627+ passed). The harvest pass is internal; external `parse/2` output is unchanged for macro-free code.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_use_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): two-phase parse harvests local macro grammars (SP1 T5)"
```

---

### Task 2: Use-site dispatch + zero-hole expansion (`now` → `Clock.now()`)

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (the `:identifier` clause in `parse_prefix/1`; add `parse_macro_use/2`, `expand_rule/2`)
- Test: `test/cure/compiler/macro_use_test.exs` (extend)

**Interfaces:**
- Produces: at a use-site of a zero-segment rule, the rule's `template` AST directly (no holes). `parse_macro_use/2` returns `{expanded_ast, state}`. `expand_rule/2` takes `(rule, bindings :: %{name => ast})` and returns the template with `{:variable, _, holename}` occurrences replaced by `bindings[holename]` — for a zero-hole rule, the template unchanged.
- **Reserved-keyword guard.** The new dispatch clause is inserted as the FIRST clause of `parse_prefix/1`'s `case token.value do` — before the existing hard-coded `"assert_type"`, `"rewrite"`, `"sup"`, `"app"`, `"with"`, `"macro"` clauses (verified at parser.ex:292-352). `is_map_key(state.active_macros, name)` alone does not protect those forms: a local macro whose `keyword` happens to be `"sup"` (say) would be harvested into `active_macros["sup"]` with nothing to stop it, and the new first-checked clause would then intercept every `sup` token in the module before the real `"sup" -> case peek_at(state, 1) do ...` clause is ever reached — silently disabling the supervisor container for the rest of that module (no error emitted; `sup Worker` would parse as a macro expansion instead of `{:container, [container_type: :supervisor, ...], ...}`). This must be closed in this task, since this task is what introduces the dispatch. Fixed by excluding the six reserved names from macro eligibility at the dispatch site (see Steps 5-7 below).



- [ ] **Step 1: Write the failing test**

```elixir
  test "a zero-hole local macro use-site expands to its template" do
    # `now` is defined as a macro; a later `now` use-site expands to Clock.now().
    node =
      parse!("mod M\n  macro Now\n    syntax now becomes Clock.now()\n  fn f() = now\n")
    # Find `f`'s body; it must be the expanded Clock.now() call, not a bare
    # `{:variable, _, "now"}`.
    body = find_fn_body(node, "f")
    assert {:function_call, meta, _} = body
    assert Keyword.get(meta, :name) in ["Clock.now", "now"]  # Clock.now() call shape
    refute match?({:variable, _, "now"}, body)
  end

  # Walk to a function_def's body by name.
  defp find_fn_body({:function_def, meta, [body]}, name) do
    if to_string(Keyword.get(meta, :name)) == name, do: body, else: nil
  end
  defp find_fn_body({_t, _m, children}, name) when is_list(children),
    do: Enum.find_value(children, &find_fn_body(&1, name))
  defp find_fn_body(_, _), do: nil
```

Note: **verified against `lib/cure/compiler/parser.ex` and by running the parser directly** — Cure's function-definition keyword is `fn`, not `def` (`lib/cure/compiler/lexer.ex:47-58`'s `@keywords` has no `"def"` entry; `def` lexes as a plain `:identifier` with no special dispatch). Confirmed empirically: `Parser.parse` on `"mod M\n  def f() = now\n"` yields `{:variable, _, "def"}` followed by a sibling `{:assignment, _, [{:function_call, [name: "f", ...], []}, {:variable, _, "now"}]}` — never a `{:function_def, ...}` node. `"mod M\n  fn f() = now\n"` correctly yields `{:function_def, [name: "f", params: [], visibility: :public, arity: 0, ...], [{:variable, _, "now"}]}` (see `parse_fn_def/3`, parser.ex:2393-2500, the `%Token{type: :assign}` branch at :2453-2461). `find_fn_body/2` as written matches this confirmed shape — no further "confirm before running" step is needed; the test sources above already use `fn`.

- [ ] **Step 2: Run it — expect FAIL** (the `now` use-site currently parses as `{:variable, _, "now"}`; no dispatch consults `active_macros`).

Run: `mix test test/cure/compiler/macro_use_test.exs` → the new test FAILs.

- [ ] **Step 3: Add use-site dispatch + expansion**

In `parse_prefix/1`'s `:identifier` `case token.value do`, add a FIRST-CHECKED clause (before the specific soft-keyword names, so a macro keyword wins) — but guard on membership so non-macro identifiers are unaffected:

```elixir
          name when is_map_key(state.active_macros, name) ->
            parse_macro_use(state, name)
```

(Place this as the first clause of the `case token.value do`. `state` is in scope in `parse_prefix/1`.)

Add the expansion functions near `parse_macro_def/1`:

```elixir
  # A use-site of an active macro keyword. Milestone-2 handles a single rule per
  # keyword with zero holes; multi-rule / hole matching is Task 3.
  defp parse_macro_use(state, keyword) do
    [rule | _] = Map.fetch!(state.active_macros, keyword)
    state = advance(state)  # consume the keyword token
    # Zero-hole rule: no segments to match; expand the template with no bindings.
    expanded = expand_rule(rule, %{})
    {expanded, state}
  end

  # Substitute hole bindings into a rule's template: replace any
  # `{:variable, _, name}` whose `name` is a bound hole with its bound AST.
  # A zero-hole rule (empty bindings) returns the template unchanged.
  defp expand_rule(rule, bindings) do
    subst_holes(rule.template, bindings)
  end

  defp subst_holes({:variable, _meta, name} = v, bindings) do
    case Map.fetch(bindings, name) do
      {:ok, arg} -> arg
      :error -> v
    end
  end

  defp subst_holes({t, meta, children}, bindings) when is_list(children) do
    {t, meta, Enum.map(children, &subst_holes(&1, bindings))}
  end

  defp subst_holes(other, _bindings), do: other
```

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_use_test.exs` → PASS.

- [ ] **Step 5: Write the failing reserved-keyword-collision test**

```elixir
  test "a local macro cannot claim a reserved dispatch keyword (sup stays the supervisor container)" do
    # `sup` is one of parse_prefix/1's existing :identifier soft-keyword names
    # (parser.ex:292-352). A macro rule that claims it must NOT be able to
    # shadow the supervisor container: `sup Worker` (no body needed — an
    # empty sup block is valid, see parse_sup_block/1) must still produce it.
    node =
      parse!("mod M\n  macro Trap\n    syntax sup becomes Clock.now()\n  sup Worker\n")

    assert has_supervisor?(node)
  end

  defp has_supervisor?({:container, meta, _}),
    do: Keyword.get(meta, :container_type) == :supervisor
  defp has_supervisor?({_t, _m, children}) when is_list(children),
    do: Enum.any?(children, &has_supervisor?/1)
  defp has_supervisor?(_), do: false
```

- [ ] **Step 6: Run it — expect FAIL** (with the Step 3 dispatch clause as written, `"sup"` was harvested into `active_macros` with no exclusion, so the new first-checked clause intercepts the `sup Worker` line as a macro use before `parse_supervisor/1` ever runs; the resulting tree has no `:supervisor` container).

Run: `mix test test/cure/compiler/macro_use_test.exs` → the new test FAILs.

- [ ] **Step 7: Add the reserved-keyword exclusion**

Add a module attribute next to `@definition_keywords` (parser.ex:50-64) — NOT inside a function body, since `@`-attributes must be registered at module scope before use:

```elixir
  # Names parse_prefix/1's :identifier case already dispatches on via a
  # hard-coded clause (the soft-keyword container forms sup/app/macro/with,
  # plus the assert_type/rewrite builtins). A local macro can never claim one
  # of these: the guarded macro-use clause below is checked FIRST, so an
  # unguarded collision would silently disable the existing form for the rest
  # of the module with no error raised. Reserved names simply keep today's
  # soft-keyword behavior; they are never macro-usable.
  @reserved_macro_keywords ~w(assert_type rewrite sup app with macro)
```

Then tighten the Step 3 dispatch clause to exclude them:

```elixir
          name when is_map_key(state.active_macros, name) and name not in @reserved_macro_keywords ->
            parse_macro_use(state, name)
```

- [ ] **Step 8: Run the test file — expect PASS** (both the zero-hole test and the reserved-keyword test).

Run: `mix test test/cure/compiler/macro_use_test.exs` → PASS.

- [ ] **Step 9: Full parser suite — no regression** (the dispatch is guarded by `is_map_key(state.active_macros, name) and name not in @reserved_macro_keywords`, empty/excluded for all existing code, so non-macro identifiers and every existing soft-keyword form are untouched).

Run: `mix test test/cure/compiler/` → all pass.

- [ ] **Step 10: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_use_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): zero-hole local macro use-site expansion (SP1 T6a)"
```

---

### Task 3: Hole matching + template substitution + progress (`every <t: Duration>` use-site)

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_macro_use/2`; add `match_segments/4`)
- Test: `test/cure/compiler/macro_use_test.exs` (extend)

**Interfaces:**
- `match_segments(state, segments, bindings, progress)` walks the rule's `segments` against the use-site tokens: a `{:lit, w}` must match the next token's value (else a failure with the progress reached); a `{:hole, %{name}}` binds `name` to a `parse_expr` result. Returns `{:ok, bindings, progress, state}` or `{:error, progress, state}`. **Progress** = count of segments consumed — the syntax-parse "how far did we get" used to pick the maximal failure when multiple rules share a keyword (deferred multi-rule selection is noted; single-rule keyword uses it for the failure message).
- **Test-coverage note:** the Step 3 implementation below (written as a single `parse_macro_use`/`match_segments` change) exercises three distinct outcomes — hole-binding, literal-segment match, and literal-segment mismatch/error-recovery. All three need their own named red test *before* Step 3 is written, per strict TDD; a single hole-matching test would leave the `{:lit, w}` match arm and the entire `{:error, progress, state}` recovery arm (parser.ex-to-be, the `add_error(state, {:macro_use_mismatch, ...})` + synthetic-token recovery) uncovered dead code. Step 1 below writes all three.

- [ ] **Step 1: Write the three failing tests**

```elixir
  test "a one-hole local macro use-site binds the hole and substitutes it" do
    node =
      parse!(
        "mod M\n  macro Every\n    syntax every <t: Code> becomes Timer.repeat(t)\n  fn f() = every 500\n"
      )
    body = find_fn_body(node, "f")
    # every 500  ==>  Timer.repeat(500)
    assert {:function_call, meta, [arg]} = body
    assert Keyword.get(meta, :name) in ["Timer.repeat", "repeat"]
    assert {:literal, _, 500} = arg
  end

  test "a two-literal-segment local macro use-site matches both literals" do
    # `say hello` has no hole at all: keyword "say", one literal segment
    # "hello". Verified (pre-milestone-2 baseline) that without segment
    # matching, "hello" is left unconsumed and becomes a stray third sibling
    # in the module container alongside macro_def and fn f() — segment
    # matching must consume it so the container has exactly the two real
    # top-level forms.
    node =
      parse!(
        "mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say hello\n"
      )
    {:container, _meta, children} = node
    assert length(children) == 2
    body = find_fn_body(node, "f")
    assert {:function_call, meta, []} = body
    assert Keyword.get(meta, :name) in ["Clock.now", "now"]
  end

  test "a macro use-site literal-segment mismatch records a :macro_use_mismatch error" do
    # `say` is defined expecting the literal "hello" next; using it with
    # "goodbye" must fail the segment match and record an error rather than
    # silently mis-expanding.
    {:ok, tokens} =
      Lexer.tokenize(
        "mod M\n  macro Say\n    syntax say hello becomes Clock.now()\n  fn f() = say goodbye\n",
        emit_events: false
      )

    assert {:error, errors} = Parser.parse(tokens, emit_events: false)
    assert Enum.any?(errors, &match?({:macro_use_mismatch, "say", :at_segment, 0, _, _}, &1))
  end
```

(Uses hole kind `Code` and arg `500` to avoid the not-yet-built `Duration` literal machinery, which is T4. The literal-segment tests use a hole-free rule so they don't depend on T4 either.)

- [ ] **Step 2: Run all three — expect FAIL**

- Test 1 FAILs: `parse_macro_use` ignores segments; `every`'s hole isn't matched, so `500` isn't bound/substituted — the `t` in the template stays an unbound `{:variable, _, "t"}`.
- Test 2 FAILs: `parse_macro_use` ignores segments entirely, so `say hello`'s trailing `hello` is never consumed — `length(children) == 2` sees 3 (macro_def, fn f(), and the stray `hello`), confirmed against the current parser: `Parser.parse` on this exact source yields a 3-child container with `{:variable, _, "hello"}` as the third child.
- Test 3 FAILs: `parse_macro_use` never calls `match_segments`, so no `:macro_use_mismatch` error is ever recorded; `Parser.parse` returns `{:ok, ast}`, and `assert {:error, errors} = ...` raises a `MatchError`.

Run: `mix test test/cure/compiler/macro_use_test.exs` → FAIL (all three new tests).

- [ ] **Step 3: Implement segment matching in `parse_macro_use/2`**

```elixir
  defp parse_macro_use(state, keyword) do
    [rule | _] = Map.fetch!(state.active_macros, keyword)
    state = advance(state)  # consume the keyword token

    case match_segments(state, rule.segments, %{}, 0) do
      {:ok, bindings, _progress, state} ->
        {expand_rule(rule, bindings), state}

      {:error, progress, state} ->
        t = peek(state)
        state =
          add_error(
            state,
            {:macro_use_mismatch, keyword, :at_segment, progress, t.line, t.col}
          )
        # Recover: yield the bare keyword variable so the outer parse continues.
        {variable(%Cure.Compiler.Token{type: :identifier, value: keyword, line: t.line, col: t.col}), state}
    end
  end

  defp match_segments(state, [], bindings, progress), do: {:ok, bindings, progress, state}

  defp match_segments(state, [{:lit, w} | rest], bindings, progress) do
    tok = peek(state)
    if to_string(tok.value) == w do
      match_segments(advance(state), rest, bindings, progress + 1)
    else
      {:error, progress, state}
    end
  end

  defp match_segments(state, [{:hole, %{name: name}} | rest], bindings, progress) do
    {arg, state} = parse_expr(state, 0)
    match_segments(state, rest, Map.put(bindings, name, arg), progress + 1)
  end
```

Note: `parse_expr(state, 0)` for a hole greedily parses a full expression. For milestone 2 (holes are the trailing/only argument, e.g. `every <t>`), that is correct. A hole followed by a literal segment (`every <n> ms`) needs a bounded parse; that refinement is deferred with T4's `literal` rules — add a plan note, do not silently mis-handle. For this task all test rules have a single trailing hole.

- [ ] **Step 4: Run all three — expect PASS**

Run: `mix test test/cure/compiler/macro_use_test.exs` → PASS (all three).

- [ ] **Step 5: Full parser suite — no regression**

Run: `mix test test/cure/compiler/` → all pass.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_use_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): local macro use-site hole matching + substitution + progress (SP1 T6b)"
```

---

## Milestone boundary

Tasks 1–3 deliver **local macro expansion**: a `macro` defined in a module, then used
(zero-hole or single-trailing-hole), expands to its substituted template as surface AST
that the elaborator re-checks — the first point a user macro *does something*. Full
parser suite green.

**Remaining SP1 tasks** (subsequent Stage-2 increments):
- **T7 — hygiene:** `<fresh Name>` gensym in templates; capture-avoidance so a
  template-introduced name cannot capture a use-site name. (Milestone-2 expansion is
  unhygienic; a template that binds names needs T7 before it is safe.)
- **T4 — `literal` rules + numeric-suffix lexer** (`500ms`): the one lexer change; also
  unblocks bounded hole+literal segment matching (the `every <n> ms` case noted in Task 3).
- **T8 — feed expansion through parse→elaborate; assert it kernel-checks** (green + a red
  ill-typed-expansion fixture → rejected-not-unsound). The re-elaboration is the
  soundness guarantee (TCB delta zero).
- **T9 — cross-module (imported) macros + import scoping + same-keyword conflict;
  two-pass name resolution** (macro-derived names visible before the def).

Each is a task with a named red test, following the pattern above. SP2 (Tier 3 + the
self-proving typed-error obligations) begins once SP1's tasks are executed + code-reviewed
+ the full suite is green.

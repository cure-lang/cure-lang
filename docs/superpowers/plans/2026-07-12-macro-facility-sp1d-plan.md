# SP1 T7 — Template Hygiene: `<fresh Name>` Gensym Primitive — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4). Steps use `- [ ]`. Strict red-green TDD; commit per task. Builds on milestone 2 (local macro use-site expansion) + T8 (soundness firewall).

**Goal:** Give macro authors a hygiene primitive: `<fresh Name>` in a `becomes` template mints a per-expansion **gensym**, so a name a template introduces (e.g. a `let` binder) cannot capture — or be captured by — a use-site identifier of the same spelling. This closes the proven capture bug (below) for authors who opt in.

**Architecture:** Expansion is a parse-time surface rewrite (milestone 2). `<fresh Name>` is parsed (in template/prefix position) to a `{:fresh_name, meta, name}` marker. At each use-site expansion, a **freshening pass** runs *before* hole substitution: it collects the distinct fresh names a template declares, mints one deterministic gensym per name (`name$N`, `N` from a monotonic counter in parser state — build determinism per design §5), and rewrites both the markers and plain template references of those names to the gensym. Hole args (use-site material) are substituted *after* freshening, so their identifiers are never freshened. **TCB delta zero** — still surface-AST-to-surface-AST, re-elaborated by the unchanged kernel (guarded by the T8 firewall).

**Tech Stack:** Elixir; `lib/cure/compiler/parser.ex`; ExUnit.

## Global Constraints

- **TCB delta ZERO.** Only `lib/cure/compiler/parser.ex` (+ tests). No `lib/cure/core/*`, no `lib/cure/elab/*`.
- **Ghost commits** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. `git add -- <path>`, never `-A`.
- **One build at a time.** Scoped `mix test test/cure/compiler/macro_hygiene_test.exs`; `mix test test/cure/compiler/` for regression.
- **Run mix from the worktree root** (`.claude/worktrees/core-let-binder`), NEVER the parent clone.
- **Tests immutable once green.**

## The proven capture bug (grounding — probed live, not assumed)

Milestone-2 expansion is deliberately unhygienic. Verified live: the macro
```
mod M
  macro AddTmp
    syntax addtmp <e: Code> becomes let tmp = 100 in e + tmp
  fn f(tmp: Int) -> Int = addtmp tmp
```
expands `f`'s body to (real AST, `mix run` probe):
```
{:block, _, [
  {:assignment, [let: true,...], [{:variable,_,"tmp"}, {:literal,_,100}]},
  {:binary_op, [operator: :+,...], [{:variable, [line: 4,...], "tmp"}, {:variable, [line: 3,...], "tmp"}]}]}
```
The first `tmp` of `tmp + tmp` (line 4 — the **hole-substituted** use-site arg, meant to be the parameter) is now **captured** by the template's `let tmp = 100`. So `f(tmp) = addtmp tmp` computes `100 + 100` regardless of its argument. `<fresh Name>` lets the author write `let <fresh g> = 100 in e + g` so the binder can't capture the arg.

**Verified parser facts (probed):**
- `<fresh g>` tokenizes as `:lt`, `:identifier "fresh"`, `:identifier "g"`, `:gt` (a 4-token window; `fresh` is NOT a reserved keyword).
- The `becomes` template is parsed via `parse_expr(state, 0)` at `parser.ex:4120` (in `parse_macro_rule/1`); a `let`-binder pattern is parsed via `parse_expr(state, 6)` inside `parse_let/1`. Both route through `parse_prefix/1` (`parser.ex:381`).
- `parse_prefix/1` has **no `:lt` case**; a bare `:lt` in prefix position hits the default clause (`parser.ex:560-563`) → `{:unexpected_token, :lt, …}`. Infix `<` (comparisons `a < b`) is handled in infix position and never reaches `parse_prefix`, so adding a prefix `:lt` case cannot affect comparisons.
- The `:lbrace` case (`parser.ex:545-554`) is the exact windowed-lookahead-then-fall-through idiom to mirror.
- Expansion lives at `parse_macro_use/2` → `expand_rule/2` → `subst_holes/2` (`parser.ex:195-221`, plus the meta-walking `subst_holes_meta` added by the T8 review `6e01715`). Parser state `defstruct` is at `parser.ex:45` (currently `[:tokens, :file, pos: 0, errors: [], emit_events: false, active_macros: %{}]`).

## Scope note

This task delivers the **explicit** `<fresh Name>` primitive (design §5's named mechanism, cited for generated container names like `fsm <fresh Tick>`). **Automatic** full hygiene (auto-renaming *every* template-introduced binder with no author annotation, per §5's headline) requires template scope analysis over all binding forms (let, lambda, match-arm patterns, fn params, fsm binders) and is a larger, separate effort — deferred to **T7b** with its own plan. `<capture Name>` (the deliberate-capture escape, §5/§11.12) is also deferred. Rationale: `<fresh Name>` is tractable, testable, and gives authors the tool to write capture-free templates today; auto-hygiene's scope-correct reference renaming is high-risk and warrants its own grounded plan.

---

### Task 1: Parse `<fresh Name>` to a `{:fresh_name, meta, name}` marker

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (add a `:lt` case in `parse_prefix/1`, before the default clause at `:560`)
- Test: `test/cure/compiler/macro_hygiene_test.exs` (create)

**Interfaces:**
- Produces: `{:fresh_name, [line: l, col: c], name :: String.t()}` for a `<fresh Name>` window in prefix position. Consumed by Task 2's freshening pass. Non-`<fresh …>` `:lt` prefixes keep today's `{:unexpected_token, :lt, …}` behavior exactly.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/macro_hygiene_test.exs
defmodule Cure.Compiler.MacroHygieneTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    Parser.parse(tokens, emit_events: false)
  end

  # Find the first {:fresh_name, _, _} anywhere in an AST. A macro's rule is
  # stored as a plain Elixir map (`%{template: ..., segments: ..., ...}`),
  # not an AST tuple, so the generic tuple-recursion clause below can never
  # reach a rule's `:template` on its own (verified live: without this clause,
  # find_fresh/1 returns nil even after <fresh Name> parses correctly, because
  # {:macro_def, _, [%{...}]}'s child is a bare map, which matches neither the
  # :fresh_name clause nor the {_t,_m,ch} tuple clause). Unwrap it explicitly.
  defp find_fresh(%{template: t}), do: find_fresh(t)
  defp find_fresh({:fresh_name, _, _} = f), do: f
  defp find_fresh({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &find_fresh/1)
  defp find_fresh(_), do: nil

  test "a <fresh Name> in a becomes template parses to a {:fresh_name, meta, name} marker" do
    {:ok, ast} =
      parse("mod M\n  macro G\n    syntax g becomes let <fresh h> = 100 in h\n")
    assert {:fresh_name, _meta, "h"} = find_fresh(ast)
  end
end
```

- [ ] **Step 2: Run it — expect FAIL** (no `:lt` prefix case; `<fresh h>` errors, so `parse` returns `{:error, …}` and the `{:ok, ast} =` match raises / no fresh_name node).

Run: `mix test test/cure/compiler/macro_hygiene_test.exs` → FAIL.

**Verified live (with Task 1's Step 3 diff temporarily applied, then reverted):**
parsing `"mod M\n  macro G\n    syntax g becomes let <fresh h> = 100 in h\n"` correctly
yields `{:fresh_name, [line: 3, col: 26], "h"}` nested inside the rule map's
`:template` — confirming the implementation below is correct — but `find_fresh/1`
without the `%{template: t}` clause returns `nil` for this AST regardless of
whether Task 1 is implemented (a macro rule's fields live in a bare Elixir map,
not an AST tuple, so the generic recursion never reaches `:template`). The
`find_fresh` fix above is therefore load-bearing, not cosmetic: without it Step 4
below cannot pass no matter how Step 3 is implemented.

- [ ] **Step 3: Add the `:lt` prefix case**

In `parse_prefix/1`'s `case token.type do`, add before the default `_ ->` clause (mirroring the `:lbrace` idiom):

```elixir
      # `<fresh Name>` — a template hygiene marker minting a per-expansion
      # gensym (design §5). Only this exact window is special; every other
      # leading `<` keeps its previous unexpected-token error. Infix `<`
      # (comparisons) never reaches this prefix clause.
      :lt ->
        case {peek_at(state, 1), peek_at(state, 2), peek_at(state, 3)} do
          {%Token{type: :identifier, value: "fresh"}, %Token{type: :identifier, value: name},
           %Token{type: :gt}} ->
            node = {:fresh_name, [line: token.line, col: token.col], name}
            state = state |> advance() |> advance() |> advance() |> advance()
            {node, state}

          _ ->
            error = {:unexpected_token, token.type, token.line, token.col}
            state = add_error(state, error)
            {error_node(token), advance(state)}
        end
```

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_hygiene_test.exs` → PASS.

- [ ] **Step 5: Full parser suite — no regression** (comparisons `a < b` unaffected — infix; bare-`<` prefix errors unchanged).

Run: `mix test test/cure/compiler/` → all pass.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_hygiene_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): parse <fresh Name> template hygiene marker (SP1 T7)"
```

---

### Task 2: Freshen `<fresh Name>` to a per-expansion gensym (capture-free)

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (defstruct `:45`; `parse_macro_use/2` and `expand_rule/2` at `:195`; add `freshen/2`, `collect_fresh_names/1` + `collect_fresh_names_meta/1` + `collect_fresh_names_value/1`, `apply_freshening/2` + `apply_freshening_meta/2` + `apply_freshening_value/2`)
- Test: `test/cure/compiler/macro_hygiene_test.exs` (extend)

**Interfaces:**
- Adds `fresh_counter: 0` to parser state — a monotonic per-parse counter making gensyms deterministic (build determinism, §5).
- `freshen(template, state)` → `{freshened_template, state}`: mints one gensym per distinct declared fresh name (`"#{name}$#{n}"`), rewrites markers and plain references, threads the counter. Runs **before** `subst_holes/2`.
- `expand_rule/2` becomes `expand_rule/3` `(rule, bindings, state)` → `{ast, state}` so the counter threads out to the caller.

- [ ] **Step 1: Write the failing test**

```elixir
  # Find fn body by name (function_def carries name in meta, body as [body]).
  defp fn_body({:function_def, meta, [body]}, name),
    do: if(to_string(Keyword.get(meta, :name)) == name, do: body)
  defp fn_body({_t, _m, ch}, name) when is_list(ch), do: Enum.find_value(ch, &fn_body(&1, name))
  defp fn_body(_, _), do: nil

  test "a <fresh> template binder is gensym'd so it cannot capture a same-named use-site arg" do
    # addg's template binds `g` via <fresh g>; the use-site passes its own `g`
    # (the parameter) as the hole. After expansion the binder must be a fresh
    # name (not "g"), distinct from the substituted parameter `g`, so no capture.
    {:ok, ast} =
      parse(
        "mod M\n  macro AddG\n    syntax addg <e: Code> becomes let <fresh g> = 100 in e + g\n  fn f(g: Int) -> Int = addg g\n"
      )

    body = fn_body(ast, "f")
    # body = let <gensym> = 100 in g + <gensym>
    {:block, _, [assign, plus]} = body
    {:assignment, _, [{:variable, _, binder}, _]} = assign
    {:binary_op, _, [{:variable, _, lhs}, {:variable, _, rhs}]} = plus

    # binder was freshened away from "g"
    refute binder == "g"
    # the hole-substituted param stays "g" (NOT captured/freshened)
    assert lhs == "g"
    # the template's own reference `g` was freshened to match the binder
    assert rhs == binder
    # and there is no leftover unexpanded marker ANYWHERE in the expanded body
    # (not just at the binder position destructured above — reuses Task 1's
    # find_fresh/1, which walks the full tree including node meta).
    refute find_fresh(body)
  end
```

Note: the prior destructure (`{:assignment, _, [{:variable, _, binder}, _]} = assign`)
already forces a `MatchError` — i.e. a red failure — if the binder position still
holds a raw `{:fresh_name, _, _}` marker, so this is not the only guard against a
leftover marker. But that destructure only inspects the binder's position; `find_fresh`
additionally covers markers hiding elsewhere in the tree (e.g. under node `meta`,
mirroring how Task 1's helper already looks past plain children). Keeping both keeps
the test's failure mode precise (a MatchError pinpoints the binder; a bare `refute`
failure at the last line means the marker survived somewhere else).

- [ ] **Step 2: Run it — expect FAIL** (Task 1 parses `<fresh g>` to a `{:fresh_name}` marker but expansion does not freshen yet: the binder stays a `{:fresh_name, _, "g"}` node, so `{:assignment, _, [{:variable, _, binder}, _]}` does not match / `binder == "g"` is not established).

Run: `mix test test/cure/compiler/macro_hygiene_test.exs` → the new test FAILs.

- [ ] **Step 3: Implement freshening in expansion**

Add `fresh_counter: 0` to the defstruct (`parser.ex:45`):

```elixir
  defstruct [:tokens, :file, pos: 0, errors: [], emit_events: false, active_macros: %{}, fresh_counter: 0]
```

Thread state through `parse_macro_use/2`'s success arm and rewrite `expand_rule` (`parser.ex:195-208`):

```elixir
  defp parse_macro_use(state, keyword) do
    [rule | _] = Map.fetch!(state.active_macros, keyword)
    state = advance(state)

    case match_segments(state, rule.segments, %{}, 0) do
      {:ok, bindings, _progress, state} ->
        expand_rule(rule, bindings, state)

      {:error, progress, state} ->
        t = peek(state)

        state =
          add_error(
            state,
            {:macro_use_mismatch, keyword, :at_segment, progress, t.line, t.col}
          )

        {variable(%Cure.Compiler.Token{
           type: :identifier,
           value: keyword,
           line: t.line,
           col: t.col
         }), state}
    end
  end

  # Freshen the template (gensym its <fresh> names) BEFORE substituting holes, so
  # use-site hole material is never freshened. Returns {expanded_ast, state}.
  defp expand_rule(rule, bindings, state) do
    {freshened, state} = freshen(rule.template, state)
    {subst_holes(freshened, bindings), state}
  end

  # Mint one deterministic gensym per distinct declared fresh name, then rewrite
  # markers and plain references of those names. Counter lives in parser state so
  # gensyms are stable within a build (design §5) and unique across use-sites.
  defp freshen(template, state) do
    names = collect_fresh_names(template) |> MapSet.to_list() |> Enum.sort()

    {rename, state} =
      Enum.reduce(names, {%{}, state}, fn n, {m, s} ->
        {Map.put(m, n, "#{n}$#{s.fresh_counter}"), %{s | fresh_counter: s.fresh_counter + 1}}
      end)

    {apply_freshening(template, rename), state}
  end

  defp collect_fresh_names({:fresh_name, _meta, name}), do: MapSet.new([name])

  defp collect_fresh_names({_t, meta, ch}) when is_list(ch) do
    Enum.reduce(ch, collect_fresh_names_meta(meta), fn c, acc ->
      MapSet.union(acc, collect_fresh_names(c))
    end)
  end

  defp collect_fresh_names(_), do: MapSet.new()

  # Fresh markers can hide in meta (e.g. a match-arm guard), same reason
  # subst_holes walks meta (T8 review 6e01715). A meta VALUE can itself be a
  # raw list of AST nodes rather than a single tuple -- e.g. a `with`
  # rematch-arm's `:parent_patterns` (`{:with_rematch_arm, [parent_patterns:
  # [pat1, pat2, ...], pattern: p], [body]}`, confirmed real and exercised by
  # test/cure/compiler/with_parse_test.exs:121 -- `Keyword.fetch!(m1,
  # :parent_patterns)` returns a bare list). subst_holes_meta_value splits on
  # is_tuple/is_list for exactly this reason; mirror it here via
  # collect_fresh_names_value, or a `<fresh Name>` used as a with-rematch
  # parent pattern is invisible to collection (never gets a gensym) and its
  # raw marker then leaks unrewritten into the final AST -- the kernel has no
  # `:fresh_name` node, so this would silently violate the "zero TCB delta,
  # still surface-AST-to-surface-AST" invariant for that one construct.
  defp collect_fresh_names_meta(meta) when is_list(meta) do
    Enum.reduce(meta, MapSet.new(), fn
      {_k, v}, acc -> MapSet.union(acc, collect_fresh_names_value(v))
      _, acc -> acc
    end)
  end

  defp collect_fresh_names_meta(_), do: MapSet.new()

  defp collect_fresh_names_value(v) when is_tuple(v), do: collect_fresh_names(v)

  defp collect_fresh_names_value(v) when is_list(v),
    do: Enum.reduce(v, MapSet.new(), &MapSet.union(&2, collect_fresh_names_value(&1)))

  defp collect_fresh_names_value(_), do: MapSet.new()

  # Rewrite: a marker becomes a variable of its gensym; a plain variable whose
  # name is a declared fresh name becomes its gensym; everything else recurses
  # (children AND meta, mirroring subst_holes).
  defp apply_freshening({:fresh_name, meta, name}, rename),
    do: {:variable, meta, Map.get(rename, name, name)}

  defp apply_freshening({:variable, meta, name} = v, rename) do
    case Map.fetch(rename, name) do
      {:ok, g} -> {:variable, meta, g}
      :error -> v
    end
  end

  defp apply_freshening({t, meta, ch}, rename) when is_list(ch),
    do: {t, apply_freshening_meta(meta, rename), Enum.map(ch, &apply_freshening(&1, rename))}

  defp apply_freshening(other, _rename), do: other

  defp apply_freshening_meta(meta, rename) when is_list(meta) do
    Enum.map(meta, fn
      {k, v} -> {k, apply_freshening_value(v, rename)}
      other -> other
    end)
  end

  defp apply_freshening_meta(meta, _rename), do: meta

  defp apply_freshening_value(v, rename) when is_tuple(v), do: apply_freshening(v, rename)

  defp apply_freshening_value(v, rename) when is_list(v),
    do: Enum.map(v, &apply_freshening_value(&1, rename))

  defp apply_freshening_value(v, _rename), do: v
```

Note: a fresh name that collides with a hole name (e.g. `<fresh e>` when `e` is also a hole) would freshen the hole's references before substitution — an author error. This is out of scope for T7 (single trailing holes, distinct names in all tests); T7b's grounding should add a collision diagnostic. Do NOT silently mis-handle: leave a plan note, do not add speculative code.

**Reviewer addendum (verified live):** `collect_fresh_names_meta`/`apply_freshening_meta`
now delegate to `collect_fresh_names_value`/`apply_freshening_value`, mirroring
`subst_holes_meta_value`'s `is_tuple`/`is_list` split exactly (parser.ex:237-239) —
without this split, a meta value that is itself a raw list of AST nodes (confirmed
real: `with`-rematch's `:parent_patterns`, per `with_parse_test.exs:121`) bypasses
both collection and rewriting, since neither the `{:fresh_name,...}` clause nor the
`{t, meta, ch}` tuple clause of `apply_freshening`/`collect_fresh_names` can match a
bare Elixir list. A `<fresh Name>` written as a with-rematch parent pattern inside a
template would otherwise reach the elaborator as a raw, unrecognized `:fresh_name`
node. No new dedicated test is added for this specific edge case (constructing a
typed with-rematch scenario purely inside a one-line `becomes` template is disproportionate
scope for T7); the fix is a direct structural mirror of already-proven code
(`subst_holes_meta_value`), not new speculative logic, and Task 2's existing
`refute find_fresh(body)` assertion (added above) would catch a regression in the
common case even though it doesn't exercise this specific list-meta path.

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_hygiene_test.exs` → PASS (both Task-1 and Task-2 tests).

- [ ] **Step 5: Full parser suite — no regression**

Run: `mix test test/cure/compiler/` → all pass. Then confirm the milestone-2 macro tests still pass (expansion of non-`<fresh>` templates is unchanged: `collect_fresh_names` returns ∅, `freshen` is identity, counter untouched):

Run: `mix test test/cure/compiler/macro_use_test.exs` → all pass.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_hygiene_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): freshen <fresh Name> template binders to per-expansion gensym (SP1 T7)"
```

---

## Task boundary + what remains in SP1

T7 delivers the `<fresh Name>` hygiene primitive: authors can mint capture-free
template binders. Combined with the T8 firewall (expansion is kernel-checked),
a `<fresh>`-using template is both hygienic (author-controlled) and sound.

**Remaining SP1 tasks** (subsequent Stage-2 rounds):
- **T7b — automatic hygiene:** auto-rename *every* template-introduced binder (no annotation) via template scope analysis; `<capture Name>` escape. The larger §5 headline; own grounded plan.
- **T4 — `literal` rules + numeric-suffix lexer** (`500ms`); unblocks bounded hole+literal segment matching.
- **T9 — cross-module (imported) macros + import scoping + same-keyword conflict.**

When T7b/T4/T9 are executed + code-reviewed, run SP1's Stage 6 (full `mix test`), update the state file, and start **SP2** (Tier 3 + self-proving typed-error obligations).

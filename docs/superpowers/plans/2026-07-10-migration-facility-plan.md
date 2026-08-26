# Migration Facility + `cure migrate` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a lossless, extensible source-migration facility to the Cure compiler — a rule registry with two consumers (`cure build` warn-and-tolerate; a new `cure migrate` command that rewrites files in place) built on a comment-preserving whole-file reprint.

**Architecture:** Approach A (whole-file canonical reprint). Make `Cure.Compiler.Printer` total over the AST; add a token-anchored **trivia** model (comments + blank-lines attached to AST-node `meta` by a single post-parse pass) so the Printer round-trips losslessly; add a `Cure.Migrate` rule registry; expose it via `cure build` (warn) and `cure migrate` (rewrite, gated by a git-clean guard + batch atomicity).

**Tech Stack:** Elixir (mix project `cure`), ExUnit tests, the existing hand-rolled Pratt `Cure.Compiler.{Lexer,Parser,Printer}`, `cli.ex` command dispatch, `git` shelled out via `System.cmd/3`.

## Global Constraints

- **Compiler is Elixir**; escript built via `mix escript.build`. Run tests with `mix test`.
- **Source of truth spec:** `docs/superpowers/specs/tooling/2026-07-10-migration-facility-implementation-design.md`. Every task's requirements implicitly include it.
- **Lossless is mandatory** — every comment survives a rewrite; an unplaced trivia item is a hard error, never a silent drop (spec §5.2).
- **AST shape is fixed:** Metastatic 3-tuples `{type, meta, children_or_value}`; `meta` is a keyword list. Trivia lives in `meta` under new keys (`:leading`, `:trailing`, `:trailer`) — **no tuple-shape change** (spec §4.2).
- **Blank-line policy (spec §5.4), fully opinionated:** top of file 0 blanks; bottom exactly 1; exactly 1 between top-level defs; inside a block cap runs at 1 and trim adjacent to open/close; normalization applies to statement lists only, not arbitrary expression spans (§5.4.5).
- **One registry, two consumers, identical per-file `ctx`** (spec §5.5): a rule fires in `cure build` warn-mode on exactly the inputs `cure migrate` rewrites — **with one explicit, spec-mandated exception** (spec §5.5's `if/elif→pickup` seed-rule note, option (a)): a legacy conditional inside a round-paren context (a call argument, a bare grouped expression, etc.) always **warns** (the user should still be told to modernize it) but is deliberately **not rewritten** (rewriting it would produce output that fails to reparse) — so for that one input shape, `fired` is true while `rewritten` is false. This is a documented, intentional carve-out, not a bug; see Task 8's paren-context note and Task 10's exception test.
- **Git discipline:** all work stays on branch `autopilot/migration-facility` in worktree `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/migration-facility`. Commit per task. **No co-authored-by trailer** (project rule: commits are the user's alone).
- **One build/test run at a time** — never launch concurrent `mix test` runs.
- **Tests are set in stone once written and passing green.** Every task below follows write-red-test → confirm-fail → implement → confirm-pass → commit. Once a test in this plan is green, the *only* legitimate way to keep it green through a later task's changes is to change implementation code — never delete it, `@tag :skip` it, loosen its assertions, or rewrite it to match whatever the code currently does. The sole exception is a test later *proven* wrong (a bug in the test itself, or a misunderstanding of the intended behavior it encodes) — and that requires stating explicitly why the test is wrong and what the correct behavior is before touching it, not "it's failing and editing it is faster than fixing the code."
- **v1 scope note:** `cure fmt` keeps its existing Algebra formatter (`Cure.Compiler.Formatter.format_algebra`); this plan does NOT rewire `cure fmt` onto the trivia Printer. The trivia Printer powers `cure migrate` only. (Spec §4.1 states the trivia Printer "is *also* the engine behind `cure fmt`" as part of Approach A's eventual payoff, and §5.1's pipeline diagram shows a `cure fmt` row using it too — but the spec's own authoritative, sequenced build order, §6, contains exactly 4 phases and does not include a `cmd_fmt` rewiring step anywhere in them, nor does §7's testing strategy name a `cure fmt` gate. Read together, §4.1/§5.1 describe Approach A's target architecture/rationale; §6 is what this plan actually commits to building. This plan follows §6: `cure fmt` rewiring is real future work, not silently in scope here.)

---

## File Structure

**New files:**
- `lib/cure/compiler/printer/unprintable_node_error.ex` — exception raised by the Printer catch-all (Phase 1).
- `lib/cure/compiler/trivia.ex` — `Cure.Compiler.Trivia`: post-parse trivia attachment pass + `carry/2` helper (Phase 2).
- `lib/cure/migrate.ex` — `Cure.Migrate`: registry, `run/2`, warning struct (Phase 3).
- `lib/cure/migrate/rule.ex` — `Cure.Migrate.Rule` struct (Phase 3).
- `lib/cure/migrate/rules/if_elif_to_pickup.ex` — first seed rule (Phase 3).
- `lib/cure/migrate/rules/uppercase_type_var.ex` — second seed rule (Phase 3).
- `lib/cure/migrate/rules/group_hoist.ex` — third seed rule, `@group` hoist (Phase 3, Task 9b).
- Tests: `test/cure/compiler/printer_totality_test.exs`, `test/cure/compiler/trivia_test.exs`, `test/cure/compiler/lossless_roundtrip_test.exs`, `test/cure/migrate/rule_registry_test.exs`, `test/cure/migrate/if_elif_to_pickup_test.exs`, `test/cure/migrate/uppercase_type_var_test.exs`, `test/cure/migrate/group_hoist_test.exs`, `test/cure/migrate/warn_tolerate_parity_test.exs`, `test/cure/cli/migrate_cli_test.exs`.
- Fixture: `test/fixtures/printer_totality.cure` — exercises every surface construct (Phase 1).

**Modified files:**
- `lib/cure/compiler/printer.ex` — raise-catch-all; missing node clauses; trivia emission.
- `lib/cure/compiler/lexer.ex` — lossless-mode trivia collection to a side list.
- **`lib/cure/compiler/parser.ex` is deliberately NOT in this list** (an earlier draft of this section listed it, for exposing per-node position spans; that approach was superseded by Task 5's position-metadata-gap fix, which computes a node's effective span recursively entirely inside the new `Trivia` module instead, precisely so the "no grammar change" Global Constraint holds — see Task 5's note. No task's own `Files:` block lists `parser.ex` as a Create/Modify target; this bullet exists only to head off the stale claim being reintroduced.)
- `lib/cure/cli.ex` — `["migrate" | paths]` dispatch + `cmd_migrate/2`.
- `lib/cure/compiler.ex` — warn-and-tolerate hook in `compile_string/2`'s `with` chain (after `{:ok, ast} <- parse(tokens, file, emit?)`, compiler.ex:103). **Not** `cli.ex`: `cli.ex`'s `compile_one/3` (cli.ex:517-534, the per-file worker `cmd_compile/2` calls) does not call `Parser.parse` itself — it delegates entirely to `Cure.Compiler.compile_file/2`, which calls `compile_string/2`, which is where parsing actually happens for `cure build`/`cure compile`. (The line `cli.ex:749` a naive grep for `Parser.parse` finds is real but belongs to `cmd_check/2` — the `cure check` command — not `compile_one/3`; hooking there would make migration warnings fire only on `cure check`, never on an actual build.)

---

## Phase 1 — Printer totality

**Why first:** whole-file reprint is only safe if the Printer handles every node kind. Today the catch-all (`printer.ex:536`) silently `inspect`s unknown nodes → unparseable output (spec §3 Bug 1). This phase is independently valuable (fixes `cure.rewrite` reparse breakage).

### Task 1: Printer catch-all raises instead of `inspect`

**Files:**
- Create: `lib/cure/compiler/printer/unprintable_node_error.ex`
- Modify: `lib/cure/compiler/printer.ex:536-538`
- Test: `test/cure/compiler/printer_totality_test.exs`

**Interfaces:**
- Produces: `Cure.Compiler.Printer.UnprintableNodeError` (exception; fields `:node`), raised by `Printer.quoted_to_string/2` on an unhandled node kind.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/printer_totality_test.exs
defmodule Cure.Compiler.PrinterTotalityTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Printer
  alias Cure.Compiler.Printer.UnprintableNodeError

  test "an unhandled node kind raises loudly, never silently inspects" do
    # A synthetic node kind the Printer has no clause for.
    bogus = {:definitely_not_a_real_node_kind, [line: 1, col: 1], []}

    assert_raise UnprintableNodeError, fn ->
      Printer.quoted_to_string(bogus)
    end
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/compiler/printer_totality_test.exs`
Expected: FAIL — current catch-all returns `inspect(other)` (a string), so no error is raised.

- [ ] **Step 3: Create the exception module**

```elixir
# lib/cure/compiler/printer/unprintable_node_error.ex
defmodule Cure.Compiler.Printer.UnprintableNodeError do
  @moduledoc """
  Raised when `Cure.Compiler.Printer` is asked to render an AST node kind it
  has no clause for. Whole-file reprint (migration facility, Approach A)
  requires the Printer to be total; a silent `inspect` fallback used to emit
  unparseable output (spec §3 Bug 1). Failing loudly converts a future gap
  into an immediate crash at the first offending node.
  """
  defexception [:node]

  @impl true
  def message(%__MODULE__{node: node}) do
    kind =
      case node do
        {k, _meta, _} when is_atom(k) -> inspect(k)
        _ -> "non-tuple"
      end

    pos =
      case node do
        {_k, meta, _} when is_list(meta) ->
          " at line #{Keyword.get(meta, :line, "?")}, col #{Keyword.get(meta, :col, "?")}"

        _ ->
          ""
      end

    "Printer has no clause for AST node kind #{kind}#{pos}. " <>
      "Add a `to_string/3` clause in Cure.Compiler.Printer. Node: #{inspect(node)}"
  end
end
```

- [ ] **Step 4: Change the catch-all to raise**

In `lib/cure/compiler/printer.ex`, replace the fallback at lines 536-538:

```elixir
  defp to_string(other, _depth, _indent) do
    raise Cure.Compiler.Printer.UnprintableNodeError, node: other
  end
```

Keep the binary passthrough clause immediately above it (`defp to_string(other, _depth, _indent) when is_binary(other), do: other`) unchanged. Add an `alias` if the module prefers short names; a fully-qualified `raise` is fine.

- [ ] **Step 5: Run test to verify it passes**

Run: `mix test test/cure/compiler/printer_totality_test.exs`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/compiler/printer/unprintable_node_error.ex lib/cure/compiler/printer.ex test/cure/compiler/printer_totality_test.exs
git commit -m "feat(printer): raise on unprintable node kinds instead of inspecting"
```

### Task 2: Construct-complete fixture + exhaustiveness/round-trip gate (RED)

This gate is the falsifiable "total" claim (spec §5.3 point 2, §7). It parses a fixture that exercises every surface construct, and asserts `parse → print` (a) raises nowhere, (b) reparses, (c) is a print-fixpoint. It will be RED until Task 3 fills the missing clauses.

**Files:**
- Create: `test/fixtures/printer_totality.cure`
- Modify: `test/cure/compiler/printer_totality_test.exs`

**Interfaces:**
- Consumes: `Cure.Compiler.Lexer.tokenize/2`, `Cure.Compiler.Parser.parse/2`, `Printer.quoted_to_string/1`.

- [ ] **Step 1: Build the construct-complete fixture**

Create `test/fixtures/printer_totality.cure`. It must parse cleanly and, between it and the existing in-repo corpus, exercise every non-error surface node kind. Seed it from real constructs; grow it in Task 3 as the gate reports gaps. Minimum contents (add module/imports so it parses):

```cure
mod PrinterTotality

# A pin pattern, an as-pattern, a guard, a GADT/ctor, records, lambdas,
# interface/implementation, supervisor, dependent-type surface (pi/sigma),
# a hole, with-abstraction — one of each construct the parser can build.
# (Fill from lib/std examples; each construct added here is driven by the
#  gate in Step 3 reporting its node kind as unprinted.)

fn classify(n: Int) -> String =
  match n
    ^zero -> "zero"          # :pin
    x as whole -> "some"     # :as_pattern
    _ -> "other"
```

Note: the fixture is *grown by the Task-3 loop*. Start minimal; every time the gate in Step 3 raises `UnprintableNodeError` for a node kind, ensure a construct producing that kind is present here (or in the corpus) and add its Printer clause.

- [ ] **Step 2: Write the gate test (expected RED for now)**

Append to `test/cure/compiler/printer_totality_test.exs`:

```elixir
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    ast
  end

  # Every non-error node kind the parser can construct in a *well-formed*
  # program. Error/diagnostic node kinds (produced only on parse failure)
  # are excluded — they never appear in a successfully parsed AST.
  @error_node_kinds ~w(
    error expected unexpected_token parser ok pickup_no_else pickup_else_not_last
    pickup_multiple_else lambda_block_unterminated with_multi_arity_mismatch
    named_implicit_not_in_pattern if_deprecated
  )a

  defp node_kinds(ast, acc \\ MapSet.new())
  defp node_kinds({k, _m, ch}, acc) when is_atom(k) and is_list(ch),
    do: Enum.reduce(ch, MapSet.put(acc, k), &node_kinds/2)
  defp node_kinds({k, _m, _v}, acc) when is_atom(k), do: MapSet.put(acc, k)
  defp node_kinds(l, acc) when is_list(l), do: Enum.reduce(l, acc, &node_kinds/2)
  defp node_kinds(_, acc), do: acc

  test "printer is total over the construct-complete fixture (no raise, reparses, fixpoint)" do
    file = "test/fixtures/printer_totality.cure"
    src = File.read!(file)
    ast = parse!(src, file)

    # (a) prints without raising UnprintableNodeError
    out1 = Cure.Compiler.Printer.quoted_to_string(ast)

    # (b) reparses
    ast2 = parse!(out1, file)

    # (c) print is a byte-fixpoint
    out2 = Cure.Compiler.Printer.quoted_to_string(ast2)
    assert out1 == out2
  end

  test "the whole in-repo corpus prints without raising, reparses, and is a print-fixpoint" do
    # Spec §5.3/§7's Printer-totality gate is explicit that this applies to
    # "the whole in-repo .cure corpus", not only the synthetic fixture above:
    # "corpus parse->print never inspects a tuple and always reparses; print
    # is a fixpoint." The fixture test above proves construct-completeness
    # (it is *designed* to contain one of everything); this test proves the
    # same three properties additionally hold for every real file that
    # already exists in this repo, which is a separate, non-redundant claim
    # -- a corpus file could in principle exercise a node-kind combination,
    # ordering, or depth the hand-built fixture doesn't.
    files = Path.wildcard("lib/**/*.cure") ++ Path.wildcard("examples/**/*.cure")

    for file <- files do
      src = File.read!(file)

      with {:ok, toks} <- Lexer.tokenize(src, file: file, emit_events: false),
           {:ok, ast} <- Parser.parse(toks, file: file, emit_events: false) do
        # A successfully-parsed AST must never contain an error/diagnostic node
        # kind (those are only ever produced on parse failure, per the comment
        # on @error_node_kinds above) -- a genuine invariant this gate is
        # well-positioned to check, since it already walks every corpus file's
        # AST. This is also what actually exercises `@error_node_kinds` and
        # `node_kinds/2` in real test code (both were otherwise unused module
        # attribute/private-function definitions, which fails this project's
        # `mix test --warnings-as-errors` alias -- see mix.exs's `test` alias).
        kinds = node_kinds(ast)

        assert MapSet.disjoint?(kinds, MapSet.new(@error_node_kinds)),
               "#{file}: a successfully parsed AST contained an error node kind: " <>
                 "#{inspect(MapSet.to_list(MapSet.intersection(kinds, MapSet.new(@error_node_kinds))))}"

        # (a) must not raise UnprintableNodeError for any node the corpus exercises.
        out1 = Cure.Compiler.Printer.quoted_to_string(ast)

        # (b) reparses
        {:ok, toks2} = Lexer.tokenize(out1, file: file, emit_events: false)

        assert {:ok, ast2} = Parser.parse(toks2, file: file, emit_events: false),
               "#{file}: migrated/reprinted output failed to reparse"

        # (c) print is a byte-fixpoint
        out2 = Cure.Compiler.Printer.quoted_to_string(ast2)
        assert out1 == out2, "#{file}: print(reparse(print(ast))) != print(ast) -- not a fixpoint"
      end
    end
  end
```

- [ ] **Step 3: Run to verify it fails (surfacing the first missing clause)**

Run: `mix test test/cure/compiler/printer_totality_test.exs`
Expected: FAIL with `UnprintableNodeError` naming a node kind (e.g. `:pin`).

- [ ] **Step 4: Write the static-exhaustiveness gate (spec §5.3 point 2 / §7's second, distinct gate)**

The corpus/fixture round-trip test above (spec §7's "Printer-totality gate") only proves totality over what happens to be in today's corpus — spec §5.3 and §7 both require a **second, separate gate**: a static check that every node-kind atom the parser's grammar can construct has a matching Printer clause, independent of corpus content. (Note: this new gate does not itself consume `@error_node_kinds` or `node_kinds/2` — those are instead now exercised by Step 2's own corpus test, per the disjointness assertion added there; see that test's comment.) Append:

```elixir
  # The kinds Cure.Compiler.Printer currently has a `to_string/3` clause
  # for — derived by scanning the module's own source text, not by
  # calling it (calling it would require already knowing each kind's
  # correct arity/shape, which is circular for an exhaustiveness check).
  defp printer_handled_kinds do
    "lib/cure/compiler/printer.ex"
    |> File.read!()
    |> then(&Regex.scan(~r/defp to_string\(\{:([a-z_]+),/, &1))
    |> Enum.map(fn [_, k] -> String.to_atom(k) end)
    |> MapSet.new()
  end

  # Every node-kind atom `parser.ex` constructs as a genuine
  # `{tag, meta, children}` dispatch target (verified by hand against
  # each construction site during the 2026-07-10 plan hardening pass —
  # see the corrected Task-3 list; deliberately NOT auto-derived from a
  # blind regex over parser.ex, which cannot distinguish a real node tag
  # from an internal 2-tuple or a `meta[:kind]` value without reading
  # the surrounding code). Whoever adds a new node kind to the grammar
  # must add it here in the same commit, or this gate cannot do its job.
  @all_node_kinds ~w(
    assignment async_operation attribute_access augmented_assignment
    bin_segment binary_op block comment comprehension conditional
    container decorator early_return exception_handling filter
    function_call function_def generator import lambda list literal map
    match_arm pair pattern_match pickup pickup_clause pickup_else
    property range record_update send string_interpolation throw tuple
    type_annotation unary_op variable yield
    pin as_pattern assert_type gadt_ctor indexed_type interface
    implementation pi_type sigma_type with_abs hole forced_pattern
    child_spec binary_generator named_implicit_pat
  )a

  test "every node kind the parser can construct has a matching Printer clause (static, corpus-independent)" do
    missing = MapSet.difference(MapSet.new(@all_node_kinds), printer_handled_kinds())
    assert MapSet.to_list(missing) == [],
           "Printer is missing a to_string/3 clause for: #{inspect(MapSet.to_list(missing))}"
  end
```

- [ ] **Step 5: Run to verify it fails**

Run: `mix test test/cure/compiler/printer_totality_test.exs`
Expected: FAIL — the new test reports the same 15 missing kinds Task 3 is about to fill in (the first 40 entries in `@all_node_kinds` already pass; the last 15 do not).

- [ ] **Step 6: Commit the RED gate**

```bash
git add test/cure/compiler/printer_totality_test.exs test/fixtures/printer_totality.cure
git commit -m "test(printer): construct-complete totality + corpus + static-exhaustiveness gates (red)"
```

### Task 3: Fill missing Printer clauses (TDD loop, one node kind per iteration)

Drive entirely by the Task-2 gate. The **known missing surface node kinds** (verified 2026-07-10 against `parser.ex`: each constructed as a genuine `{tag, meta, children}` 3-tuple the Printer's `to_string/3` would receive, and confirmed absent from `printer.ex` by `grep -c "{:<kind>," lib/cure/compiler/printer.ex`) are:

```
:pin :as_pattern :assert_type :gadt_ctor :indexed_type :interface
:implementation :pi_type :sigma_type :with_abs :hole
:forced_pattern :child_spec :binary_generator :named_implicit_pat
```

(15 entries. An earlier draft of this list omitted `:named_implicit_pat` from the enumeration even though the very next paragraph already discussed it as needing a new clause — a bookkeeping slip caught during the 2026-07-10 hardening pass; it is now included so this list matches Task 2's `@all_node_kinds` exactly: 40 already-handled + these 15 = 55.)

Three of these have a **non-standard shape** relative to this plan's Global Constraint ("AST shape is fixed: Metastatic 3-tuples... `meta` is a keyword list") — verify the real shape at the cited construction site before writing the clause, do not assume the `:pin` template's shape applies uniformly:
- `:gadt_ctor` — `{:gadt_ctor, meta, sig}` (parser.ex:3227) where `sig` is itself `{:arrow_chain, [dom_or_named_dom, ...]}` (parser.ex:3251), i.e. the third position is **not a list of children**, it's a single 2-tuple wrapping the list. `:arrow_chain` and its element `:named_dom` (`{:named_dom, name, inner}` where the 2nd position is a bare **string**, not a keyword-list meta, parser.ex:3273) never escape as independent top-level Printer-dispatch targets — they only ever appear nested inside a `:gadt_ctor`'s third slot. Render them as part of the `:gadt_ctor` clause (unwrap `sig`, join with `" -> "`, render a `:named_dom` element as `"(#{name}: #{type})"`), not as their own `to_string/3` clauses.
- A named-implicit dot pattern `{:named_implicit_pat, meta, name, inner}` (parser.ex:471) is a **4-tuple**, not 3. It needs a `defp to_string({:named_implicit_pat, meta, name, inner}, depth, indent)` clause matching that exact arity; the standard `{tag, meta, children}` template does not apply verbatim. Surface form: `"{ #{name} = #{to_string(inner, depth, indent)} }"`.

The following entries appeared in an earlier draft of this list but are **not** real Printer-dispatch gaps — verified 2026-07-10 by reading their construction sites in `parser.ex` — and must NOT be treated as node kinds needing their own `to_string/3` clause:
- `:ctor` (parser.ex:1820,1834) — an internal 2-tuple `{:ctor, name}` used only inside `pattern_ctor_head/1` to group match-arm heads; never constructed as a 3-tuple.
- `:type` (parser.ex:1076-1089) — an internal 2-tuple `{:type, atom}` used only inside binary-segment-specifier parsing; already rendered via the existing `bin_segment_specifier_string/3` helper (printer.ex:1032), not a generic node.
- `:string_part` / `:expr` (parser.ex:497,500) — internal 2-tuples from string-interpolation token values, fully consumed inside `parse_string_interpolation/1` before becoming real AST nodes (`:literal` / a parsed sub-expression); the wrapping node, `:string_interpolation`, is already handled by the Printer (printer.ex:333).
- `:on_phase` (parser.ex:4487) — a `meta_acc` entry (`{:on_phase, [{phase, clauses}]}`) spliced into a `:container` node's `meta` keyword list; not a node tag.
- `:supervisor` (parser.ex:4278) — the value of `meta[:kind]` on a real `:child_spec` node (`sup Foo as bar` vs. plain `Foo as bar`); not a node tag itself. `:child_spec` (listed above) is the actual missing clause; its Printer clause must branch on `meta[:kind]` (`:supervisor` -> prefix `"sup "`, `:worker` -> no prefix) alongside `meta[:module]`/`meta[:id]`/options.
- `:variadic` / `:keyword_variadic` / `:positional` (parser.ex:2578-2621) — values of `meta[:kind]` on a real `:param` node; not node tags.
- `:param` — **already fully handled**: `typed_params_to_string/3` (printer.ex:744-761), called from `fn_def_to_string/4` (printer.ex:656, the function-definition renderer), already renders `:param` including `meta[:kind]` (variadic prefixes), `meta[:type]`, and `meta[:default]`. Do not add a redundant clause. (Two narrower, pre-existing sites — the `:lambda` clause at printer.ex:346-350 and `record_to_string/4`'s field mapper at printer.ex:810-818 — inline-destructure `:param` without honoring `kind`/`default`; if the Task-2 gate's fixture exercises a variadic lambda param or a defaulted record field and fails there, fix those two call sites to reuse `typed_params_to_string/3` rather than adding a new generic `:param` clause.)

For **each** kind in the corrected list above (and any other the gate raises on), do this five-step cycle. `:pin` is worked in full as the template; repeat similarly for the rest — deriving each node's *actual* shape from its construction site in `parser.ex` (not assumed from the `:pin` template, per the non-standard-shape note above) and its surface syntax from a real example in `lib/std/**` or `docs/`.

- [ ] **Step 1 (per kind): Write a round-trip unit test**

For `:pin` — add to `test/cure/compiler/printer_totality_test.exs`:

```elixir
  test "pin pattern round-trips as ^name" do
    src = """
    mod M
    fn f(t: Atom) -> Bool =
      match t
        ^target -> true
        _ -> false
    """

    ast = parse!(src, "pin.cure")
    out = Cure.Compiler.Printer.quoted_to_string(ast)
    assert out =~ "^target"
    # and it reparses
    assert _ = parse!(out, "pin.cure")
  end
```

- [ ] **Step 2 (per kind): Run to confirm RED**

Run: `mix test test/cure/compiler/printer_totality_test.exs -k "pin pattern"`
Expected: FAIL with `UnprintableNodeError` for `:pin`.

- [ ] **Step 3 (per kind): Find the node shape and add the clause**

Find the construction site: `grep -n "{:pin," lib/cure/compiler/parser.ex`. The pin node is `{:pin, meta, [inner_expr]}` where `inner_expr` is the pinned variable. Add a clause to `printer.ex` (place it near the other pattern clauses, before the fallback):

```elixir
  # -- Pin pattern -----------------------------------------------------------
  defp to_string({:pin, _meta, [inner]}, depth, indent) do
    "^" <> to_string(inner, depth, indent)
  end
```

For each other kind, the clause is analogous: read the parser construction site to learn the children layout, read a real source example to learn the surface syntax, write the clause. Do NOT guess — verify the shape against `parser.ex` and the surface against a `.cure` example.

- [ ] **Step 4 (per kind): Run to confirm GREEN**

Run: `mix test test/cure/compiler/printer_totality_test.exs`
Expected: the per-kind test passes; the gate advances to the next missing kind (or passes fully when none remain).

- [ ] **Step 5 (per kind): Commit**

```bash
git add lib/cure/compiler/printer.ex test/cure/compiler/printer_totality_test.exs test/fixtures/printer_totality.cure
git commit -m "feat(printer): render <kind> node to surface syntax"
```

- [ ] **Loop exit:** repeat Steps 1–5 until `mix test test/cure/compiler/printer_totality_test.exs` is fully green (the fixture round-trip gate, the corpus gate, AND the static-exhaustiveness gate from Task 2 Step 4 — three tests total). Then run the full suite once: `mix test`. Expected: green. Commit any incidental fixes.

---

## Phase 2 — Trivia model

Make comments + blank-lines survive a reprint (spec §5.2). Trivia is collected by the lexer, attached to AST nodes by a new pass, and emitted by the Printer.

### Task 4: Lexer collects positioned trivia to a side list

**Files:**
- Modify: `lib/cure/compiler/lexer.ex` (add lossless trivia collection alongside existing `preserve_comments`)
- Test: `test/cure/compiler/trivia_test.exs`

**Interfaces:**
- Produces: `Lexer.tokenize(src, file: f, trivia: true)` returns `{:ok, tokens, trivia}` where `trivia` is an ordered list of `{:comment, text, line, col} | {:doc_comment, text, line, col} | {:blank, count, line}`. When `trivia:` is absent/false, behavior is unchanged (`{:ok, tokens}`).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/trivia_test.exs
defmodule Cure.Compiler.TriviaTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Lexer

  test "lexer collects every comment and blank run as positioned trivia" do
    src = """
    mod M

    # leading comment
    fn f() -> Int = 1  # trailing comment
    """

    {:ok, _tokens, trivia} = Lexer.tokenize(src, file: "t.cure", trivia: true)

    texts = for {:comment, t, _l, _c} <- trivia, do: String.trim(t)
    assert "leading comment" in texts
    assert "trailing comment" in texts
    assert Enum.any?(trivia, &match?({:blank, _, _}, &1))
  end

  test "a blank line that contains only indentation whitespace still counts as blank" do
    # Pins the fix for reusing lex_indentation/1's own blank-line branch
    # (lexer.ex:210-231, which strips leading whitespace via measure_indent/1
    # BEFORE checking for end-of-line) rather than a fresh "newline-only line"
    # definition that would miss this case. The blank line between `x` and `y`
    # below has two leading spaces (mirroring the block's own indent), which a
    # naive "line is exactly empty" check would fail to classify as blank.
    src = "mod M\nfn f() -> Int =\n  let x = 1\n  \n  x\n"

    {:ok, _tokens, trivia} = Lexer.tokenize(src, file: "t2.cure", trivia: true)

    assert Enum.any?(trivia, &match?({:blank, _, _}, &1)),
           "a whitespace-only blank line was not collected as trivia: #{inspect(trivia)}"
  end
end
```

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/compiler/trivia_test.exs`
Expected: FAIL — `tokenize/2` returns a 2-tuple, no `trivia` element.

- [ ] **Step 3: Implement trivia collection**

In `lib/cure/compiler/lexer.ex`: add a `trivia: false` option (mirroring `preserve_comments`). When `trivia: true`, accumulate every comment (`#`, `##`, `###`) and every run of blank lines into a `trivia` accumulator on the lexer state as positioned items (reuse the existing comment-emission sites at `lexer.ex:255,265,376,386,441`; the position is already known there). **Do not track blank runs by a fresh "newline-only line" definition of your own** — reuse the lexer's own existing blank-line branch instead. `lex_indentation/1` (lexer.ex:210-231) already calls `measure_indent/1` to consume the line's leading whitespace *first*, and only then checks whether the next char is `\n`/`\r`/EOF (lexer.ex:216-217) to decide the line is blank — meaning a line containing only spaces (common: many editors preserve a block's indentation on an otherwise-empty line) is already treated as blank by this exact check, not just a literally zero-character line. A "consecutive newline-only lines" counter written fresh, without reading this branch, would plausibly miss whitespace-only blank lines and undercount a blank run, corrupting the `{:blank, count, line}` item the trivia model (Task 5) and blank-line policy (Task 6) both depend on. Increment the trivia accumulator's blank-run counter inside this existing branch (lexer.ex:216-231) rather than introducing a second, parallel definition of "blank" elsewhere. Return `{:ok, tokens, Enum.reverse(state.trivia)}` from the public `tokenize/2` when `trivia: true`; keep the existing `{:ok, tokens}` return otherwise. (Keep `preserve_comments` untouched for existing callers.)

**Note on `##` doc comments (verified 2026-07-10, not a blocker):** `:doc_comment` tokens (`##`/`###`) are, unlike plain `#` comments, **unconditionally** emitted into the main token stream regardless of `preserve_comments`/`trivia` (lexer.ex:253-257, 371-375 — no `_if_enabled` gate). The parser independently consumes them from that main stream via a pre-existing mechanism (`collect_all_doc_comments`/`collect_leading_docs`, parser.ex:5182-5199, 5420-5459) that stashes the docstring text into a node's `meta`. This new trivia accumulator collects the *same* `##` text a second time, into the separate lexer-side `trivia` list — but this does not create a double-print risk today, because `printer.ex` never reads that pre-existing doc-comment meta back out (confirmed: zero references to `:doc`/`doc_comment` anywhere in `printer.ex`) — it is dead, write-only data as far as printing is concerned. The new trivia-attachment path (Tasks 5-6) becomes the sole thing that actually reprints `##` comments; nothing needs to change about the parser's existing doc-collection to avoid conflict.

- [ ] **Step 4: Run to verify it passes**

Run: `mix test test/cure/compiler/trivia_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/lexer.ex test/cure/compiler/trivia_test.exs
git commit -m "feat(lexer): collect positioned comment/blank trivia in trivia mode"
```

### Task 5: `Cure.Compiler.Trivia` attachment pass (total by construction)

**Files:**
- Create: `lib/cure/compiler/trivia.ex`
- Test: `test/cure/compiler/trivia_test.exs`

**Interfaces:**
- Produces: `Cure.Compiler.Trivia.attach(ast, trivia_list) :: ast` — returns the AST with each trivia item placed in a node's `meta[:leading]` / `meta[:trailing]` / `meta[:trailer]`. Raises `Cure.Compiler.Trivia.UnplacedTriviaError` (fields `:item`) if any item cannot be placed (spec §5.2 "total by construction").
- Produces: `Cure.Compiler.Trivia.carry(from_node, to_node) :: to_node` — moves `from_node`'s attached leading/trailing/trailer trivia onto `to_node` (for restructuring rules, spec §5.2).

Attachment rule (spec §5.2): an item on the **same line** as, and **after**, a node's last token → that node's `:trailing`. Otherwise → the `:leading` of the next node that starts at or after the item's line. An item after the last child of a container (program, block, branch body, fsm state) with no following sibling → that container's `:trailer`. Attach to the **innermost** enclosing container.

**Position-metadata gap (verified 2026-07-10, load-bearing for a correct implementation — and a correction to spec §4.2's own claim that meta is "already carrying `line`/`col`/`subtype`" universally):** the rule above presumes every node's own `meta` carries `line:`/`col:`, letting attachment read a node's span directly off its own meta. That premise is **false for many real, common node kinds** — confirmed via `grep -noE '\{:[a-z_]+, \[[^]]*\],' lib/cure/compiler/parser.ex | grep -v "line:"`, which surfaces dozens of construction sites with no `line`/`col` key at all, including some that are mainline, everyday syntax: **`:pair`** (parser.ex:932,944,954 — i.e. *every entry of every map/record literal*, `%{k: v, ...}`), **`:match_arm`** (parser.ex:1768 etc.), **`:generator`**/**`:filter`** (comprehensions), **`:param`** (parser.ex:2648), **`:tuple`** (parser.ex:3855,3926,4529), **`:record_update`**, **`:child_spec`**, **`:pi_type`**/**`:sigma_type`**, and the `{:variable, [scope: :local], name}` shape `parse_type_atom/1` builds for every bare type-position identifier. A comment adjacent to any of these cannot be classified by reading that node's own meta — there is nothing there to read.

Do **not** attempt to patch each of these sites individually in `parser.ex` (that list is not guaranteed exhaustive, and missing even one silently reintroduces the gap for whatever real `.cure` file happens to hit it — several of the kinds above, e.g. `:pair`, are exercised by ordinary map/record literals throughout `lib/std/`). Instead, `attach/2`'s position-index step must compute a node's **effective span recursively**: if a node's own `meta` has `line:`/`col:`, use that; otherwise, its effective start is its **first child's** effective start (recursively) and its effective end is its **last child's** effective end (recursively).

**A residual leaf case the recursive-children fallback alone does NOT cover (also verified 2026-07-10):** a lambda parameter node, `{:param, [], name}` (parser.ex:2648, built by `parse_lambda_params/1` — distinct from the top-level function-param `:param` built elsewhere, which does carry richer meta but was not verified to include `line`/`col` either), has an empty `meta` **and** a bare string (not a children list) as its third element — a true leaf with zero position information anywhere in its own subtree, so there is nothing to recurse into. Lambdas are common Cure syntax, so this is a live path, not a hypothetical: `attach/2` must not crash or infinite-loop when it hits one. The correct handling: such a positionless, childless leaf contributes **no boundary information** to trivia classification — skip it entirely when building the position index (treat it as transparent/invisible for the "which gap does this trivia item fall into" comparison) and let the trivia item attach to whichever positioned ancestor or sibling actually encloses it, per the normal innermost-enclosing-container rule above. This is a fallback of last resort, not the common case — most positionless nodes (`:pair`, `:match_arm`, `:tuple`, etc.) do have positioned descendants and should use the recursive-children rule first.

This makes span computation total over the AST (every node either has its own position, a derivable one from children, or is treated as transparent) without touching `parser.ex` at all, consistent with this plan's Global Constraint of no grammar change.

**Blank-run items classify by the same rule, leading-only:** a `{:blank, count, line}` item can never be `:trailing` (a blank line by definition contains no token for it to trail), so it always becomes part of the `:leading` list of the next node starting at or after `line`, or the enclosing container's `:trailer` if none follows — interleaved with `:comment`/`:doc_comment` items in source order within the same list (do not maintain a separate blank-items list; spec §5.4 point 5 requires blank trivia to be "attached ... like any other trivia").

**Spec §5.4 point 5 is a distinct requirement from point 4 and is NOT covered by Task 6's blank-line-policy step as currently scoped — this needs its own step.** Point 4 ("inside a block body: cap runs at 1 ... otherwise preserve the author's 0-or-1") governs blank lines *between statements/clauses in a statement list* (top-level defs, block bodies) and is a **normalize-on-print** policy — the Printer computes it from the join position, not from reading back attached trivia verbatim. Point 5 governs a *different* case entirely: blank-line trivia that falls **inside a single multi-line expression that isn't a statement list at all** — e.g. a record/map/list literal or a call-argument list spanning several lines has no "block" for point 4 to apply to. Point 5's explicit requirement: such blank trivia is attached via `attach/2` exactly like any other trivia (per this task) and the Printer (Task 6) must emit it **unchanged** — not capped, not collapsed, not injected if absent. Task 6 must implement both behaviors and must not conflate them: when joining a statement list, consult attached `:blank` items only to decide 0-vs-≥1 (already-capped per point 4); when rendering the interior of a non-statement-list multi-line expression (map/record/list/call-arg), print any attached `:blank` item's `count` verbatim. Failing to implement the point-5 case at all would silently regress the exact "Bug 2" (trivia silently dropped) this whole model exists to prevent — for blank lines specifically inside multi-line literals, which are common in `lib/std/*.cure` record/map definitions.

- [ ] **Step 1: Write the failing tests (incl. nested-block trailer + totality)**

```elixir
  # append to test/cure/compiler/trivia_test.exs
  alias Cure.Compiler.{Parser, Trivia}
  alias Cure.Compiler.Trivia.UnplacedTriviaError

  defp attach(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    Trivia.attach(ast, trivia)
  end

  test "leading comment attaches to the following definition" do
    ast = attach("mod M\n\n# doc\nfn f() -> Int = 1\n", "a.cure")
    leadings =
      ast |> collect_meta(:leading) |> List.flatten() |> Enum.map(&elem(&1, 1)) |> Enum.map(&String.trim/1)
    assert "doc" in leadings
  end

  test "comment after last statement of a nested block lands in that block's trailer" do
    src = """
    mod M
    fn f() -> Int =
      let x = 1
      x
      # nested trailer
    """
    ast = attach(src, "b.cure")
    trailers =
      ast |> collect_meta(:trailer) |> List.flatten() |> Enum.map(&elem(&1, 1)) |> Enum.map(&String.trim/1)
    assert "nested trailer" in trailers
  end

  test "trailing comment on a map-literal pair attaches correctly (pair nodes carry no line/col of their own)" do
    # Exercises the recursive-children span fallback: `:pair` (parser.ex:932,
    # 944, 954) has empty meta, so its effective end must be derived from its
    # value child's position, not read off the pair node itself.
    src = "mod M\nfn f() -> Int =\n  let m = %{x: 1, y: 2}  # tail comment\n  1\n"
    ast = attach(src, "pair.cure")
    trailings =
      ast |> collect_meta(:trailing) |> List.flatten() |> Enum.map(&elem(&1, 1)) |> Enum.map(&String.trim/1)
    assert "tail comment" in trailings
  end

  test "a comment near a lambda with a positionless param leaf does not crash attach/2" do
    # Exercises the transparent-leaf fallback: a lambda `:param` node
    # (parser.ex:2648, `{:param, [], name}`) has no meta AND no children list
    # (its 3rd element is a bare string), so it contributes no position of its
    # own and must not be recursed into.
    src = "mod M\nfn f() -> Int =\n  let g = fn (x) -> x\n  # after the let\n  g(1)\n"
    ast = attach(src, "lambda.cure")
    texts =
      ((ast |> collect_meta(:trailer) |> List.flatten()) ++ (ast |> collect_meta(:leading) |> List.flatten()))
      |> Enum.map(&elem(&1, 1))
      |> Enum.map(&String.trim/1)
    assert "after the let" in texts
  end

  test "attachment is total: an item that cannot be placed raises, never drops" do
    # NOTE on what this input is and isn't: a single node, even an empty
    # container like `{:block, meta, []}`, is NOT a valid forcing input here
    # — per the attachment rule above, an item after the last child of a
    # container (vacuously true for an empty one) with no following sibling
    # belongs to THAT container's `:trailer`, so a spec-compliant `attach/2`
    # would place it, not raise.
    #
    # Correction (2026-07-10 hardening pass): a bare `[]` here does NOT
    # represent "an entirely empty parsed file", as an earlier draft of this
    # comment claimed. Verified against `Cure.Compiler.Parser.parse/2`
    # (parser.ex:92-113): its public return is never a bare list — it wraps
    # zero-or-many top-level expressions as `case exprs do [single] ->
    # single; many -> {:block, [line: 1, col: 1], many} end`, so an empty
    # file parses to `{:ok, {:block, [line: 1, col: 1], []}}` (an empty
    # *block node*, which per the paragraph above would take the trivia as
    # its `:trailer`, not raise). Consequently, no output of a real
    # `Parser.parse/2` call — for any source, including an empty one — ever
    # gives `Trivia.attach/2` an ast with zero nodes/containers to attach
    # to; `UnplacedTriviaError` is a pure defense-in-depth invariant for
    # this pipeline's actual inputs, not a path any real `.cure` file is
    # expected to trigger.
    #
    # `Trivia.attach([], ...)` below is instead a direct, synthetic unit
    # test of `attach/2`'s own recursive contract: per this plan's Global
    # Constraint and its own helper functions elsewhere (e.g. `node_kinds/2`
    # and `collect_meta/3` above both have a `when is_list(l)` clause),
    # a bare Elixir list is an anticipated *recursive-position* AST shape
    # (a children list, or — as here — a top-level list of zero AST
    # fragments with no enclosing node of its own) even though it is never
    # what `Parser.parse/2`'s public API hands back at the top level. Calling
    # `attach/2` directly with `[]` exercises that base case in isolation:
    # zero nodes exist for the trivia item to become a `:leading` on, and
    # there is no container node's `meta` to hold it as a `:trailer` either
    # — genuinely nothing to attach to, hence the raise.
    assert_raise UnplacedTriviaError, fn ->
      Trivia.attach([], [{:comment, "orphan", 1, 1}])
    end
  end

  # helper: collect all values of a given meta key across the AST
  defp collect_meta(ast, key, acc \\ [])
  defp collect_meta({_k, m, ch}, key, acc) when is_list(m) and is_list(ch) do
    acc = if v = Keyword.get(m, key), do: [v | acc], else: acc
    Enum.reduce(ch, acc, &collect_meta(&1, key, &2))
  end
  defp collect_meta({_k, m, _v}, key, acc) when is_list(m) do
    if v = Keyword.get(m, key), do: [v | acc], else: acc
  end
  defp collect_meta(l, key, acc) when is_list(l), do: Enum.reduce(l, acc, &collect_meta(&1, key, &2))
  defp collect_meta(_, _key, acc), do: acc
```

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/compiler/trivia_test.exs`
Expected: FAIL — `Cure.Compiler.Trivia` does not exist.

- [ ] **Step 3: Implement the attachment pass**

Create `lib/cure/compiler/trivia.ex`. Implement `attach/2` as: (1) build a position index of nodes from the AST using the **effective-span algorithm from the position-metadata-gap note above** — own `meta`'s `line`/`col` if present; else recurse into first/last child; else (a positionless, childless leaf, e.g. a lambda `:param`) treat the node as transparent and contributing no boundary; (2) for each trivia item in source order, classify trailing vs leading vs container-trailer by the rule above; (3) place it, threading placement back into the node's `meta`; (4) track placed items in a set — after the walk, if any item is unplaced, `raise UnplacedTriviaError, item: item`. Also create the `UnplacedTriviaError` exception (define it in the same file or a sibling). Implement `carry/2` to move `:leading`/`:trailing`/`:trailer` keys from one node's meta to another's (concatenating if the target already has some).

- [ ] **Step 4: Run to verify it passes**

Run: `mix test test/cure/compiler/trivia_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/trivia.ex test/cure/compiler/trivia_test.exs
git commit -m "feat(trivia): total post-parse trivia attachment pass + carry helper"
```

### Task 6: Printer emits attached trivia + blank-line policy

**Files:**
- Modify: `lib/cure/compiler/printer.ex`
- Test: `test/cure/compiler/lossless_roundtrip_test.exs`

**Interfaces:**
- The Printer, when a node's `meta` carries `:leading`/`:trailing`/`:trailer`, emits them: `:leading` each on its own line at the node's indent before the node; `:trailing` as ` # …` after the node's line; a container's `:trailer` at the end of that container's body. Blank-line normalization per §5.4 points 1–4 is applied between *statement-list* entries (top-level defs, block bodies) only. Per §5.4 point 5 (see Task 5's note above), an attached `:blank` item that falls **inside a single multi-line non-statement-list expression** (a record/map/list literal or call-argument list spanning several lines) is emitted verbatim — not capped, not collapsed, not injected — since points 1–4 have no "statement list" to normalize there.

- [ ] **Step 1: Write the failing lossless round-trip gate**

```elixir
# test/cure/compiler/lossless_roundtrip_test.exs
defmodule Cure.Compiler.LosslessRoundtripTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}

  # Local helper (test modules do not share `defp` helpers across files —
  # this is NOT the same function as `PrinterTotalityTest`'s `parse!/2`,
  # it is a separate copy for this module).
  defp parse!(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    ast
  end

  defp comments(src) do
    src
    |> String.split("\n")
    |> Enum.flat_map(fn line ->
      case Regex.run(~r/#+\s?(.*)$/, line) do
        [_, txt] -> [String.trim(txt)]
        _ -> []
      end
    end)
    |> Enum.reject(&(&1 == ""))
    |> Enum.sort()
  end

  @corpus Path.wildcard("lib/std/*.cure")

  for file <- @corpus do
    @file file
    test "lossless round-trip preserves every comment: #{file}" do
      src = File.read!(@file)
      {:ok, toks, trivia} = Lexer.tokenize(src, file: @file, trivia: true)
      {:ok, ast} = Parser.parse(toks, file: @file, emit_events: false)
      out = ast |> Trivia.attach(trivia) |> Printer.quoted_to_string()

      # every comment present in the source is present in the output
      assert comments(src) -- comments(out) == []
      # and the output reparses
      assert _ = parse!(out, @file)
    end
  end

  test "a blank line inside a multi-line map literal is preserved verbatim (§5.4 point 5, not a statement list)" do
    src = """
    mod M
    fn f() -> Int =
      let m = %{
        x: 1,

        y: 2
      }
      1
    """

    {:ok, toks, trivia} = Lexer.tokenize(src, file: "blank_in_map.cure", trivia: true)
    {:ok, ast} = Parser.parse(toks, file: "blank_in_map.cure", emit_events: false)
    out = ast |> Trivia.attach(trivia) |> Printer.quoted_to_string()

    # the blank line between the two map entries survives the reprint --
    # points 1-4's statement-list normalization does not apply inside a map
    # literal (there is no enclosing block/statement-list here), so nothing
    # should collapse or inject it.
    assert out =~ ~r/x:\s*1,\s*\n\s*\n\s*y:\s*2/
    assert _ = parse!(out, "blank_in_map.cure")
  end
```

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/compiler/lossless_roundtrip_test.exs`
Expected: FAIL — the Printer does not yet emit `:leading`/`:trailing`/`:trailer`, so comments are lost (this is the §3 measurement, now a gate); the new blank-in-map test also fails since no blank-line handling exists yet at all.

- [ ] **Step 3: Implement trivia emission + blank-line policy**

In `printer.ex`: (1) at the start of rendering any node, if `meta[:leading]` is present, emit each leading item on its own line at the current indent — for a `{:blank, count, _}` item this means `count` blank lines, for a `{:comment, text, _, _}`/`{:doc_comment, text, _, _}` item this means the comment text; (2) after a node's line, if `meta[:trailing]` is present, append ` # text`; (3) in the container/statement-list join (`:block`, program body, branch bodies), after the last child emit `meta[:trailer]` items; (4) apply the §5.4 points 1-4 blank-line policy when joining *statement-list* entries specifically (0 at top, exactly 1 between top-level defs, cap-at-1-but-preserve-0 inside blocks, exactly 1 trailing at EOF) — for these joins, consult an attached `:blank` item only to decide 0-vs-≥1, never emit its raw `count` uncapped. (5) Everywhere else a `:blank` item is attached — i.e. inside a non-statement-list multi-line expression (map/record/list/call-arg literal) per §5.4 point 5 — emit its `count` verbatim instead of applying rule 4's cap. The node-kind context (statement list vs. expression span) is already known at each call site (the `:block`/program/branch-body join vs. e.g. the `:map`/`:tuple`/`:function_call`-args renderer), so this is a matter of which renderer calls which blank-emission helper, not a new AST-wide classification. Factor small `render_leading/trailing/trailer` helpers (parameterized by "capped" vs. "verbatim" blank handling) to avoid duplicating across clauses.

- [ ] **Step 4: Run to verify it passes**

Run: `mix test test/cure/compiler/lossless_roundtrip_test.exs`
Expected: PASS for the `lib/std/*.cure` corpus.

- [ ] **Step 5: Run the full suite once**

Run: `mix test`
Expected: green. Fix any Printer-output regressions in existing tests. `comment_preservation_test.exs` and `algebra_test.exs` (confirmed via `grep -n "Printer\." test/cure/compiler/*.exs`) never reference `Cure.Compiler.Printer` at all and are unaffected. The tests that actually DO exercise `Printer.quoted_to_string/1` today, and are the real candidates to check for output-format regressions, are `test/cure/compiler/melquiades_parser_test.exs`, `test/cure/compiler/pickup_test.exs`, and `test/cure/compiler/match_spec_test.exs` (confirmed by the same grep; `bin_segment_test.exs` does not use the Printer at all — despite an earlier draft of this plan claiming it did — it only exercises `Lexer`/`Parser`/`Codegen`/`BeamWriter` for `<<...>>` binary-segment syntax, per its own `alias` line).

- [ ] **Step 6: Commit**

```bash
git add lib/cure/compiler/printer.ex test/cure/compiler/lossless_roundtrip_test.exs
git commit -m "feat(printer): emit attached trivia and apply blank-line policy (lossless round-trip)"
```

---

## Phase 3 — Rule registry

One registry, two consumers (spec §5.5). Seed rules: `if/elif→pickup` and uppercase-type-var→lowercase.

### Task 7: `Cure.Migrate.Rule` struct + registry + ordered-fold `run/2`

**Files:**
- Create: `lib/cure/migrate/rule.ex`, `lib/cure/migrate.ex`
- Test: `test/cure/migrate/rule_registry_test.exs`

**Interfaces:**
- Produces: `%Cure.Migrate.Rule{id: atom, description: String.t, phase: :syntactic | :needs_resolution, detect_and_rewrite: (ast, ctx -> {:rewrite, ast} | :no_change), warning_template: String.t}`.
- Produces: `Cure.Migrate.rules() :: [Rule.t]` (declaration order) — the real seed-rule list, populated in Tasks 8, 9, and 9b.
- Produces: `Cure.Migrate.run(ast, opts) :: {ast, [warning]}` where `opts` carries `:file` and an **optional `:rules` override** (`Keyword.get(opts, :rules, rules())`, defaulting to the real registry — this override exists solely so the ordered-fold *mechanism* is unit-testable in this task, before any real rule exists); `ctx` is built from the AST alone (declared + imported type names); rules run once each as an ordered fold (spec §5.5); `warning` is `%Cure.Migrate.Warning{rule: atom, message: String.t, file: String.t, line: pos_integer}`.

**Sequencing note:** this task must NOT depend on `:W_if_elif_pickup` or `:W_uppercase_type_var` — neither rule module exists until Tasks 8/9. This task's test proves the fold/warning-collection *mechanism* using a synthetic rule constructed inline in the test, passed via the `:rules` override above, so Task 7 is a fully closable, independently-green unit.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/migrate/rule_registry_test.exs
defmodule Cure.Migrate.RuleRegistryTest do
  use ExUnit.Case, async: true
  alias Cure.Migrate
  alias Cure.Migrate.Rule

  # A synthetic rule local to this test — it proves the ordered-fold
  # mechanism (a rule's rewrite is threaded to the next rule, and a
  # `{:rewrite, _}` return produces a warning) without depending on
  # Tasks 8/9's real seed rules, which do not exist yet at this point
  # in the plan.
  @marker {:literal, [subtype: :string, injected: true], "synthetic-marker"}

  defp append_marker_rule do
    %Rule{
      id: :W_test_append_marker,
      description: "test-only: appends a marker literal",
      phase: :syntactic,
      detect_and_rewrite: fn ast, _ctx -> {:rewrite, ast ++ [@marker]} end,
      warning_template: "test marker appended"
    }
  end

  test "run threads rules as an ordered fold and returns warnings" do
    src = "mod M\nfn f(x: Int) -> Int = 1\n"
    {:ok, toks} = Cure.Compiler.Lexer.tokenize(src, file: "r.cure", emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(toks, file: "r.cure", emit_events: false)

    {new_ast, warnings} = Migrate.run(ast, file: "r.cure", rules: [append_marker_rule()])

    assert new_ast == ast ++ [@marker]
    assert Enum.any?(warnings, &(&1.rule == :W_test_append_marker))
  end
end
```

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/migrate/rule_registry_test.exs`
Expected: FAIL — `Cure.Migrate` does not exist.

- [ ] **Step 3: Implement the struct, registry, and `run/2`**

Create `lib/cure/migrate/rule.ex` (the struct + `@type`). Create `lib/cure/migrate.ex` with: `Warning` struct; `rules/0` returning `[]` for now (Tasks 8/9/9b will each register their seed rule here); `build_ctx/1` computing the per-file declared+imported type-name `MapSet` from the AST, **seeded with Cure's built-in primitive type names** (see the note below — this seeding is load-bearing, not optional); `run/2` reading `Keyword.get(opts, :rules, rules())`, folding those rules in order, each called with `(ast, ctx)`, collecting a warning (rendered from `warning_template`) whenever a rule returns `{:rewrite, _}`. `run/2` returns `{final_ast, warnings}`.

**Why `build_ctx/1` must seed primitive type names (verified 2026-07-10):** `parse_type_atom/1` (parser.ex:3281-3305) parses a bare type-position identifier — whether `Int`, `T`, or `Foo` — into the exact same node shape, `{:variable, [scope: :local], name}`. The parser makes **zero syntactic distinction** between a reference to a built-in primitive type and a free/undeclared type variable; both are equally "a bare uppercase identifier in a type position" from the AST's point of view. Task 9's uppercase-type-var rule detects exactly that shape and treats anything not in `ctx` as a free type var to rename. If `build_ctx/1` only scanned the file's own `type ... = ...` declarations and `import`/`use` list (as spec §5.5's prose alone might suggest), a file with no local type declarations — e.g. `"mod M\nfn f(x: Int) -> Int = x\n"`, which is the shape of nearly every fixture in this entire plan — would have an **empty** ctx, and the rule would incorrectly treat `Int` itself as a free uppercase type var and rename it. `build_ctx/1` must therefore start from the real built-in primitive set: `Int`, `Float`, `String`, `Bool`, `Atom`, `Unit`, `Any`, `Never`, `Char` (confirmed at `lib/cure/types/env.ex:35-44`, `Cure.Types.Env.new/0`'s `builtin_types` map). **Derive this set programmatically from `Cure.Types.Env.new/0` at runtime — do not hardcode a second, duplicate literal list of these 9 names inside `Cure.Migrate`.** Concretely: `Map.keys(Cure.Types.Env.new().types) |> MapSet.new()` (the `Env` struct's `:types` field, `env.ex:11`, is exactly this map). A copy-pasted literal list would silently drift the moment a future primitive is added to `Cure.Types.Env` without a corresponding edit here — `Cure.Migrate` sits before the elaborator (spec §5.1) and never type-checks, but calling `Env.new/0` is a pure, side-effect-free struct constructor, not a type-checking call, so this dependency is safe and carries no elaboration coupling. Union the file's own declared/imported names on top of that derived seed, never instead of it.

- [ ] **Step 4: Run to verify it passes** — `mix test test/cure/migrate/rule_registry_test.exs` → PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/migrate.ex lib/cure/migrate/rule.ex test/cure/migrate/rule_registry_test.exs
git commit -m "feat(migrate): rule struct + registry + ordered-fold run/2 with per-file ctx"
```

### Task 8: Port `if/elif → pickup` rule (with paren-context fix)

**Files:**
- Create: `lib/cure/migrate/rules/if_elif_to_pickup.ex`
- Test: `test/cure/migrate/if_elif_to_pickup_test.exs`

**Interfaces:**
- Consumes: the rewrite logic in `lib/mix/tasks/cure.rewrite.ex` (`rewrite/1`, `conditional_to_pickup/3`, `do_chain/4`).
- Produces: `Cure.Migrate.Rules.IfElifToPickup.rule() :: Rule.t` with `id: :W_if_elif_pickup`, `phase: :syntactic`.

Spec §5.5 requires resolving the known parenthesised-context reparse bug: a `{:conditional, …}` embedded inside a round-paren context must NOT be rewritten (skip it — still emit the warning), because a multi-line `pickup` block cannot live inside one and would fail to reparse.

**Why a structural "is this a `:function_call` argument" AST check cannot be the whole fix (verified 2026-07-10):** the lexer's `paren_depth` (which actually gates `:indent`/`:dedent` suppression — `lexer.ex:1379,1384`) is incremented/decremented **only** by `(`/`)` (`lexer.ex:179-180`), never by `{`/`}` or `[`/`]` — so the true condition is specifically about round-paren grammar positions, and `grep -n "expect(state, :lparen)" lib/cure/compiler/parser.ex` shows round parens are consumed at **at least six** distinct sites: function-call arguments, lambda parameter lists (parser.ex:2641), a bare grouped/precedence expression (`parse_grouped/1`, parser.ex:526-533), and others (parser.ex:2326, 3045, 3897, 4498). Worse, `parse_grouped/1` **discards the grouping entirely** — it returns `{expr, state}`, the bare inner expression, with no wrapper node recording that it was parenthesized (parser.ex:532). That means a grouped conditional used as an operand, e.g. `(if x > 0 then 1 else 2) + 1`, is **structurally indistinguishable in the AST** from a bare top-level conditional — there is no ancestor node to detect at all. No enumeration of AST shapes can fix this; the information is genuinely erased by the parser before the rule ever sees the AST.

**Fix: verify by reparse, per conditional, not by structural ancestry.** Rewrite conditionals to `pickup` **one at a time**, in a stable order (pre-order tree walk): for each `{:conditional, …}` found, build a candidate AST with just that one node replaced by its `{:pickup, …}` equivalent, render the **whole file** via `Printer.quoted_to_string/1`, and re-lex+re-parse the result. If it reparses, commit that substitution and continue to the next conditional using the updated AST; if it does not, leave that specific conditional as-is (do not commit the substitution) but still record the warning for it, and continue to the next conditional using the AST from before this attempt. This is the only approach proven correct given the information loss above — a structural check can be added as a fast-path pre-filter (skip the reparse round-trip when a conditional is a direct `:function_call` argument, since that case is already known-bad), but the reparse check must remain the actual authority, not merely a fallback for cases the structural filter happens to miss.

- [ ] **Step 1: Write failing tests (rewrite happy-path, comment preservation, paren-skip)**

```elixir
# test/cure/migrate/if_elif_to_pickup_test.exs
defmodule Cure.Migrate.IfElifToPickupTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate

  defp migrate(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {new_ast, warns} = Migrate.run(Trivia.attach(ast, trivia), file: file)
    {Printer.quoted_to_string(new_ast), warns}
  end

  # Full reparse (lex AND parse), not just tokenize -- tokenizing successfully
  # does not prove the output is syntactically valid; a malformed `pickup`
  # block could still tokenize while failing to parse. This helper is what
  # every "reparses"/"NOT rewritten ... still warns" assertion below actually
  # calls, so none of them can pass on lex-only success.
  defp reparses?(src, file) do
    with {:ok, toks} <- Lexer.tokenize(src, file: file, emit_events: false),
         {:ok, _ast} <- Parser.parse(toks, file: file, emit_events: false) do
      true
    else
      _ -> false
    end
  end

  test "top-level if/else rewrites to pickup and reparses" do
    {out, _} = migrate("mod M\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n", "a.cure")
    assert out =~ "pickup"
    assert reparses?(out, "a.cure")
  end

  test "comments on branches survive the restructuring rewrite" do
    src = "mod M\nfn f(x: Int) -> Int =\n  if x > 0 then\n    1  # positive\n  else\n    2  # non-positive\n"
    {out, _} = migrate(src, "b.cure")
    assert out =~ "positive"
    assert out =~ "non-positive"
  end

  test "conditional inside a call-argument list is NOT rewritten (paren-context), still warns" do
    src = "mod M\nfn g(x: Int) -> Int = h(if x > 0 then 1 else 2)\n"
    {out, warns} = migrate(src, "c.cure")
    refute out =~ "pickup"
    assert Enum.any?(warns, &(&1.rule == :W_if_elif_pickup))
    assert reparses?(out, "c.cure")
  end

  test "a bare-grouped conditional used as an operand is NOT rewritten either (no :function_call ancestor exists to detect structurally), still warns" do
    # `parse_grouped/1` discards the grouping node entirely (parser.ex:526-533)
    # -- this conditional has NO distinguishing ancestor in the AST at all, so
    # only a verify-by-reparse strategy (not an ancestor-shape check) catches
    # this case.
    src = "mod M\nfn g(x: Int) -> Int = (if x > 0 then 1 else 2) + 1\n"
    {out, warns} = migrate(src, "d.cure")
    refute out =~ "pickup"
    assert Enum.any?(warns, &(&1.rule == :W_if_elif_pickup))
    assert reparses?(out, "d.cure")
  end
end
```

- [ ] **Step 2: Run to verify it fails** — `mix test test/cure/migrate/if_elif_to_pickup_test.exs` → FAIL (module missing).

- [ ] **Step 3: Implement the rule**

Create `lib/cure/migrate/rules/if_elif_to_pickup.ex`. Port `cure.rewrite`'s `rewrite/1`/`conditional_to_pickup/3`/`do_chain/4`. Per the verify-by-reparse design above: find every `{:conditional, …}` in the AST (pre-order); for each one, in order, build a candidate whole-AST with only that node's `{:pickup, …}` replacement applied (using `Trivia.carry/2` so branch comments travel to the replacement node), render the candidate via `Printer.quoted_to_string/1`, and attempt `Lexer.tokenize/2` + `Parser.parse/2` on the result — commit the candidate (thread it into the AST used for the next conditional) if that succeeds, otherwise keep the original `{:conditional, …}` at that position (still record its warning) and continue with the pre-candidate AST. `detect_and_rewrite/2` returns `{:rewrite, final_ast}` if at least one conditional was actually committed, `:no_change` if every candidate failed reparse (still emit each conditional's warning regardless of commit outcome — the rule always warns on every legacy `if/elif` it finds, per the spec's "warn on exactly the inputs that would change" parity requirement in Task 10, read as "would change in an ideal world with no paren restriction," not "did change after the reparse guard"). Register `rule/0` in `Cure.Migrate.rules/0`.

- [ ] **Step 4: Run to verify it passes** — `mix test test/cure/migrate/if_elif_to_pickup_test.exs` → PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/migrate/rules/if_elif_to_pickup.ex lib/cure/migrate.ex test/cure/migrate/if_elif_to_pickup_test.exs
git commit -m "feat(migrate): if/elif->pickup rule with paren-context skip and comment carry"
```

### Task 9: Uppercase-type-var → lowercase rule

**Files:**
- Create: `lib/cure/migrate/rules/uppercase_type_var.ex`
- Test: `test/cure/migrate/uppercase_type_var_test.exs`

**Interfaces:**
- Produces: `Cure.Migrate.Rules.UppercaseTypeVar.rule() :: Rule.t` with `id: :W_uppercase_type_var`, `phase: :needs_resolution`.

Detection (spec §5.5): a *free* uppercase identifier in a type-parameter position that does NOT resolve to a known type constructor (consult `ctx`, the declared+imported type-name set). Lowercase the binder consistently across the signature. On a `T`+`t` collision, freshen with the smallest unused numeric suffix (`t` → `t1` → `t2`), recursively checked; never silently merge.

- [ ] **Step 1: Write failing tests (basic rename, ctx-respecting non-rename, T+t collision)**

```elixir
# test/cure/migrate/uppercase_type_var_test.exs
defmodule Cure.Migrate.UppercaseTypeVarTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.Migrate

  defp migrate(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {new_ast, warns} = Migrate.run(ast, file: file)
    {Printer.quoted_to_string(new_ast), warns}
  end

  test "free uppercase type var is lowercased across the signature" do
    {out, warns} = migrate("mod M\nfn id(x: T) -> T = x\n", "a.cure")
    assert out =~ "x: t"
    assert out =~ "-> t"
    refute out =~ "T"
    assert Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "an uppercase name that resolves to a declared type is left alone" do
    {out, _} = migrate("mod M\ntype Foo = Int\nfn f(x: Foo) -> Foo = x\n", "b.cure")
    assert out =~ "Foo"
  end

  test "a built-in primitive type is left alone even with no local type declaration" do
    # `Int` is parsed identically to a free type var (both are a bare
    # `{:variable, [scope: :local], name}` at parser.ex:3281-3305) and this
    # file declares/imports nothing locally -- this only stays untouched if
    # `build_ctx/1` seeds Cure's built-in primitive type names, not just
    # this file's own `type`/`import` declarations.
    {out, warns} = migrate("mod M\nfn f(x: Int) -> Int = x\n", "e.cure")
    assert out =~ "x: Int"
    assert out =~ "-> Int"
    refute Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "T and t in the same signature freshen rather than merge" do
    {out, _} = migrate("mod M\nfn f(x: T, y: t) -> T = x\n", "c.cure")
    # every occurrence of the freshened `T` binder becomes `t1` consistently...
    assert out =~ "x: t1"
    assert out =~ "-> t1"
    # ...and the pre-existing `t` binder is untouched, not merged onto
    assert out =~ "y: t)"
    refute out =~ "T"
  end

  test "freshening skips an already-used t1, landing on t2 (spec §7)" do
    {out, _} = migrate("mod M\nfn f(x: T, y: t, z: t1) -> T = x\n", "d.cure")
    # both `t` and `t1` are taken, so the freshened `T` must become `t2`,
    # not collide with either
    assert out =~ "x: t2"
    assert out =~ "-> t2"
    assert out =~ "y: t,"
    assert out =~ "z: t1)"
    refute out =~ "T"
  end
end
```

- [ ] **Step 2: Run to verify it fails** — `mix test test/cure/migrate/uppercase_type_var_test.exs` → FAIL (module missing).

- [ ] **Step 3: Implement the rule** — create the module; walk type-annotation positions; use `ctx` to distinguish free vars from known constructors; apply the consistent lowercase + freshen-on-collision scheme; register in `rules/0`.

- [ ] **Step 4: Run to verify it passes** — `mix test test/cure/migrate/uppercase_type_var_test.exs` → PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/migrate/rules/uppercase_type_var.ex lib/cure/migrate.ex test/cure/migrate/uppercase_type_var_test.exs
git commit -m "feat(migrate): uppercase-type-var->lowercase rule with ctx resolution and freshening"
```

### Task 9b: `@group(:x)` hoist rule (relocation + trivia-carry)

Added post-plan-review (operator, 2026-07-10) as the **third day-one seed rule**
(spec §5.5). It is the first *relocation* rule — it moves a decorator node
rather than transforming a node in place — so it is the load-bearing exercise of
`Trivia.carry/2` and the §5.4 blank-line policy. It supersedes the fragile
line-regex codemod at `787a9745…/scratchpad/migrate_group.exs`.

**Files:**
- Create: `lib/cure/migrate/rules/group_hoist.ex`
- Test: `test/cure/migrate/group_hoist_test.exs`

**Interfaces:**
- Consumes: `Cure.Migrate.Rule`, `Cure.Compiler.Trivia.carry/2`, `Cure.Migrate.run/2`.
- Produces: `Cure.Migrate.Rules.GroupHoist.rule() :: Rule.t` with `id: :W_group_hoist`, `phase: :syntactic`. Registered in `Cure.Migrate.rules/0`.

Behavior (spec §5.5): relocate an in-body `@group(...)` decorator to directly
above the module's `mod` declaration. Idempotent (already-above-`mod` → no
change, no warning). Comments attached to the `@group` node travel with it
(`Trivia.carry/2`); the old slot's trivia re-homes to the following sibling.

- [ ] **Step 1: Determine the AST representation and canonical target form (discovery, no code yet)**

Before writing the red test, establish how a module-level `@group` is
represented and rendered — the rule's *target output* depends on it, so this is
not optional. Run:

```bash
grep -n "group\|:decorator\|decorators" lib/cure/compiler/parser.ex | head -30
grep -n "decorator" lib/cure/compiler/printer.ex
```

Then in `iex -S mix`, parse both an in-body and an above-`mod` `@group` and
inspect the AST:

```elixir
{:ok, t1} = Cure.Compiler.Lexer.tokenize("mod M\n@group(:core)\nfn f() -> Int = 1\n", emit_events: false)
{:ok, a1} = Cure.Compiler.Parser.parse(t1, emit_events: false)
IO.inspect(a1, limit: :infinity)
{:ok, t2} = Cure.Compiler.Lexer.tokenize("@group(:core)\nmod M\nfn f() -> Int = 1\n", emit_events: false)
{:ok, a2} = Cure.Compiler.Parser.parse(t2, emit_events: false)
IO.inspect(a2, limit: :infinity)
```

Record: is a module-attached `@group` a child of the module node, a sibling
before it, or an entry in a decorator list on `mod`'s meta? What does
`Printer.quoted_to_string(a2)` emit (confirm it renders the decorator above
`mod`, and that it reparses)? The rewrite in Step 3 transforms the in-body shape
(`a1`) into the above-`mod` shape (`a2`); use the *actual* `a2` shape as the
target, not an assumed one.

- [ ] **Step 2: Write failing tests (hoist, idempotence, comment-carry)**

```elixir
# test/cure/migrate/group_hoist_test.exs
defmodule Cure.Migrate.GroupHoistTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate

  defp reparses?(src, file) do
    with {:ok, toks} <- Lexer.tokenize(src, file: file, emit_events: false),
         {:ok, _ast} <- Parser.parse(toks, file: file, emit_events: false) do
      true
    else
      _ -> false
    end
  end

  defp migrate(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {new_ast, warns} = Migrate.run(Trivia.attach(ast, trivia), file: file)
    {Printer.quoted_to_string(new_ast), warns}
  end

  test "in-body @group is hoisted to directly above mod and output reparses" do
    {out, warns} = migrate("mod M\n@group(:core)\nfn f() -> Int = 1\n", "a.cure")
    # decorator now appears before `mod`, and not after it
    assert out =~ ~r/@group\(:core\)\s*\n\s*mod\s+M/
    refute out =~ ~r/mod\s+M[\s\S]*@group\(:core\)/
    assert Enum.any?(warns, &(&1.rule == :W_group_hoist))
    assert reparses?(out, "a.cure")
  end

  test "a file already in above-mod form is unchanged and does not warn" do
    src = "@group(:core)\nmod M\nfn f() -> Int = 1\n"
    {out, warns} = migrate(src, "b.cure")
    assert out =~ ~r/@group\(:core\)\s*\n\s*mod\s+M/
    refute Enum.any?(warns, &(&1.rule == :W_group_hoist))
  end

  test "a comment on the @group line travels with the hoisted decorator (never dropped or orphaned)" do
    {out, _} = migrate("mod M\n@group(:core)  # grouping tag\nfn f() -> Int = 1\n", "c.cure")
    # the comment survives...
    assert out =~ "grouping tag"
    # ...and rides above mod with the decorator, not left stranded below it
    assert out =~ ~r/@group\(:core\).*grouping tag[\s\S]*mod\s+M/
    refute out =~ ~r/mod\s+M[\s\S]*grouping tag/
    assert reparses?(out, "c.cure")
  end
end
```

- [ ] **Step 3: Run to verify it fails**

Run: `mix test test/cure/migrate/group_hoist_test.exs`
Expected: FAIL — `Cure.Migrate.Rules.GroupHoist` does not exist.

- [ ] **Step 4: Implement the rule**

Create `lib/cure/migrate/rules/group_hoist.ex`. `detect_and_rewrite/2`: locate the
in-body `@group(...)` decorator node (using the representation found in Step 1)
and the module (`mod`) node; if the decorator is already above `mod`, return
`:no_change`. Otherwise detach the decorator from its in-body position and
reinsert it in the module-attached position that renders above `mod` (matching
the `a2` shape from Step 1), calling `Trivia.carry(old_group_node,
new_group_node)` so its leading/trailing comments travel, and re-homing the old
slot's trailer/leading trivia to the following sibling. Return `{:rewrite,
final_ast}`. Register `rule/0` in `Cure.Migrate.rules/0` (append after the
uppercase-type-var rule).

- [ ] **Step 5: Run to verify it passes**

Run: `mix test test/cure/migrate/group_hoist_test.exs`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/migrate/rules/group_hoist.ex lib/cure/migrate.ex test/cure/migrate/group_hoist_test.exs
git commit -m "feat(migrate): @group hoist relocation rule with trivia carry"
```

### Task 10: `cure build` warn-and-tolerate consumer + parity test

**Files:**
- Modify: `lib/cure/compiler.ex` (`compile_string/2`'s `with` chain, after `{:ok, ast} <- parse(tokens, file, emit?)` at compiler.ex:103)
- Test: `test/cure/migrate/warn_tolerate_parity_test.exs`

**Interfaces:**
- Consumes: `Cure.Migrate.run/2`.
- Effect: `cure build`/`compile` runs `Migrate.run/2` on the parsed AST, prints each warning to stderr, and continues compiling with the tolerated (rewritten-in-memory) AST — the file is not modified.

**Why `lib/cure/compiler.ex`, not `lib/cure/cli.ex`:** `cli.ex`'s `compile_one/3` (the per-file worker `cmd_compile/2` — i.e. `cure build`/`cure compile` — calls, cli.ex:517-534) never calls `Parser.parse` itself; it delegates entirely to `Cure.Compiler.compile_file/2` (compiler.ex:45), which calls `compile_string/2` (compiler.ex:84), where the actual parse happens. The hook must go in `compile_string/2`'s own `with` chain (compiler.ex:102-106), which today reads:
```elixir
    with {:ok, tokens} <- lex(source, file, emit?),
         {:ok, ast} <- parse(tokens, file, emit?),
         {:ok, _} <- maybe_check(ast, file, emit?, check?),
         {:ok, ast} <- maybe_optimize(ast, optimize?, optimize_opts),
         {:ok, forms, cg_warnings} <- codegen(ast, file, emit?, output_dir, declared_phases) do
```
Note this `with` chain already rebinds `ast` in a later clause (`{:ok, ast} <- maybe_optimize(ast, ...)`), confirming that inserting a new clause between `parse` and `maybe_check` that also rebinds `ast` is valid, precedented Elixir in this exact file — no new pattern is being introduced.

**Scope note — do not touch the shared `parse/3` helper or `parse_source/2`:** `parse/3` (compiler.ex:251, called by `compile_string/2`, `compile_and_load/2`, and the public `parse_source/2`) must NOT gain the migration hook itself, even though that would be the most DRY-looking chokepoint. `parse_source/2` (compiler.ex:182) is documented as returning the **"raw parser AST"** and is consumed by `Cure.Compiler.DepGraph` (lib/cure/compiler/dep_graph.ex:194) and by tests that assert on exact raw parse shapes (`test/cure/compiler/group_decorator_parse_test.exs`, `test/cure/compiler/empty_type_parse_test.exs`) — silently rewriting its output would violate that documented contract and risks breaking those tests. `compile_and_load/2` (compiler.ex:197-230, used by `cure run` and the REPL, not by `cure build`) is explicitly **out of scope for this task** — the spec (§5.1) names `cure build` specifically; wiring `cure run` the same way is a separate future decision, not silently bundled in here.

- [ ] **Step 1: Write the failing parity test**

```elixir
# test/cure/migrate/warn_tolerate_parity_test.exs
defmodule Cure.Migrate.WarnTolerateParityTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Migrate

  # The set of rules that fire (warn) equals the set that rewrite: same
  # per-file ctx, same detect_and_rewrite. Assert identical fired-rule sets.
  # NOTE: this equivalence holds for every input EXCEPT the one deliberate,
  # spec-mandated exception exercised by the second test below (a legacy
  # conditional inside a round-paren context always warns but is never
  # rewritten, since rewriting it would break reparse -- spec §5.5's
  # if/elif->pickup seed-rule note, option (a)). This test's own input is
  # chosen to NOT hit that exception, so the strict `==` holds here.
  test "warn-mode fires on exactly the inputs rewrite-mode changes (non-paren case)" do
    src = "mod M\nfn id(x: T) -> T = if x_len(x) > 0 then 1 else 2\n"
    {:ok, toks} = Lexer.tokenize(src, file: "p.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "p.cure", emit_events: false)

    {rewritten, warnings} = Migrate.run(ast, file: "p.cure")
    fired = warnings |> Enum.map(& &1.rule) |> Enum.sort()

    # rewrite happened iff a rule fired
    assert (rewritten != ast) == (fired != [])
    # both seed rules fired for this input
    assert :W_if_elif_pickup in fired
    assert :W_uppercase_type_var in fired
  end

  test "the one documented exception: a paren-embedded conditional warns without rewriting" do
    # Spec §5.5 explicitly sanctions this as option (a) for the if/elif->pickup
    # seed rule: "emit the warning but leave the source untouched, same as an
    # unmatched rule" -- for THIS specific input shape, `fired` is true while
    # `rewritten` is false, which is the one place the strict `==` above does
    # not hold. This test exists so nobody "fixes" that as a regression later.
    src = "mod M\nfn g(x: Int) -> Int = h(if x > 0 then 1 else 2)\n"
    {:ok, toks} = Lexer.tokenize(src, file: "q.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "q.cure", emit_events: false)

    {rewritten, warnings} = Migrate.run(ast, file: "q.cure")
    fired = warnings |> Enum.map(& &1.rule) |> Enum.sort()

    assert rewritten == ast
    assert :W_if_elif_pickup in fired
  end
end
```

- [ ] **Step 2: Run to verify it fails / passes at unit level** — `mix test test/cure/migrate/warn_tolerate_parity_test.exs`. (These assert registry-level parity and its one documented exception; both should pass once Tasks 7–9 are done. If they pass immediately, that's correct — the parity is structural. Keep them as regression guards.)

- [ ] **Step 3: Wire the build hook**

In `lib/cure/compiler.ex`, add a new private helper next to `parse/3` (compiler.ex:251):

```elixir
  defp migrate_warn(ast, file) do
    {ast, warnings} = Cure.Migrate.run(ast, file: file)
    Enum.each(warnings, fn w -> IO.warn("#{w.file}:#{w.line}: #{w.message}", []) end)
    {:ok, ast}
  end
```

Then in `compile_string/2`'s `with` chain (compiler.ex:102-106 today), insert a new clause between `parse` and `maybe_check`:

```elixir
    with {:ok, tokens} <- lex(source, file, emit?),
         {:ok, ast} <- parse(tokens, file, emit?),
         {:ok, ast} <- migrate_warn(ast, file),
         {:ok, _} <- maybe_check(ast, file, emit?, check?),
         {:ok, ast} <- maybe_optimize(ast, optimize?, optimize_opts),
         {:ok, forms, cg_warnings} <- codegen(ast, file, emit?, output_dir, declared_phases) do
```

so compilation proceeds on the tolerated `ast`. `compile_and_load/2` (compiler.ex:214-218) and `parse_source/2` are intentionally left untouched (see the scope note above).

- [ ] **Step 4: Run the full suite once** — `mix test`. Expected: green (no existing program regresses; warnings are informational).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler.ex test/cure/migrate/warn_tolerate_parity_test.exs
git commit -m "feat(migrate): cure build warn-and-tolerate consumer + parity guard"
```

---

## Phase 4 — `cure migrate` CLI + policy + git guard

### Task 11: Git-safety guard (preflight, precise cleanliness)

**Files:**
- Modify: `lib/cure/migrate.ex` (add `git_guard/1`)
- Test: `test/cure/cli/migrate_cli_test.exs`

**Interfaces:**
- Produces: `Cure.Migrate.git_guard(paths) :: :ok | {:error, [{path, :dirty | :untracked | :not_a_repo}]}` — **one reason per failing path**, not one reason for the whole batch: `paths` can be many files at once (Task 12's default, no-explicit-paths scan alone can resolve to the entire `lib/**/*.cure` + `test/**/*.cure` corpus), and it is entirely plausible for some of them to be untracked scratch files while others are merely dirty in the same invocation — a single `{reason, [path]}` pair cannot represent that mix without silently misreporting some paths' actual reason. Clean = `git status --porcelain -- <path>` yields empty output; tracked = `git ls-files --error-unmatch <path>` exits 0. Runs as a preflight over the whole set, classifying **every** path independently rather than stopping at the first failure.

**Working-directory gotcha (verified 2026-07-10, load-bearing — every test in this task fails without it):** `git status --porcelain -- <path>` and `git ls-files --error-unmatch <path>` are run relative to the **calling process's cwd**, not the repository containing `path`. Confirmed empirically: from an unrelated repo's checkout, `git status --porcelain -- <abs path in a different repo>` exits 128 with `fatal: <path>: '<path>' is outside repository at '<cwd's repo root>'` — it does **not** silently succeed or auto-detect the right repo from the path argument. Since `mix test` runs with cwd at this project's own root (a real git repo — `cure-lang`), and Task 11's own test fixture below creates a **separate, unrelated temp git repo** for each test (`System.cmd("git", ["init", "-q", dir])`), calling `git status`/`git ls-files` without pinning the working directory to that temp repo would make every test in this task fail with exactly that "outside repository" error, not the intended `:dirty`/`:untracked`/`:ok` result. Fix: every `System.cmd("git", [...])` call in `git_guard/1` must pass `cd: Path.dirname(path)` (confirmed empirically to resolve correctly, since git auto-discovers the repository root upward from any directory inside it) — or equivalently pass `-C <dir>` as the first git argument. Do not rely on the caller's cwd.

- [ ] **Step 1: Write failing tests using a temp git repo fixture**

```elixir
# test/cure/cli/migrate_cli_test.exs
defmodule Cure.CLI.MigrateCliTest do
  use ExUnit.Case, async: false
  alias Cure.Migrate

  setup do
    dir = Path.join(System.tmp_dir!(), "curemig_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    {_, 0} = System.cmd("git", ["init", "-q", dir])
    {_, 0} = System.cmd("git", ["-C", dir, "config", "user.email", "t@t"])
    {_, 0} = System.cmd("git", ["-C", dir, "config", "user.name", "t"])
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "untracked file is rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    assert {:error, [{^f, :untracked}]} = Migrate.git_guard([f])
  end

  test "dirty (uncommitted) tracked file is rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    File.write!(f, "mod A\n# changed\n")
    assert {:error, [{^f, :dirty}]} = Migrate.git_guard([f])
  end

  test "staged-only change (index dirty, no worktree diff) is still rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    File.write!(f, "mod A\n# staged\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    assert {:error, [{^f, :dirty}]} = Migrate.git_guard([f])
  end

  test "clean tracked file passes", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    assert :ok = Migrate.git_guard([f])
  end

  test "a mixed batch reports each file's own reason, not one reason for all", %{dir: dir} do
    # Proves the per-file list shape: one file is untracked, a second is a
    # dirty tracked file, a third is clean -- a single {reason, [path]} pair
    # could not represent "untracked" and "dirty" simultaneously without
    # misreporting one of them.
    untracked_f = Path.join(dir, "untracked.cure")
    dirty_f = Path.join(dir, "dirty.cure")
    clean_f = Path.join(dir, "clean.cure")

    File.write!(dirty_f, "mod D\n")
    File.write!(clean_f, "mod C\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "dirty.cure", "clean.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    File.write!(untracked_f, "mod U\n")
    File.write!(dirty_f, "mod D\n# changed\n")

    assert {:error, reasons} = Migrate.git_guard([untracked_f, dirty_f, clean_f])
    assert {untracked_f, :untracked} in reasons
    assert {dirty_f, :dirty} in reasons
    refute Enum.any?(reasons, &match?({^clean_f, _}, &1))
  end
end
```

- [ ] **Step 2: Run to verify it fails** — `mix test test/cure/cli/migrate_cli_test.exs` → FAIL (`git_guard/1` missing).

- [ ] **Step 3: Implement `git_guard/1`** — for **each** path independently (do not short-circuit on the first failure — the whole point of a batch preflight is to surface every problem file in one pass, not force the user to fix them one at a time): run `System.cmd("git", ["ls-files", "--error-unmatch", path], cd: Path.dirname(path))`; a non-zero exit whose stderr indicates "not a git repository" classifies that path as `:not_a_repo`, any other non-zero exit classifies it `:untracked`. Otherwise run `System.cmd("git", ["status", "--porcelain", "--", path], cd: Path.dirname(path))`; non-empty stdout classifies it `:dirty`. A path with neither failure is clean and contributes nothing. **Every git invocation must pass `cd: Path.dirname(path)`** (see the working-directory note above — without it, every test in this task fails with `fatal: ... is outside repository`, not the intended result). Collect `{path, reason}` for every non-clean path, in the order `paths` was given. Return `:ok` only if that collected list is empty; else `{:error, collected}` where `collected` is the full `[{path, reason}]` list — never a single reason for the whole batch (see the Interfaces note above on why).

- [ ] **Step 4: Run to verify it passes** — `mix test test/cure/cli/migrate_cli_test.exs` → PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/migrate.ex test/cure/cli/migrate_cli_test.exs
git commit -m "feat(migrate): git-safety preflight guard (tracked + porcelain-clean)"
```

### Task 12: `cure migrate` command — in-place / `--check` / `--print` / `--strict` + batch atomicity

**Files:**
- Modify: `lib/cure/cli.ex` (dispatch `["migrate" | paths]`; add `cmd_migrate/2`)
- Test: `test/cure/cli/migrate_cli_test.exs`

**Interfaces:**
- Consumes: `Cure.Migrate.run/2`, `Cure.Migrate.git_guard/1`, `Trivia.attach/2`, `Printer.quoted_to_string/1`.
- Produces: `cmd_migrate(paths, opts) :: :ok | {:error, {:git_guard_failed, [{path, :dirty | :untracked | :not_a_repo}]} | {:preflight_failed | :pending | :strict_warnings, [path]}}` (the `:git_guard_failed` detail list is `Cure.Migrate.git_guard/1`'s own per-file `{:error, reasons}` payload from Task 11, wrapped under one top-level tag rather than re-flattened — re-flattening it back into a single reason atom would reintroduce exactly the mixed-batch ambiguity Task 11 fixed). Default: rewrite in place (git-guarded). `--check`: list pending files, **no write**, and return `{:error, {:pending, paths}}` if any file has an unapplied migration (this is the CI gate — spec §5.6 "non-zero exit" — distinct from `{:error, {:preflight_failed, _}}`, which means a file could not be migrated cleanly at all; §5.8 point 4 requires the two be distinguishable). `--print`: stdout, no write, `:ok` (or `{:error, {:preflight_failed, _}}` if a file can't print/reparse cleanly). `--strict`: migration warnings become errors (`{:error, {:strict_warnings, paths}}`). Target selection mirrors `cmd_fmt/2` (explicit paths, else `lib/**/*.cure` + `test/**/*.cure`). Batch atomicity (spec §5.8): run the full `lex→parse→attach→run→print→reparse-and-comment-check` in memory for **all** files first; only if every file passes does it write any; on any failure, write nothing and report the failing file(s).

**Testability constraint (verified against `cli.ex`):** every one of the ~45 existing `defp cmd_*` functions in `cli.ex` is private, and `main/1` never calls `System.halt`/`:erlang.halt` anywhere — the only existing "hard failure" precedent in this file is `exit({:shutdown, 1})` (used by `cmd_compile`/`cmd_check`/`cmd_run` on fatal errors), which raises an exit signal that would tear down an ExUnit test process calling `CLI.main` in-process. Given that, `cmd_migrate/2`:
- **Must be a public function** (`def cmd_migrate(paths, opts)`, with a one-line comment noting the deviation from the `defp cmd_*` convention: it needs direct unit-testability without spawning a subprocess or killing the test runner). This resolves the private-function-testability problem directly — tests call `Cure.CLI.cmd_migrate/2` (not `Cure.CLI.main/1`, and not `System.halt`/`exit`).
- **Must return `:ok | {:error, {reason, detail}}`** and must NOT call `System.halt` or `exit` itself. "Non-zero exit" (spec §5.6/§7's CI-facing requirement for `--check`/`--strict`/git-guard failure) is achieved by `main/1`'s dispatch arm converting a non-`:ok` return into `System.halt(1)` — but that `System.halt` call lives ONLY in `main/1`'s dispatch line, which the test suite never invokes for the failure-path assertions (tests call `cmd_migrate/2` directly and assert on its return value + on-disk side effects, never on `CLI.main`'s process-level behavior for a failing case). This mirrors the one precedent for `System.halt` already in this codebase (`lib/mix/tasks/antigen.ex:226`), and matches the fact that no other `cmd_*` in `cli.ex` sets a real exit code today — this task is not silently reusing an established convention, it is introducing the first one, deliberately scoped to a code path tests don't execute.

- [ ] **Step 1: Write failing CLI-level tests**

```elixir
  # append to test/cure/cli/migrate_cli_test.exs
  alias Cure.CLI

  test "in-place migrate rewrites a clean tracked file and reparses", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    assert :ok = CLI.cmd_migrate([f], [])

    out = File.read!(f)
    assert out =~ "pickup"
  end

  test "a dirty tree is rejected with the per-file git-guard detail, not a single flattened reason", %{dir: dir} do
    # Proves cmd_migrate/2 propagates git_guard/1's per-file [{path, reason}]
    # list under one :git_guard_failed tag end-to-end, rather than re-flattening
    # it back into a single top-level reason atom (which would reintroduce the
    # mixed-batch ambiguity Task 11 fixed at the Cure.Migrate.git_guard/1 layer).
    clean_f = Path.join(dir, "clean.cure")
    File.write!(clean_f, "mod C\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "clean.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    untracked_f = Path.join(dir, "untracked.cure")
    File.write!(untracked_f, "mod U\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")

    before_clean = File.read!(clean_f)
    before_untracked = File.read!(untracked_f)

    assert {:error, {:git_guard_failed, reasons}} = CLI.cmd_migrate([clean_f, untracked_f], [])
    assert {untracked_f, :untracked} in reasons
    refute Enum.any?(reasons, &match?({^clean_f, _}, &1))
    # nothing was written -- the git guard runs before the batch preflight
    assert File.read!(clean_f) == before_clean
    assert File.read!(untracked_f) == before_untracked
  end

  test "batch atomicity: if one file fails, zero files are written", %{dir: dir} do
    good = Path.join(dir, "good.cure")
    bad = Path.join(dir, "bad.cure")
    File.write!(good, "mod G\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    File.write!(bad, "mod B\nthis is not valid cure @@@\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "."])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    before_good = File.read!(good)
    assert {:error, {:preflight_failed, failed}} = CLI.cmd_migrate([good, bad], [])
    assert bad in failed
    # good is untouched because bad failed the in-memory preflight
    assert File.read!(good) == before_good
  end

  test "--check lists a pending file, writes nothing, and reports pending", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    before = File.read!(f)

    assert {:error, {:pending, [^f]}} = CLI.cmd_migrate([f], check: true)
    # --check never writes, regardless of outcome
    assert File.read!(f) == before
  end

  test "--check on an already-canonical file returns :ok and writes nothing", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\nfn f(x: Int) -> Int = x\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    before = File.read!(f)

    assert :ok = CLI.cmd_migrate([f], check: true)
    assert File.read!(f) == before
  end

  test "--print emits the migrated form to stdout and writes nothing, even on a dirty (unguarded) tree", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    # deliberately NOT added/committed: --print is read-only and git-guard-exempt
    before = File.read!(f)

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        assert :ok = CLI.cmd_migrate([f], print: true)
      end)

    assert output =~ "pickup"
    assert File.read!(f) == before
  end

  test "--strict promotes a migration warning to an error and writes nothing", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    before = File.read!(f)

    assert {:error, {:strict_warnings, [^f]}} = CLI.cmd_migrate([f], strict: true)
    assert File.read!(f) == before
  end

  test "no explicit paths: scans lib/**/*.cure and test/**/*.cure under cwd, mirroring cmd_fmt/2, and nothing else", %{dir: dir} do
    # Spec §5.6 explicitly requires this default-scan behavior, distinct from
    # every other test in this file (which all pass an explicit path) -- this
    # is the one test exercising it. Sandboxed via File.cd!/2 (which restores
    # cwd on return, even if the callback raises) so a bug here can never
    # touch this project's own `.cure` files.
    lib_dir = Path.join(dir, "lib")
    test_dir = Path.join(dir, "test")
    other_dir = Path.join(dir, "other")
    Enum.each([lib_dir, test_dir, other_dir], &File.mkdir_p!/1)

    in_lib = Path.join(lib_dir, "a.cure")
    in_test = Path.join(test_dir, "a_test.cure")
    outside_scan = Path.join(other_dir, "z.cure")

    body = "mod A\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n"
    File.write!(in_lib, body)
    File.write!(in_test, body)
    File.write!(outside_scan, body)

    {_, 0} = System.cmd("git", ["-C", dir, "add", "."])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    File.cd!(dir, fn ->
      assert :ok = CLI.cmd_migrate([], [])
    end)

    assert File.read!(in_lib) =~ "pickup"
    assert File.read!(in_test) =~ "pickup"
    # a .cure file outside lib/**/test/** must not be touched by the default
    # (no-explicit-paths) scan, same as cmd_fmt/2's own file-discovery.
    refute File.read!(outside_scan) =~ "pickup"
  end
```

`CLI.cmd_migrate/2` is called directly (not via `CLI.main/1`) precisely because it must be exercised without triggering `System.halt`/`exit` — see the testability-constraint note above. The module under test is `Cure.CLI` (all-caps — confirmed via `defmodule Cure.CLI do` at cli.ex:1; NOT `Cure.Cli`).

- [ ] **Step 2: Run to verify it fails** — `mix test test/cure/cli/migrate_cli_test.exs` → FAIL (`CLI.cmd_migrate/2` undefined).

- [ ] **Step 3: Implement dispatch + `cmd_migrate/2`**

Add to the `cli.ex` command `case` inside `main/1` (near the `["fmt" | paths]` arm, ~line 135):
```elixir
        ["migrate" | paths] ->
          case cmd_migrate(paths, opts) do
            :ok -> :ok
            {:error, _} -> System.halt(1)
          end
```
This is the ONLY `System.halt` call this task adds, and it lives on a line the test suite never calls (tests call `cmd_migrate/2` directly, per Step 1). `check: :boolean` (cli.ex:62) and `strict: :boolean` (cli.ex:68) **already exist** in the single, shared `OptionParser.parse/2` switches list (cli.ex:36-82 — one global switches list for every subcommand, not one per command, confirmed by reading the file: `--check`/`--strict` are already reused by other existing commands, e.g. `cure compile`'s own `--check`). Only `print: :boolean` is actually missing from that list and needs adding — do NOT re-add `check`/`strict` a second time (a duplicate keyword-list key is not a compile error but is dead, confusing code; verify with `grep -n "check: :boolean\|strict: :boolean\|print: :boolean" lib/cure/cli.ex` before editing to confirm only `print` is absent). Implement `def cmd_migrate(paths, opts)` (public — see testability-constraint note; add a one-line comment on why it deviates from the file's `defp cmd_*` convention): resolve targets (mirror `cmd_fmt/2`); unless `--check`/`--print`, run `git_guard/1` and, on `{:error, reasons}`, print each `{path, reason}` pair on its own line (a clear message per file, not one generic message for the batch) and return `{:error, {:git_guard_failed, reasons}}` verbatim — do not collapse `reasons` down to a single atom, that is exactly the ambiguity Task 11's per-file list shape exists to avoid; run the in-memory batch preflight for all files (lex→parse→attach→`Migrate.run`→print→reparse+comment-count check) — on any file failing that pipeline (parse error, reparse failure, comment-count mismatch), print which file(s) and why, and return `{:error, {:preflight_failed, failed_paths}}`, writing nothing; if `--strict` and any warnings fired, print them and return `{:error, {:strict_warnings, warned_paths}}`; else apply the mode:
  - `--check`: print each pending file (one whose `Migrate.run/2` produced a rewrite); return `{:error, {:pending, pending_paths}}` if the list is non-empty, else `:ok`. Never writes.
  - `--print`: print each file's migrated form to stdout; return `:ok`.
  - default: write every file whose preflight run produced a rewrite; return `:ok`.

- [ ] **Step 4: Run to verify it passes** — `mix test test/cure/cli/migrate_cli_test.exs` → PASS.

- [ ] **Step 5: Run the full suite once** — `mix test`. Expected: green.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/cli.ex test/cure/cli/migrate_cli_test.exs
git commit -m "feat(cli): cure migrate command with check/print/strict and batch atomicity"
```

### Task 13: Retire `mix cure.rewrite` in favor of the registry (optional cleanup)

**Files:**
- Modify: `lib/mix/tasks/cure.rewrite.ex` (delegate to `Cure.Migrate` or deprecate)
- Test: `test/mix/tasks/cure_rewrite_test.exs` (create if it does not already exist — check first)

This delegation is a behavior change, not a pure refactor: `cure.rewrite.ex`'s own moduledoc (line 44-52) documents the exact parenthesised-context reparse bug that Task 8 fixes. Delegating without a test risks silently reintroducing (or silently fixing without proof) that behavior change. Use `Cure.Migrate.run/2`'s `:rules` override (added in Task 7) to scope the delegate to **only** the if/elif rule — `mix cure.rewrite` must not start also applying the uppercase-type-var rule, which is out of its historical scope.

- [ ] **Step 1: Write the failing regression test**

```elixir
# test/mix/tasks/cure_rewrite_test.exs (append if the file already exists)
defmodule Mix.Tasks.Cure.RewriteTest do
  use ExUnit.Case, async: false

  test "a conditional embedded in a call-argument list is left unrewritten (paren-context), not turned into unparseable output" do
    src = "mod M\nfn g(x: Int) -> Int = h(if x > 0 then 1 else 2)\n"
    ast = Cure.Compiler.Lexer.tokenize(src, file: "t.cure", emit_events: false)
          |> then(fn {:ok, toks} -> Cure.Compiler.Parser.parse(toks, file: "t.cure", emit_events: false) end)
          |> then(fn {:ok, ast} -> ast end)

    new_ast = Mix.Tasks.Cure.Rewrite.rewrite(ast)
    out = Cure.Compiler.Printer.quoted_to_string(new_ast)

    refute out =~ "pickup"
    # Full reparse (lex AND parse), not just tokenize -- tokenizing alone does
    # not prove the output is syntactically valid.
    assert {:ok, toks2} = Cure.Compiler.Lexer.tokenize(out, file: "t.cure", emit_events: false)
    assert {:ok, _ast2} = Cure.Compiler.Parser.parse(toks2, file: "t.cure", emit_events: false)
  end
end
```

- [ ] **Step 2: Run to verify it fails** — `mix test test/mix/tasks/cure_rewrite_test.exs` → FAIL (today's `rewrite/1`, per its own documented caveat, rewrites into the paren context and produces output that does not reparse).

- [ ] **Step 3: Implement the delegation**

Add a moduledoc deprecation note pointing to `cure migrate`. Replace `Mix.Tasks.Cure.Rewrite.rewrite/1`'s body with a call to the registry, scoped to just the if/elif rule:
```elixir
  def rewrite(ast) do
    {new_ast, _warnings} =
      Cure.Migrate.run(ast, file: "cure.rewrite", rules: [Cure.Migrate.Rules.IfElifToPickup.rule()])

    new_ast
  end
```
Keep the rest of the mix task's CLI surface (`--check`/`--print`, file expansion) unchanged for back-compat.

- [ ] **Step 4: Run to verify it passes** — `mix test test/mix/tasks/cure_rewrite_test.exs` → PASS.

- [ ] **Step 5: Run the full suite once** — `mix test`. Expected: green.

- [ ] **Step 6:** Commit: `git add lib/mix/tasks/cure.rewrite.ex test/mix/tasks/cure_rewrite_test.exs && git commit -m "refactor(migrate): route mix cure.rewrite through the shared registry"`.

---

## Self-Review

**Spec coverage:**
- §5.2 trivia model → Tasks 4–6. §5.3 Printer totality (raise catch-all + exhaustiveness + corpus gate) → Tasks 1–3. §5.4 blank-line policy → Task 6. §5.5 registry + three seed rules (incl. paren-context fix, T+t freshening, and the `@group` relocation/trivia-carry rule) → Tasks 7–10 (rules in Tasks 8, 9, 9b). §5.6 CLI → Task 12. §5.7 git guard → Task 11. §5.8 batch atomicity → Task 12. §7 gates → Tasks 2, 3, 6, 10, 11, 12. §8 out-of-scope respected (no `cure fmt` rewire; one global `--strict`).
- **Known plan-shape caveat:** Task 3 is a TDD *loop* over the corrected list of 15 genuinely-missing node kinds (down from an initial, unverified 25 — see the recursive-skeptical-review note below) rather than a fixed step count. This is deliberate — the exact per-node clause code depends on each node's shape in `parser.ex`, which the implementer verifies at the construction site. The method and one full worked example (`:pin`) are given; the loop's exit condition (both gates green) is concrete and falsifiable.

**Placeholder scan:** No "TBD"/"handle edge cases"/"similar to Task N". Task 3's per-kind steps are a genuine repeated TDD cycle with a worked example, not a placeholder.

**Recursive-skeptical-review hardening (2026-07-10):**
- *Pass 1 (goal alignment / factual grounding):* Task 3's "known missing node kinds" list (25 entries) was checked against `parser.ex`/`printer.ex` and found to contain 9 phantom entries (`:ctor`, `:type`, `:string_part`, `:expr`, `:on_phase`, `:supervisor`, `:variadic`, `:keyword_variadic`, `:positional` — none are real `{tag, meta, children}` Printer-dispatch targets; several are already fully rendered via existing helpers) plus 3 non-standard-shape entries requiring extra care (`:gadt_ctor`'s embedded `:arrow_chain`/`:named_dom`, and the 4-tuple `:named_implicit_pat`). The list is now 15 verified entries with the non-standard shapes called out explicitly. Task 10's build-hook was retargeted from a nonexistent `Parser.parse` call inside `cli.ex`'s `compile_one/3` to the real call site in `lib/cure/compiler.ex`'s `compile_string/2`. Task 12's `cmd_migrate/2` was made an explicitly-public, `System.halt`-free function so its tests don't crash the test runner or depend on a private function. The git-repo module reference was corrected from the nonexistent `Cure.Cli` to the real `Cure.CLI`. Task 5's `UnplacedTriviaError` test input was corrected to one that's actually unplaceable under the stated attachment rule. Task 6's reparse assertion was replaced with a real local `parse!/2` helper instead of a "simplify later" placeholder.
- *Pass 2 (type consistency / sequencing / coverage):* Task 7's registry test depended on `:W_if_elif_pickup`, a rule that doesn't exist until Task 8 — this made Task 7 unable to reach green on its own; fixed by adding an `opts[:rules]` override to `run/2` and a self-contained synthetic test rule, decoupling the fold-mechanism test from Tasks 8/9's content (and reused in Task 13). The git-guard error-reason atom was briefly inconsistent between Task 11 (`:dirty`) and my own Task 10/12 edits (`:git_dirty`) — reconciled to `:dirty` everywhere. Task 9's T+t collision test was missing the spec §7-mandated "freshen must skip an already-used `t1` to `t2`" case — added. Task 12 was missing CLI-level tests for `--check`, `--print`, and `--strict` despite spec §7 explicitly requiring them — added four tests. Task 13 had no red test at all for a genuine behavior change (delegating `cure.rewrite` through the registry) — added one, and wired it through the `:rules` override so `cure.rewrite` stays scoped to only the if/elif rule. Most significantly: Task 9's uppercase-type-var rule detection is fully dependent on `ctx` correctly recognizing built-in primitive types (`Int`, `Bool`, etc.) as "known" — but `parse_type_atom/1` (parser.ex:3281-3305) parses `Int` and a free type var `T` into the *identical* `{:variable, [scope: :local], name}` shape, and spec §5.5's "declared+imported type-name set" prose never mentions seeding built-ins. Without that seed, `build_ctx/1` would treat every bare `Int`/`Bool`/`Float`/etc. reference as a free type var and rename it — a catastrophic false-positive matching nearly every real Cure file (and most fixtures in this very plan). Fixed by requiring `build_ctx/1` to seed the real built-in set confirmed at `lib/cure/types/env.ex:35-44` (`Int`, `Float`, `String`, `Bool`, `Atom`, `Unit`, `Any`, `Never`, `Char`), and adding an explicit red test for it in Task 9.
- *Pass 3 (codebase-convention consistency / ambiguity):* Task 2 (and the plan's §6/§7 coverage claims) implemented only the corpus/fixture round-trip totality gate — the plan never actually specified spec §5.3 point 2 / §7's **second, distinct** "Printer static-exhaustiveness gate" (a static check that every node-kind atom the parser can construct has a matching Printer clause, independent of what today's corpus happens to contain), even though the spec's own build-order (§6 phase 1) explicitly requires landing "both the corpus totality gate and the static-exhaustiveness gate." This also explained why `@error_node_kinds` was defined in Task 2's test code but never referenced by either existing test — it was the intended input to a gate that hadn't been written yet. Fixed by adding Task 2 Steps 4–6: a `printer_handled_kinds/0` helper that regex-scans `printer.ex`'s own source for `defp to_string({:kind,` clauses, an explicit curated `@all_node_kinds` list (the 40 already-handled kinds plus Task 3's corrected 15, including `:named_implicit_pat` — itself folded back into Task 3's own enumerated list as part of this fix, since an earlier draft discussed it in prose but omitted it from the headline count), and a new test asserting the difference is empty — RED until Task 3 completes, per the existing loop-exit condition (now updated to require all three tests green, not two). Separately, Task 5's "attachment is total" test carried a factually wrong justifying comment (inherited from Pass 1's earlier fix): it claimed a bare `Trivia.attach([], ...)` input represents "an entirely empty parsed file," citing "Parser.parse/2 returns a list" — verified false by reading `parser.ex:92-113`: the public `parse/2` wraps zero-or-many top-level expressions as `case exprs do [single] -> single; many -> {:block, [line: 1, col: 1], many} end`, so an empty file actually parses to `{:ok, {:block, [line: 1, col: 1], []}}` (an empty *block node*, which per the attachment rule would correctly take the trivia as its own `:trailer`, not raise) — meaning no output of a real `Parser.parse/2` call ever gives `attach/2` zero nodes to work with, and `UnplacedTriviaError` is a pure defense-in-depth invariant for this pipeline's real inputs, not a scenario any actual `.cure` file triggers. The test itself was not wrong (`Trivia.attach([], ...)` is a legitimate direct unit test of `attach/2`'s own base-case contract for a bare list, which this plan's own helpers elsewhere already treat as an anticipated recursive-position AST shape), but its comment's factual claim was — corrected in place.
- *Pass 4 (hidden assumptions):* Task 5's attachment rule assumed "each node's `meta` carries `line`/`col`," letting `attach/2` read a node's span directly off its own meta. Verified false by scanning `parser.ex` for node constructions with no `line:`/`col:` key: dozens of sites lack it, including mainline, everyday syntax — every `:pair` (map/record-literal entry, parser.ex:932/944/954), `:match_arm`, `:generator`/`:filter` (comprehensions), `:tuple`, `:record_update`, `:child_spec`, `:pi_type`/`:sigma_type`, and the `{:variable, [scope: :local], name}` shape used for every bare type-position identifier. A comment adjacent to any of these could not be span-classified by reading that node's own meta. Fixed by specifying a recursive effective-span algorithm in `attach/2` (own meta if present, else recurse into first/last child) and adding a red test exercising it against a real map-literal trailing comment. A second, deeper gap surfaced while designing that fix: a lambda parameter node (`{:param, [], name}`, parser.ex:2648) is a true leaf with an empty meta AND a bare-string (non-list) third element — nothing to recurse into — so the naive recursive-children fallback alone would crash or misbehave on ordinary lambda syntax. Fixed by adding a final "positionless childless leaf is transparent to boundary classification" fallback, plus a second red test exercising a comment near a lambda. Neither fix touches `parser.ex` (both live entirely inside the new `Trivia` module), preserving the plan's "no grammar change" constraint. A third hidden assumption surfaced in the same pass: Task 6's blank-line handling only described spec §5.4 points 1–4 (statement-list join normalization) and silently dropped point 5 (blank trivia *inside a single multi-line non-statement-list expression* — a map/record/list literal or call-argument list — must be attached like any other trivia and printed back **unchanged**, not capped/collapsed/injected). As scoped, the plan would have silently dropped an author's blank line inside e.g. a multi-line map literal — exactly the "Bug 2" silent-drop failure mode the whole trivia model exists to prevent. Fixed by adding a blank-classification note to Task 5 (a `:blank` item is always `:leading`-only, since a blank line has no token to trail), splitting Task 6's Step 3 into the capped statement-list case and the verbatim expression-span case, updating the Interfaces bullet accordingly, and adding a red test asserting a blank line inside a multi-line map literal survives the round-trip. A fourth issue: Task 8's paren-context guard ("track whether a `{:conditional, …}` is a descendant of a `{:function_call, …}` argument (or other paren context)") was structurally incomplete and, worse, provably incompletable — the lexer's `paren_depth` (`lexer.ex:1379,1384`, the thing that actually suppresses `:indent`/`:dedent`) is driven only by `(`/`)` tokens (`lexer.ex:179-180`), which parser.ex uses in at least six distinct grammar positions, and `parse_grouped/1` (parser.ex:526-533) — a bare precedence-grouping `(expr)` — discards the grouping node entirely, so a grouped conditional used as an operand (`(if x > 0 then 1 else 2) + 1`) is structurally indistinguishable in the AST from an unparenthesized one; no ancestor-shape enumeration can detect it. Fixed by replacing the structural-only design with a verify-by-reparse strategy (rewrite each conditional one at a time, in order, keeping only the ones whose whole-file reprint still reparses), with a new red test for the grouped-operand case a structural check would silently miss. This surfaced a second, distinct internal-consistency defect while cross-checking Task 8's paren-skip test against Task 10's strict parity assertion (`(rewritten != ast) == (fired != [])`) and the top-level Global Constraint ("a rule fires ... on exactly the inputs `cure migrate` rewrites"): Task 8's own paren-skip test already warns without rewriting, which falsifies that strict equivalence and the Global Constraint as literally worded — but re-reading spec §5.5's seed-rule note confirms this is a **deliberate, spec-mandated exception** (option (a): "emit the warning but leave the source untouched, same as an unmatched rule"), not a plan defect to remove. Fixed by qualifying the Global Constraint with this explicit carve-out and adding a dedicated exception test to Task 10 (`the one documented exception: a paren-embedded conditional warns without rewriting`) so the exception is proven intentional rather than silently contradicting the general parity claim. A fifth issue, empirically verified rather than merely reasoned about: Task 11's `git_guard/1` description never mentioned a working directory for its `git status`/`git ls-files` subcommands. Confirmed by direct reproduction (`git status --porcelain -- <path in repo A>` run from cwd in unrelated repo B exits 128 with `fatal: ... is outside repository at '<B's root>'`, not a silent success or a correct result) that this is not a hypothetical: `mix test` runs with cwd at this project's own git repo, while Task 11's own test fixture creates a **separate, unrelated temp git repo** per test — meaning every test in Task 11 (and transitively Task 12, which calls `git_guard/1`) would fail with an "outside repository" error rather than the intended `:dirty`/`:untracked`/`:ok` result. Fixed by requiring every `System.cmd("git", [...])` call in `git_guard/1` to pass `cd: Path.dirname(path)` (confirmed empirically to resolve correctly, since git auto-discovers the repo root upward from any directory inside it).
- *Pass 5 (dedicated testing-discipline check):* every task already follows write-red-test → confirm-fail → implement → confirm-pass → commit (verified via `grep -n "Step 1:\|Step 2:\|Run to verify it fails\|Run to verify it passes"` across all 13 tasks — the pattern is uniform), and every test asserts observable behavior (printed output, return-value shapes, file contents, warning lists, reparseability) rather than private call counts or internal structure, so three of the four required criteria were already satisfied. The fourth was not: the plan never stated that tests, once green, are immutable except by proving a specific test itself wrong — nothing in the plan would have stopped an implementer from quietly loosening or deleting an inconvenient test to reach green faster. Fixed by adding an explicit "tests are set in stone" rule to Global Constraints.
- *Pass 6 (failure modes / test coverage):* every one of Task 12's CLI-level tests passed an explicit target path, leaving spec §5.6's separately-required "no explicit paths → scan `lib/**/*.cure` + `test/**/*.cure`" default-discovery behavior with zero test coverage (confirmed via `grep -n "cmd_migrate(\[\]"` across the whole plan — zero matches). This is a real, spec-mandated behavior, not an edge case invented for this review, and its failure mode is not benign: `cmd_migrate/2`'s default scan is cwd-relative (mirroring `cmd_fmt/2`'s own `Path.wildcard("lib/**/*.cure")`), so an untested implementation of it is exactly the kind of thing that could silently touch this project's own real `.cure` files if ever exercised carelessly. Fixed by adding a dedicated test sandboxed via `File.cd!/2` (which restores cwd even on a raise) with its own isolated `lib/`/`test/`/`other/` subdirectories, asserting the scan covers the first two and not the third.
- *Pass 7 (internal numeric consistency, post-hoc cross-check):* Task 3's explicit code-fenced "known missing node kinds" list and Task 2's `@all_node_kinds` list were introduced in separate passes (Pass 1 and Pass 3 respectively) and had silently drifted out of sync: Task 3's fenced list enumerated only 14 atoms (it omitted `:named_implicit_pat`, even though the very next paragraph already discussed it as a 4-tuple shape requiring its own Printer clause), while three separate pieces of prose (Task 2 Step 5's expected-failure text, the "Known plan-shape caveat" bullet, and Pass 1's own self-review narrative) all asserted the count was "13," none of which matched either list's actual length. Cross-checked by mechanically counting both lists: `@all_node_kinds` has 55 entries (40 already-Printer-handled + 15 missing), Task 3's fenced list had 14. Fixed by adding `:named_implicit_pat` to Task 3's fenced list (now 15, matching `@all_node_kinds`) and correcting all four "13" occurrences (Task 2 Step 5, the caveat bullet, Pass 1's bullet, and this Pass 3 bullet) to read "15." Re-grepped the whole file for `corrected 1[0-9]`, `1[0-9] missing`, and `missing 1[0-9]` after the fix — no remaining inconsistencies found.
- *Pass 8 (fresh full-document reread against spec §5.1–§5.8 scope):* two further defects surfaced on a cold re-read of the whole plan (not a narrower per-section check). First: Task 2's test file defines `@error_node_kinds` (a curated list of parse-failure-only node kinds) and a private helper `node_kinds/2` (walks an AST collecting every node-kind atom present), but neither is ever called by either test in Step 2, nor by the new exhaustiveness test added in Pass 3's Step 4 — confirmed by grepping the whole plan for `error_node_kinds` and `node_kinds(` and finding only the definition sites and one prose mention. An unused `@`-attribute and an unused private function both produce a compile warning in Elixir, and this project's own `mix.exs` `test` alias runs `test --warnings-as-errors` — meaning the plan, implemented exactly as written, would fail its own test suite's compile step before a single assertion ran. Fixed by giving both a genuine use: the corpus-wide test ("every surface node kind in the whole in-repo corpus prints without raising") now also asserts `MapSet.disjoint?(node_kinds(ast), MapSet.new(@error_node_kinds))` for every corpus file — a real invariant (a successfully parsed AST should never contain an error/diagnostic node kind) this gate is well-positioned to check since it already walks every corpus file's AST — and Task 2 Step 4's prose (which had incorrectly implied the *new* exhaustiveness test would be what consumes `@error_node_kinds`) was corrected to point at the actual consumer. Second, more significant: Task 11's `git_guard/1` was specified to return `{:error, {:dirty | :untracked | :not_a_repo, [path]}}` — one reason atom for the *entire* batch of paths — but `git_guard/1` runs over a whole target set that Task 12's default (no-explicit-paths) scan can resolve to every `.cure` file under `lib/**` and `test/**` at once, and it is entirely realistic for that set to contain both an untracked scratch file and a separately dirty tracked file in the same invocation; the plan's own return shape has no way to represent that mix without silently misreporting at least one path's true reason (e.g. tagging a dirty file `:untracked` or vice versa merely because it happened to be classified first). None of Task 11's four original tests exercised a mixed-reason batch — each used exactly one file in exactly one state — so this gap had no failing test pinning it down. Fixed by changing `git_guard/1`'s contract to `:ok | {:error, [{path, reason}]}` (a per-file list, classifying every path independently rather than short-circuiting on the first failure), updating all four existing tests' assertion shapes accordingly, and adding a new test ("a mixed batch reports each file's own reason, not one reason for all") with one untracked, one dirty, and one clean file in the same call. This propagated to Task 12: `cmd_migrate/2`'s error type was changed from re-exposing `:dirty`/`:untracked`/`:not_a_repo` as its own top-level tag to wrapping `git_guard/1`'s per-file list intact under `{:git_guard_failed, reasons}` (re-flattening it back to a single atom at the CLI layer would have silently reintroduced the exact ambiguity just fixed one layer down), and a new CLI-level test was added proving `cmd_migrate/2` surfaces the untracked/dirty distinction end-to-end and writes nothing. The stale "Type consistency" bullet claiming `git_guard/1`'s reason atom "is propagated verbatim" was corrected to describe the new wrapped-list shape.

- *Pass 9 (dedicated spec-cross-check: §7's gate wording against Task 2's actual test code):* spec §5.3 and §7 both state the Printer-totality gate applies to "the whole in-repo `.cure` corpus": "parse→print never inspects a tuple and always reparses; print is a fixpoint" — three properties (no-raise, reparses, fixpoint), explicitly over the real corpus, not only a synthetic fixture. Task 2's actual corpus test (`"every surface node kind in the whole in-repo corpus prints without raising"`, as it was named before this pass) checked only the first of the three: it called `Printer.quoted_to_string(ast)` and discarded the result without ever re-lexing/re-parsing it, so a corpus file that printed successfully but produced unparseable or non-fixpoint output would pass this test regardless. Only the separate, synthetic single-fixture test (`test/fixtures/printer_totality.cure`) checked reparse+fixpoint — and a hand-built fixture designed to be construct-complete is not a substitute for checking the same property against files that already exist in this repo (a real corpus file can exercise a node-kind combination, nesting depth, or ordering the fixture doesn't). Fixed by extending the corpus test (renamed to `"the whole in-repo corpus prints without raising, reparses, and is a print-fixpoint"`) to additionally re-lex/re-parse each file's printed output and assert both that it reparses and that a second print is byte-identical to the first, matching §5.3/§7's stated gate exactly. This is additive to Pass 8's fix on the same test (the error-node-kind disjointness assertion) — both now live in one test body.

- *Pass 10 (ambiguity lens, Task 4 re-read):* Step 3's implementation instructions told the implementer to "track blank runs by counting consecutive newline-only lines." Cross-checked against the real lexer: `lex_indentation/1` (lexer.ex:210-231) already has its own, different definition of a blank line — it calls `measure_indent/1` to consume the line's leading whitespace *first*, and only afterward checks whether the next character is `\n`/`\r`/EOF (lexer.ex:216-217) to decide the line is blank. That means a line containing only spaces (e.g. an indented blank line inside a block, which many editors produce by preserving the surrounding indentation) is already blank by the lexer's own existing check, not just a literally zero-character line. "Newline-only lines," read literally, is a narrower definition that would plausibly miss the whitespace-only case if implemented fresh without consulting lexer.ex:210-231, silently undercounting a blank run and corrupting the `{:blank, count, line}` item both Task 5's attachment and Task 6's blank-line policy depend on. Fixed by rewriting Step 3's instruction to explicitly point at and reuse the existing branch (lexer.ex:216-231) rather than inventing a second, narrower definition of "blank," and by adding a dedicated red test ("a blank line that contains only indentation whitespace still counts as blank") using an indented, space-only blank line inside a `let`-block, which a naive "line is exactly empty" implementation would fail.

- *Pass 11 (codebase-consistency re-check, Task 12's CLI wiring):* Task 12 Step 3 instructed "Ensure `migrate` opts include `check`, `print`, `strict` in the `OptionParser` switches (~cli.ex:35)," implying all three need adding. Verified against the real file: `cli.ex` has exactly one, shared `OptionParser.parse/2` call (cli.ex:34-84) whose `switches:` list is global across every subcommand, not per-command — and `check: :boolean` (cli.ex:62) and `strict: :boolean` (cli.ex:68) **already exist** there (reused by other existing commands). Only `print: :boolean` is actually absent. Following the plan's original wording literally, an implementer could plausibly re-add `check:`/`strict:` as duplicate keys in that keyword list — not a compile error, but dead, confusing code, and a sign of not having actually read the existing switches list before editing it. Fixed by correcting Step 3's instruction to state precisely which one switch is missing, citing the exact existing lines for the two that already exist, and adding a `grep` verification command to run before editing.

- *Pass 12 (factual-grounding re-check, Task 6's regression-check pointer):* Step 5's guidance named `bin_segment_test.exs` as a file that "uses the Printer" and should be checked for output regressions. Verified false by reading the file directly: its own `alias` line imports only `Lexer`, `Parser`, `Codegen`, `BeamWriter`, and a full-file grep for `Printer`/`to_string` returns zero matches across all 109 lines — it exercises binary-segment (`<<...>>`) lexing/parsing/codegen only and has nothing to do with the Printer. Pointing an implementer at the wrong file for a regression check is worse than pointing at no file at all: it wastes verification effort on a file immune to the change while leaving the files that actually DO call `Printer.quoted_to_string/1` today unnamed. Grepped the whole test suite (`grep -rl "Printer\." test/`) to find them: `test/cure/compiler/melquiades_parser_test.exs`, `test/cure/compiler/pickup_test.exs`, and `test/cure/compiler/match_spec_test.exs`. Fixed by correcting Step 5 to name these three real Printer-consuming test files instead, and to note (with the disproving grep command inline) that `bin_segment_test.exs` is not one of them despite the earlier draft's claim.

- *Pass 13 (internal consistency, top-level File Structure vs. actual task bodies):* the top-level "File Structure" section's **Modified files** list included `lib/cure/compiler/parser.ex`, described as exposing "per-node position spans needed by attachment." Cross-checked against every one of the 13 tasks' own `Files:` blocks (`grep -n "^- Modify:\|^- Create:"` across the whole plan) — none of them lists `parser.ex` as a Create or Modify target. This was stale: Task 5's position-metadata-gap fix (logged under Pass 4) explicitly redesigned the attachment pass to compute a node's effective span *recursively inside the new `Trivia` module*, specifically because patching individual `parser.ex` construction sites was shown to be unreliable ("that list is not guaranteed exhaustive... Instead, `attach/2`'s position-index step must compute a node's effective span recursively") and because doing so preserves the plan's own "no grammar change" Global Constraint. The top-level summary was never updated to match that redesign, so a reader skimming only the File Structure section (not Task 5's full body) would incorrectly expect a `parser.ex` diff. Fixed by removing the stale bullet and replacing it with an explicit note stating `parser.ex` is deliberately untouched and pointing at Task 5's actual mechanism, so the omission reads as intentional rather than as a checklist gap.

- *Pass 14 (goal alignment + factual-grounding re-check, Task 7's `build_ctx/1`):* re-verified the `lib/cure/types/env.ex:35-44` citation directly against the file (struct field `:types` at `env.ex:11`, the exact 9-key map at lines 35-44) — accurate, no drift. While there, applied one small robustness polish to Step 3's prose: `build_ctx/1` should derive the builtin-name set programmatically (`Map.keys(Cure.Types.Env.new().types)`) rather than hardcoding a second, duplicate literal copy of the same 9 names inside `Cure.Migrate`, so the two lists cannot silently drift apart if a future primitive is added to `Cure.Types.Env`. On reflection this is **not counted as a new defect for convergence purposes**: the original Step 3 text never mandated hardcoding either way, v1 behavior is byte-identical under both implementations (no test distinguishes them), and this is a refinement of this same hardening pass's own earlier Pass-2 phrasing rather than a mistake introduced by the plan's original author — the honest call, per this skill's "calibrate defect vs. preference" guidance, is that this is a preference-level robustness improvement, kept because it's free and strictly better, not a finding that resets the counter. No other issue surfaced on this sweep.

- *Pass 15 (factual-grounding re-check of Tasks 3 and 8, testing-discipline lens on the reparse assertions):* re-verified several highly specific, load-bearing AST-shape claims in Task 3 directly against `parser.ex`/`printer.ex` — `:gadt_ctor`'s 2-tuple sig, `:named_dom`, `:named_implicit_pat`'s 4-tuple shape, `typed_params_to_string/3` (printer.ex:744-761), `fn_def_to_string/4` (printer.ex:656), the `:lambda` clause (printer.ex:346-350), and `record_to_string/4`'s field mapper (printer.ex:805-818, including the specific claim that it inline-destructures `:param` without honoring `kind`/`default`) — all confirmed accurate, no drift. While re-reading Task 8 in full, found a genuine gap: grepping the whole plan for `Lexer.tokenize(out` / `Lexer.tokenize(new_ast` turned up four tests whose own names/purpose claim to prove the migrated output "reparses" (Task 8's three tests — "top-level if/else rewrites to pickup and reparses," "conditional inside a call-argument list is NOT rewritten (paren-context), still warns," "a bare-grouped conditional used as an operand is NOT rewritten either... still warns" — plus Task 13's regression test) but whose assertion only calls `Lexer.tokenize/2` and never `Parser.parse/2`. Tokenizing successfully does not prove the output is syntactically valid — a malformed `pickup` block, or malformed output in the not-rewritten cases, could easily still tokenize (produce a token stream) while failing to parse. This directly undersells Task 8's own Step 3, which specifies the rule's internal verify-by-reparse mechanism as doing *both* `Lexer.tokenize/2` *and* `Parser.parse/2` before committing to a rewrite — the tests meant to pin that mechanism down were weaker than the mechanism itself. (One other match, the corpus test fixed in Pass 9, was already correct — it calls both and was excluded from this finding.) Fixed by adding a shared `reparses?/2` helper to Task 8's test module (tokenize-then-parse, returning a boolean) and switching all three of Task 8's tests to `assert reparses?(out, "<file>.cure")`, and by expanding Task 13's inline assertion from a single `Lexer.tokenize` call to an explicit `Lexer.tokenize` followed by `Parser.parse` on the resulting tokens. This is one root cause (weak reparse assertions) with four fix-sites, counted as a single finding.

Clean-pass counter: 0 of 2 (Pass 15 found a new issue; per the skill's 15-pass ceiling, no further passes are permitted — see Convergence Status below).

**Convergence Status: NOT CONVERGED.** This review ran the maximum 15 passes without reaching two consecutive clean passes (only Pass 14 was clean; Pass 15 — the last pass permitted — found and fixed one genuine issue, which resets the counter to 0). Per this review's own governing instructions, the loop stops here rather than running a 16th pass, and the plan is left in its current, heavily-hardened-but-unconverged state. All 15 passes' findings above were fixed in place as they were found; nothing here is left pending. What remains unverified is only the meta-property that a 16th pass would have found nothing new — that could not be established within the pass budget. A human reviewer (or a fresh review run) should do at least one more pass, focused first on the two lenses least recently applied in isolation (edge cases, order/sequencing), before this plan is treated as fully hardened.

**Type consistency:** `Cure.Migrate.run/2` → `{ast, [warning]}` used consistently in Tasks 7, 8, 9, 10, 12; the `opts[:rules]` override introduced in Task 7 (so Task 7's own test doesn't depend on Tasks 8/9's not-yet-existing rules) is reused by Task 13 to scope `mix cure.rewrite`'s delegation to only the if/elif rule. `Rule` fields (`id`, `phase`, `detect_and_rewrite`, `warning_template`) consistent between Task 7 definition and Tasks 8/9 producers. `Trivia.attach/2` + `carry/2` and `git_guard/1` signatures consistent across producer and consumer tasks. Rule ids `:W_if_elif_pickup` / `:W_uppercase_type_var` / `:W_group_hoist` consistent across Tasks 8/9/9b/10 (the `@group` hoist, Task 9b, is a relocation rule reusing `Trivia.carry/2` from Task 5 and registered in `rules/0` after the other two); `git_guard/1`'s per-file `[{path, reason}]` list (reason atoms `:dirty` / `:untracked` / `:not_a_repo`, defined in Task 11 — reworked from an earlier, ambiguous single-reason-per-batch shape during this hardening pass, see Pass 8 below) is propagated by Task 12's `cmd_migrate/2` intact, wrapped under one `{:git_guard_failed, reasons}` tag rather than re-flattened.

# Anonymous ADTs (`Int | String`) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add anonymous union types (`Int | String`, `3 | :north`) to Cure's type-expression grammar, elaborating to compiler-generated discriminated inductive families with auto-derived constructors.

**Architecture:** A union's identity is its canonical member list (flattened, normalised to full `nf`, keyed by type-distinguishing printing, deduped, lexically sorted). That sorted key list *names* a generated parameterless inductive family, so `Int | String` and `String | Int` produce literally the same `{:data, name}` and are definitionally equal with zero kernel involvement. Injection is an elaborator-inserted coercion in check-position only; elimination is an ordinary Core `:case`. The kernel is untouched.

**Tech Stack:** Elixir, ExUnit. Cure compiler: `lib/cure/compiler/` (lexer, parser, printer), `lib/cure/elab/` (elaborator, declarations, emit, resolution), `lib/cure/core/` (kernel — **do not modify**).

---

## Global Constraints

- **ZERO TCB CHANGE.** Do not modify anything under `lib/cure/core/`. The kernel, `Conv`, `Kernel.check/infer`, `Normalise`, `Inductive`, `Term`, `Eval` are all off-limits. If a task appears to require a kernel change, **STOP and report** — that is a design failure, not a licence to edit the kernel.
- **Every generated family must pass the existing kernel gate.** Declaration goes through `declare_indexed_at_min_level/6` (`lib/cure/elab/declarations.ex:1646`), which runs `Kernel.check_family`, `check_all_ctors`, and `Inductive.positive?`. Never bypass it by calling `Inductive.declare/3` directly and stopping there.
- **Run the full suite with `mix test`. ONE build/test run at a time — never launch concurrent suites.**
- **Union members must be ground and closed** — no free type variables, no unsolved metavariables.
- Union family key format: `:"Union<k1|k2|...|kn>"` where `k1..kn` are the sorted member keys. The `<`, `>` and `|` characters are **not producible by the type-name lexer**, so a generated key can never collide with a user-declared type.
- Union constructor name format: `:"<union_key>$<member_key>"`, e.g. `:"Union<Int|String>$Int"`.
- **Numeric-literal defaulting:** a bare numeral in a type-expression member position defaults to `Int` (keyed `Int#3`). `Nat` members are only produced by an explicit `Nat`-typed context, which v1 does not provide — so `Nat#n` keys are unreachable in v1 and Task 3's test pins that.
- **Strict TDD, non-negotiable.** Every task that adds or changes production behaviour (Tasks 1-8) is structured red→green: Step 1 writes the test(s) for that step's behaviour, Step 2 runs them and states the expected failure mode, and only the step(s) after that add implementation — write the minimum code needed to turn that step's tests green, not more. Do not write or edit implementation code before its corresponding test exists and has been observed to fail for the stated reason. The two exceptions are explicit and self-declared in their own task text, not silent: Task 9 ("a pin, not a feature") and the round-trip portion of Task 10 add no new production code, so their tests are written and are expected to pass immediately, pinning existing behaviour rather than driving new behaviour — that is not a violation of red-green, it is the correct shape for a regression pin. Tests assert observable behaviour (elaboration result, parsed AST shape as the parser's actual output contract, emitted/erased runtime value) through the project's public entry points (`Program.elaborate/1`, `Parser.parse/1`, `Cure.Compiler.compile_and_load/1`, `Cure.Elab.Union`'s public API) — never private call counts or internal-only state.
- **Tests are immutable once green-confirmed correct.** Once a test in this plan passes for the right reason, the only way to keep it passing through a later change is to fix the implementation — never delete, skip, loosen, or rewrite the test to match new code. The sole exception is a test later proven to itself encode wrong behaviour; if that happens, state explicitly what the correct behaviour is and where the test diverges from it before changing it. "The test is inconvenient" or "editing the test is the fastest path to green" are never valid reasons.

---

## ⚠️ Two corrections to the spec, discovered during planning

These are **binding**; the plan implements the corrected behaviour, not the spec's original text.

**Correction 1 — constructor names MUST be family-qualified (contradicts spec §7 and §10).**
The spec says the constructor atom "can literally be the key" (`:'Int'`, erasing to `{:'Int', 42}`). This is unsound. `Inductive.declare/3` (`lib/cure/core/inductive.ex:332-345`) registers constructors in a **global flat map** `env.ctors`, with a global `ctor_to_family`:

```elixir
Enum.reduce(ctors, env, fn %{name: cname} = c, acc ->
  %{acc | ctors: Map.put(acc.ctors, cname, c),
          ctor_to_family: Map.put(acc.ctor_to_family, cname, fname)}
end)
```

Two unions that each have an `Int` member would both register ctor `:Int`; last write wins, and `ctor_to_family[:Int]` would point at the wrong family, silently miscompiling every `match` on the other union.

**Therefore:** constructor names are `:"<union_key>$<member_key>"`. Erasure becomes `{:'Union<Int|String>$Int', 42}` for type members and `:'Union<Int|String>$Int#3'` for literal members. Uglier in crash dumps than the spec promised; correct.

**Correction 2 — no synthetic module is needed (simplifies spec §6 and §10).**
The spec requires generated families be "emitted exactly once per program, into a synthetic module, referenced remotely." **This is unnecessary.** `Emit.compile_forms/2` builds its work list from `%Env{defs: defs}` **only** (`lib/cure/elab/emit.ex:56-64`); `module_forms/4` (`emit.ex:127-147`) emits a module attribute, an export attribute, and one function form per **def** — no family descriptor, no ctor function. Constructors are lowered **inline** at each use site (`emit.ex:263-309`): nullary → bare atom, n-ary → tagged tuple. Types erase entirely.

So two modules independently declaring the identical family produce **no BEAM-level conflict** — registration is a pure `Map.put` of identical content, and every use site lowers to the identical inline tag. `Program.import_origins/1` (`program.ex:436-447`) is a **defs-only** map and is irrelevant to types and constructors.

**Therefore:** no synthetic-module task exists in this plan. The cross-module identity requirement reduces to: *both modules must derive the same key, the same ctor names, the same arities, and the same quantities.* Task 8 tests exactly that.

---

## File Structure

| File | Status | Responsibility |
|---|---|---|
| `lib/cure/elab/union.ex` | **create** | The whole feature's brain: canonicalisation (flatten/normalise/key/dedupe/sort/collapse), admission rules, family generation. Pure and directly unit-testable. |
| `lib/cure/compiler/parser.ex` | modify | `\|` in type-expression position (Task 1); typed patterns `n: Int` (Task 2). |
| `lib/cure/compiler/printer.ex` | modify | Print `{:union_type, meta, members}` (Task 1). |
| `lib/cure/elab/declarations.ex` | modify | Per-declaration union pre-pass; `idx_to_core` lookup clause (Task 4). |
| `lib/cure/elab/elaborator.ex` | modify | Injection coercion (Task 5); widening (Task 6); typed-pattern match arms (Task 7). |
| `lib/cure/elab/resolution.ex` | modify | Rekey generated union families when a member type is rekeyed (Task 8). |
| `test/cure/elab/union_canonical_test.exs` | **create** | Task 3 — canonicalisation unit tests. |
| `test/cure/compiler/union_parse_test.exs` | **create** | Tasks 1–2 — parser tests. |
| `test/cure/elab/union_test.exs` | **create** | Tasks 4–7 — elaboration, injection, match. |
| `test/cure/elab/union_identity_test.exs` | **create** | Task 8 — cross-module + shadowing identity. |
| `test/cure/types/union_classic_test.exs` | **create** | Task 9 — classic pipeline does not crash. |
| `test/oracle/union/` | **create** | Task 10 — oracle cluster. |

**Dependency order:** 1 → 2 → 3 → 4 → 5 → 6 → 7 → 8 → 9 → 10. Task 3 (canonicaliser) is the keystone; 4–8 all consume it.

---

### Task 1: Parser — `|` in type-expression position

**Files:**
- Modify: `lib/cure/compiler/parser.ex:4681-4752` (rename + new wrapper), `:3287`, `:4696`, `:4742`, `:4871`
- Modify: `lib/cure/compiler/printer.ex` (new clause), `test/cure/compiler/printer_totality_test.exs:122-133` (`@all_node_kinds`)
- Create: `test/cure/compiler/union_parse_test.exs`
- Modify: `test/fixtures/printer_totality.cure`

**Interfaces:**
- Produces: AST node `{:union_type, [], [member_ast, ...]}` — **meta is an empty keyword list**, matching the type-expression parser's existing no-`line`/`col` convention (`parser.ex:4743`, `:4736`, `:4707`). Members are ordinary type-expression ASTs or literal ASTs, **in source order** (canonicalisation happens later, in the elaborator).
- Produces: `parse_type_arrow/1` — the old `parse_type_expr/1`, renamed. Callers that must **not** absorb `|` call this.

**Background you need:**
- `parse_type_expr/1` is the single entry point for every type annotation (**17 real call sites** — verified by `grep -n 'parse_type_expr' lib/cure/compiler/parser.ex`, which returns 20 hits: the 1 definition, 2 prose-comment mentions, and 17 actual invocations). It is a hand-written recursive-descent ladder; there is no precedence table for types.
- The `:bar` token is `%Token{type: :bar, value: "|"}` (`lexer.ex:1432-1443`).
- **The landmine:** `parser.ex:3287` sits in `parse_type_def_adt`'s `{:lparen, _}` branch — the RHS-starts-with-`(` case (`type Endo = (Nat) -> Nat`). **Correction (verified against the real branch):** this branch has *no* existing bar-continuation logic of its own — the "`|` means next ADT variant" behaviour actually lives in the separate catch-all branch a few lines below (`parser.ex:3319-3326`, `parse_more_variants`), which parses the first variant via `parse_type_variant`, not `parse_type_expr`, and never reaches this call site. The real reason line 3287 **must** switch to `parse_type_arrow/1` is narrower but still binding: today, `type Endo = (Nat) -> Nat | X` hitting this branch has no bar-continuation logic at all, so a stray `|` here is a parse error; that is the strict, conservative behaviour to preserve. If the new `|`-aware `parse_type_expr` is left in place at 3287 instead, `type Endo = (Nat) -> Nat | X` would silently start parsing as a union-typed alias RHS rather than erroring or falling through to variant-parsing — a **silent semantics change** to this branch, not a break of an already-working "next variant" feature. Switch it to `parse_type_arrow/1` to preserve current behaviour; do not carry forward the "it protects ADT variant continuation" rationale in commit messages or comments, since that description does not match this branch.
- **The second landmine:** arrow *codomain* recursion (`parser.ex:4696`, `:4742`, `:4871`) must also call `parse_type_arrow/1`, so that `A -> B | C` parses as `(A -> B) | C` — i.e. `|` binds **looser** than `->`, per spec §5.1. (Independently re-enumerated: these three plus 3287 are the complete and correct "must switch" set — no other call site among the 17 sits adjacent to a following token that a leading/infix `|` would collide with.)

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/union_parse_test.exs`:

```elixir
defmodule Cure.Compiler.UnionParseTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # Collect every {tag, meta, children} 3-tuple in the AST.
  defp collect(node, acc) do
    acc = if is_tuple(node) and tuple_size(node) == 3, do: [node | acc], else: acc

    cond do
      is_tuple(node) -> Enum.reduce(Tuple.to_list(node), acc, &collect/2)
      is_list(node) -> Enum.reduce(node, acc, &collect/2)
      true -> acc
    end
  end

  defp find_union(ast) do
    collect(ast, []) |> Enum.find(&match?({:union_type, _, _}, &1))
  end

  describe "union types in type-expression position" do
    test "parses a two-member union in a parameter annotation" do
      ast = parse!("mod M\n  fn f(x: Int | String) -> Int = 1\nend\n")

      assert {:union_type, [], [a, b]} = find_union(ast)
      assert {:variable, _, "Int"} = a
      assert {:variable, _, "String"} = b
    end

    test "parses a three-member union in a return annotation" do
      ast = parse!("mod M\n  fn f(x: Int) -> Int | String | Bool = 1\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 3
    end

    test "parses literal members" do
      ast = parse!("mod M\n  fn f(x: 3 | :north | \"s\") -> Int = 1\nend\n")

      assert {:union_type, [], [i, s, str]} = find_union(ast)
      assert {:literal, m1, 3} = i
      assert m1[:subtype] == :integer
      assert {:literal, m2, :north} = s
      assert m2[:subtype] == :symbol
      assert {:literal, m3, "s"} = str
      assert m3[:subtype] == :string
    end

    test "parses an applied type as a member" do
      ast = parse!("mod M\n  fn f(x: List(Int) | Int) -> Int = 1\nend\n")
      assert {:union_type, [], [{:function_call, fm, _}, {:variable, _, "Int"}]} = find_union(ast)
      assert fm[:name] == "List"
    end

    test "allows a leading bar" do
      ast = parse!("mod M\n  typealias P = | Int | String\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 2
    end

    test "binds LOOSER than -> : `A -> B | C` is `(A -> B) | C`" do
      ast = parse!("mod M\n  typealias P = Int -> Bool | String\nend\n")

      assert {:union_type, [], [arrow, {:variable, _, "String"}]} = find_union(ast)
      assert {:function_call, am, _} = arrow
      assert am[:function_type] == true
    end

    test "parses a union nested in a type argument" do
      ast = parse!("mod M\n  fn f(m: Map(String, Int | Bool)) -> Int = 1\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 2
    end

    test "parses a parenthesised union in domain position" do
      ast = parse!("mod M\n  typealias P = (Int | String) -> Bool\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 2
    end
  end

  describe "regression: `|` in ADT declaration bodies still means constructor alternatives" do
    test "plain enum is unaffected" do
      ast = parse!("mod M\n  type Color = Red | Green | Blue\nend\n")
      assert find_union(ast) == nil
    end

    test "enum whose first variant is parenthesised-arrow-shaped is unaffected" do
      # This is the landmine: parser.ex:3287 routes this RHS through the type-expr
      # parser, where a `|` previously meant "next variant".
      ast = parse!("mod M\n  type Handler = Cb(Int) | Nope\nend\n")
      assert find_union(ast) == nil
      assert {:container, meta, variants} = ast |> collect([]) |> Enum.find(&match?({:container, _, _}, &1))
      assert meta[:container_type] == :enum
      assert length(variants) == 2
    end

    test "the empty type `type Empty = |` still parses" do
      ast = parse!("mod M\n  type Empty = |\nend\n")
      assert find_union(ast) == nil
    end
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/compiler/union_parse_test.exs`
Expected: FAIL — `find_union/1` returns `nil` (no `:union_type` node exists yet), so the first assertion `{:union_type, [], [a, b]} = nil` raises `MatchError`.

- [ ] **Step 3: Rename `parse_type_expr/1` to `parse_type_arrow/1`**

In `lib/cure/compiler/parser.ex`, rename **the definition only** at line 4681:

```elixir
  defp parse_type_arrow(state) do
```

Then update **only the recursive calls inside the arrow ladder** — these must NOT absorb `|`:

- `parser.ex:4696` (codomain of the parenthesised arrow) → `parse_type_arrow(state)`
- `parser.ex:4742` (codomain of the unary `Name -> B` arrow) → `parse_type_arrow(state)`
- `parser.ex:4871` (codomain inside `maybe_parse_function_type/2`) → `parse_type_arrow(state)`
- `parser.ex:3287` (the ADT-declaration alias-RHS probe) → `parse_type_arrow(state)`

Leave every **other** `parse_type_expr` call site alone — they should get the new `|`-aware entry point.

- [ ] **Step 4: Add the new `parse_type_expr/1` wrapper**

Insert immediately **above** the (now-renamed) `parse_type_arrow/1` in `lib/cure/compiler/parser.ex`:

```elixir
  # Type-expression entry point. `|` binds LOOSER than `->`, so
  # `A -> B | C` is `(A -> B) | C`. A leading `|` is permitted.
  #
  # Members are collected in SOURCE order; canonicalisation (flatten, dedupe,
  # sort) is the elaborator's job — see Cure.Elab.Union.
  defp parse_type_expr(state) do
    state =
      case peek(state) do
        %Token{type: :bar} -> advance(state) |> skip_newlines()
        _ -> state
      end

    {first, state} = parse_union_first_member(state)
    {rest, state} = parse_union_members(state)

    case rest do
      [] -> {first, state}
      _ -> {{:union_type, [], [first | rest]}, state}
    end
  end
```

**Literal members — corrected during plan review (regression risk found).** The plan originally proposed adding an unconditional literal-token guard at the very top of `parse_type_arrow/1` itself. **That is wrong and would be a severe regression**: `parse_type_arrow/1` is the SHARED function underneath all 17 real call sites of the old `parse_type_expr/1`, not just union members — including every dependent type-index argument (`Bounded(3)`, `typealias Char = Bounded(1114112)` in `lib/std/char.cure:17`, `Equivalent(Int, 3, 3)`). Verified against the real `idx_to_core/5` (`lib/cure/elab/declarations.ex`): today, a bare numeral in type position parses to `{:variable, [scope: :local], "3"}`, and `idx_to_core`'s `{:variable, _meta, name}` clause recovers the integer via `numeric_index_value(name)` — there is **no** `idx_to_core` clause for `{:literal, ...}`. Making `parse_type_arrow/1` unconditionally emit `{:literal, [subtype: :integer], 3}` for *every* caller would send that node straight to `idx_to_core`'s catch-all, `{:error, {:unsupported_index_expr, {:literal, ...}}}` — silently breaking `Bounded(3)`, `Bounded(1114112)`, and every other existing numeral-in-type-index declaration in the tree and the standard library.

**The fix: scope literal-recognition to union-member parsing only, and leave `parse_type_arrow/1` byte-for-byte unchanged from today's `parse_type_expr/1` body** (do not add anything to its `case token.type do` — the rename in Step 3 is the *only* change to that function). Two new functions carry the literal logic instead:

```elixir
  # The first candidate member of a possible union. A literal-shaped token is
  # ONLY treated as a literal member if a `|` immediately follows — e.g. the
  # `3` in `3 | String`. If no `|` follows, fall through to parse_type_arrow/1
  # UNCHANGED, so every existing non-union numeral-in-type-position use
  # (Bounded(3), Equivalent(Int, 3, 3), Bounded(1114112)) keeps parsing to
  # {:variable, [scope: :local], "N"} exactly as it does today and keeps
  # working through idx_to_core's existing numeric_index_value path — this
  # function never needs to change.
  defp parse_union_first_member(state) do
    token = peek(state)
    next = peek_at(state, 1)

    if literal_token?(token) and match?(%Token{type: :bar}, next) do
      {literal(literal_subtype(token.type), token), advance(state)}
    else
      parse_type_arrow(state)
    end
  end

  defp parse_union_members(state) do
    case peek(state) do
      %Token{type: :bar} ->
        state = advance(state) |> skip_newlines()
        {member, state} = parse_union_member(state)
        {rest, state} = parse_union_members(state)
        {[member | rest], state}

      _ ->
        {[], state}
    end
  end

  # A subsequent member, reached only after a `|` has already been consumed —
  # so, unlike the first member, we already KNOW we're inside a union here.
  # A literal-shaped token is unconditionally a literal member; no lookahead
  # needed (this covers the `4` in `3 | 4`, which is not itself followed by
  # another `|`).
  defp parse_union_member(state) do
    token = peek(state)

    if literal_token?(token) do
      {literal(literal_subtype(token.type), token), advance(state)}
    else
      parse_type_arrow(state)
    end
  end

  defp literal_token?(%Token{type: t}), do: t in [:integer, :float, :string, :atom, :char, :bool]

  defp literal_subtype(:integer), do: :integer
  defp literal_subtype(:float), do: :float
  defp literal_subtype(:string), do: :string
  defp literal_subtype(:atom), do: :symbol
  defp literal_subtype(:char), do: :char
  defp literal_subtype(:bool), do: :boolean
```

Note: `parse_union_members/1` does **not** `skip_newlines` before peeking for `:bar`. That is deliberate — a newline terminates the type annotation, and skipping it would let the parser swallow the `|` of a following ADT variant.

`peek_at/2` (`parser.ex:5652-5664`, alongside `peek/1` and `peek_ahead/2`) is the existing nil-safe 1-token-lookahead helper — the same one `parse_map_pair/1` uses for its own `identifier`-then-`:colon` lookahead. Always guard with a `match?`/`!= nil` check before reading `next.type`, since it returns `nil` past end-of-stream.

- [ ] **Step 5: Run the parser test**

Run: `mix test test/cure/compiler/union_parse_test.exs`
Expected: PASS.

- [ ] **Step 6: Add the printer clause**

`test/cure/compiler/printer_totality_test.exs` gate 4 (line 328-332) statically diffs a hand-maintained `@all_node_kinds` list against a regex scan of `printer.ex` for `defp to_string({:<kind>,`. A new node tag **must** have both.

In `lib/cure/compiler/printer.ex`, add near the other type-position clauses (e.g. after the `:sigma_type` clause around line 997):

```elixir
  defp to_string({:union_type, _meta, members}, depth, indent) do
    members
    |> Enum.map(&to_string(&1, depth, indent))
    |> Enum.join(" | ")
  end
```

In `test/cure/compiler/printer_totality_test.exs`, add `:union_type` to `@all_node_kinds` (line 122-133).

- [ ] **Step 7: Add a fixture construct so printer gates 2/3 exercise it**

Append to `test/fixtures/printer_totality.cure`:

```
typealias UnionFixture = Int | String | Bool
```

- [ ] **Step 8: Run the printer + full parser suites**

Run: `mix test test/cure/compiler/`
Expected: PASS, including `printer_totality_test.exs` and `lossless_roundtrip_test.exs`.

- [ ] **Step 9: Commit**

```bash
git add lib/cure/compiler/parser.ex lib/cure/compiler/printer.ex \
        test/cure/compiler/union_parse_test.exs \
        test/cure/compiler/printer_totality_test.exs \
        test/fixtures/printer_totality.cure
git commit -m "feat(parser): union types in type-expression position

\`|\` binds looser than \`->\`. The ADT-declaration alias-RHS probe and every
arrow codomain now call parse_type_arrow/1 so they do not absorb the bar."
```

---

### Task 2: Parser — typed patterns (`n: Int`) in match arms

**Files:**
- Modify: `lib/cure/compiler/parser.ex:2088-2101` (`maybe_wrap_as/2`)
- Modify: `lib/cure/compiler/printer.ex`, `test/cure/compiler/printer_totality_test.exs`
- Modify: `test/cure/compiler/union_parse_test.exs`

**Interfaces:**
- Consumes: `parse_type_expr/1` from Task 1 (a typed pattern's annotation may itself be a union — `rest: String | Bool`, spec §9).
- Produces: AST node `{:typed_pattern, meta, [name_string, type_ast]}` where `meta` carries `line`/`col`.

**Background:**
- `parse_match_arm/1` (`parser.ex:2076`) parses the pattern with the ordinary expression parser, then calls `maybe_wrap_as/2` at `parser.ex:2079` (the function itself is defined at `parser.ex:2088-2101`), which already handles the `x @ pat` as-pattern by peeking for `:at`. **A `:colon` clause slots in beside it with zero disruption**, because `:colon` has no infix binding power, so `parse_expr(state, 0)` already stops cleanly at it.
- Scope, per spec §5.1: match-arm top level **and** constructor-pattern arguments. **Brace-delimited record/map patterns are excluded.** `parse_map_pair/1` (`parser.ex:967`) has two relevant branches: the **explicit key:value** branch (`identifier` immediately followed by `:colon`, `parser.ex:972-979`) and the separate **field-punning** branch (`identifier` followed by `,`/`}`/newline, i.e. *no* colon, `parser.ex:981-991`). It is the explicit key:value branch — not the punning branch, despite the plan's original text conflating the two — that already unconditionally claims `identifier :` inside braces; do not touch either branch.
- **Hazard:** `parse_match_arm_tail/2` calls `expect(state, :arrow)`. A pattern annotation whose type is a *function type* (`x: A -> B`) would have its `->` stolen by the arm. Require parens for that case; do not attempt to disambiguate.

- [ ] **Step 1: Write the failing test**

Append to `test/cure/compiler/union_parse_test.exs`:

```elixir
  describe "typed patterns in match arms" do
    test "binds a name at a member type" do
      ast =
        parse!("""
        mod M
          fn f(x: Int | String) -> Int = match x
            n: Int -> 1
            s: String -> 2
        end
        """)

      arms = collect(ast, []) |> Enum.filter(&match?({:match_arm, _, _}, &1))
      pats = Enum.map(arms, fn {:match_arm, meta, _} -> meta[:pattern] end)

      assert [{:typed_pattern, _, ["n", {:variable, _, "Int"}]},
              {:typed_pattern, _, ["s", {:variable, _, "String"}]}] = Enum.sort_by(pats, fn {_, _, [n, _]} -> n end)
    end

    test "a typed pattern's annotation may itself be a union (sub-union branch)" do
      ast =
        parse!("""
        mod M
          fn f(x: Int | String | Bool) -> Int = match x
            n: Int -> 1
            rest: String | Bool -> 2
        end
        """)

      arms = collect(ast, []) |> Enum.filter(&match?({:match_arm, _, _}, &1))
      pats = Enum.map(arms, fn {:match_arm, meta, _} -> meta[:pattern] end)

      assert Enum.any?(pats, fn
               {:typed_pattern, _, ["rest", {:union_type, [], ms}]} -> length(ms) == 2
               _ -> false
             end)
    end

    test "literal patterns in match arms are untouched" do
      ast =
        parse!("""
        mod M
          fn f(x: Int) -> Int = match x
            3 -> 1
            _ -> 2
        end
        """)

      assert collect(ast, []) |> Enum.find(&match?({:typed_pattern, _, _}, &1)) == nil
    end

    test "a typed pattern also parses inside a constructor-pattern argument list" do
      # Cons(n: Int, rest) — this is NOT a separate parser change (see Step 4):
      # parse_call_args/1 and parse_more_args/1 (parser.ex:692-720) already call
      # maybe_wrap_as/2 on every parsed argument, the same helper parse_match_arm/1
      # uses, so this comes free once Step 3's :colon clause lands.
      ast = parse!("mod M\n  fn f(x) -> Int = match x\n    Cons(n: Int, rest) -> 1\n    _ -> 2\nend\n")

      assert collect(ast, []) |> Enum.any?(&match?({:typed_pattern, _, ["n", {:variable, _, "Int"}]}, &1))
    end
  end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/compiler/union_parse_test.exs -k "typed patterns"`
Expected: FAIL — no `:typed_pattern` node is produced; the pattern parses as a bare `{:variable, _, "n"}` and the trailing `: Int` derails the arm (all four tests in this `describe` block fail, including the constructor-argument one — `maybe_wrap_as/2` doesn't yet have a `:colon` clause anywhere it's called from).

- [ ] **Step 3: Add the `:colon` clause to `maybe_wrap_as/2`**

In `lib/cure/compiler/parser.ex`, add a clause **before** the existing `{:variable, vm, name}` / `:at` clause at line 2088:

```elixir
  defp maybe_wrap_as({:variable, vm, name}, state) do
    case peek(state) do
      %Token{type: :colon} ->
        state = advance(state)
        {type_ast, state} = parse_type_expr(state)
        {{:typed_pattern, vm, [name, type_ast]}, state}

      %Token{type: :at} ->
        state = advance(state)
        {inner, state} = parse_expr(state, 0)
        {inner, state} = maybe_wrap_as(inner, state)
        {{:as_pattern, vm, [name, inner]}, state}

      _ ->
        {{:variable, vm, name}, state}
    end
  end

  defp maybe_wrap_as(pattern, state), do: {pattern, state}
```

(Merge the two `:colon` / `:at` branches into the single existing clause; do not add a second `maybe_wrap_as({:variable, ...})` head, which would be unreachable.)

- [ ] **Step 4: Confirm constructor-pattern arguments already get typed patterns for free**

**Correction, found during plan review: no new parser code is needed here.** The plan originally assumed the argument-list loop needed to be located and a `maybe_wrap_as/2` call added to it. That is not so: `parse_call_args/1` and `parse_more_args/1` (`lib/cure/compiler/parser.ex:692-720`, invoked from `parse_call/2` at `parser.ex:671`, itself reached from the postfix-call branch at `parser.ex:202`) **already** call `maybe_wrap_as/2` on every parsed argument today, at lines 701 and 716 — the exact same helper `parse_match_arm/1` calls at line 2079. So once Step 3's `:colon` clause lands in `maybe_wrap_as/2`, `Cons(n: Int, rest)` parses to a `:typed_pattern` node for `n` with **zero additional production-code changes** — Step 1's "constructor-pattern argument list" test above already exercises and proves this. This step is therefore just verification, not implementation: read `parser.ex:692-720` and confirm the two `maybe_wrap_as/2` call sites are there before moving on; do not add a duplicate call.

It is safe in expression position because `f(x: 1)` is not valid Cure surface syntax today (argument labels are a separate, deferred feature).

- [ ] **Step 5: Add the printer clause and register the node kind**

In `lib/cure/compiler/printer.ex`:

```elixir
  defp to_string({:typed_pattern, _meta, [name, type_ast]}, depth, indent) do
    name <> ": " <> to_string(type_ast, depth, indent)
  end
```

Add `:typed_pattern` to `@all_node_kinds` in `test/cure/compiler/printer_totality_test.exs`.

- [ ] **Step 6: Run the tests**

Run: `mix test test/cure/compiler/`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add lib/cure/compiler/parser.ex lib/cure/compiler/printer.ex \
        test/cure/compiler/union_parse_test.exs \
        test/cure/compiler/printer_totality_test.exs
git commit -m "feat(parser): typed patterns \`n: Int\` in match arms and ctor args

Brace-delimited record/map patterns are deliberately excluded: parse_map_pair
already claims \`identifier :\` there as field-punning."
```

---

### Task 3: The canonicaliser — `Cure.Elab.Union`

This is the keystone. It is a **pure function** over surface member ASTs plus an `Env`, and every later task consumes it.

**Files:**
- Create: `lib/cure/elab/union.ex`
- Create: `test/cure/elab/union_canonical_test.exs`

**Interfaces:**
- Produces:
  - `Cure.Elab.Union.member_key(core_term) :: String.t()` — the type-distinguishing canonical printing of a **lowered, nf'd** Core type.
  - `Cure.Elab.Union.canonicalise(member_asts, scope, env) :: {:ok, [member()]} | {:error, term()}` where
    `member() :: %{key: String.t(), ctor_suffix: String.t(), payload: nil | Core.Term.t(), lit_type_key: nil | String.t()}`.
    The list is flattened, deduped, and **lexically sorted by `:key`**.
  - `Cure.Elab.Union.family_key(members) :: atom()` — `:"Union<k1|k2|...>"`.
  - `Cure.Elab.Union.ctor_key(family_key, member) :: atom()` — `:"<family_key>$<member_key>"`.
  - `Cure.Elab.Union.union_family?(atom) :: boolean()` — true iff the atom looks like a generated union key.
- Consumes: `Cure.Elab.Declarations.lower_type/3` (`declarations.ex:1292`) to lower a member AST to Core; `Cure.Core.Normalise.nf/3` with `Context.empty(env)` to reach full normal form.

**Why `nf`, not `whnf` (spec §6 step 2):** plain `eval` leaves a neutral global application inside an index (`Bounded(1+1)`) stuck rather than folding it to `Bounded(2)`. Without full normal form, two *definitionally equal* ground members would print as different keys and silently produce two distinct families for one type. `Normalise.nf(Context.empty(env), term, delta: :certified)` is the required call; `Context.empty/1` is at `lib/cure/core/context.ex:29`, and the precedent for this exact call from declaration time is `lib/cure/types/reduce.ex:100-106`.

**Key format (see Global Constraints):**
- Type member: the printed Core type — `Int`, `List(Int)`, `Std.Option#Option`.
- Literal member: `<TypeKey>#<printed value>` — `Int#3`, `String#"4"`, `Atom#:4`, `Char#'c'`, `Bool#true`, `Float#4.0`.
  The `<TypeKey>#` prefix is what keeps `"4"` (`String#"4"`) and `:4` (`Atom#:4`) from colliding on `4`, **and** it makes the literal/type-overlap check (spec §5.2) a pure string comparison: reject iff some literal member's `lit_type_key` equals some type member's `key`.

- [ ] **Step 1: Write the failing test**

Create `test/cure/elab/union_canonical_test.exs`:

```elixir
defmodule Cure.Elab.UnionCanonicalTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.Env
  alias Cure.Elab.{Declarations, Union}

  # Elaborate a prelude of declarations, returning the resulting Env.
  defp env_for(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    items = case ast do {:block, _, xs} -> xs; x -> [x] end

    {:ok, env} =
      Enum.reduce_while(items, {:ok, Env.empty()}, fn decl, {:ok, env} ->
        case Declarations.elaborate(decl, env) do
          {:ok, env2} -> {:cont, {:ok, env2}}
          err -> {:halt, err}
        end
      end)

    env
  end

  # Parse a bare type expression by wrapping it in a typealias and digging the RHS out.
  defp type_ast(src) do
    {:ok, toks} = Lexer.tokenize("typealias T = " <> src <> "\n", emit_events: false)
    {:ok, {:type_annotation, _, [rhs]}} = Parser.parse(toks, emit_events: false)
    rhs
  end

  defp members(src, env) do
    {:union_type, [], asts} = type_ast(src)
    Union.canonicalise(asts, [], env)
  end

  defp key(src, env) do
    {:ok, ms} = members(src, env)
    Union.family_key(ms)
  end

  @base ""

  describe "set semantics" do
    test "Int | String and String | Int produce the identical family key" do
      env = env_for(@base)
      assert key("Int | String", env) == key("String | Int", env)
    end

    test "the key is sorted lexically" do
      env = env_for(@base)
      assert key("String | Int", env) == :"Union<Int|String>"
    end

    test "Int | Int dedupes to a single member (caller collapses to Int)" do
      env = env_for(@base)
      assert {:ok, [%{key: "Int"}]} = members("Int | Int", env)
    end
  end

  describe "keys are type-distinguishing" do
    test "the string \"4\" and the atom :4 do not collide" do
      env = env_for(@base)
      {:ok, ms} = members("\"4\" | :4", env)
      keys = Enum.map(ms, & &1.key)
      assert length(Enum.uniq(keys)) == 2
      assert "String#\"4\"" in keys
      assert "Atom#:4" in keys
    end

    test "a bare numeral member defaults to Int" do
      env = env_for(@base)
      {:ok, ms} = members("3 | String", env)
      assert Enum.any?(ms, &(&1.key == "Int#3"))
      # Nat-keyed literal members are unreachable in v1 (Global Constraints).
      refute Enum.any?(ms, &String.starts_with?(&1.key, "Nat#"))
    end
  end

  describe "flattening and alias unfolding" do
    test "(A | B) | C flattens to three members" do
      env = env_for("typealias P = Int | String\n")
      {:ok, ms} = members("P | Bool", env)
      assert Enum.map(ms, & &1.key) |> Enum.sort() == ["Bool", "Int", "String"]
    end

    test "typealias members unfold before keying" do
      env = env_for("typealias MyInt = Int\n")
      assert key("MyInt | String", env) == key("Int | String", env)
    end
  end

  describe "full-nf soundness (spec §6 step 2)" do
    test "definitionally-equal members with different syntax key identically" do
      # Bounded(1+1) and Bounded(2) are the same type; whnf would leave the
      # `1+1` index stuck as a neutral and produce two distinct keys.
      env = env_for(@base)
      assert key("Bounded(1 + 1) | String", env) == key("Bounded(2) | String", env)
    end
  end

  describe "admission rules (spec §5.2), checked on the CANONICAL member list" do
    test "rejects a non-ground member (a bare type variable)" do
      env = env_for(@base)
      assert {:error, {:union_member_not_ground, _}} = members("a | Int", env)
    end

    test "rejects a literal that overlaps its own type" do
      env = env_for(@base)
      assert {:error, {:union_member_overlap, "Int#3", "Int"}} = members("Int | 3", env)
    end

    test "the overlap check sees through a typealias (admission runs AFTER normalisation)" do
      env = env_for("typealias T = Int\n")
      assert {:error, {:union_member_overlap, "Int#3", "Int"}} = members("T | 3", env)
    end
  end

  describe "ctor naming" do
    test "ctor names are qualified by the family key" do
      env = env_for(@base)
      {:ok, ms} = members("Int | String", env)
      fk = Union.family_key(ms)
      int_m = Enum.find(ms, &(&1.key == "Int"))
      assert Union.ctor_key(fk, int_m) == :"Union<Int|String>$Int"
    end

    test "union_family?/1 recognises a generated key and rejects a user type name" do
      assert Union.union_family?(:"Union<Int|String>")
      refute Union.union_family?(:Option)
    end
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/elab/union_canonical_test.exs`
Expected: FAIL — `Cure.Elab.Union` does not exist (`UndefinedFunctionError`).

- [ ] **Step 3: Write `lib/cure/elab/union.ex`**

```elixir
defmodule Cure.Elab.Union do
  @moduledoc """
  Canonicalisation and family generation for anonymous union types (`Int | String`).

  A union's IDENTITY is its canonical member list: flattened, normalised to full
  normal form, keyed by a type-distinguishing printing, deduped, and lexically
  sorted. That sorted key list names the generated family, so `Int | String` and
  `String | Int` produce literally the same `{:data, name}` and are definitionally
  equal with zero kernel involvement.

  See `docs/superpowers/specs/types/2026-07-11-anonymous-adts-design.md`.
  """

  alias Cure.Core.{Context, Env, Inductive, Normalise}

  @type member :: %{
          key: String.t(),
          payload: nil | tuple(),
          lit_type_key: nil | String.t()
        }

  @prefix "Union<"

  # ── Public API ────────────────────────────────────────────────────────────

  @doc "True iff `atom` is a generated union family key."
  @spec union_family?(atom()) :: boolean()
  def union_family?(atom) when is_atom(atom) do
    atom |> Atom.to_string() |> String.starts_with?(@prefix)
  end

  @doc "The generated family key for a canonical member list."
  @spec family_key([member()]) :: atom()
  def family_key(members) do
    inner = members |> Enum.map(& &1.key) |> Enum.join("|")
    String.to_atom(@prefix <> inner <> ">")
  end

  @doc "The constructor name for `member` within family `family_key`."
  @spec ctor_key(atom(), member()) :: atom()
  def ctor_key(family_key, %{key: k}) do
    String.to_atom(Atom.to_string(family_key) <> "$" <> k)
  end

  @doc """
  Canonicalise a list of surface member ASTs into a sorted, deduped member list.

  Returns `{:error, {:union_member_not_ground, ast}}` or
  `{:error, {:union_member_overlap, lit_key, type_key}}` per spec §5.2.
  """
  @spec canonicalise([tuple()], [String.t()], Env.t()) :: {:ok, [member()]} | {:error, term()}
  def canonicalise(asts, scope, env) do
    with {:ok, raw} <- lower_members(asts, scope, env) do
      members =
        raw
        |> List.flatten()
        |> Enum.uniq_by(& &1.key)
        |> Enum.sort_by(& &1.key)

      case overlap(members) do
        nil -> {:ok, members}
        {lit_key, type_key} -> {:error, {:union_member_overlap, lit_key, type_key}}
      end
    end
  end

  @doc "The type-distinguishing canonical printing of a lowered, nf'd Core type."
  @spec member_key(tuple()) :: String.t()
  def member_key({:int_type}), do: "Int"
  def member_key({:float_type}), do: "Float"
  def member_key({:binary_type}), do: "Binary"
  def member_key({:atom_type}), do: "Atom"
  def member_key({:type, l}), do: "Type#{l}"

  def member_key({:data, name, params, indices}) do
    args = params ++ indices

    case args do
      [] -> Atom.to_string(name)
      _ -> Atom.to_string(name) <> "(" <> Enum.map_join(args, ",", &member_key/1) <> ")"
    end
  end

  def member_key({:nat_lit, n}), do: Integer.to_string(n)
  def member_key({:int_lit, n}), do: Integer.to_string(n)
  def member_key({:float_lit, f}), do: Float.to_string(f)
  def member_key({:bounded_lit, k}), do: Integer.to_string(k)
  def member_key({:atom_lit, a}), do: ":" <> Atom.to_string(a)
  def member_key({:ctor, name, []}), do: Atom.to_string(name)
  def member_key({:global, name}), do: Atom.to_string(name)

  # ── Lowering ──────────────────────────────────────────────────────────────

  defp lower_members(asts, scope, env) do
    Enum.reduce_while(asts, {:ok, []}, fn ast, {:ok, acc} ->
      case lower_member(ast, scope, env) do
        {:ok, ms} -> {:cont, {:ok, acc ++ [ms]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # A literal member becomes a NULLARY constructor: the value is fully determined
  # by the constructor, so there is nothing to store (spec §7).
  defp lower_member({:literal, meta, value}, _scope, _env) do
    case Keyword.get(meta, :subtype) do
      :integer -> {:ok, [lit("Int", Integer.to_string(value))]}
      :float -> {:ok, [lit("Float", Float.to_string(value))]}
      :string -> {:ok, [lit("String", ~s("#{value}"))]}
      :symbol -> {:ok, [lit("Atom", ":" <> Atom.to_string(value))]}
      :char -> {:ok, [lit("Char", "'" <> <<value::utf8>> <> "'")]}
      :boolean -> {:ok, [lit("Bool", to_string(value))]}
      other -> {:error, {:union_member_not_ground, {:literal, other, value}}}
    end
  end

  defp lower_member(ast, scope, env) do
    with {:ok, core} <- Cure.Elab.Declarations.lower_type(ast, scope, env) do
      case Normalise.nf(Context.empty(env), core, delta: :certified) do
        :fuel_exhausted ->
          {:error, {:union_member_not_ground, ast}}

        nf ->
          cond do
            # A member that is ITSELF a union splices its members in (flatten).
            match?({:data, _, [], []}, nf) and union_family?(elem(nf, 1)) ->
              {:ok, explode(env, elem(nf, 1))}

            ground?(nf) ->
              {:ok, [%{key: member_key(nf), payload: nf, lit_type_key: nil}]}

            true ->
              {:error, {:union_member_not_ground, ast}}
          end
      end
    end
  end

  defp lit(type_key, printed) do
    %{key: type_key <> "#" <> printed, payload: nil, lit_type_key: type_key}
  end

  # Recover a union family's canonical members from its registered constructors.
  # A nullary ctor is a literal member; a 1-ary ctor is a type member whose
  # payload is its single argument's type.
  defp explode(env, family_key) do
    prefix = Atom.to_string(family_key) <> "$"

    env
    |> Inductive.ctors_of(family_key)
    |> Enum.map(fn ctor ->
      key = ctor.name |> Atom.to_string() |> String.replace_prefix(prefix, "")

      case ctor.args do
        [] -> %{key: key, payload: nil, lit_type_key: lit_type_key_of(key)}
        [{_n, ty}] -> %{key: key, payload: ty, lit_type_key: nil}
      end
    end)
  end

  # "Int#3" -> "Int". A type key never contains `#` unless it is a rekeyed
  # module-qualified name (`Std.Option#Option`), which is not a literal member,
  # so we only split keys that came from a nullary ctor.
  defp lit_type_key_of(key) do
    case String.split(key, "#", parts: 2) do
      [t, _v] -> t
      _ -> nil
    end
  end

  # A member is ground iff its Core term contains no free variables and no
  # metavariables. Union members are lowered in an empty scope, so any `{:var, _}`
  # is by definition free. Metavariables are the 2-tuple `{:meta, id}`
  # (`lib/cure/elab/unify.ex`, `lib/cure/elab/subst.ex:20`) — there is no 3-tuple
  # `{:meta, _, _}` form anywhere in this codebase, so no clause for it is needed.
  defp ground?(term) do
    not has?(term, fn
      {:var, _} -> true
      {:meta, _} -> true
      _ -> false
    end)
  end

  defp has?(term, pred) when is_tuple(term) do
    if pred.(term) do
      true
    else
      term |> Tuple.to_list() |> Enum.any?(&has?(&1, pred))
    end
  end

  defp has?(list, pred) when is_list(list), do: Enum.any?(list, &has?(&1, pred))
  defp has?(_other, _pred), do: false

  # ── Admission: literal/type overlap (spec §5.2) ────────────────────────────

  defp overlap(members) do
    type_keys = for %{lit_type_key: nil, key: k} <- members, into: MapSet.new(), do: k

    Enum.find_value(members, fn
      %{lit_type_key: nil} ->
        nil

      %{lit_type_key: lt, key: k} ->
        if MapSet.member?(type_keys, lt), do: {k, lt}, else: nil
    end)
  end
end
```

- [ ] **Step 4: Run the canonicaliser test**

Run: `mix test test/cure/elab/union_canonical_test.exs`
Expected: PASS. If the non-ground test fails because a bare lowercase `a` lowers to `{:global, :a}` rather than `{:var, _}`, extend `ground?/1` to also reject `{:global, n}` when `n` is not a registered family/def — add that clause and re-run.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab/union.ex test/cure/elab/union_canonical_test.exs
git commit -m "feat(elab): Cure.Elab.Union — canonicalisation for anonymous unions

Members are lowered, reduced to FULL normal form (nf, not whnf — otherwise
Bounded(1+1) and Bounded(2) key differently), keyed type-distinguishingly,
deduped, and lexically sorted. That sorted key list names the family, so
Int | String and String | Int are literally the same {:data, name}.

Ctor names are qualified by the family key: env.ctors is a GLOBAL flat map,
so a bare :Int ctor would collide across unions and corrupt ctor_to_family."
```

---

### Task 4: Declare the family, and lower `{:union_type, …}` to `{:data, key, [], []}`

**Files:**
- Modify: `lib/cure/elab/union.ex` (add `declare/3`)
- Modify: `lib/cure/elab/declarations.ex:32` (`elaborate/2` — add the pre-pass), `:1329-1525` (`idx_to_core` — add the lookup clause)
- Create: `test/cure/elab/union_test.exs`

**Interfaces:**
- Consumes: `Union.canonicalise/3`, `Union.family_key/1`, `Union.ctor_key/2` (Task 3).
- Produces:
  - `Cure.Elab.Union.declare(member_asts, scope, env) :: {:ok, Env.t(), atom()} | {:ok, Env.t(), tuple()} | {:error, term()}` — declares the family (idempotently) and returns its key. **On a one-member union it returns the member's Core term directly instead of a key** (spec §6 step 6: a one-member union *is* that member; no family is generated).
  - `Cure.Elab.Union.predeclare_all(decl_ast, env) :: {:ok, Env.t()} | {:error, term()}` — walks a declaration's AST for `{:union_type, …}` nodes and declares each family.

**The architectural constraint (discovered during planning):** `idx_to_core/5` returns `{:ok, term}` and **cannot thread a mutated `Env` back out** — every one of its call sites expects that shape (verified: ~13 direct call sites plus 4 more via the `map_idx_to_core/5` wrapper, all consuming a bare `{:ok, term}` / `{:error, reason}`, never `{:ok, env, term}`). So the family cannot be declared as a side-effect of lowering. Instead:

1. **Pre-pass:** at the top of `Declarations.elaborate/2`, walk the declaration's AST, find every `{:union_type, …}`, and declare its family into `env`. `Declarations.elaborate/2` *does* return `{:ok, Env.t()}`, so it can thread the env.
2. **Lowering:** `idx_to_core`'s new `{:union_type, …}` clause then only has to *look the key up* and return `{:ok, {:data, key, [], []}}`.

Declaration is **idempotent**: the key is content-derived, so re-declaring an identical family is an identical `Map.put`. Guard on `Inductive.family?(env, key)` and skip.

- [ ] **Step 1: Write the failing test**

Create `test/cure/elab/union_test.exs`:

```elixir
defmodule Cure.Elab.UnionTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.Program

  describe "family generation" do
    test "a union in a parameter annotation declares its family" do
      src = """
      mod M
        fn f(x: Int | String) -> Int = 1
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert Inductive.family?(env, :"Union<Int|String>")
    end

    test "the family has one constructor per member, family-qualified" do
      src = """
      mod M
        fn f(x: Int | String) -> Int = 1
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      names = env |> Inductive.ctors_of(:"Union<Int|String>") |> Enum.map(& &1.name) |> Enum.sort()
      assert names == [:"Union<Int|String>$Int", :"Union<Int|String>$String"]
    end

    test "a type member's constructor takes one payload argument; a literal member's takes none" do
      src = """
      mod M
        fn f(x: Int | :north) -> Int = 1
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      key = :"Union<Atom#:north|Int>"

      arities =
        env
        |> Inductive.ctors_of(key)
        |> Map.new(fn c -> {c.name, length(c.args)} end)

      assert arities[:"#{key}$Int"] == 1
      assert arities[:"#{key}$Atom#:north"] == 0
    end

    test "Int | String and String | Int declare ONE family, not two" do
      src = """
      mod M
        fn f(x: Int | String) -> Int = 1
        fn g(y: String | Int) -> Int = 2
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      union_families =
        env.families |> Map.keys() |> Enum.filter(&Cure.Elab.Union.union_family?/1)

      assert union_families == [:"Union<Int|String>"]
    end

    test "a one-member union collapses to the member itself — no family is generated" do
      src = """
      mod M
        fn f(x: Int | Int) -> Int = x
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      assert env.families |> Map.keys() |> Enum.filter(&Cure.Elab.Union.union_family?/1) == []
    end
  end

  describe "admission errors surface from elaboration" do
    test "rejects a non-ground member" do
      src = """
      mod M
        fn f(a, x: a | Int) -> Int = 1
      end
      """

      assert {:error, {:union_member_not_ground, _}} = Program.elaborate(src)
    end

    test "rejects a literal overlapping its own type" do
      src = """
      mod M
        fn f(x: Int | 3) -> Int = 1
      end
      """

      assert {:error, {:union_member_overlap, "Int#3", "Int"}} = Program.elaborate(src)
    end
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/elab/union_test.exs`
Expected: FAIL — `idx_to_core` has no `{:union_type, …}` clause, so lowering returns `{:error, {:unsupported_index_expr, {:union_type, …}}}` (`declarations.ex:1525`).

- [ ] **Step 3: Add `declare/3` and `predeclare_all/2` to `Cure.Elab.Union`**

Append to `lib/cure/elab/union.ex`:

```elixir
  # ── Family generation ─────────────────────────────────────────────────────

  @doc """
  Declare the generated family for a union's surface members, idempotently.

  Returns `{:ok, env, {:data, key, [], []}}` for a real union, or
  `{:ok, env, core_term}` for a ONE-member union, which collapses to the member
  itself (spec §6 step 6) — no family is generated.
  """
  @spec declare([tuple()], [String.t()], Env.t()) :: {:ok, Env.t(), tuple()} | {:error, term()}
  def declare(asts, scope, env) do
    with {:ok, members} <- canonicalise(asts, scope, env) do
      case members do
        [%{payload: nil}] = [_one] ->
          # A lone literal member still needs a family: there is no Core term for
          # a bare literal in TYPE position. Fall through to the general path.
          declare_family(members, env)

        [%{payload: payload}] when payload != nil ->
          {:ok, env, payload}

        _ ->
          declare_family(members, env)
      end
    end
  end

  defp declare_family(members, env) do
    key = family_key(members)

    if Inductive.family?(env, key) do
      {:ok, env, {:data, key, [], []}}
    else
      ctors =
        Enum.map(members, fn m ->
          cname = ctor_key(key, m)

          case m.payload do
            nil -> Inductive.ctor(cname, [], [], [], [])
            ty -> Inductive.ctor(cname, [{:v, ty}], [], [:unrestricted], [])
          end
        end)

      case Cure.Elab.Declarations.declare_generated_family(env, key, ctors) do
        {:ok, env2} -> {:ok, env2, {:data, key, [], []}}
        {:error, _} = err -> err
      end
    end
  end

  @doc """
  Walk a declaration's AST, declaring the family for every `{:union_type, …}` it
  contains. Called as a pre-pass because `idx_to_core/5` cannot thread a mutated
  Env back out to its callers.
  """
  @spec predeclare_all(term(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def predeclare_all(ast, env) do
    ast
    |> collect_unions()
    |> Enum.reduce_while({:ok, env}, fn union_ast, {:ok, env} ->
      {:union_type, _meta, members} = union_ast

      case declare(members, [], env) do
        {:ok, env2, _} -> {:cont, {:ok, env2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # Innermost-first, so a nested union (`(A | B) | C`) has its inner family
  # declared before the outer one tries to splice it in.
  defp collect_unions(node) when is_tuple(node) do
    inner = node |> Tuple.to_list() |> Enum.flat_map(&collect_unions/1)
    if match?({:union_type, _, _}, node), do: inner ++ [node], else: inner
  end

  defp collect_unions(list) when is_list(list), do: Enum.flat_map(list, &collect_unions/1)
  defp collect_unions(_other), do: []
```

- [ ] **Step 4: Expose a public generated-family declaration helper**

`declare_parameterized/5` and `declare_indexed_at_min_level/6` are private. Add a public entry point beside `declare_record/4` (`lib/cure/elab/declarations.ex:508-517`):

```elixir
  @doc """
  Declare a compiler-GENERATED, parameterless, index-free inductive family from
  pre-built Core constructor records. Used by `Cure.Elab.Union`.

  Goes through the same kernel gate as every surface declaration —
  `Kernel.check_family`, `check_all_ctors`, `Inductive.positive?` — so a
  generated family cannot bypass the TCB.
  """
  @spec declare_generated_family(Env.t(), atom(), [map()]) :: {:ok, Env.t()} | {:error, term()}
  def declare_generated_family(env, name, ctors) do
    declare_indexed_at_min_level(env, name, [], [], ctors, 0)
  end
```

- [ ] **Step 5: Add the pre-pass to `Declarations.elaborate/2`**

`Declarations.elaborate/2` is a **multi-clause function with SIX existing clauses** (`lib/cure/elab/declarations.ex:26, 32, 131, 139, 146, 150` — the plan's earlier citation of line 32 is only one of the six, the `{:container, meta, variants}` clause; line 26, the `{:function_def, ...}` clause, is the first). **Rename the function name on ALL SIX existing clause headers from `elaborate` to `do_elaborate`** (change `def elaborate(` to `defp do_elaborate(` — or `def do_elaborate(` if any caller outside this module depends on it directly — at each of the six `def elaborate(...)` lines; do not rename only the clause nearest line 32, or the other five clauses remain named `elaborate/2` and collide with the new wrapper head below). Then add ONE new public head, placed before or after the renamed clauses (Elixir dispatches multi-clause functions by pattern match, not declaration order across a rename boundary, but keep it adjacent to the old clauses for readability), that runs the pre-pass first and delegates to `do_elaborate/2`:

```elixir
  @spec elaborate(tuple(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def elaborate(decl, env) do
    with {:ok, env} <- Cure.Elab.Union.predeclare_all(decl, env) do
      do_elaborate(decl, env)
    end
  end
```

- [ ] **Step 6: Add the `idx_to_core` lookup clause**

Insert **immediately before** the catch-all at `lib/cure/elab/declarations.ex:1525`:

```elixir
  # An anonymous union. Its family was already declared by the pre-pass in
  # `elaborate/2` (idx_to_core cannot thread a mutated Env back out), so this
  # only has to recompute the content-derived key and look it up.
  defp idx_to_core({:union_type, _meta, members}, scope, _fam, env, _ctx) do
    with {:ok, ms} <- Cure.Elab.Union.canonicalise(members, scope, env) do
      case ms do
        [%{payload: payload}] when payload != nil -> {:ok, payload}
        _ -> {:ok, {:data, Cure.Elab.Union.family_key(ms), [], []}}
      end
    end
  end
```

- [ ] **Step 7: Run the tests**

Run: `mix test test/cure/elab/union_test.exs test/cure/elab/union_canonical_test.exs`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add lib/cure/elab/union.ex lib/cure/elab/declarations.ex test/cure/elab/union_test.exs
git commit -m "feat(elab): declare generated union families; lower union_type to {:data,key,[],[]}

Families are pre-declared by a per-declaration pass, because idx_to_core/5
returns {:ok, term} and cannot thread a mutated Env back out to its callers.
Declaration is idempotent (the key is content-derived) and goes through the
same kernel gate as every surface declaration."
```

---

### Task 5: Injection at check-position

**Files:**
- Modify: `lib/cure/elab/elaborator.ex:1658-1672` (`elaborate_expr_checked_fallback/5`)
- Modify: `test/cure/elab/union_test.exs`

**Interfaces:**
- Consumes: `Union.union_family?/1`, `Union.member_key/1`, `Union.ctor_key/2` (Task 3).
- Produces: no new public API — a behavioural change to check-mode elaboration.

**Background:** `elaborate_expr_checked_fallback/5` is the **single infer-then-check funnel**; every non-special expression flows through it. It currently discards the inferred type (`_type`). The injection belongs here: when the expected type normalises to a generated union family and the term's inferred type is definitionally one of its members, wrap the term in that member's constructor.

Everything the elaborator builds is independently re-verified by `Kernel.check/3`, so the elaborator stays untrusted — an incorrect injection is caught by the kernel, not silently accepted.

**Literal members** need a separate hook, because a literal's *inferred* type is `Int`, not the union — but the union's member is the literal `3`, not the type `Int`. Handle literals in the existing type-directed literal clause at `elaborator.ex:1483`, which already inspects `expected_core` and emits a different Core node (the `nat_lit` / `bounded_lit` precedent).

- [ ] **Step 1: Write the failing test**

Append to `test/cure/elab/union_test.exs`:

```elixir
  describe "injection at check-position" do
    test "a member value is injected when checked against the union" do
      src = """
      mod M
        fn f(n: Int) -> Int | String = n
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()
      assert {:ctor, :"Union<Int|String>$Int", [{:var, 0}]} = body
    end

    test "a literal is injected into its literal member constructor" do
      src = """
      mod M
        fn f() -> 3 | 4 = 3
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert {:ctor, :"Union<Int#3|Int#4>$Int#3", []} = Env.get_def(env, :f).body
    end

    test "a value whose type is not a member is rejected" do
      src = """
      mod M
        fn f(b: Bool) -> Int | String = b
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end

    test "the Map case: a union value position accepts any member" do
      src = """
      mod M
        use Std.Map
        fn f(m: Map(String, Int | String)) -> Map(String, Int | String) =
          Std.Map.insert(m, "k", 1)
      end
      """

      assert {:ok, _} = Program.elaborate(src)
    end
  end

  defp unwrap_lams({:lam, _g, _dom, body}), do: unwrap_lams(body)
  defp unwrap_lams(term), do: term
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/elab/union_test.exs -k "injection"`
Expected: FAIL with `{:error, {:conversion_failure, …}}` — `Kernel.check` rejects an `Int` at type `Union<Int|String>`, exactly as designed (there is no subtyping).

- [ ] **Step 3: Add the injection to the check-mode funnel**

Replace `elaborate_expr_checked_fallback/5` (`lib/cure/elab/elaborator.ex:1658-1672`):

```elixir
  defp elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env) do
    if Unify.has_meta?(expected_core) do
      {:error, {:unsolved_metavariable_in_type, expected_core}}
    else
      with {:ok, term, type} <- elaborate_expr_typed(expr, names, ctx, env) do
        term = maybe_inject_union(term, type, expected_core, ctx, env)

        with :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
          {:ok, term}
        end
      end
    end
  end

  # Anonymous-union subsumption: a coercion inserted by the ELABORATOR in check
  # mode only — never a kernel rule (spec §8). If the expected type is a generated
  # union family and the term's inferred type is one of its members, inject.
  # Otherwise pass the term through untouched and let the kernel reject it.
  defp maybe_inject_union(term, type, expected_core, ctx, env) do
    with {:data, ukey, [], []} <- Kernel.normalize(ctx, expected_core),
         true <- Cure.Elab.Union.union_family?(ukey),
         member_term <- Quote.reify(type, Context.length(ctx), Context.signature(ctx)),
         cname <- Cure.Elab.Union.ctor_key(ukey, %{key: Cure.Elab.Union.member_key(member_term)}),
         true <- Inductive.get_ctor(env, cname) != nil do
      {:ctor, cname, [term]}
    else
      _ -> term
    end
  end
```

- [ ] **Step 4: Add the literal injection clause**

In the type-directed literal clause at `lib/cure/elab/elaborator.ex:1483`, add a branch to the `cond` **before** the `int?`/`string?` branches:

```elixir
    cond do
      union_literal_ctor(meta, value, expected_core, ctx, env) != nil ->
        {:ok, {:ctor, union_literal_ctor(meta, value, expected_core, ctx, env), []}}

      string? ->
        # ... existing branches unchanged
```

and add the helper beside it:

```elixir
  # A literal checked against a union whose members include that literal
  # elaborates to the member's NULLARY constructor (spec §7): the value is fully
  # determined by the constructor, so there is nothing to store.
  defp union_literal_ctor(meta, value, expected_core, ctx, env) do
    with {:data, ukey, [], []} <- Kernel.normalize(ctx, expected_core),
         true <- Cure.Elab.Union.union_family?(ukey),
         {:ok, key} <- literal_member_key(Keyword.get(meta, :subtype), value),
         cname <- Cure.Elab.Union.ctor_key(ukey, %{key: key}),
         true <- Inductive.get_ctor(env, cname) != nil do
      cname
    else
      _ -> nil
    end
  end

  defp literal_member_key(:integer, v), do: {:ok, "Int#" <> Integer.to_string(v)}
  defp literal_member_key(:float, v), do: {:ok, "Float#" <> Float.to_string(v)}
  defp literal_member_key(:string, v), do: {:ok, "String#" <> ~s("#{v}")}
  defp literal_member_key(:symbol, v), do: {:ok, "Atom#:" <> Atom.to_string(v)}
  defp literal_member_key(:char, v), do: {:ok, "Char#'" <> <<v::utf8>> <> "'"}
  defp literal_member_key(:boolean, v), do: {:ok, "Bool#" <> to_string(v)}
  defp literal_member_key(_other, _v), do: :error
```

**These key builders MUST stay byte-for-byte identical to `Union.lower_member/3`'s `lit/2` calls (Task 3).** A divergence produces a ctor name that does not exist and the injection silently no-ops into a conversion failure. If you find yourself editing one, edit both — or better, extract a shared `Union.literal_key(subtype, value)` and call it from both sites.

- [ ] **Step 5: Refactor — extract the shared literal-key builder**

Do the extraction now rather than leaving the duplication: move `literal_member_key/2` into `Cure.Elab.Union` as a public `literal_key(subtype, value) :: {:ok, String.t()} | :error`, and have both `Union.lower_member/3` and the elaborator call it.

- [ ] **Step 6: Run the tests**

Run: `mix test test/cure/elab/union_test.exs`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add lib/cure/elab/elaborator.ex lib/cure/elab/union.ex test/cure/elab/union_test.exs
git commit -m "feat(elab): inject union members at check-position

Subsumption is an elaborator-inserted coercion in check mode only, never a
kernel rule. The injected {:ctor, …} is independently re-verified by
Kernel.check, so the elaborator stays untrusted."
```

---

### Task 6: Widening — union-to-wider-union coercion

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (`maybe_inject_union/5`)
- Modify: `test/cure/elab/union_test.exs`

**Interfaces:**
- Consumes: Task 5's `maybe_inject_union/5`.
- Produces: no new public API.

**Background (spec §8):** when the term's inferred type is a union whose member set is a **subset** of the expected union's, insert a **widening** — a Core `:case` remapping each source constructor to its counterpart in the wider family. This is a real function, not a cast: the two families are genuinely distinct types.

The Core `:case` needs a motive. Follow `bool_case/4` (`elaborator.ex:3310`) as the minimal hand-built-`:case` precedent: `{:case, scrut, motive, [{cname, arity, body}, …]}`, where the motive is the constant type family returning the wider union.

- [ ] **Step 1: Write the failing test**

Append to `test/cure/elab/union_test.exs`:

```elixir
  describe "widening" do
    test "a narrower union is widened into a wider one" do
      src = """
      mod M
        fn narrow(n: Int) -> Int | String = n
        fn wide(n: Int) -> Int | String | Bool = narrow(n)
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :wide).body |> unwrap_lams()
      assert {:case, _scrut, _motive, branches} = body

      assert branches |> Enum.map(fn {c, ar, _} -> {c, ar} end) |> Enum.sort() ==
               [{:"Union<Int|String>$Int", 1}, {:"Union<Int|String>$String", 1}]
    end

    test "widening to a union that does not contain every source member is rejected" do
      src = """
      mod M
        fn narrow(n: Int) -> Int | Bool = n
        fn wide(n: Int) -> Int | String = narrow(n)
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end
  end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/elab/union_test.exs -k "widening"`
Expected: FAIL with `{:error, {:conversion_failure, …}}` — `Union<Int|String>` is not convertible with `Union<Bool|Int|String>`.

- [ ] **Step 3: Implement widening**

Extend `maybe_inject_union/5` in `lib/cure/elab/elaborator.ex` with a widening branch, tried when the plain member injection does not apply:

```elixir
  defp maybe_inject_union(term, type, expected_core, ctx, env) do
    with {:data, ukey, [], []} <- Kernel.normalize(ctx, expected_core),
         true <- Cure.Elab.Union.union_family?(ukey) do
      member_term = Quote.reify(type, Context.length(ctx), Context.signature(ctx))

      cond do
        # (a) the term's type IS a narrower union — widen it.
        match?({:data, _, [], []}, member_term) and
            Cure.Elab.Union.union_family?(elem(member_term, 1)) ->
          widen(term, elem(member_term, 1), ukey, expected_core, ctx, env)

        # (b) the term's type is a plain member — inject it.
        true ->
          cname = Cure.Elab.Union.ctor_key(ukey, %{key: Cure.Elab.Union.member_key(member_term)})
          if Inductive.get_ctor(env, cname), do: {:ctor, cname, [term]}, else: term
      end
    else
      _ -> term
    end
  end

  # Remap each constructor of the narrower family to its counterpart in the wider
  # one. Every source member must exist in the target, or we return the term
  # untouched and let the kernel reject it with a conversion failure.
  defp widen(term, from_key, to_key, to_core, ctx, env) do
    from_prefix = Atom.to_string(from_key) <> "$"
    sig = Context.signature(ctx)

    branches =
      sig
      |> Inductive.ctors_of(from_key)
      |> Enum.map(fn ctor ->
        suffix = ctor.name |> Atom.to_string() |> String.replace_prefix(from_prefix, "")
        target = String.to_atom(Atom.to_string(to_key) <> "$" <> suffix)
        arity = length(ctor.args)

        cond do
          Inductive.get_ctor(env, target) == nil -> :missing
          arity == 0 -> {ctor.name, 0, {:ctor, target, []}}
          true -> {ctor.name, 1, {:ctor, target, [{:var, 0}]}}
        end
      end)

    if Enum.any?(branches, &(&1 == :missing)) do
      term
    else
      # `Cure.Core.Grade.unrestricted()` (not the bare atom) to match the
      # established `:lam`/`:pi` idiom elsewhere in elaborator.ex (see bool_case/4)
      # — grade.ex's own doc asks callers to go through the module's API rather
      # than write grade atoms literally. `Grade.unrestricted() == :unrestricted`
      # by definition, so this is a style match, not a behaviour change.
      motive = {:lam, Cure.Core.Grade.unrestricted(), {:data, from_key, [], []}, to_core}
      {:case, term, motive, branches}
    end
  end
```

- [ ] **Step 4: Run the tests**

Run: `mix test test/cure/elab/union_test.exs`
Expected: PASS. If the kernel rejects the motive, compare against `build_motive/6` (`elaborator.ex`, used by `elaborate_match/6`) — a parameterless, index-free family's motive is a single lambda over the scrutinee, and `to_core` must be weakened under that binder if it mentions any de Bruijn variable. A union family's Core term `{:data, key, [], []}` is **closed**, so no weakening is needed; if you hit a de Bruijn error here, the bug is elsewhere.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab/elaborator.ex test/cure/elab/union_test.exs
git commit -m "feat(elab): widen a narrower union into a wider one at check-position

A real Core :case remapping each ctor to its counterpart — not a cast. The two
families are genuinely distinct types."
```

---

### Task 7: Elimination — typed patterns become an ordinary Core `:case`

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (`elaborate_match/6`'s arm desugaring)
- Modify: `test/cure/elab/union_test.exs`

**Interfaces:**
- Consumes: the `{:typed_pattern, meta, [name, type_ast]}` node (Task 2); `Union.ctor_key/2` (Task 3).
- Produces: no new public API.

**Background:** `elaborate_match/6` (`elaborator.ex:1994`) requires the scrutinee to infer to `{:vdata, dname, …}` — which a union-typed scrutinee does, for free, once the union is a real family. `elaborate_branches/11` (`elaborator.ex:2753`) then iterates over the **declared constructors** and looks each up in an arm map built by `partition_arms/4`. So the entire job is: **rewrite `{:typed_pattern, _, [name, type_ast]}` arms into ordinary constructor-pattern arms** before `partition_arms` runs, and let the existing machinery do coverage, exhaustiveness, and totality.

- A **type member** arm `n: Int` becomes the ctor pattern `Union<…>$Int(n)`.
- A **literal member** arm `:north` is already a literal pattern; map it to the nullary ctor `Union<…>$Atom#:north()`.
- A **sub-union** arm `rest: String | Bool` expands to *one arm per member of the sub-union*, each binding a fresh variable and injecting it into the sub-union — i.e. Task 6's widening run backwards.

**Overlap (spec §9):** a member named by more than one arm resolves to the **first arm in source order**. Core's `:case` takes one branch per constructor (`term.ex:49`), so this must be settled at elaboration time. `partition_arms/4` builds a `%{cname => arm}` map, so simply fold arms in source order with `Map.put_new/3`.

- [ ] **Step 1: Write the failing test**

Append to `test/cure/elab/union_test.exs`:

```elixir
  describe "elimination via typed patterns" do
    test "a match over a union becomes a Core :case with one branch per member" do
      src = """
      mod M
        fn f(x: Int | String) -> Int = match x
          n: Int -> n
          s: String -> 0
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()
      assert {:case, _scrut, _motive, branches} = body

      assert branches |> Enum.map(fn {c, ar, _} -> {c, ar} end) |> Enum.sort() ==
               [{:"Union<Int|String>$Int", 1}, {:"Union<Int|String>$String", 1}]
    end

    test "a literal member is matched as a bare literal and binds nothing" do
      src = """
      mod M
        fn f(x: Int | :north) -> Int = match x
          n: Int -> n
          :north -> 0
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()
      assert {:case, _, _, branches} = body

      arities = Map.new(branches, fn {c, ar, _} -> {c, ar} end)
      assert arities[:"Union<Atom#:north|Int>$Atom#:north"] == 0
      assert arities[:"Union<Atom#:north|Int>$Int"] == 1
    end

    test "a non-exhaustive match is rejected by the existing coverage check" do
      src = """
      mod M
        fn f(x: Int | String) -> Int = match x
          n: Int -> n
      end
      """

      assert {:error, {:missing_branch, _}} = Program.elaborate(src)
    end

    test "a branch naming a non-member is rejected" do
      src = """
      mod M
        fn f(x: Int | String) -> Int = match x
          n: Int -> n
          b: Bool -> 0
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end

    test "a sub-union branch binds the narrowed value" do
      src = """
      mod M
        fn f(x: Int | String | Bool) -> Int | String | Bool = match x
          n: Int -> n
          rest: String | Bool -> rest
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()
      assert {:case, _, _, branches} = body
      # One Core branch per member of the WIDE union — the sub-union arm expanded.
      assert length(branches) == 3
    end
  end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/elab/union_test.exs -k "elimination"`
Expected: FAIL — `partition_arms/4` does not recognise `{:typed_pattern, …}` and cannot map it to a constructor name.

- [ ] **Step 3: Desugar typed-pattern arms into constructor-pattern arms**

Add a desugaring pass in `lib/cure/elab/elaborator.ex`. **Placement, precisely:** it does NOT slot in next to `desugar_list_patterns/1` (`elaborator.ex:4752`) or `try_guard_match/6` (`elaborator.ex:3104`) — those two calls are not adjacent in `elaborate_match/6` (`elaborator.ex:1994`); several other desugaring passes (`desugar_tuple_scrutinee`, `desugar_as_patterns`, `desugar_tuple_args`, `desugar_nested_arms`, `desugar_ctor_guards`) and the scrutinee's own elaboration run between them. The pass needs the scrutinee's union family key, which is known only *after* the scrutinee is elaborated and only inside the `{:vdata, dname, …}` branch — so, unlike the other desugarings (which run early, before the scrutinee is even elaborated), this one **must** run late: inside the `{:vdata, dname, combined_vals}` branch, on the arms, with `dname` threaded in, immediately before the `elaborate_branches/11` call (see the wiring at the end of this step):

```elixir
  # Rewrite `{:typed_pattern, _, [name, type_ast]}` arms into ordinary ctor-pattern
  # arms against the union family `dname`. A sub-union arm expands into ONE arm per
  # member of the sub-union (spec §9). Overlapping arms resolve first-in-source-order,
  # which the downstream `Map.put_new`-shaped partition already does.
  defp desugar_union_arms(arms, dname, scope, env) do
    if Cure.Elab.Union.union_family?(dname) do
      Enum.reduce_while(arms, {:ok, []}, fn arm, {:ok, acc} ->
        case expand_union_arm(arm, dname, scope, env) do
          {:ok, expanded} -> {:cont, {:ok, acc ++ expanded}}
          {:error, _} = err -> {:halt, err}
        end
      end)
    else
      {:ok, arms}
    end
  end

  defp expand_union_arm({:match_arm, meta, body} = arm, dname, scope, env) do
    case Keyword.get(meta, :pattern) do
      {:typed_pattern, pm, [name, type_ast]} ->
        with {:ok, members} <- Cure.Elab.Union.canonicalise([type_ast], scope, env) do
          arms =
            Enum.map(members, fn m ->
              cname = Cure.Elab.Union.ctor_key(dname, m)

              pattern =
                case m.payload do
                  nil -> {:function_call, [name: Atom.to_string(cname)], []}
                  _ -> {:function_call, [name: Atom.to_string(cname)], [{:variable, pm, name}]}
                end

              {:match_arm, Keyword.put(meta, :pattern, pattern), body}
            end)

          {:ok, arms}
        end

      {:literal, lm, value} ->
        with {:ok, key} <- Cure.Elab.Union.literal_key(Keyword.get(lm, :subtype), value) do
          cname = Cure.Elab.Union.ctor_key(dname, %{key: key})
          pattern = {:function_call, [name: Atom.to_string(cname)], []}
          {:ok, [{:match_arm, Keyword.put(meta, :pattern, pattern), body}]}
        end

      _ ->
        {:ok, [arm]}
    end
  end
```

**Note on the sub-union arm's binder.** When a sub-union arm expands into several arms, each bound `rest` is the *payload of one member*, not a value of the sub-union — so the body, which expects `rest : String | Bool`, would be ill-typed. Wrap the binder: the expanded pattern binds a fresh variable, and the body is rewritten to `let rest = <inject fresh into the sub-union> in body`.

**The real `let`-node shape (verified against `parse_let/1`, `lib/cure/compiler/parser.ex:1423`, and its consumer `elaborate_let_block/5`, `lib/cure/elab/elaborator.ex:4475` — there is no `:let_binding` tag anywhere in the tree; grepping for it turns up nothing but unrelated REPL helper function names).** A `let` is `{:assignment, meta, [pattern, value]}`:

- **Tag:** `:assignment`, not `:let_binding`.
- **`meta`:** a keyword list carrying `:line`, `:col`, the flag `let: true`, and — only when the surface source has an annotation — `:type_annotation` (the type AST). There is **no** `:name` or `:type` meta key; the bound name lives in the `pattern` child, not in meta.
- **Children:** exactly `[pattern, value]` — the LHS pattern (here, `{:variable, pm, name}`) and the RHS value expression. This is *not* `[value_expr, body_expr]`; the body is not a child of the assignment at all.
- **Sequencing:** `let x = e` followed by more statements is just the bare `{:assignment, ...}` node as one statement in an enclosing block/list — there is no single node that bundles "bind" with "body". To get `let x = e in body` behaviour here, wrap the assignment and the body together in a `{:block, meta, [assignment, body]}` node (mirroring how `parse_let/1` itself builds the inline `let ... in ...` form).

Implement this by emitting, for a sub-union arm, a pattern binding a fresh name and a body wrapped in a real `:assignment` inside a `:block`:

```elixir
                  _ ->
                    fresh = "__u" <> Integer.to_string(:erlang.phash2({name, m.key}))
                    inner_pat = {:function_call, [name: Atom.to_string(cname)], [{:variable, pm, fresh}]}
                    # `rest` is re-injected into the SUB-union so the body typechecks.
                    # Real node shape: {:assignment, meta, [pattern, value]}, meta carries
                    # `let: true` + `:type_annotation` (NOT `:name`/`:type`); the bound name
                    # lives in the pattern child, not in meta. See parse_let/1, parser.ex:1423.
                    assignment_meta = pm |> Keyword.put(:let, true) |> Keyword.put(:type_annotation, type_ast)
                    assignment = {:assignment, assignment_meta, [{:variable, pm, name}, {:variable, pm, fresh}]}
                    wrapped_body = [{:block, pm, [assignment, hd(body)]}]
                    {:match_arm, Keyword.put(meta, :pattern, inner_pat), wrapped_body}
```

The assignment's `:type_annotation` is the sub-union, so Task 5's check-position injection fires and re-injects the payload when `elaborate_let_block/5` checks the RHS against it.

Wire the pass in, inside `elaborate_match/6`'s `{:vdata, dname, combined_vals}` branch, before the `elaborate_branches/11` call:

```elixir
          with {:ok, arms} <- desugar_union_arms(arms, dname, names, env),
               {:ok, branches, join} <-
                 elaborate_branches(arms, names, ctx, env, dname, ...) do
```

- [ ] **Step 4: Run the tests**

Run: `mix test test/cure/elab/union_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab/elaborator.ex test/cure/elab/union_test.exs
git commit -m "feat(elab): eliminate unions via typed patterns

Typed-pattern arms desugar to ordinary ctor-pattern arms before partition_arms
runs, so coverage, exhaustiveness and totality all come from existing machinery.
A sub-union arm expands to one arm per member, re-injecting the payload."
```

---

### Task 8: Cross-module and shadowing identity

The load-bearing soundness property, and the one the spec's review specifically demanded (§13).

**Files:**
- Modify: `lib/cure/elab/resolution.ex`
- Create: `test/cure/elab/union_identity_test.exs`

**Interfaces:**
- Consumes: `Union.union_family?/1`, `Union.family_key/1`, `Union.ctor_key/2`.

**The two properties:**

1. **Same union in two modules ⇒ ONE family.** Two modules independently writing `Int | String` must derive the same key, the same ctor names, the same arities and the same quantities. Per **Correction 2**, no BEAM artifact is emitted, so this is purely an Env-level property — but it must actually hold, or a value built in module A will not typecheck in module B.

2. **Two unrelated same-named local types in two different modules must key DIFFERENTLY.** This is the hazard the spec review found. `Resolution.rekey_module_env/6` (`resolution.ex:93-141`) re-keys a shadowed type's *own declarations* from `:Point` to `:"Mod#Point"`, and `rekey_term/3` (`resolution.ex:36-54`) rewrites `{:data, n, …}` / `{:ctor, n, …}` / `{:case, …}` occurrences via an `amap`. **A compiler-generated union family is not in `declared_type_names(ast)`, so it is not "owned" and will not be rekeyed** — meaning a union `Point | Int` declared in the loser module would embed a now-dangling bare `:Point` and would key identically to an unrelated `Point | Int` in another module.

**The fix:** extend `rekey_module_env/6` so that, after building `amap`, it also rewrites every **generated union family**: rewrite each ctor's argument types with `rekey_term/3`, recompute the family key and the ctor names from the rewritten members, re-register under the new key, and add the old→new family and ctor names into `amap` so the existing `rekey_term/3` machinery rewrites every `{:data, …}` / `{:ctor, …}` / `{:case, …}` occurrence in the slice's terms for free.

- [ ] **Step 1: Write the failing test**

Create `test/cure/elab/union_identity_test.exs`:

```elixir
defmodule Cure.Elab.UnionIdentityTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Inductive
  alias Cure.Elab.{Program, Union}

  defp union_families(env) do
    env.families |> Map.keys() |> Enum.filter(&Union.union_family?/1) |> Enum.sort()
  end

  describe "cross-module identity" do
    test "two modules writing the same union share ONE family" do
      src = """
      mod A
        fn mk(n: Int) -> Int | String = n
      end

      mod B
        use A
        fn use_it(n: Int) -> Int | String = A.mk(n)
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert union_families(env) == [:"Union<Int|String>"]
    end

    test "a union value built in A typechecks and eliminates in B" do
      src = """
      mod A
        fn mk(n: Int) -> Int | String = n
      end

      mod B
        use A
        fn out(n: Int) -> Int = match A.mk(n)
          i: Int -> i
          s: String -> 0
      end
      """

      assert {:ok, _} = Program.elaborate(src)
    end
  end

  describe "shadowing: unrelated same-named types must NOT merge" do
    test "two modules' unrelated local `Point` types key differently" do
      src = """
      mod A
        type Point = APoint
        fn mk(p: Point) -> Point | Int = p
      end

      mod B
        type Point = BPoint
        fn mk(p: Point) -> Point | Int = p
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      # Two DISTINCT union families — one per module's Point.
      assert length(union_families(env)) == 2

      # And neither key mentions a bare, unqualified `Point`.
      refute :"Union<Int|Point>" in union_families(env)
    end

    test "each shadowed union's ctors carry the qualified member type" do
      src = """
      mod A
        type Point = APoint
        fn mk(p: Point) -> Point | Int = p
      end

      mod B
        type Point = BPoint
        fn mk(p: Point) -> Point | Int = p
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      for key <- union_families(env) do
        payload_types =
          env
          |> Inductive.ctors_of(key)
          |> Enum.flat_map(fn c -> Enum.map(c.args, fn {_n, ty} -> ty end) end)

        # No ctor argument may reference a bare `:Point` — it must be qualified.
        refute Enum.any?(payload_types, &match?({:data, :Point, _, _}, &1))
      end
    end
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/elab/union_identity_test.exs`
Expected: The cross-module tests PASS (identity is content-derived, so it works already). The **shadowing tests FAIL** — both modules' unions key as `:"Union<Int|Point>"` and collapse into one family whose ctor payload is a dangling bare `:Point`.

- [ ] **Step 3: Rekey generated union families**

In `lib/cure/elab/resolution.ex`, inside `rekey_module_env/6`, after `amap` and `def_map` are built and **before** the `%Env{env | …}` struct update, add a pass that rewrites generated union families and extends `amap` with their old→new names:

```elixir
    # Compiler-generated union families are not "owned" by any surface declaration,
    # so they are not in `amap` — but their ctor argument types may reference a type
    # that IS being rekeyed. Rewrite those payload types, recompute the content-derived
    # family key and ctor names, and fold the renames into `amap` so `rekey_term/3`
    # rewrites every {:data,…} / {:ctor,…} / {:case,…} occurrence in the slice for free.
    {env, amap} = rekey_union_families(env, amap, def_map)
```

and implement it:

```elixir
  defp rekey_union_families(%Env{} = env, amap, def_map) do
    env.families
    |> Map.keys()
    |> Enum.filter(&Cure.Elab.Union.union_family?/1)
    |> Enum.reduce({env, amap}, fn old_key, {env, amap} ->
      old_ctors = Inductive.ctors_of(env, old_key)
      old_prefix = Atom.to_string(old_key) <> "$"

      members =
        Enum.map(old_ctors, fn c ->
          suffix = c.name |> Atom.to_string() |> String.replace_prefix(old_prefix, "")

          case c.args do
            [] ->
              %{key: suffix, payload: nil, old_ctor: c.name, quantities: c.quantities}

            [{n, ty}] ->
              ty2 = rekey_term(ty, amap, def_map)
              %{key: Cure.Elab.Union.member_key(ty2), payload: {n, ty2}, old_ctor: c.name, quantities: c.quantities}
          end
        end)
        |> Enum.sort_by(& &1.key)

      new_key = Cure.Elab.Union.family_key(members)

      if new_key == old_key do
        {env, amap}
      else
        new_ctors =
          Enum.map(members, fn m ->
            cname = Cure.Elab.Union.ctor_key(new_key, m)

            case m.payload do
              nil -> Inductive.ctor(cname, [], [], [], [])
              {n, ty} -> Inductive.ctor(cname, [{n, ty}], [], m.quantities, [])
            end
          end)

        env =
          env
          |> drop_family(old_key, Enum.map(old_ctors, & &1.name))
          |> Inductive.declare(Inductive.family(new_key, [], [], env.families[old_key].level), new_ctors)

        amap =
          members
          |> Enum.reduce(Map.put(amap, old_key, new_key), fn m, acc ->
            Map.put(acc, m.old_ctor, Cure.Elab.Union.ctor_key(new_key, m))
          end)

        {env, amap}
      end
    end)
  end

  defp drop_family(%Env{} = env, fname, cnames) do
    %Env{
      env
      | families: Map.delete(env.families, fname),
        ctors: Map.drop(env.ctors, cnames),
        ctor_to_family: Map.drop(env.ctor_to_family, cnames)
    }
  end
```

**Ordering matters:** `rekey_union_families/3` must run **before** `rekey_families/4` / `rekey_ctors/4` build the new `%Env{}`, because it *extends* `amap`, and the existing rewriters consume `amap`. If the existing code shadows `env` in the struct-update expression, restructure so the union pass's `env` and `amap` feed into it.

- [ ] **Step 4: Run the tests**

Run: `mix test test/cure/elab/union_identity_test.exs test/cure/elab/resolution_test.exs`
Expected: PASS, including the pre-existing resolution suite.

- [ ] **Step 5: Run the full suite** (this task touches shared resolution machinery)

Run: `mix test`
Expected: PASS, no regressions.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/elab/resolution.ex test/cure/elab/union_identity_test.exs
git commit -m "fix(elab): rekey generated union families when a member type is shadowed

A generated family is not 'owned' by any surface declaration, so it escaped the
rekey pass — two modules' unrelated local \`Point\` types would collapse into one
\`Union<Int|Point>\` family with a dangling bare :Point payload. Recompute the
content-derived key from rekeyed members and fold the rename into amap."
```

---

### Task 9: Classic pipeline does not crash

**Files:**
- Create: `test/cure/types/union_classic_test.exs`

**Interfaces:** none — a pin, not a feature.

**Background (spec §12, as corrected by the spec review):** `Type.resolve/1` has **no clause** for `{:union_type, meta, members}`, so it falls through to the pre-existing unconditional catch-all `def resolve(_), do: :any` (`lib/cure/types/type.ex:362`). That catch-all is what makes "must not crash" true. Classic sees an anonymous union as `:any` (the top type), **not** as its structural `{:union, [...]}` type. That is acceptable: classic's only job here is to not crash while the dependent pipeline does the real checking. **Write no classic code.** This task exists solely to pin the behaviour so a future change to the catch-all cannot silently break it.

- [ ] **Step 1: Write the test**

Create `test/cure/types/union_classic_test.exs`:

```elixir
defmodule Cure.Types.UnionClassicTest do
  @moduledoc """
  Pins spec §12: the classic checker must not crash on a `{:union_type, …}` node.

  It resolves to `:any` via the pre-existing catch-all at `lib/cure/types/type.ex:362`
  — NOT to classic's structural `{:union, [...]}` type. That is deliberate; classic's
  only job here is to not crash while the dependent pipeline does the real checking.
  """
  use ExUnit.Case, async: true

  alias Cure.Types.Type

  test "Type.resolve/1 maps a union_type node to :any rather than raising" do
    node = {:union_type, [], [{:variable, [scope: :local], "Int"}, {:variable, [scope: :local], "String"}]}
    assert Type.resolve(node) == :any
  end
end
```

- [ ] **Step 2: Run it**

Run: `mix test test/cure/types/union_classic_test.exs`
Expected: PASS immediately (no production change needed). If it *raises*, the catch-all is not reached and this task grows a real fix — report before proceeding.

- [ ] **Step 3: Commit**

```bash
git add test/cure/types/union_classic_test.exs
git commit -m "test(types): pin that the classic checker resolves union_type to :any

Zero classic code. The pre-existing catch-all is what makes 'must not crash'
true, so pin it before someone tightens it."
```

---

### Task 10: Oracle cluster + BEAM round-trip

**Files:**
- Create: `test/oracle/union/un01_heterogeneous_map.cure` + `.idr`
- Create: `test/oracle/union/un02_literal_sentinel.cure` + `.idr`
- Create: `test/oracle/union/un03_ffi_wrapper.cure` + `.idr`
- Create: `test/oracle/union/verdicts.json` (generated)
- Modify: `test/cure/elab/union_test.exs` (round-trip)

**Interfaces:** none.

**Background:** the oracle convention is one directory per feature under `test/oracle/`, each holding paired `name.cure` + `name.idr` files plus a `verdicts.json`. `test/oracle_replay_test.exs` auto-discovers clusters and asserts Cure's live accept/reject verdict matches the recorded one. Generate the fixture with `mix cure.oracle union`.

**Scope note — AtomVM.** Spec §13 asks for a round-trip "executed on generic-unix AtomVM." **That is not runnable from this repo**: `cure-lang` is the compiler, and the AtomVM loop lives in the parent `esp32-beam` repo. The in-repo equivalent is a **BEAM round-trip** — compile the module, load it, call it, assert the recovered value. That is what this task does. AtomVM validation is a follow-up **outside this repo** and is listed in the completion report, not silently dropped.

- [ ] **Step 1: Write the three oracle programs**

`test/oracle/union/un01_heterogeneous_map.cure` — the strongest motivating case (spec §1.3): throwaway heterogeneity without declaring a public ADT.

```
mod Un01

use Std.Map

fn describe(v: Int | String | Bool) -> Int = match v
  n: Int -> n
  s: String -> 0
  b: Bool -> 1

fn build() -> Map(String, Int | String | Bool) =
  Std.Map.insert(Std.Map.empty(), "n", 1)
```

`test/oracle/union/un02_literal_sentinel.cure` — literal members as case sentinels.

```
mod Un02

fn dir(d: :north | :south) -> Int = match d
  :north -> 0
  :south -> 1
```

`test/oracle/union/un03_ffi_wrapper.cure` — a discriminating wrapper over a well-typed extern (spec §10).

```
mod Un03

@extern(:erlang, :abs, 1)
fn raw_abs(n: Int) -> Int

fn magnitude(n: Int) -> Int | :unsupported = raw_abs(n)
```

Write the paired `.idr` files as the closest Idris2 equivalent, using a named sum (Idris has no anonymous unions — that divergence is the point, and it goes in `verdicts.json`'s `reason`).

- [ ] **Step 2: Generate the verdicts fixture**

Run: `mix cure.oracle union`
Expected: `test/oracle/union/verdicts.json` is written with a `"cure": "accept"` verdict per program. Where Cure accepts and Idris cannot express the construct, set `"relation": "cure_stricter"` (or `"idris_only": false`) with a non-empty `reason` — the replay test **requires** a non-empty reason on any divergence.

- [ ] **Step 3: Run the oracle replay**

Run: `mix test test/oracle_replay_test.exs`
Expected: PASS — the new `union` cluster is auto-discovered.

- [ ] **Step 4: Add the BEAM round-trip test**

Append to `test/cure/elab/union_test.exs`:

```elixir
  describe "BEAM round-trip" do
    test "construct, match, and recover the value" do
      src = """
      mod URT
        fn wrap(n: Int) -> Int | String = n
        fn unwrap(x: Int | String) -> Int = match x
          n: Int -> n
          s: String -> 0
        fn go(n: Int) -> Int = unwrap(wrap(n))
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)
      assert apply(:"Cure.URT", :go, [7]) == 7
    end

    test "a literal member erases to its family-qualified nullary ctor atom" do
      src = """
      mod ULT
        fn pick() -> :north | :south = :north
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)
      assert apply(:"Cure.ULT", :pick, []) == :"Union<Atom#:north|Atom#:south>$Atom#:north"
    end
  end
```

**Verified during plan review:** `Cure.Compiler.compile_and_load/2` (`lib/cure/compiler.ex:216`, `def compile_and_load(source, opts \\ [])`, `@spec compile_and_load(String.t(), keyword()) :: {:ok, module()} | {:error, term()}`). The plan's 1-arg call is valid (the default `opts \\ []` gives a real `/1` clause). It takes a raw source string, compiles through to forms, and — for a plain-function module like this test's — calls `BeamWriter.compile_and_load/1` (`beam_writer.ex:81-92`), which does `:code.load_binary(module, ~c"nofile", binary)`, genuinely loading the module into the running BEAM so the immediately-following `apply/3` works. Per the project's memory, it auto-selects dependent codegen once a module elaborates dependently, which is what we want here.

- [ ] **Step 5: Run the tests**

Run: `mix test test/cure/elab/union_test.exs test/oracle_replay_test.exs`
Expected: PASS.

- [ ] **Step 6: Run the FULL suite once**

Run: `mix test`
Expected: PASS. The one known pre-existing red is the `single_pipeline` fsm test (skipped, `#18`-paused) — it is **not** a regression from this work.

- [ ] **Step 7: Commit**

```bash
git add test/oracle/union test/cure/elab/union_test.exs
git commit -m "test(union): oracle cluster + BEAM round-trip

AtomVM validation is a follow-up outside this repo (cure-lang is the compiler;
the AtomVM loop lives in the parent esp32-beam repo)."
```

---

## Self-Review

**Spec coverage:**

| Spec section | Task |
|---|---|
| §5.1 grammar (`\|` in type-expr, looser than `->`) | 1 |
| §5.1 typed patterns in match arms | 2 |
| §5.2 admission (ground/closed, literal-type overlap) | 3 |
| §6 canonicalisation (flatten, nf, key, dedupe, sort, collapse) | 3 |
| §6 admission runs AFTER normalisation | 3 (test: "sees through a typealias") |
| §6 content-addressed family identity | 3, 4, 8 |
| §6 resolved-identity keying (shadowing) | 8 |
| §7 generated family, auto-derived ctors | 4 — **with Correction 1** (ctors are family-qualified) |
| §8 injection at check-position | 5 |
| §8 widening | 6 |
| §9 elimination via type patterns | 7 |
| §9 sub-union branches | 7 |
| §9 overlapping arms resolve first-in-source-order | 7 |
| §10 erasure (tagged, uniform) | 4, 10 (round-trip asserts the erased form) |
| §10 synthetic module | **DELETED — Correction 2**; families emit no BEAM artifact |
| §11 error taxonomy | 3 (non-ground, overlap), 5 (no matching member), 7 (non-member branch), 7 (non-exhaustive, via existing coverage) |
| §11 "ambiguous numeral" | Global Constraints — numerals default to `Int`; Task 3 pins that `Nat#` keys are unreachable in v1 |
| §12 classic coexistence | 9 |
| §13 testing | 3, 8, 10 |
| §14 out of scope | not implemented, by design |

**Gaps and deviations, stated plainly:**
- **Correction 1** (family-qualified ctor names) contradicts spec §7/§10's erased forms. The spec is wrong; `env.ctors` is a global flat map and bare `:Int` would corrupt `ctor_to_family`.
- **Correction 2** (no synthetic module) simplifies spec §6/§10. Emit walks `env.defs` only.
- **AtomVM round-trip** (§13) is replaced by an in-repo BEAM round-trip; the AtomVM run is outside this repo. Flagged in Task 10 and to be listed in the completion report.

**Type consistency:** `member()` is `%{key, payload, lit_type_key}` throughout. `Union.literal_key/2` is the single source of truth for literal keys, called from both `Union.lower_member/3` (Task 3) and the elaborator's literal clause (Task 5, Step 5 extracts it). `Union.family_key/1` and `Union.ctor_key/2` are used identically in Tasks 3, 4, 5, 6, 7, 8.

**Riskiest steps, flagged for the implementer:**
- Task 1, Step 3: the four call sites that must switch to `parse_type_arrow/1`. Getting `parser.ex:3287` wrong silently changes the behaviour of a parenthesised-first-variant alias RHS (`type Endo = (Nat) -> Nat | X`) from today's parse error into a silently-accepted union-typed alias — the regression tests in Step 1 (including the `Handler = Cb(Int) | Nope` case) are the guard.
- Task 1, Step 4 — **the single highest-severity finding of this review, found and fixed during plan review.** The plan originally proposed an unconditional literal-token guard at the top of `parse_type_arrow/1` — the function underlying all 17 real `parse_type_expr` call sites, not just union members. Verified against the real `idx_to_core/5`: today a bare numeral in type position parses to `{:variable, [scope: :local], "N"}` and is lowered via `numeric_index_value/1`; there is no `idx_to_core` clause for `{:literal, ...}`. The original design would have silently broken `Bounded(3)`, `Bounded(1114112)` (`lib/std/char.cure:17`), `Equivalent(Int, 3, 3)`, and every other existing numeral-in-type-index declaration in the tree — with no test in the plan catching it, since none of Task 1-10's tests exercise a standalone dependent numeral index. **Fixed:** literal-recognition now lives only in `parse_union_first_member/1` (gated on a `|` lookahead via the existing `peek_at/2` helper) and `parse_union_member/1` (unconditional, reached only after a `|` is already consumed) — `parse_type_arrow/1` itself is untouched beyond the Step 3 rename. If you are executing this plan and see a version of Task 1 Step 4 with the guard inside `parse_type_arrow/1`, that is the pre-review draft; use the corrected version.
- Task 7, Step 3: the sub-union binder re-injection. **Resolved during plan review:** the real node is `{:assignment, meta, [pattern, value]}` (not `:let_binding`) — see the corrected snippet and node-shape writeup in this task.
- Task 8, Step 3: ordering inside `rekey_module_env/6` — the union pass extends `amap` and must run before the existing rewriters consume it.

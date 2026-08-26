# Char literal expressions — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A source character literal (`'a'`, `'😀'`) elaborates to the compact `{:bounded_lit, cp}` Core node — the `Char = Bounded(0x110000)` value model — in the dependent pipeline, and the lexer decodes multi-byte UTF-8 char literals.

**Architecture:** A char literal is sugar for a bounded literal at the full Unicode bound `Bounded(0x110000)`. The elaborator change is infer-only (check mode works via the existing `elaborate_expr_checked_fallback` = infer-then-`Kernel.check`). A companion lexer fix decodes UTF-8 so non-ASCII char literals can be produced from real source.

**Tech Stack:** Elixir; Cure dependent elaborator (`lib/cure/elab/elaborator.ex`) + kernel (`lib/cure/core/*`); lexer (`lib/cure/compiler/lexer.ex`). Spec: `docs/superpowers/specs/language/2026-07-10-char-literal-expressions-design.md`.

## Global Constraints

- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>` / `git commit -- <path>`; NEVER `git add -A`/`git add .` (a concurrent agent shares this worktree).
- **Branch:** stay on `autopilot/kernel-parity-batch` (operator preference — no new worktree).
- **One build at a time.** Never run two `mix` suites concurrently. Prefer scoped `mix test <file>`; run the full suite once, alone, at the gate.
- **Strict red-green TDD.** Write the failing test, run it, watch it fail for the right reason, implement minimally, run green, commit.
- **Tests immutable once written.** Go green by changing implementation code only — never by deleting, skipping, weakening, or rewriting a test, unless the test itself is proven to encode wrong behavior (state why explicitly first).
- **Two pipelines:** the dependent machinery is ONLY `lib/cure/elab/*` + `lib/cure/core/*`. IGNORE `lib/cure/compiler/{codegen,pattern_compiler}.ex` and `lib/cure/types/*` (non-dependent decoys). The lexer (`lib/cure/compiler/lexer.ex`) is shared and legitimately in scope for Task 2.

---

### Task 1: Char literal expression elaboration (infer + scope-only loci)

Implements spec §3.1–§3.5. Tested with ASCII source and AST-constructed nodes — needs no lexer change (Task 2 adds emoji-from-source).

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` — `elaborate_expr_typed/4` literal clause (~446-460), `elaborate_expr/3` literal clause (~4987-4994), new private helper `char_type_value/1`.
- Test: `test/cure/elab/char_literal_test.exs` (new).

**Interfaces:**
- Consumes: `{:bounded_lit, k}` Core node + `Inductive.builtin(sig, :bounded)` (both already exist, commit 425f0bb); `Context.signature/1`, `Inductive` alias (both already used in this module).
- Produces: a `{:literal, [subtype: :char], cp}` AST elaborates in infer mode to `{:ok, {:bounded_lit, cp}, {:vdata, bounded_fid, [{:vnat, 0x110000}]}}`, and in the scope-only path to `{:ok, {:bounded_lit, cp}}`. Errors: `{:char_literal_out_of_range, cp}` (cp<0 or cp>0x10FFFF), `{:char_literal_needs_bounded, cp}` (Bounded family unregistered).

- [ ] **Step 1: Write the failing test**

Create `test/cure/elab/char_literal_test.exs`:

```elixir
defmodule Cure.Elab.CharLiteralTest do
  # A character literal is sugar for a compact Bounded literal at the full
  # Unicode bound: `'a'` is `{:bounded_lit, 97}` typed at Char = Bounded(0x110000).
  # One integer at every stage — never a `Next(...First)` tower. (Char literal
  # PATTERNS, string literals, Binary, Std.String are separate wave items.)
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Elaborator}
  alias Cure.Core.{Env, Context}

  defp body_of(env, name), do: Env.get_def(env, name).body

  # An AST char-literal node (the lexer cannot emit an out-of-range or, until
  # Task 2, a non-ASCII one, so drive those directly through the elaborator).
  defp char_node(cp), do: {:literal, [subtype: :char, line: 1, col: 1], cp}

  describe "elaboration: character literal -> compact bounded_lit" do
    test "an ASCII char literal in infer position is {:bounded_lit, cp}" do
      src = """
      mod M
        use Std.Bounded
        typealias Char = Bounded(1114112)
        fn a() -> Char = 'a'
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert {:bounded_lit, 97} = body_of(env, :a)
    end

    test "a full-plane emoji codepoint stays ONE compact node (AST-constructed)" do
      # Until Task 2 (lexer UTF-8), '😀' cannot be lexed from source; drive the
      # 128512 codepoint node straight through the infer-mode elaborator.
      {:ok, env} = Program.elaborate("mod M\n  use Std.Bounded\nend\n")
      sig = env
      ctx = Context.empty(sig)
      assert {:ok, {:bounded_lit, 128_512}, _ty} =
               Elaborator.elaborate_expr_typed(char_node(128_512), [], ctx, sig)
    end

    test "a char literal passed as a plain call argument elaborates (locus 3)" do
      src = """
      mod M
        use Std.Bounded
        typealias Char = Bounded(1114112)
        fn plain(c: Char) -> Char = c
        fn a() -> Char = plain('a')
      end
      """

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "an out-of-range codepoint is rejected cleanly (both loci, no crash)" do
      {:ok, sig} = Program.elaborate("mod M\n  use Std.Bounded\nend\n")
      ctx = Context.empty(sig)

      # locus 1 (infer)
      assert {:error, {:char_literal_out_of_range, 0x110000}} =
               Elaborator.elaborate_expr_typed(char_node(0x110000), [], ctx, sig)
      assert {:error, {:char_literal_out_of_range, -1}} =
               Elaborator.elaborate_expr_typed(char_node(-1), [], ctx, sig)

      # locus 3 (scope-only) — the case that would otherwise crash the kernel
      assert {:error, {:char_literal_out_of_range, 0x110000}} =
               Elaborator.elaborate_expr(char_node(0x110000), [], sig)
      assert {:error, {:char_literal_out_of_range, -1}} =
               Elaborator.elaborate_expr(char_node(-1), [], sig)
    end

    test "a char literal with no Bounded family registered errors cleanly, not a crash" do
      # A genuinely bare Env (no `use Std.Bounded` processed) — unlike every
      # other test above, which registers Bounded via `Program.elaborate` on
      # source containing `use Std.Bounded`. `Env.empty()` has `builtins: %{}`,
      # so `char_type_value/1`'s `:no_bounded` branch is reached for real.
      env = Env.empty()
      ctx = Context.empty(env)

      assert {:error, {:char_literal_needs_bounded, 97}} =
               Elaborator.elaborate_expr_typed(char_node(97), [], ctx, env)
    end
  end
end
```

- [ ] **Step 2: Run it, watch it fail**

Run: `mix test test/cure/elab/char_literal_test.exs`
Expected: FAIL — the ASCII/emoji/plain-call cases error `{:unsupported_expression, {:literal, [subtype: :char], _}}`; the out-of-range and no-Bounded cases return `{:unsupported_expression, ...}` instead of `{:char_literal_out_of_range, _}` / `{:char_literal_needs_bounded, _}`.

- [ ] **Step 3: Implement the infer clause (locus 1)**

In `lib/cure/elab/elaborator.ex`, in `elaborate_expr_typed/4`'s `{:literal, meta, value}` clause (the `case Keyword.get(meta, :subtype)`), add these clauses immediately before the `_ ->` catch-all:

```elixir
      :char when is_integer(value) and value >= 0 and value <= 0x10FFFF ->
        case char_type_value(Context.signature(ctx)) do
          {:ok, ty} -> {:ok, {:bounded_lit, value}, ty}
          :no_bounded -> {:error, {:char_literal_needs_bounded, value}}
        end

      :char when is_integer(value) ->
        {:error, {:char_literal_out_of_range, value}}
```

Then add the private helper (place it near `bounded_expected/2`, ~line 1162):

```elixir
  # The type of every character literal: Char = Bounded(0x110000). A char literal
  # is a codepoint value; the bound 0x110000 (= 1_114_112) is intrinsic, not from
  # context. `:no_bounded` when the Bounded family is unregistered (needs
  # `use Std.Bounded`), so the caller reports a fix-naming error, not a crash.
  defp char_type_value(sig) do
    case Inductive.builtin(sig, :bounded) do
      nil -> :no_bounded
      fid -> {:ok, {:vdata, fid, [{:vnat, 0x110000}]}}
    end
  end
```

- [ ] **Step 4: Implement the scope-only clause (locus 3)**

In the same file, `elaborate_expr/3`'s `{:literal, meta, value}` clause (~4987), add before its `_ ->` catch-all:

```elixir
      :char when is_integer(value) and value >= 0 and value <= 0x10FFFF ->
        {:ok, {:bounded_lit, value}}

      :char when is_integer(value) ->
        {:error, {:char_literal_out_of_range, value}}
```

The guard is required, not cosmetic: an unguarded negative `{:bounded_lit, k}` reaching the kernel raises an uncaught `FunctionClauseError` (`Kernel.infer/2` has no catch-all) — see spec §3.4.

- [ ] **Step 5: Run it green**

Run: `mix test test/cure/elab/char_literal_test.exs`
Expected: PASS (all 5 tests).

- [ ] **Step 6: Scoped regression check**

Run: `mix test test/cure/elab/ test/cure/core/`
Expected: PASS, no regressions.

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/elab/elaborator.ex test/cure/elab/char_literal_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): char literal expressions ('a' -> bounded_lit at Bounded(0x110000))"
```

---

### Task 2: Lexer UTF-8 decoding for char literals

Implements spec §3.6. Enables non-ASCII char literals (`'😀'`) from real source. Two sites in `lex_char/1` have the identical single-raw-byte defect.

**Files:**
- Modify: `lib/cure/compiler/lexer.ex` — `lex_char/1` (886-935): the non-escape branch (`c ->` at ~920) and the escape-fallback arm (`c -> {c, advance(state, 1)}` at ~902); new private helper `decode_char_at/1`.
- Test: `test/cure/compiler/char_lexer_test.exs` (new).

**Interfaces:**
- Consumes: lexer state `%{source: binary, pos: integer, col: integer}`; `advance/2` (moves `pos`+`col` by n bytes); `Token.new(:char, value, line, col)`.
- Produces: `'😀'` lexes to a `:char` token with value `128512`; a truncated/invalid multi-byte tail, OR zero remaining bytes (e.g. a backslash at end-of-source), falls through to the existing `{:error, {:unterminated_char, _, _}}` — never a raised exception.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/char_lexer_test.exs`:

```elixir
defmodule Cure.Compiler.CharLexerTest do
  # `lex_char` must decode a full UTF-8 codepoint, not a single raw byte, so a
  # multi-byte character literal like '😀' becomes its Unicode codepoint (128512),
  # not a lex error. ASCII behavior is unchanged.
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Token}

  defp char_tokens(src) do
    {:ok, toks} = Lexer.tokenize(src)
    for %Token{type: :char} = t <- toks, do: t.value
  end

  test "an ASCII char literal still lexes to its byte/codepoint" do
    assert [97] = char_tokens("fn f() = 'a'")
  end

  test "a multi-byte emoji char literal lexes to its Unicode codepoint" do
    assert [128_512] = char_tokens("fn f() = '😀'")
  end

  test "a 2-byte char (é, U+00E9) lexes to its codepoint, not a raw byte" do
    assert [233] = char_tokens("fn f() = 'é'")
  end

  test "a recognized escape is unaffected" do
    assert [?\n] = char_tokens(~S"fn f() = '\n'")
  end

  test "a truncated multi-byte tail at EOF is an unterminated-char error, not a crash" do
    # Opening quote then a lone UTF-8 lead byte, no closing quote.
    assert {:error, {:unterminated_char, _, _}} = Lexer.tokenize(<<"fn f() = '", 0xF0>>)
  end

  test "a backslash immediately at end-of-source is an unterminated-char error, not a crash" do
    # Regression guard, not a newly-red case: today, `peek(state)` returning nil
    # right after the backslash falls through to the escape-fallback catch-all
    # harmlessly (it binds the loop variable to nil and just advances). The
    # multi-byte-decode fix below must preserve that — `decode_char_at` must not
    # call `:binary.at` past the end of source. This test already passes on the
    # unfixed lexer (same status as the ASCII/escape cases above); it exists to
    # catch a regression if the fix is implemented without the EOF guard.
    assert {:error, {:unterminated_char, _, _}} = Lexer.tokenize("fn f() = '\\", emit_events: false)
  end
end
```

- [ ] **Step 2: Run it, watch it fail**

Run: `mix test test/cure/compiler/char_lexer_test.exs`
Expected: FAIL — the emoji and `é` cases return `{:error, {:unterminated_char, _, _}}` (the lexer reads one byte then hits a continuation byte where it expects `'`), so `char_tokens` crashes on the `{:ok, toks}` match. ASCII/escape/truncated/backslash-at-EOF cases pass (pre-existing behavior; the last two are regression guards for the fix, not currently-broken cases).

- [ ] **Step 3: Implement the decode helper**

In `lib/cure/compiler/lexer.ex`, add near `lex_char/1`:

```elixir
  # Read one character at the current position as a full Unicode codepoint,
  # advancing past all its UTF-8 bytes. ASCII (byte < 0x80) keeps the fast
  # single-byte path. A multi-byte sequence is decoded via String.next_codepoint/1
  # on the remaining source; a truncated/invalid tail yields :invalid so the caller
  # can surface the existing unterminated-char error rather than crash.
  #
  # The `pos >= byte_size(source)` clause is required, not defensive boilerplate:
  # the escape-fallback call site (Step 4) reaches this function even when there
  # is no byte left to read (a backslash at end-of-source) — `peek/1` returns nil
  # there today and that nil falls through harmlessly to its catch-all. Without
  # this guard, `:binary.at(source, pos)` raises `ArgumentError` on an
  # out-of-range position, and `do_tokenize/1`'s `catch` clause does not rescue
  # raised errors (only `throw`), so the lexer would crash instead of returning
  # `{:unterminated_char, _, _}`. Mirrors the existing two-clause guard idiom
  # already used by `peek/1` just below in this file.
  defp decode_char_at(%{source: source, pos: pos}) when pos >= byte_size(source), do: :invalid

  defp decode_char_at(%{source: source, pos: pos} = state) do
    case :binary.at(source, pos) do
      byte when byte < 0x80 ->
        {byte, advance(state, 1)}

      _ ->
        rest = binary_part(source, pos, byte_size(source) - pos)

        case String.next_codepoint(rest) do
          {<<cp::utf8>>, _tail} -> {cp, advance(state, byte_size(<<cp::utf8>>))}
          _ -> :invalid
        end
    end
  end
```

- [ ] **Step 4: Route both sites through the helper**

In `lex_char/1`, replace the escape-fallback arm (currently `c -> {c, advance(state, 1)}` at ~902) with:

```elixir
            _ ->
              case decode_char_at(state) do
                {cp, state2} -> {cp, state2}
                :invalid -> {:invalid, state}
              end
```

and its surrounding `{value, state}` binding must handle `:invalid` — after the inner `case`, if `value == :invalid`, return `{:error, {:unterminated_char, state.line, start_col}, state}` before the "expect closing `'`" check. (Simplest: wrap the closing-quote check in `if value == :invalid, do: {:error, ...}, else: <existing closing-quote case>`.)

Replace the non-escape branch (currently `c -> state = advance(state, 1); ...` at ~920-933) so it decodes first:

```elixir
      _ ->
        case decode_char_at(state) do
          {cp, state} ->
            case peek(state) do
              ?' ->
                state = advance(state, 1)
                token = Token.new(:char, cp, state.line, start_col)
                maybe_emit_event(state, token)
                {:ok, %{state | tokens: [token | state.tokens]}}

              _ ->
                {:error, {:unterminated_char, state.line, start_col}, state}
            end

          :invalid ->
            {:error, {:unterminated_char, state.line, start_col}, state}
        end
```

(The `nil` arm at ~917 is unchanged; keep it. Note the non-escape guard was a bare `c ->`; it becomes `_ ->` since `decode_char_at` re-reads the byte. Ensure the `nil` case still precedes it so EOF is caught first.)

- [ ] **Step 5: Run it green**

Run: `mix test test/cure/compiler/char_lexer_test.exs`
Expected: PASS (all 6 tests).

- [ ] **Step 6: Switch the emoji tests to real source + add end-to-end**

Now that the lexer decodes emoji, update `test/cure/elab/char_literal_test.exs`'s emoji test to use real source instead of the AST-constructed node, and add the end-to-end runtime test (spec §4 items 3, 5). Replace the AST-constructed emoji test body with:

```elixir
    test "a full-plane emoji codepoint stays ONE compact node" do
      src = """
      mod M
        use Std.Bounded
        typealias Char = Bounded(1114112)
        fn emoji() -> Char = '😀'
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert {:bounded_lit, 128_512} = body_of(env, :emoji)
    end

    test "end-to-end: a char literal compiles and runs as its codepoint integer" do
      src = """
      mod CharRun
        use Std.Bounded
        typealias Char = Bounded(1114112)
        fn emoji() -> Char = '😀'
      end
      """

      {:ok, env} = Program.elaborate(src)

      {:ok, mod} =
        Cure.Elab.Emit.compile_and_load(env, module: :"Cure.CharRun", functions: [:emoji])

      assert apply(mod, :emoji, []) == 128_512
    end
```

This edits a test written in Task 1's step 1. That is permitted here because the change is *strengthening* (AST-constructed → real source, plus a new runtime assertion) once its lexer prerequisite lands — not weakening to dodge a failure. The original assertion (`{:bounded_lit, 128_512}`) is preserved; only its input path changes from an AST node to source text, which is the more faithful test. State this reason in the commit message.

Run: `mix test test/cure/elab/char_literal_test.exs`
Expected: PASS.

- [ ] **Step 7: Scoped regression check**

Run: `mix test test/cure/compiler/ test/cure/elab/`
Expected: PASS, no regressions.

- [ ] **Step 8: Commit**

```bash
git add -- lib/cure/compiler/lexer.ex test/cure/compiler/char_lexer_test.exs test/cure/elab/char_literal_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(lexer): decode multi-byte UTF-8 char literals ('😀' -> 128512)

Also strengthens the emoji char-literal test from an AST-constructed node to
real source now that the lexer can produce it, and adds an end-to-end runtime
check (compile + run returns the codepoint integer)."
```

---

## Final gate (after both tasks)

- [ ] Run the full suite ONCE, alone: `mix test`. Expected: green (the pre-existing flaky perf/Antigen seeds noted in the milestone may need a `--seed 0` confirmation run). Confirm no new failures attributable to char literals.

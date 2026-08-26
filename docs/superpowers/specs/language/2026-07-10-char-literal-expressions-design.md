# Char literal expressions — design

**Status:** design approved (operator: "Yea add char literals"; `Char = Bounded(0x110000)` established in the 2026-07-10 milestone, commit 425f0bb).

**Scope:** the *expression* form of a character literal — `'a'`, `'😀'` — in the **dependent** pipeline (`lib/cure/elab/*` + `lib/cure/core/*`), plus one small, contained companion fix to the lexer's UTF-8 decoding for char literals (§3.6) — required because the lexer cannot yet produce a non-ASCII char literal at all, and is not otherwise an elaborator change. Char literal *patterns* (`case c of 'a' ->`), string literals, `Binary`, and `Std.String` are **out of scope** (separate wave items, tasks #25–#30).

## 1. Goal

A source character literal elaborates to the compact `{:bounded_lit, cp}` Core node — the same value model as `Char = Bounded(0x110000)`. `'a'` is the codepoint `97`; `'😀'` is `128512` (requires the lexer fix in §3.6 — see the gap noted in §2). One integer at every stage, never a `Next(…First)` tower. This is the last surface piece needed before `String = List(Char)` string literals can be built on top.

## 2. Background (already in place)

- The lexer already emits a character literal as `{:literal, [subtype: :char, line: L, col: C], cp}`; for single-byte (ASCII, `cp < 0x80`) characters `cp` is the correct codepoint integer (verified: `'a'` → value `97`). **This does not generalize to non-ASCII characters today.** `lex_char/1` (`lib/cure/compiler/lexer.ex:886-935`) reads one raw source *byte* at a time via `peek/1` (`:binary.at/2`) and performs no UTF-8 decoding — for ASCII the byte value happens to equal the codepoint, but a multi-byte character like `'😀'` (4 UTF-8 bytes: `F0 9F 98 80`) is not decoded into codepoint `128512`; instead the lexer consumes the first byte, then finds the second UTF-8 continuation byte where it expects a closing `'`, and fails with `{:error, {:unterminated_char, _, _}}`. Confirmed by running `Cure.Compiler.Lexer.tokenize("fn f() = '😀'")` against this codebase, which returns exactly that error. See §3.6 for the required companion fix.
- The compact Bounded value model landed (425f0bb): `{:bounded_lit, k}` : `Bounded(k+1)` minimal, `check(k, Bounded(n)) = ok` iff `0 ≤ k < n`, erases to the native integer `k`. `@builtin(:bounded)` registers the family from `Std.Bounded`.
- Integer literals already route to `{:bounded_lit, k}` in **check** mode against a `Bounded(n)` type (`elaborate_expr_checked`, the `int?`/`bounded_expected` branch).

Today a `:char` literal is rejected by all three literal dispatchers. `elaborate_expr_typed/4` and `elaborate_expr/3` reject it directly, from their own bare `_` catch-all: `{:error, {:unsupported_expression, {:literal, [subtype: :char, …], cp}}}`. `elaborate_expr_checked/5` has no catch-all of its own for this — it reaches the same error indirectly, by falling through its `cond` to `elaborate_expr_checked_fallback`, which calls `elaborate_expr_typed` and surfaces its catch-all error (see §3.2 locus 2).

## 3. Design

A character literal is **sugar for a bounded literal at the full Unicode bound.** `'a'` ≡ the value `97` typed at `Char = Bounded(0x110000)` (decimal `Bounded(1_114_112)`). The codepoint bound `0x110000` is intrinsic to char-ness — it does not come from context.

### 3.1 Type

`Char` is **not** a new kernel type. It is exactly `Bounded(0x110000)`. A user writes the name via `typealias Char = Bounded(1114112)` (the `typealias` keyword, already landed 6d5d8d6); the literal itself never needs that alias to exist — it produces the `Bounded(0x110000)` type value directly. Defining a canonical `Char` alias in the stdlib is a **separate** convenience item, out of scope here.

Because `Char` δ-reduces to `Bounded(0x110000)`, `'a' : Char` holds definitionally.

### 3.2 Where the change goes — infer only

The elaborator has three literal dispatchers:

1. `elaborate_expr_typed/4` (infer mode, returns `{:ok, term, type_value}`) — **the primary change.**
2. `elaborate_expr_checked/5` (check mode, returns `{:ok, term}`) — **no direct change needed.** Its fallback (`elaborate_expr_checked_fallback`) already does *infer-then-`Kernel.check`*: for a `:char` literal it will call `elaborate_expr_typed` (getting `{:bounded_lit, cp}`) and then `Kernel.check(ctx, {:bounded_lit, cp}, expected)`. The kernel re-derives the expected bound and admits iff `cp < bound`. So `'a'` checks against `Char` (= `Bounded(0x110000)`, `97 < 0x110000`), and — consistent with how integer literals behave — against any `Bounded(n)` with `n > cp`. This polymorphism over the bound is intentional and mirrors integer literals; char-ness is a *syntactic* signal, and the value is a genuine bounded literal.
3. `elaborate_expr/3` (scope-only, no `ctx`/`sig`, returns `{:ok, term}`) — despite the name suggesting type-index positions, it is **not** the type-index path; that is a separate function, `idx_to_core/5` (`lib/cure/elab/declarations.ex:949`), untouched by this spec (see note below). The real reachable path is the **argument-elaboration fallback for plain (non-constructor) function calls**: `elaborate_named_call_scoped` (`elaborator.ex:5001-5005`) maps every call argument through `&elaborate_expr/3`, so a char literal passed as a bare call argument — e.g. `plain('a')` — hits this clause. This is the common path for a literal argument to an ordinary top-level function call, not a rare corner case (confirmed by existing precedent: `classify(0)`, `pred(7)` in `test/cure/elab/literal_pattern_test.exs`, `eq0(0)` in `test/cure/elab/guard_test.exs`, all route their literal arguments through here today). Emits the bare `{:bounded_lit, cp}` Core term with no type (the kernel re-checks later).

   **Note on genuine type-index positions:** a char literal used as a *type-level* index (e.g. inside a family/GADT index expression) would go through `idx_to_core/5`, a wholly separate literal-dispatch path this spec does not touch. That is legitimately out of scope: this spec's own `Char = Bounded(0x110000)` is itself defined using a plain *integer* literal in index position (`typealias Char = Bounded(1114112)`), which `idx_to_core` already handles via its existing numeral machinery; a *char* literal appearing directly in a type index is a distinct surface not needed for this spec's stated goal (§1).

### 3.3 The infer clause (locus 1)

In `elaborate_expr_typed/4`'s `{:literal, meta, value}` `case` on `subtype`, add before the catch-all:

```
:char when is_integer(value) and value >= 0 and value <= 0x10FFFF ->
  case char_type_value(Context.signature(ctx)) do
    {:ok, ty} -> {:ok, {:bounded_lit, value}, ty}
    :no_bounded -> {:error, {:char_literal_needs_bounded, value}}
  end

:char when is_integer(value) ->
  {:error, {:char_literal_out_of_range, value}}
```

where the new private helper:

```
# The type of every character literal: Char = Bounded(0x110000). `:no_bounded`
# when the Bounded family is not registered (needs `use Std.Bounded`), so the
# error names the fix instead of crashing.
defp char_type_value(sig) do
  case Inductive.builtin(sig, :bounded) do
    nil -> :no_bounded
    fid -> {:ok, {:vdata, fid, [{:vnat, 0x110000}]}}
  end
end
```

`0x110000` = `1_114_112`; valid codepoints are `0 ≤ cp ≤ 0x10FFFF`, i.e. `cp < 0x110000`, so `{:bounded_lit, cp}` inhabits `Bounded(0x110000)`. The two-sided guard (`>= 0` and `<= 0x10FFFF`) matters because an AST-constructed literal (not from the lexer) could be out of range; the lexer itself never emits an out-of-range codepoint.

### 3.4 The scope-only clause (locus 3)

In `elaborate_expr/3`'s `subtype` `case`, add:

```
:char when is_integer(value) and value >= 0 and value <= 0x10FFFF ->
  {:ok, {:bounded_lit, value}}

:char when is_integer(value) ->
  {:error, {:char_literal_out_of_range, value}}
```

This mirrors locus 1's range guard (§3.3) rather than deferring the bound check entirely to the kernel. **The guard is required, not merely stylistic — its absence is a crash bug, not just an early-error nicety.** `Kernel.infer/2` and `Kernel.check/3` (`lib/cure/core/kernel.ex:74`, `:326`) only have clauses for `{:bounded_lit, k}` guarded `when is_integer(k) and k >= 0`; `check/3` does have a catch-all (line 344, `check_via_infer/3`), but that catch-all itself calls `infer/2` — and `infer/2` has **no catch-all** of its own. So a `{:bounded_lit, k}` term with `k < 0` reaching the kernel (from either `infer` or `check`) raises an uncaught `FunctionClauseError`, not a graceful `{:error, ...}`. This is not hypothetical: the existing bounded-integer-literal producer in `elaborate_expr_checked/5` (locus 2, `elaborator.ex:1101-1119`) already guards `value >= 0` at its `int?` test (line 1102) before it ever emits `{:bounded_lit, ...}`, so no unguarded negative-`k` path exists anywhere in the codebase today. An unguarded locus-3 clause would be the first one. No `sig` is available here to build the *typed* result (unlike locus 1, which still needs `char_type_value`), but the value-level range check needs no `sig` and must still happen to avoid handing the kernel a term it cannot handle without crashing. (Kept so a char literal passed as a plain function-call argument does not spuriously error — see §3.2 item 3 for this locus's actual, corrected, reachable path.)

### 3.5 Soundness note

The elaborator assigns the infer-mode type `Bounded(0x110000)`, while the kernel's own `infer({:bounded_lit, cp})` returns the *minimal* `Bounded(cp+1)`. This is not a contradiction: the term is validated against the assigned type by **`check`**, and `check({:bounded_lit, cp}, Bounded(0x110000))` succeeds (`cp < 0x110000`). The elaborator (untrusted) is free to assign any type the kernel will `check`; it never relies on kernel `infer` reproducing `Bounded(0x110000)`. Every downstream use (argument, return, let-binding) validates via `check`, so consistency holds.

### 3.6 Lexer prerequisite: UTF-8 decoding in `lex_char` (blocking, small, in scope)

`lex_char/1` (`lib/cure/compiler/lexer.ex:886-935`, non-escape branch at lines 920-933) currently reads a single raw source **byte** via `peek/1` (`:binary.at/2`) and treats it directly as the char literal's value. That is correct only for ASCII (`cp < 0x80`, where the byte value equals the codepoint); for any multi-byte UTF-8 character it consumes exactly one byte, then finds a UTF-8 continuation byte where it expects the closing `'`, and fails with `{:error, {:unterminated_char, _, _}}` (§2). Concretely, until this lands, **every real (lexer-derived) char literal is bounded by a single byte, `0..255`** — the `0x10FFFF` bound in §3.3/§3.4 is only reachable today via AST construction, not real source text.

This is orthogonal to the elaborator work in §3.1–§3.4 (it is a lexer change, not `lib/cure/elab/*`/`lib/cure/core/*`) but is a **blocking dependency**: without it, no source text can produce a `:char` literal with codepoint `> 127`, so this spec's headline example (§1, `'😀'`) and Testing items 3 and 5 (§4) cannot be exercised through real source, only through AST-constructed nodes.

**Fix** (contained to the non-escape branch of `lex_char/1`): when the byte at `peek(state)` is `< 0x80`, keep today's single-byte behavior unchanged. When it is `>= 0x80`, decode the full UTF-8 sequence starting at the current position — e.g. via `String.next_codepoint/1` on the remaining source (`binary_part(source, pos, byte_size(source) - pos)`), which yields both the codepoint string and its byte length — extract the codepoint integer (e.g. `<<cp::utf8>> = codepoint_str`), and `advance/2` the state by that many bytes (not `1`) before checking for the closing `'`. If `String.next_codepoint/1` returns `nil` (a truncated or invalid sequence runs to end-of-source), fall through to the same `{:error, {:unterminated_char, state.line, start_col}}` result the branch already produces today for a missing closing quote — do not let a malformed tail crash the lexer. The five *recognized* backslash-escapes (`\n \t \\ \' \0`) are unaffected by this fix and need no change — each is a fixed single-character mapping, not a decode of the escaped byte itself. **One more site has the identical defect and needs the same fix:** the escape branch's own fallback for an *unrecognized* escaped character (`c -> {c, advance(state, 1)}` at `lexer.ex:902`) is the same single-raw-byte read as the non-escape branch, so `'\😀'` fails the same way `'😀'` does today. Route that arm through the same UTF-8-decode-and-advance-by-length logic for consistency (escaping a multi-byte character is not a documented feature, but leaving this one site unfixed would mean a backslash before a non-ASCII character behaves differently, and worse, than the character alone). There is no `\u{...}` numeric escape, and adding one is out of scope, matching §5.

## 4. Testing

New `test/cure/elab/char_literal_test.exs`, modeled on `bounded_literal_test.exs`, using the `body_of(env, name) = Env.get_def(env, name).body` probe helper:

1. **Infer, no annotation** — `fn a() = 'a'` (or with a `Char` alias return) → body is `{:bounded_lit, 97}`.
2. **Check against `Char`** — `typealias Char = Bounded(1114112); fn a() -> Char = 'a'` → body `{:bounded_lit, 97}`.
3. **Full-plane emoji** — `'😀'` → `{:bounded_lit, 128512}` (one node). Requires the §3.6 lexer fix to exercise via real source (`'😀'`); until that fix lands, drive this test through an AST-constructed `{:literal, [subtype: :char], 128512}` node instead (same construction technique as item 4), then switch to real source once §3.6 lands.
4. **Out-of-range** — an AST-constructed `{:literal, [subtype: :char], 0x110000}` is rejected (`{:char_literal_out_of_range, _}`), and a negative codepoint likewise, through **both** `elaborate_expr_typed` (locus 1, §3.3) and `elaborate_expr/3` (locus 3, §3.4 — this is the case that would otherwise crash the kernel with `FunctionClauseError` rather than erroring cleanly). (Construct via the elaborator entry directly since the lexer cannot emit these.)
5. **End-to-end runtime** — a module `fn emoji() -> Char = '😀'` compiled via the dependent `Emit.compile_and_load` and run returns the integer `128512`. Depends on the §3.6 lexer fix landing first (it needs real source text to lex). If §3.6 is sequenced as a separate change, substitute an ASCII char for this end-to-end check instead (e.g. `fn a() -> Char = 'a'` returns `97`) and treat the emoji case as covered by item 3's AST-constructed unit test until §3.6 lands.
6. **Missing Bounded** — a char literal with no `use Std.Bounded` in scope errors `{:char_literal_needs_bounded, _}`, not a crash. (Only if the Bounded family is genuinely absent in the test env; if `Std.Bounded` is auto-seeded as core, assert the positive path instead and note it.)
7. **Plain-call argument (locus 3's real positive path)** — a literal argument to an ordinary top-level function call, mirroring the existing precedent shape in `test/cure/elab/literal_pattern_test.exs` (`classify(0)`, `pred(7)`) and `test/cure/elab/guard_test.exs` (`eq0(0)`) — e.g. `typealias Char = Bounded(1114112); fn plain(c: Char) -> Char = c; fn a() -> Char = plain('a')` — confirms a char-literal call argument elaborates successfully through `elaborate_expr/3` (§3.2 item 3), not just its out-of-range error path (item 4).

Strict red-green TDD: write the failing test, watch it fail with `{:unsupported_expression, …}` for the `:char` case, implement, watch green. Then scoped `mix test test/cure/elab/ test/cure/core/` (no regression), and the full suite once at the gate. Once a test in this list is written, it is immutable: make it pass by changing the implementation, never by weakening or deleting the test — the sole exception is discovering the test itself encodes the wrong expected behavior, which must be stated explicitly (what's correct, where the test diverges) before touching it.

## 5. Non-goals / risks

- **Not** char patterns, string literals, `Binary`, `Std.String` — separate tasks.
- **Not** a canonical stdlib `Char` alias — the literal works standalone; the alias is a later ergonomic add.
- **Risk:** the `char_type_value` helper couples char literals to a registered Bounded family. Mitigated by the clear `{:char_literal_needs_bounded, _}` error. `Std.Bounded` is `@group(:core)`; if it is auto-available the coupling is invisible in practice.
- **Risk:** allowing `'a' : Bounded(n)` for any `n > cp` (not strictly `Char`) is a deliberate consistency choice with integer literals, called out in §3.2 — not a faithfulness regression to fix.
- **Not a non-goal, but sequencing matters:** the §3.6 lexer fix is required (not optional/deferrable) for this feature to work end-to-end on non-ASCII input; it may land as a separate commit ahead of §3.1–§3.4, but §4 items 3 and 5 cannot pass against real source until it does.

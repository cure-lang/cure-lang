# SP5.1 — Quasiquotation (`quote` / `$( )`) implementation plan

**Status:** plan (2026-07-16). Promoted to non-optional SP6 prerequisite today
(`2026-07-12-macro-facility-REMAINING-WORK.md` §5.1). Layer: **P** (lexer/parser)
+ macro frontend. **TCB delta 0** — pure surface sugar; the emitted Core is
re-elaborated and kernel-checked (K3 firewall), same as hand-built `Std.Syntax`.

## 1. Goal (two deliverables)

1. **Implement** a `quote` surface that lifts ordinary Cure syntax to a
   `Std.Syntax.Syntax` value, with `$(e)` single-node splices and `$(e ...)`
   repeated-group splices, plus splice position/category checking.
2. **Port** the existing hand-built expanders (`derive_actor`, `derive_fsm`, and
   the reducer/reply-contract helpers) to author against `quote`/`$()`. The
   `Std.Syntax` typed builders / `Std.Syntax.Raw` drop to an escape hatch.

**Gate (from §5.1):** a `derive_actor`-class expander rewritten with `quote`/`$()`
produces **byte-identical Core** to the hand-built version; a wrong-category
splice is a **compile error**; full `mix test` green.

## 2. Key architectural insight — lower `quote` to the builder calls

`derive_actor` today (`lib/std/actor.cure:393`) writes, by hand:

```
block(append(message_declarations, [
  gen_server_module(module_name, state_type, [
    alias_node("Message", message_type),
    function("init", [init_spec.parameter], init_type, init_spec.body),
    ...])]))
```

The `Std.Syntax` builders (`node/leaf/variable/function/block/…`, `lib/std/syntax.cure`)
are the reflection substrate. **`quote` is sugar that the parser expands into
exactly these builder calls**, with each `$(e)` left as the spliced expression at
that argument position. Because the expansion *is* the builder-call AST, the port
producing byte-identical Core is structural, not coincidental — and category
checking is (mostly) the ordinary type-check of `node : (Atom, List(Attr),
List(Syntax)) -> Syntax` etc. This is the same principle as the existing
`to_syntax`/`from_syntax`/`to_core` bridge (`macro_syntax.ex`), reused, not
duplicated ("no second AST model").

So: **`quote <form>`** ⟶ parse `<form>` as normal Cure AST ⟶ walk that AST,
emitting the corresponding `Std.Syntax` builder call for each node, and at a
splice hole emit the splice expression verbatim.

## 3. Surface syntax (pinned decisions)

- **D1 — `quote` body.** `quote` takes ONE following form, parsed by the same
  single-form machinery `becomes` templates already use
  (`becomes-template-single-expression`): an expression, a declaration
  (`type`/`rec`/`fn`/`callback`/`module`/type-alternative fragment `| Ctor(...)`),
  or an indented/braced block for multi-statement bodies (reuses the block
  parser). No new block grammar — `quote` is a prefix over existing forms.
- **D2 — `$(e)` single splice.** `$(` opens a splice; the inner is a full Cure
  expression; `)` closes. `e : Syntax` is inserted at that node position.
- **D3 — `$(e ...)` group splice.** A trailing `...` inside the parens marks a
  splice-all: `e : List(Syntax)`, flattened into the enclosing node's child list
  (Scheme `,@` / Scala `_*` analog). Legal only where a child *sequence* is
  expected; single `$(e)` legal where one child is expected.
- **Lexing (design §2 honest-cost (a)):** reuse the existing `$(`-style hole
  lexing already present for computed markers; `$(` is unambiguous (dollar +
  paren). No conflict with `<name>` rule holes (those are Tier-2/3 grammar holes,
  a separate surface).

## 4. Semantics / lowering

`quote` lowers at PARSE time (macro frontend) to a `:quoted_syntax`-rooted
builder-call expression:

- Leaf nodes (`variable`, literals, atoms) ⟶ `Std.Syntax.{variable,integer,
  atom_literal,…}` calls.
- Interior nodes ⟶ `Std.Syntax.node(tag, attrs, [child…])` (or the specific
  builder `function`/`block`/`gen_server_module`/… where one exists — chosen to
  match the hand-built form so Core is byte-identical).
- `$(e)` at a child position ⟶ `e`.
- `$(e ...)` in a child list ⟶ `append`/list-splice of `e`.

The result is an ordinary Cure expression of type `Syntax`, type-checked and
kernel-checked downstream. Hygiene: quoted binders follow the landed SP5.3
scope-set auto-hygiene (`scoped_freshen`); `quote` bodies honor `<capture>` and
the `:quoted_syntax` data-boundary already respected by `apply_freshening`/
`scoped_freshen` (`parser.ex:1403,1461`).

## 5. Category / position checking (the "wrong-category splice is a compile error")

- **Type-level (free):** because splices land as arguments to typed builders,
  `$(e)` where `e : Int` at a `List(Syntax)` position is already a type error;
  surface it with a splice-specific diagnostic, not a raw arg-type error.
- **Group-vs-single lint:** `$(e ...)` outside a child-sequence position, or
  `$(e)` where only a sequence is legal, is a dedicated parse/elab diagnostic.
- Reach-pin: an Antigen/oracle fixture proving a wrong-category splice is rejected
  (not silently accepted).

## 6. Stages (strict red-green, one build at a time, scoped `mix test`)

1. **Stage 1 — red fixtures.** `test/cure/macro/quote_test.exs`: (a) `quote`
   over a small expr lowers to the expected builder-call AST; (b) `$(e)` single
   splice; (c) `$(e ...)` group splice; (d) wrong-category splice ⟶ compile
   error. All red.
2. **Stage 2 — lexer.** `$(` splice-open token + `...` group marker inside a
   quote/splice context (`lexer.ex`). Scoped test green for lexing.
3. **Stage 3 — parser `parse_quote`.** Parse `quote <form>`, collect splice
   holes, lower to builder-call AST (`parser.ex`, beside the existing template/
   `becomes` machinery). Stage-1 (a)(b)(c) flip green.
4. **Stage 4 — category/position checking.** Splice-specific diagnostics +
   group/single lint. Stage-1 (d) flips green; add the reach-pin.
5. **Stage 5 — port + gate.** Rewrite `derive_actor` (then `derive_fsm`, reply
   helpers) with `quote`/`$()`. **Golden test:** the ported expander's Core is
   byte-identical to a snapshot of the pre-port build (capture the snapshot from
   HEAD before editing). Wrong-category fixture is a compile error.
6. **Stage 6 — full gate + docs.** Full `mix test` alone; Antigen; oracle replay.
   Update REMAINING-WORK §5.1 → landed; `cure-language` skill surface docs;
   memory. Ghost-commit per stage.

## 7. Risk / non-negotiables

- P-layer + `lib/std/*.cure` only. **No `lib/cure/core/*` change** — if lowering
  seems to need one, STOP (HARD-STOP rule): the emitted term is ordinary
  builder-call Core the kernel already checks.
- Byte-identical-Core gate is the guard against the port silently changing
  behaviour; capture the golden snapshot BEFORE the first `actor.cure` edit.
- Ghost-writer commits, explicit-pathspec staging, one `mix` build at a time.

## 8. Status (landed)

- **Stages 1–4 LANDED** (`0c3e5a09`, `049daeb5`, `19cc6605`): `quote <form>` +
  `$(e)` single / `$(e ...)` group splice — lexer (`$(`→`:splice_open`, `...`→
  `:ellipsis`), parser (`parse_quote`/`parse_splice`), lowering
  (`MacroSyntax.lower_quote`: repr → surface `Std.Syntax` constructor AST,
  re-elaborated — Strategy B), elaborator `:quoted_syntax` clauses in BOTH
  `elaborate_expr/3` and `elaborate_expr_typed/4`, and Stage-4
  `:splice_outside_quote` diagnostic. 12 tests in
  `test/cure/compiler/quasiquote_test.exs`. TCB delta 0, no `lib/cure/core/*`.
- **Stage 5 port LANDED** (`b7a20c48`, `ea79fe85`, `6f2dc4dd`): the clean
  static-skeleton builders across the whole OTP macro family rewritten to
  `quote`/`$()` — **11 sites**: actor (6: `default_actor_init`,
  `derive_actor_init`, `actor_handler_arm`, info/terminate/code_change
  defaults), fsm (2: `callback_mode`, `init`), supervisor (1: nested
  `%[:ok, %[$(strategy), $(children)]]` — two splices), app (2: `stop`,
  `start_phase`). Covers no-splice literals/tuples/atoms, single splices, and
  nested splices. The remaining builders are deliberately NOT ported: the call
  handler's two-statement `let`-block (block-form `let` is unauthorable in
  surface and would diverge) and the all-dynamic `function(...)` emitters
  (name/params/type/body all vary — no static skeleton). `quote` earns its keep
  only for static-skeleton-with-holes.
- **Byte-identical-Core gate LANDED**: `test/cure/compiler/actor_quote_golden_test.exs`
  freezes the compiled BEAM SHA256 of **6 representative generated modules**
  (GDerived, GStructuredCall, GLifecycle, GFsmDerived, GSup, GApp). Every port
  above kept all six byte-identical, proving the extra `quote` reflection attrs
  are ignored by `from_syntax` and no line-provenance leaks. Behavioral suites
  (actor_computed, fsm_computed, structured_otp) all green alongside.
- **Stage 6**: full `mix test` alone = the closing gate (in progress).

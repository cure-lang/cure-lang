# SP1 (Minimal Macro Facility) — Parser Grounding & Architecture

> Grounding for the SP1 task-by-task plan. Records the frontend map (from a
> parser/lexer exploration, 2026-07-12) and the architecture decisions the plan is
> written against. SP1 = `macro` container + examples-with-holes grammar + Tiers 1–2
> (`literal`/`becomes`) + import scoping + two-pass resolution. TCB delta zero (macro
> output re-elaborated + kernel-checked).

## Frontend map — the anchors (all in the SHARED P layer)

- **No separate declaration grammar.** The parser is a Pratt/precedence-climbing
  expression parser; declarations are **keyword-led prefix forms** dispatched in
  `parse_keyword_prefix/2` (`parser.ex:1324`). A `macro` container is a sibling of
  `parse_fsm/1` (`parser.ex:3894`) / `parse_actor/1` (`parser.ex:4262`).
- **Keywords:** hard list `@keywords` (`lexer.ex:47`), tokenized in `lex_identifier/1`
  (`lexer.ex:676`). **Soft-keyword precedent** (`sup`/`app`): leave the word OUT of
  `@keywords`, branch on `token.value` in the `:identifier` prefix clause
  (`parser.ex:292-340`). Non-breaking.
- **AST:** MetaAST 3-tuple `{tag, meta, children}`; containers are generic
  `{:container, meta, body}` tagged by `meta[:container_type]`. Nodes: `{:function_def,
  meta, [body]}`, `{:function_call, [name:…], args}`, `{:literal, [subtype:…], value}`,
  `{:variable, [scope:…], name}`, `{:block, meta, stmts}`.
- **Use-site keyword-led forms:** strong precedent — `if`/`match`/`spawn` via
  `parse_keyword_prefix`, soft `assert_type`/`rewrite` via the `:identifier` branch;
  `parse_keyword_unary/2` = keyword-then-one-expr (closest to `every 500ms`).
- **Layout:** indentation-driven — lexer emits `:indent`/`:dedent`/`:newline`
  (`lex_indentation/1`, `lexer.ex:230`); container bodies `expect` them
  (`parse_block/1`, `parser.ex:5398`). Bracket tokens exist and are
  indentation-independent, so a `{ }`-delimited body is parser-only but cannot reuse
  `parse_block`.
- **Suffixed literals (`500ms`) UNSUPPORTED** — `lex_decimal` stops at the digit
  boundary; `500ms` → `{:integer, 500}` then `{:identifier, "ms"}`. Tier-1 `literal`
  rules need NEW lexer machinery.
- **Elaborator sinks:** `Program.body_register_pass/3` (`program.ex:1118`) dispatches
  per decl; `Declarations.elaborate/2` (`declarations.ex:26`) pattern-matches surface
  tags with a `{:unsupported_declaration, tag}` fallback — a new macro tag needs a
  clause here (but a *macro* mostly elaborates to nothing new: it registers a grammar,
  it is not itself Core).

## THE pivotal decision — use-site scoping (the one real architectural gap)

The map's biggest finding: **there is no per-module parser state and `use` is inert at
parse time** (`parse_use/1` emits a plain `{:import,…}` node, registers nothing). But a
macro use-site like `every 500ms` does **not** parse as ordinary Cure — the parser must
know the macro's grammar to parse it. So the keyword and grammar an imported macro
brings into scope must reach the parser *before* it parses the module body. Three ways:

- **(A) Two-phase parse (RECOMMENDED).** Pre-pass over the token stream: find `use`
  imports + local `macro` definitions, resolve each imported macro's grammar (from its
  compiled/loaded definition), and seed a new parser-state field
  `active_macros: %{keyword => grammar}`. Second phase parses the body with the
  `:identifier`/keyword prefix dispatch consulting `active_macros` before falling back
  to a variable. Consistent with the design's already-committed **two-pass** shape (§6
  signature→elaboration) — this is its parser-side analog. Cost: parser gains per-module
  state + a resolve step; the biggest single piece of SP1.
- **(B) Delimited invocation only** (`macroname { … }` / `raw until`). The parser sees a
  known `identifier {`/`identifier :` shape, captures the raw span, hands it to the
  macro's parser post-parse. No parser-state-from-imports. But it gives up the design's
  headline — a use-site that looks *exactly* like what the user types (`every 500ms`,
  not `every { 500ms }`). This is the Tier-5 `raw hole` mechanism, not Tier-2.
- **(C) Parse-generic-then-expand.** Impossible for genuinely custom syntax that isn't a
  valid Cure expression (`every 500ms` has no generic parse). Rejected.

**Decision: (A), with (B) available as the `raw until` escape for DSLs that genuinely
want their own delimited sub-language.** (A) is what makes Tier-1/2 deliver the "rule is
what you type" promise; (B) already exists in the design for the layout-override /
brackets case and rides on top. SP1 builds (A) for the keyword-led floor; the first-class
`region delimited by { }` layout sugar (self-proving §6) is (B) elevated, a later slice.

## Other SP1 decisions (pinned, low-risk)

- **`macro` is a soft keyword** (leave out of `@keywords`; branch in the `:identifier`
  prefix clause) — non-breaking, matches `sup`/`app`.
- **Hole lexing:** adopt the design's rule (§2 honest-cost a) — `<` opens a hole iff
  immediately followed by an identifier and closing `: Kind>`/`>` on the same line;
  escape `\<`. Pin this now; the `$name:Kind` sigil is the severable fallback if a
  pathological case appears. New lexer state, small.
- **AST tag:** a fresh `{:macro_def, meta, rules}` (not overloading `:container`) — a
  macro is not a value-producing container, and a distinct tag keeps the elaborator
  clause and the grammar-registration pass unambiguous.
- **Expansion output** is ordinary surface AST (the `becomes` template with holes
  spliced), fed back through the *existing* parse→elaborate path, so it is
  re-elaborated + kernel-checked unchanged (soundness, TCB delta zero).

## SP1 task sequence (to be expanded to complete-code tasks)

1. Soft-keyword `macro Name … end` container parsing → `{:macro_def, meta, rules}`
   (sibling of `parse_fsm`; `expect`s the `:indent … :dedent` body).
2. `syntax <example-with-holes> [is Cat] becomes <template>` rule parsing, incl. the
   hole-lexing rule; a rule stores its keyword, hole list (name+kind), and template.
3. `literal <n: Number> <suffix> becomes …` + the new lexer suffix machinery for `500ms`.
4. **Two-phase parse (A):** parser-state `active_macros`; a pre-pass seeding it from
   `use` + local `macro` defs.
5. Use-site matching: at a keyword/identifier prefix in `active_macros`, parse the
   arguments per the rule's holes, bind them.
6. Hygienic `becomes` expansion (`<fresh Name>` gensym; capture-avoidance) → surface AST.
7. Feed expansion back through parse→elaborate; assert it kernel-checks (a green +
   a red fixture whose expansion is ill-typed → a rejected-not-unsound program).
8. Import scoping + same-keyword-conflict error at `use`.
9. Two-pass name resolution (macro-derived names visible before the macro block; §6).

Tasks 1–3 are clean sibling-of-existing-parser work. Task 4 is the architectural core.
Tasks 5–9 build on it. The complete-code expansion of each is the SP1 plan proper.

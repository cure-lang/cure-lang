# The `blocks` Meta-Macro — Every Macro as a Block Language

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #26, promoted). Unlike its siblings, `blocks` is not a domain
macro — it is a **tooling macro built on the facility's grammar-as-data
guarantee** ([facility spec](2026-07-08-macro-facility-design.md) §2): a
generic exporter that turns *any* macro's grammar into a Blockly-style
visual block-programming surface.

---

## 1. Purpose

The facility spec states, as a requirement, that grammar rules are
**declarative data** — and cashes that in twice (LSP for free, docs for
free). This spec cashes it in a third time: **exporting any macro as a
drag-and-drop block palette is nearly free.** Done once, generically,
`blocks` gives every macro — `board`, dialogue trees, dive plans, home
rules, knitting rows, whatever the ecosystem writes — a visual mode with
zero per-macro work.

Nobody has gotten this for free before. Scratch, Blockly, and MakeCode each
hand-build their block sets and maintain a second representation alongside
(or instead of) text. Here the block surface *falls out* of the same
`syntax` declarations the parser, LSP, and formatter already consume — the
Scratch-to-text bridge education has wanted forever: block view and text
view are one program, and learners graduate by watching the correspondence
(§5).

Audience: the parent's beginner demographic, one step earlier — classrooms,
kids, and adults who freeze at a blank text file but will happily snap an
`every [500ms] do […]` block together.

## 2. How palettes derive from grammars

The mapping is mechanical and total over the facility's meta-grammar (§2
there):

- **Each `syntax` production becomes a block.** Literal tokens become the
  block's labels; typed non-terminals (`$period:Duration`, `$body:Block`,
  `$edges:Many(Edge)`) become sockets (§3). `Many(K)` becomes a growable
  vertical socket list; `(…)?` becomes a collapsible optional socket.
- **Each `category` becomes a block family** — its alternation's
  productions are the family's members, rendered in one consistent color so
  "these fit the same holes" is visible before it is learned.
- **Top-level forms** (container keywords like `reducer`, `packet`,
  `every`) become hat/container blocks that hold their indented structure.

Blocks are **generated, never hand-designed per macro**. A macro MAY
ship an optional **presentation annex** — declarative hints only (family
color, an icon, palette grouping/ordering, a short tooltip) — which the
generator honors when present and ignores when absent. The annex can change
nothing structural: sockets, arity, and compatibility come from the grammar
alone. The annex format is ledgered (§10.1).

Worked example — one rule from the tasks macro and its derived block:

```cure
macro Every
  syntax every $period:Duration $body:Block
```

derives (conceptually; the wire format is the palette JSON of §6):

```
block Every.every
  label  "every"
  socket period : Duration     # inline duration picker (§3)
  label  "do"
  socket body   : Block        # vertical statement mouth
  kind   container             # top-level form → hat block
```

The `reducer` macro's `Edge` category
(`$src:UpperIdent --$msg:UpperIdent--> $tgt:UpperIdent`) likewise derives
a three-socket edge block, stacked inside the reducer container's
`Many(Edge)` mouth — nobody designed that; the grammar already said it.

## 3. Typed sockets — the star of the show

**Socket compatibility IS the non-terminal type.** A socket declared
`Duration` accepts exactly the blocks whose production belongs to the
`Duration` kind; an `Expr`-only socket physically rejects a `Duration`
block. The type system is literally the jigsaw shape.

This is hiding principle 2 (correct-by-construction, parent §3) taken to
its extreme: the beginner cannot even *express* most type errors. There is
no red squiggle for "expected Duration, got Int" because the mismatched
block never snaps in. An entire error class — the one that dominates every
beginner's first week in a typed language — is not caught early; it is
**unconstructable**.

**Refinement-carrying literal kinds get inline editors,** and the editor's
constraints come from the refinement itself:

- `Duration` → a value-with-unit picker (`500` `ms|s|us`), emitting the
  facility's Tier-3 literal.
- A `Bounded(n)` / range-refined int → a slider or stepper whose min/max
  are read off the refinement. The type system configures the widget.
- Enum-like categories (a closed alternation of nullary productions) → a
  dropdown.
- `Ident`/`UpperIdent` → a name field validated live against the lexical
  rule; `Atom` similarly.

Which literal kinds get which editors is ledgered (§10.3); the principle —
**widget constraints derive from refinements, never hand-configured** — is
decided.

## 4. Round-trip — one AST, two views

Blocks and text are **the same AST**: the facility's typed quoted-AST
(facility §3). A block arrangement *is* a `Syntax(Category)` value rendered
as shapes; the text file is the same value rendered by the formatter. No
second representation, no import/export step, no lossiness by construction.

Consequences, all mandatory:

- **"View as text" is always one click**, and it shows the exact program
  the formatter would write.
- **Edits in either view reflect in the other.** Type in the text pane and
  the blocks re-render; drag a block and the text updates.
- A text edit that doesn't parse yet leaves the block view on the last
  valid AST with an "unsynced edits" banner — the block view never lies.

## 5. Progressive disclosure — the graduation story

Round-trip identity *is* the pedagogy. Learners graduate from blocks to
text by watching the correspondence, not by migrating projects:

1. **Blocks only** — the text pane hidden.
2. **Split view** — text pane visible, read-only; every drag animates the
   corresponding text change.
3. **Both editable** — fix a typo in text, see the block heal.
4. **Text with blocks as a lens** — open the block view occasionally, the
   way one opens an outline.

No stage involves an export, a rewrite, or a cliff — the file on disk is
ordinary `.cure` text throughout. The lesson/turtle teaching macros (§9)
script these stages; when to *nudge* a user up a stage is ledgered with
large-program ergonomics (§10.4).

## 6. Rendering host

Recommended host: **the toolchain's web-view surface** — a VS Code webview
panel inside the extension (toolchain spec §6) and the same bundle served
standalone in a browser via `cure blocks <file>`. One renderer, two frames.

The compiler generates the **palette JSON** from the macro registry — the
same registry the LSP consumes (toolchain §6, "LSP for free"). The pipeline
is: module's `use` lines → active macros → their grammar rules → palette.
A module that imports `Hardware.Every` and `Reducer` gets exactly those
palettes, namespaced and colored per family. No macro author ships
front-end code; the renderer is generic and lives with the toolchain.

Edits round-trip through the LSP's formatting channel: block mutations are
AST edits, serialized to text by the formatter, written to the file — so
version control, diffs, and review all see ordinary Cure source.

## 7. Error explainers on blocks

The boundary, stated plainly: **blocks make ill-*formed* programs
unconstructable; they do nothing for ill-*meant* ones.** A grammatically
valid arrangement can still fail elaboration — pin 34 as an output, an
undeclared reducer edge, a refinement that doesn't discharge. Those flow
through the error-explainer architecture unchanged
([`2026-07-08-error-explainer-design.md`](2026-07-08-error-explainer-design.md)):
elaborated terms carry provenance spans, the block view keeps the
span↔block mapping, and the explainer's domain-vocabulary message renders
**anchored on the offending block**, outlined with a callout. Raw kernel
errors reaching the block surface are a defect by the usual definition.

## 8. `check` relation

Two properties, one of each rung (parent §7.5 vocabulary):

- **"Every constructable block arrangement parses to a grammatically valid
  AST"** — true **by construction** (§3–§4: arrangements *are* typed AST
  values) and reported as *proved by construction; 0 runs*. The cute part:
  the block editor's core guarantee is a static-discharge line in the test
  report.
- **Round-trip stability** — the dynamic template: text→blocks→text is the
  identity modulo formatting (`parse(format(ast)) == Ok(ast)`). This is the
  renderer's regression suite, run over every registered macro's grammar
  by generating random valid arrangements — Antigen's generator machinery
  pointed at the meta-grammar.

## 9. Relations

- **Macro facility** — total dependency. `blocks` is the third structural
  dividend of grammar-as-data (after LSP and docs rendering); if the
  meta-grammar changes (facility ledger §11.2), the palette generator
  changes with it, and nothing else does.
- **Toolchain / LSP** — shared macro registry (§6 here, toolchain §6);
  the VS Code extension hosts the webview; `cure blocks` joins the CLI
  table.
- **Lesson / turtle macros** — primary consumers: the teaching surfaces
  script the §5 disclosure stages and ship classroom palettes.
- **A11y** — block UIs are notoriously mouse-only; keyboard navigation,
  screen-reader block traversal, and focus order are REQUIRED, specified in
  the parallel a11y spec
  ([`2026-07-08-a11y-macro-design.md`](2026-07-08-a11y-macro-design.md)).
  The always-available text view is itself the strongest a11y property.

## 10. Open decisions (ledger)

1. **Presentation-hint annex format** — where hints live (a `blocks`
   section inside the `macro`? a sibling declarative file?), the hint
   vocabulary (color, icon, group, tooltip), and inheritance for categories
   reused across macros.
2. **Block persistence** — positions, collapsed states, and free-floating
   comments have no home in the AST. Sidecar file (`.cure.blocks`) vs.
   auto-layout on every open. Leaning sidecar-optional: auto-layout must be
   good enough that losing the sidecar loses nothing semantic.
3. **Inline-editor inventory** — which literal/refinement shapes get which
   widgets (§3), and the fallback widget for refinements the generator
   can't interpret (plain field + live validation).
4. **Large-program ergonomics** — blocks do not scale to 500-line
   programs; the graduation story (§5) IS the answer, but decide the nudge:
   recommend a soft prompt past a block-count threshold, never a hard
   limit.
5. **Live values in blocks** — should a `board` palette show actual pin
   state from `cure run --sim` inside pin blocks? A powerful teaching loop,
   but couples the renderer to the sim registry; defer to a v2.
6. **Label localization** — literal tokens are keywords (untranslated),
   but block labels could carry translated tooltips/hints; ties to the
   error-explainer localization ledger (same string tables, same policy).

## 11. Non-goals

- **No new visual semantics.** Blocks are exactly the text grammar rendered
  as shapes — nothing snaps together that couldn't be typed, nothing types
  that couldn't snap.
- **No block-only macros.** Every macro is a text grammar first; a
  grammar that only works visually is a design smell the facility rejects.
- **Not replacing the text editor.** Blocks are an on-ramp and a lens; the
  LSP-backed text experience remains the primary surface.
- **No Scratch runtime or format compatibility.** We borrow the interaction
  idiom, not the ecosystem — `.sb3` import/export is out of scope.

# `a11y` — Accessibility as Types

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #78, promoted); built on the `macro` facility (parent §5) —
though more precisely it is a **rule pack**: it exports almost no syntax of
its own. It is consumed by `view`/`form`
([web trio](2026-07-08-web-trio-macro-design.md)) and `display` (backlog
#3), which run its rules over their own declarations.

---

## 1. Purpose

WCAG's checkable core is, literally, refinements plus graph properties:
contrast ratios are arithmetic over color literals, focus order is a graph
totality condition, labeling is coverage. These are exactly the obligations
the invisible-dependent-types machinery discharges by computation (parent §3,
principle 3) — so the checkable fraction of accessibility becomes
**inexpressible-to-violate at compile time**, with zero proof burden on the
user. A `view` that ships is a view whose mechanical accessibility violations
do not exist, the same way its impossible UI states do not exist.

The social leverage is unusual for a type-system feature: existing
accessibility tooling runs after the fact and is skipped under deadline
pressure precisely because it is optional. Here it is the type of the view.
And because Cure renders UI on embedded targets too, the same rules reach a
place with **no accessibility tooling at all today**: OLED and e-paper
screens built with `display`.

## 2. The static rule set

Each rule is named with the WCAG success criterion it mechanizes. All are
refinements or graph checks over *declared* data — they discharge by
computation, never by a surfaced goal.

- **Contrast (1.4.3 / 1.4.6).** Text over background must meet ratio ≥ 4.5:1
  (3:1 for large text) at AA; 7:1 / 4.5:1 at AAA. With both colors literal
  (`color: #767676` on `background: #FFFFFF`), the relative-luminance formula
  is pure arithmetic over the hex digits — the obligation reduces away in the
  delta table like any pin number. Runtime-computed colors get a **boundary
  check** at construction instead (a refined `ContrastPair` type whose
  constructor validates) plus an explainer naming that trade (§6).
- **Touch targets (2.5.5 / 2.5.8).** Interactive elements with declared
  dimensions carry `{w: Int | w >= 44}` × `{h: Int | h >= 44}` (44×44 CSS px
  by default — stricter than 2.5.8's AA floor of 24, matching platform HIGs;
  the AAA level pins 2.5.5's 44 formally). Literal dimensions discharge by
  computation; undeclared dimensions are the renderer's responsibility and
  are honestly outside the static net (§4).
- **Text-size minimums (in support of 1.4.4).** Declared font sizes carry a
  floor refinement (level-configurable). On `display` this becomes physical
  legibility: point size × pixel pitch of the declared panel must clear a
  minimum visual angle — the board file knows the panel, so this is again
  literal arithmetic.
- **Heading hierarchy (1.3.1).** Heading levels in a view tree must be
  monotonic — an `h1 → h3` skip is a compile error. A fold over the builder
  tree; no annotation exists or is needed.
- **Focus order (2.4.3, consistent with 1.3.2).** The focus graph over the
  view's interactive elements must be **total** (every element reachable, no
  traps — a cycle that excludes an element is an error) **and consistent with
  the declared reading order** (document-order traversal of the builder tree,
  unless the view declares otherwise). A graph property over the view tree,
  checked per model state.

## 3. Coverage rules

Coverage is the labeling half: every X has a Y, and *absence is never
silent* — the marked opt-out is the load-bearing design point, exactly the
`unsafe` philosophy (parent §3, principle 4) applied to accessibility.

- **Accessible names (4.1.2, 3.3.2).** Every interactive element has an
  accessible name — a `label:` attribute, associated visible text, or a text
  child. A missing name is an **error**. The opt-out is the explicit
  `decorative` marker; an unmarked, unnamed element never slips through.
- **Alt text (1.1.1).** Every image has `alt:` or `decorative`. Same rule,
  same non-negotiable shape.
- **Reduced motion (2.3.3 / 2.2.2).** Every declared animation has a
  reduced-motion variant — coverage over the view's animation declarations,
  with `reduced: none` as the common explicit case. The renderer switches on
  the client's `prefers-reduced-motion`.
- **Form labels (3.3.2).** Every `form` input is bound to a visible label —
  the form macro's single-source validation (web trio §4.2) gets its labels
  checked here: one field declaration yields the refinement, the client
  hints, the server check, *and* the label binding.

## 4. The honesty ceiling

Automated checking catches only a fraction of accessibility, and this macro
does not pretend otherwise. Static rules cannot verify that alt text is
*meaningful*, that reading order makes *sense* to a human, or that the
experience is actually usable with a screen reader. `alt: "image"` passes
coverage and fails users; a focus order can be total and consistent and still
be bewildering.

What this macro does is eliminate the **mechanical** violations — contrast
misses, unlabeled buttons, heading skips, keyboard traps — so that human
attention goes where only humans can judge. It must never be marketed as
"accessibility solved," and no report line it emits may imply conformance
beyond the checked rules.

What this does NOT check:

- alt text or label *quality* (meaningfulness, verbosity, redundancy);
- whether reading order is *sensible*, only that focus order agrees with it;
- screen-reader behavior, live-region semantics, or assistive-tech quirks;
- cognitive accessibility (plain language, error recovery UX);
- anything about content the user computes at runtime beyond the boundary
  checks in §2.

Docs rule: every mention of the macro's guarantees carries the ceiling in
the same breath. The pitch is "the mechanical violations are gone before
review," never "your app is accessible."

## 5. Surface & adoption model

There is almost no surface — that is the point. The rules are **on by
default** for every `view` and `form`, at **AA level**, and violations are
**errors, not warnings** (the parent's uniform-strictness spirit: a rule that
can be ignored is a rule that will be). Users meet the macro only as good
error messages.

```cure
view TodoPage over Todos.Model
  from Loaded with (payload) ->
    div class: "page"
      img src: payload.hero, alt: "Today's garden photo"
      img src: "corner-flourish.png", decorative
      button on_click: Refresh, label: "Refresh todos"
        icon :refresh
```

Project-level configuration selects the level; opting out entirely is an
explicit, marked declaration that surfaces in reports — the same greppable
pressure-valve contract as `unsafe`:

```cure
config
  a11y level: :aa            # :aa (default) | :aaa

view LegacyEmbed over M
  unsafe a11y off            # visible in `cure test` / audit reports
  ...
```

**`display` is in scope**, and deliberately so: contrast and text-size rules
apply to declared OLED/e-paper layouts against the panel's declared color
depth and pixel pitch (the `display` backlog entry's resolution checking,
extended). A low-contrast 6px label on 3-bit grayscale e-paper is exactly as
checkable as a web button — a genuinely novel application, not a port of
axe-core's rule list.

## 6. Explainers (parent §4 — errors ARE the UX)

Explainers show the computed evidence and a concrete fix. The
nearest-passing-color suggestion needs a context query (the read-only
elaboration-artifact interface of the
[error-explainer spec §6](2026-07-08-error-explainer-design.md)): the macro
deposits color pairs at elaboration time and registers
`nearest_passing(fg, bg, ratio)` over them.

```
error[E1xx]: text contrast too low for AA
  --> todo_page.cure:12
   |
12 |       p class: "hint", color: #767676
   |                               ^^^^^^^
  #767676 on #FFFFFF has contrast 4.48:1 — AA body text needs 4.5:1.
  Nearest passing color: #757575 (4.54:1). Large text (≥ 18pt) passes at 3:1.
```

```
error[E1xx]: the Save button has no accessible name
  --> editor.cure:31
  A screen reader announces this button as nothing. Add label: "Save",
  or mark it decorative (it isn't — it's the Save button).
```

The runtime-computed-color boundary check reuses the same text at the
`ContrastPair` constructor, per the write-once explainer rule (web trio §5).

## 7. `check` integration (check spec §6 — shipped templates)

The rule pack ships templates through `check`, and leans directly on the
reducer state-space generation the check spec built for `view`:

- **Every reachable state passes the audit.** The state generator derived
  from the reducer's edge graph drives the full static rule set over each
  rendered state — the spinner state *and* the error-banner state both get
  audited, not just the happy path a manual auditor would load. Static
  discharge applies: rules over literals report `proved by construction`.
- **Focus-order traversal simulation.** Generated Tab/Shift-Tab sequences
  walk each reachable state's focus graph, asserting totality and
  reading-order consistency dynamically — the regression net for the
  renderer's implementation of what §2 proved about the declaration.
- **Reduced-motion rendering.** Every reachable state renders under the
  reduced-motion flag without crashing and with no unreduced animation in
  the output tree.

## 8. Relations

- **`view` / `form`** (web trio) — primary consumers; the rules run as part
  of their elaboration, per model state and per form step.
- **`display`** (backlog #3) — the embedded consumer: contrast and text-size
  against declared panel physics (§5).
- **Error explainers** — context queries power the suggestions (§6); and one
  line the other direction: error messages are UI too — explainer output
  rendered through `view` is itself subject to these rules.
- **`blocks`** — block UIs are notoriously mouse-only; the blocks spec
  requires keyboard navigation, screen-reader block traversal, and focus
  order *from this spec* (blocks §9). Reciprocated: block palettes and
  workspaces are `view`s and inherit the full rule set.
- **`lesson`** (backlog #24) — teaching surfaces adopt the defaults, so
  learners build accessible-by-default UIs from day one without ever being
  taught "accessibility" as a separate topic.

## 9. Open decisions (ledger)

1. **WCAG version pinning** — 2.1 vs 2.2 vs the 3.0 draft. Leaning: rules as
   *versioned data packages* (`a11y wcag: 2.2`), so criteria, floors, and
   formulas upgrade explicitly, never silently under a compiler update.
2. **Custom rule packs** — org-specific rules (brand contrast floors,
   stricter target sizes) as user-defined packs on the same interface the
   built-ins use; decide the authoring surface.
3. **ARIA generation depth** — how much `role`/`aria-*` the web renderer
   emits from builder structure (much is derivable; over-generation is its
   own accessibility bug).
4. **Automated-testing calibration** — run axe-core over rendered output as
   a *calibration suite* in this repo's CI (do our rules catch what it
   catches?), never as a user-facing dependency.
5. **Localization interaction** — label coverage is per-locale once
   localization exists (a label present in English but missing in German is
   a coverage hole); ties to the explainer spec's localization ledger (§10.1
   there).

## 10. Non-goals

- **No screen-reader runtime behavior** — no AT simulation, no live-region
  runtime, no promises about how any given reader announces anything.
- **No manual-audit replacement** — §4 is normative; the macro's output
  is an input to human review, not a substitute for it.
- **No PDF/document accessibility** — this is about `view`/`form`/`display`
  trees; documents are a different product.
- **No scoring or certification claims** — no "accessibility score," no
  conformance badges; the only vocabulary is which checked rules pass.

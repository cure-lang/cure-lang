# `knit` — Knitting Patterns as Checked Programs

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #17, promoted). Built as a `macro` (§5) — zero compiler
special-casing; hiding principles (§3) are law here as everywhere.

---

## 1. Purpose & positioning

Knitting patterns are programs. They have loops (`repeat to end`), subroutines
(named repeats, "work rows 3–4 six more times"), parametric sizing (S/M/L),
and a well-defined abstract machine — a human with two needles — that has
executed them faithfully for two centuries, millions of interpreters strong.
No incumbent language has ever served this community; patterns ship as prose
and are debugged with a crochet hook at row 47.

And the standard failure mode is *pure arithmetic*: stitch counts that don't
balance from one row to the next — exactly the kind of fact refinement types
check trivially, since every count is a concrete literal or a size parameter
(so per hiding principle 3 every obligation discharges by computation). This
macro is the compile error every knitter has wanted for two centuries.

The user writes a pattern that reads like a published pattern — that is the
point. Cure checks every row balances, in every size, against the declared
shaping — and generates chart, stitch-count tables, yardage estimate, and
printable PDF from the one source of truth.

## 2. Surface

A `knit` block. Standard knitting abbreviations *are* the vocabulary; a
knitter should be able to read this cold:

```cure
knit WatchCap in_the_round
  gauge 20 sts, 26 rows per 10cm        # stockinette, after blocking
  sizes S, M, L
  cast_on 88 (96, 104)                  # published-pattern convention: S (M, L)

  section brim
    rounds 1 to 10: (k2, p2) repeat to end

  section body
    rounds 11 to 40: k to end

  section crown
    shape 88 (96, 104) -> 11 (12, 13) over 16 rounds
    round 41: (k6, k2tog) repeat to end
    round 42: k to end
    rounds 43 to 56: rep rounds 41 and 42, one fewer k each decrease round
```

- **`in_the_round` vs `flat`** is declared up front. It changes the
  row-mirroring semantics for charts (§6): flat wrong-side rows are read
  left-to-right with stitches reversed (a purl on the WS charts as a knit
  symbol); in the round, every round reads right-to-left with the right side
  always facing. Getting this wrong by hand is a classic charting error —
  here it is a declaration, not a discipline.
- **Sections** are named subroutines (`brim`, `body`, `crown`). Ranges and
  cross-references (`rows 5 to 12: rep rows 3 and 4`) are the loop syntax
  knitters already use.
- **Per-size values** use the published `88 (96, 104)` convention, resolved
  against the `sizes` line positionally. One number means "all sizes".
- Stitch vocabulary is the standard abbreviation set: `k`, `p`, `k2tog`,
  `ssk`, `yo`, `m1`, `kfb`, `c4f`/`c4b`, `sl1`, `bo`, plus grouping and
  `* n` / `repeat to end` combinators.

## 3. The stitch algebra

Every operation has a **(consumes, produces)** arity — how many stitches it
takes off the left needle and how many it puts on the right:

| Operation | Consumes | Produces | Note |
|---|---|---|---|
| `k`, `p` | 1 | 1 | the identity stitches |
| `k2tog`, `ssk` | 2 | 1 | decreases (right- and left-leaning) |
| `yo` | 0 | 1 | increase; leaves a hole (lace) |
| `m1` | 0 | 1 | increase from the bar between stitches |
| `kfb` | 1 | 2 | knit front and back |
| `c4f`, `c4b` | 4 | 4 | cables permute — arity-neutral |
| `sl1` | 1 | 1 | slipped, not worked — still counts |
| `cast_on n` | 0 | n | row zero |
| `bo n` | n | 0 | bind-off |

A row's arity is the sum of its stitches'. Repeats are multiplication:
`(k2, p2) * 4` consumes and produces 16; `(k6, k2tog) repeat to end` over 88
stitches is 11 repeats of (8, 7) — consumes 88, produces 77.

**The central refinement:** a row's total consumed must equal the previous
row's total produced. In Cure terms each row elaborates to a function
`Row(before: Nat) -> {after: Nat | ...}` whose domain is refined to the
previous row's count — `{sts: Int | sts == 88}` flows through the brim
unchanged, then shrinks by 11 per decrease round through the crown. The
knitter sees none of this (hiding principle 1); every index is a literal or a
size parameter, so discharge is pure computation.

**Divisibility is the second refinement**, and it catches a genuinely classic
pattern error: `repeat to end` with a repeat of width w requires
`{sts: Int | sts mod w == 0}` on the stitches remaining at that point in the
row. A 4-stitch ribbing repeat over a 90-stitch cast-on fails at compile
time — the exact mistake that ships in published patterns today and is
discovered by the knitter, at row 1, in yarn.

## 4. Parametric sizing

Sizes are parameters: the `sizes` line declares the index set, and every
per-size tuple (`cast_on 88 (96, 104)`, per-size repeat counts, per-size
shaping targets) is a function of it. **Every declared size is checked.** The
balance and divisibility refinements must hold for S *and* M *and* L — the
elaborator instantiates the whole pattern per size and discharges each one.

This is where a machine beats hand-verification decisively: published
patterns are routinely graded by adjusting one size's numbers and eyeballing
the rest, and routinely ship with exactly one broken size — the one the tech
editor didn't knit. Here, adding a size to the `sizes` line *is* requesting
the check for it; a failure names the size, the row, and the counts (§7).

## 5. Shaping — schematic vs. instructions

Shaping declares its target, then the rows must actually achieve it:

```cure
  section sleeve_decrease
    shape 96 -> 72 over 24 rows
    row 1: k1, ssk, k to last 3 sts, k2tog, k1
    rows 2 to 4: work even
    rows 5 to 24: rep rows 1 to 4
```

The `shape` line is the schematic — the little line drawing with measurements
at the edge of a published pattern. The checker sums the actual arity deltas
across the section's rows and compares: rows 1 to 4 net −2, six repeats net
−12... which is 84, not 72 — compile error. Schematic/instruction drift, the
other classic pattern-errata category, becomes inexpressible to ship. (With
gauge, `shape` also accepts measurements: `shape 48cm -> 36cm over 9cm` —
the units machinery (§9) converts through sts/10cm and rows/10cm.)

## 6. Generated artifacts

One source of truth, several renderings:

- **Charts** — the symbol-grid form, generated from written instructions with
  correct row mirroring per `flat`/`in_the_round` (§2). The reverse also
  holds: a chart is an equally valid source, and written instructions are
  generated from it — **round-trip, both directions**, checked (§8). No more
  "the chart and the written directions disagree" errata.
- **Per-size stitch-count tables** — count at every row for every size; the
  table a careful knitter builds in a margin, printed for all of them.
- **Yardage estimate** — from gauge plus total stitch count, per size
  (stitch-type consumption factors ledgered, §10).
- **Printable pattern PDF** — abbreviation key, schematic with per-size
  measurements, charts, written instructions, the stitch-count tables. The
  artifact a designer actually publishes.

## 7. Errors — explainers in knitter vocabulary

Per parent §4, no kernel vocabulary ever surfaces; the macro's `explain`
block owns the failure shapes. (Error-code block allocation for `knit` is
pending in the explainer registry — E17x used illustratively.)

```
error[E220]: stitch counts don't balance between rows 47 and 48 (size M)
  --> cardigan.cure:52
   |
52 |   row 48: k1, (k2tog, k5) repeat to end, k2tog, k1
   |
  row 47 produces 89 stitches but row 48 consumes 91 — check the k2togs.
  Row 48 as written needs 91: two k2togs too many, or one k7 repeat short.
```

```
error[E221]: repeat doesn't fit (size S)
  --> cowl.cure:9
   |
 9 |   rounds 1 to 8: (k2, p2) repeat to end
   |
  repeat width 4 doesn't divide the 90 stitches remaining — 2 left over.
  Add a selvedge stitch each side, or adjust the cast-on to a multiple of 4
  (88 or 92).
```

Template as everywhere: what you wrote → why the fabric forbids it → what
to write instead — in stitches and rows, never in types.

## 8. `check` integration

`knit` ships property templates per parent §7.5:

- **Per-size balance** — every row balances against its predecessor, every
  size, plus every `shape` line against its section. This is **largely
  static discharge**: the counts are literals per size, so the report reads
  `proved by construction — 0 runs` for almost every pattern. The prop
  exists so the guarantee is *visible* in `cure test` output, not because
  running is expected.
- **Chart ↔ written round-trip** — render to chart, read back, compare;
  and the reverse. Exercised generatively over the pattern's own stitch
  vocabulary, including the flat-knitting WS mirroring.
- **Gauge-swatch arithmetic** — measurements derived from gauge (finished
  circumference, `shape` lines given in cm) recompute consistently under
  unit round-trips (cm ↔ inches, sts/10cm ↔ sts/4in).

## 9. Relations

- **`units`** (parent §6.6) — gauge is a unit-of-measure fact: `20 sts, 26
  rows per 10cm`, with cm/inches conversion and `sts/10cm` as a derived
  unit. All measurement-form shaping (§5) flows through it.
- **`parse`** (parent §7.2) — importing existing patterns from standard
  abbreviation text ("CO 88 sts. *K2, p2; rep from * to end.") is a `parse`
  grammar over the abbreviation vocabulary. High-value on-ramp, real
  ambiguity in the wild corpus — **ledgered** (§10), not v1.
- **`blocks`** — a chart-grid editor as an alternative visual input surface
  rides [`2026-07-08-blocks-macro-design.md`](2026-07-08-blocks-macro-design.md); one line here.
- **Report/PDF generation** — §6's printable artifact shares whatever
  document-rendering machinery other macros' reports use; the pattern PDF
  is a renderer target, not new macro semantics.
- **`check`** — §8; the generator/oracle machinery is Antigen's, reused.

## 10. Open decisions (ledger)

1. **Crochet** — a genuinely different algebra (stitches build on chains and
   into arbitrary earlier stitches; turning chains; rounds that spiral).
   A separate macro, explicitly **not** scope creep here — ledgered so
   nobody bolts it onto the knit algebra. **Promoted 2026-07-08:**
   [`2026-07-08-crochet-macro-design.md`](2026-07-08-crochet-macro-design.md)
   — position-vector state (`Vec(Position,_)`) generalizing this macro's
   `Nat` count; same checking discipline, floor identical to knit.
2. **Colorwork** — probably v1.5, and the idea is worth preserving verbatim:
   **Fair Isle float lengths as refinements** — "no float longer than 5
   stitches" is `{run: Int | run <= 5}` over the color-run lengths of each
   row, checked at compile time; intarsia gets bobbin-count derivation per
   row. Chart generation already wants color as a per-stitch attribute, so
   the surface hook can land early even if the checks wait.
3. **Brioche and short-rows** — honestly harder algebra. Brioche pairs
   stitches with their yarn-overs across rows (arity isn't row-local);
   short-rows make "the previous row" nonlinear (wrap-and-turn leaves part
   of the row unworked). Ledgered without a designed answer yet; neither
   blocks v1, but both are common enough that v2 must face them.
4. **Charting symbol standard** — Craft Yarn Council symbols vs. Japanese
   (JIS) vs. the various publisher house styles. Pick one canonical set for
   v1 rendering with the choice isolated in the renderer; per-publisher
   symbol themes later.
5. **Pattern import** (`parse` bridge, §9) — grammar coverage for the wild
   corpus of published abbreviation styles; what fraction imports clean vs.
   needs hand-fixup; whether import emits the `knit` surface (it should —
   round-trip discipline again).
6. **Machine-knitting output** — punchcard and modern machine file formats
   as additional artifact targets; the algebra already carries everything
   needed. Ledgered until someone with a machine wants it.
7. **Yardage model fidelity** — per-stitch-type consumption factors (cables
   eat yarn; stockinette doesn't); does the estimate state an error bar?

## 11. Non-goals

- **No crochet** — separate algebra, separate macro (§10.1, now spec'd at
  [`2026-07-08-crochet-macro-design.md`](2026-07-08-crochet-macro-design.md)).
- **No garment *design* automation** — the macro checks patterns; it does
  not grade, draft, or design them. "Given these measurements, generate a
  sweater" is a different product; `knit` is the tech editor, not the
  designer.
- **No yarn-store inventory, queue, or stash management** — pattern-adjacent
  apps exist and are welcome to consume the generated artifacts; none of it
  is language work.

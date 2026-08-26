# The `knit` Vertical — Scope, Personas, Ergonomics

**Date:** 2026-07-08
**Status:** vertical scoping (operator-requested). Companion to
[`2026-07-08-knit-macro-design.md`](2026-07-08-knit-macro-design.md) —
that spec defines the macro; this document scopes the *product vertical*
around it: who it serves, the full workflow, and the ergonomic surface shown
by worked example. Ergonomics rule inherited and sharpened here: **a
published pattern is nearly valid source, and every convention knitters
already write becomes a checked assertion.**

---

## 1. The vertical map — personas & the economic story

- **Knitters (pattern followers)** — the mass audience. Want: patterns that
  don't have errors, per-size clarity, yardage before buying yarn, and
  knowing where they left off. They never see the macro; they see PDFs,
  charts, and the companion (§5).
- **Designers** — the authors. Want: grading that doesn't break one size,
  charts generated from written instructions (not maintained in parallel),
  schematic conformance, professional-looking output. They write the
  macro, and it reads like what they already publish.
- **Tech editors** — the load-bearing persona nobody outside the industry
  knows exists: professionals paid per-pattern/hourly to verify exactly the
  arithmetic this macro checks — stitch counts, repeats, grading, chart/
  text agreement. `cure test` does the mechanical 80% of tech editing at
  zero marginal cost; the human tech editor moves up-stack to fit, style,
  and construction judgment. **This is the vertical's economic wedge**: a
  designer's per-pattern editing spend becomes a compile step, and "machine
  tech-edited, all sizes verified" becomes a quality badge on the pattern.
- **Yarn shops & brands** — pattern support and substitution math (§6);
  patterns that carry their own gauge-conversion logic reduce support load.

Workflow, end to end: *write (macro) → check (balance, all sizes,
schematic, charts) → generate (PDF, charts, tables, yardage) → publish
(Ravelry-ready, errata-free-by-construction) → knit (companion + device,
progress persisted)*.

## 2. Ergonomic principles (the additions this scope commits to)

1. **Stitch-count callouts are checked assertions.** Published patterns
   already write `— 84 sts` at the end of shaping rows. That exact syntax
   is an *assertion the compiler verifies* — the convention knitters trust
   most becomes machine-checked without changing how it's written.
2. **Measurement repeats are honest.** `rep rows 5 and 6 until piece
   measures 150cm` is legal; the compiler bounds it via gauge (`~450 rows
   at gauge`) for yardage/chart purposes and prints the measurement
   instruction verbatim — the knitter's judgment stays authoritative, the
   estimate is labeled an estimate.
3. **Markers are vocabulary.** `pm`, `sm`, `k to 1 before m` — first-class,
   because raglan/lace shaping is written against markers in every modern
   pattern.
4. **Errors name rows, sizes, and stitches — never types** (per the parent
   hiding principles; examples throughout §3).
5. **Repetition speaks knitter, not programmer — in English** (operator
   direction, twice refined: `rnds 1..2` reads wrong, and so does the
   relative `rep last 2 rnds`; patterns reference rounds *by number, with
   English connectives*). The connectives: **`and` joins two**
   (`rep rnds 1 and 2`), **`to` is the range operator**
   (`rows 1 to 4`, `rep rows 5 to 8`). Neither `..` nor dashes exist in
   source (the PDF generator may typeset ranges per house style). Rounds
   may carry an optional name for readability — `rnd 1 (increase):` — but
   the number is the reference. The repeat forms that compose with this:
   the **frequency form** (`work rnd 1 every other rnd 13 times total`)
   and **repeat-until-count** (`rep rnds 1 and 2 until 168 sts` — the
   checker derives the iteration count from the rounds' net delta and
   verifies the target is *reachable*: `until 170 sts` from 64 by +8 is a
   compile error, "you'll pass 168 → 176"). Bare `times` remains REJECTED
   as ambiguous — `12 more times` or `13 times total`, the disambiguation
   tech editors already enforce, independently verified by the trailing
   callout.

## 3. Worked examples

### 3.1 Lace, and the divisibility save

```cure
knit EyeletScarf flat
  gauge 22 sts, 30 rows per 10cm in pattern, after blocking
  yarn fingering, 400m per 100g
  cast_on 42

  section border
    rows 1 to 4: k to end                              # garter edge

  section lace
    row 5 (RS): k1, (yo, ssk) repeat to last st, k1    — 42 sts
    row 6 (WS): k1, p to last st, k1
    rep rows 5 and 6 until piece measures 150cm        # ~450 rows at gauge

  section top_border
    rows: k to end * 4
  bind_off loosely
```

`yo` (+1) pairs with `ssk` (−1): row 5 is arity-neutral, and the trailing
`— 42 sts` assertion is verified. Had the designer cast on 43 (an easy
"odd numbers frame nicely" instinct):

```
error[E220]: row 5 doesn't divide
  (yo, ssk) is 2 stitches wide, but 41 stitches remain after `k1` —
  1 left over. Cast on 42, or absorb the extra into the border (k2 at
  one edge).
```

That error currently ships in real published patterns and is found by a
knitter, in yarn, at row 5.

### 3.2 Crown decreases — the convention you already write, now checked

```cure
knit PlainBeanie in_the_round
  gauge 20 sts, 26 rows per 10cm
  cast_on 96

  section crown
    rnd 41: (k6, k2tog) repeat to end     — 84 sts
    rnd 42: k to end
    rnd 43: (k5, k2tog) repeat to end     — 72 sts
    rnd 44: k to end
    rnd 45: (k4, k2tog) repeat to end     — 60 sts
```

Every `— n sts` is checked: `(k6, k2tog)` is 8 wide over 96 = 12 repeats,
consumes 96, produces 84 ✓. Mis-write the third callout as `— 70 sts`:

```
error[E221]: round 45's count is wrong
  (k4, k2tog) over 72 sts works 12 repeats: 72 consumed, 60 produced.
  The pattern says 70. (Off-by-a-round? Round 44 ends at 72.)
```

### 3.3 Grading — a raglan yoke, all sizes proved

```cure
knit TopDownRaglan in_the_round
  gauge 18 sts, 24 rows per 10cm
  sizes XS (S, M, L, XL)
  cast_on 64 (68, 72, 76, 80)

  section setup
    ## Divide for back, sleeves, front; markers are placed HERE.
    rnd 0: (k10 (11, 12, 13, 14), pm, k22 (23, 24, 25, 26), pm) * 2
      — 4 markers: sleeve 10 (11, 12, 13, 14), body 22 (23, 24, 25, 26)

  section yoke
    rnd 1 (increase): (k to 1 before m, m1r, k1, sm, k1, m1l) * 4, k to end   — +8 sts
    rnd 2: k to end
    rep rnds 1 and 2 until 168 (188, 208, 228, 248) sts
```

**Markers are tracked state, and placement is checked.** The round state is
not just a stitch count — it carries the ordered marker positions, so
`pm`/`sm`/`k to [1 before] m` are part of the algebra: `pm` inserts a marker
at the cursor, `sm` requires the cursor to be *at* one, and `k to 1 before m`
requires a next marker to exist. Referencing a marker before any `pm` is the
compile error this example originally contained (caught by the operator, to
the author's chagrin — the checker exists precisely because humans ship this):

```
error[E223]: rnd 1 knits "to 1 before m", but there are no markers yet
  No pm has been worked before this round. Add a setup round that places
  the raglan markers (and says where — that's the fit).
```

Marker tracking buys more than placement errors: the checker knows every
inter-marker *segment* width, so the setup round's marker callout is verified
(10+22+10+22 = 64 for XS ✓, per size), the yoke's `* 4` is checked against
the actual marker count, and segment growth is auditable — each raglan round
adds exactly 2 sts per segment, so the schematic's per-piece numbers
(sleeve 10 → 36 at separation for XS) fall out of the same arithmetic.

The per-size tuple convention does the grading; the compiler instantiates
all five sizes and verifies the arithmetic chain per size — including the
`+8` incremental and the final absolute callouts. `cure test`:

```
knit TopDownRaglan
  ✓ all sizes balance         proved by construction — 5 instantiations
                              (XS to XL), every round, every callout; 0 runs
  ✓ schematic conformance     proved by construction — yoke depth 18 (19.5,
                              21, 22.5, 24)cm at gauge matches shape targets
  ✓ chart/text agreement      proved by construction — round-trip identical
```

The industry failure this kills: patterns graded by adjusting one size and
eyeballing the rest ship with exactly one broken size — the one the tech
editor didn't knit. Here, adding `XXL (…)` to the sizes line *is* the
request to prove it.

### 3.4 Colorwork — Fair Isle floats (promoted from the macro ledger)

```cure
  colorwork Fern over 12 sts
    colors mc "Storm", cc "Birch"
    require floats <= 5
    row 1: mc3 cc1 mc3 cc1 mc4
    row 2: mc2 (cc1 mc1) * 2 cc3 mc3
    row 3: mc1 cc2 mc5 cc2 mc2
```

The chart renders both as a symbol grid and as knitting-vocabulary text;
the float refinement is checked per color per row:

```
error[E222]: row 3 carries Birch too far
  Birch floats across 5 background stitches twice — fine — but Storm
  floats 7 (cols 4–10) on the wrong side. Long floats snag fingers and
  pull the fabric. Catch the float mid-run, or redesign the motif.
  (This pattern's limit: 5.)
```

### 3.5 The companion — and the row counter that knows the pattern

Generated from the same source, two forms:

- **Web companion** (`view`): row-by-row mode — current instruction, the
  live expected stitch count, progress bar per section; progress persists
  (`schema`), works offline.
- **The MCU crossover:** `cure knit companion PlainBeanie --device` builds
  an **e-paper row counter** (ESP32 + rotary encoder — `board`/`display`
  macros): click to advance, long-press to step back, screen shows

  ```
  crown · rnd 43 of 56
  (k5, k2tog) repeat to end
  ends at 72 sts
  ```

  Progress survives battery swaps (NVS via `schema`). A row counter that
  shows *the instruction and the checked count* is a genuinely new object —
  and it points the knitting audience at the hardware vertical through
  their own craft.

## 4. Generated artifacts & publishing

From one source: written pattern PDF in standard layout (per-size numbers
inline, both aggregate and size-isolated variants — "just my size" is a
beloved feature), charts (SVG, correct RS/WS mirroring per the macro's
`flat`/`in_the_round` semantics), schematic with per-size measurements at
gauge, stitch-count tables, yardage per size (from gauge + area + a declared
stitch-pattern take-up factor), difficulty metadata (derived: stitch
vocabulary used, shaping density, colorwork presence). Ravelry-ready PDF
export. The publishing pitch, printable on the pattern itself:
**"machine-verified: every row, every size"** — the errata section, that
fixture of published knitting patterns, becomes structurally empty.

## 5. Yarn substitution (§6 of the workflow)

```
$ cure knit substitute EyeletScarf --gauge "20 sts/10cm"
  Declared gauge 22 sts/10cm; your swatch is 20 — denser yarn or looser hand.
  At your gauge this scarf blocks to ~46 × 165cm (pattern: 42 × 150cm)
  and needs ~410m (pattern: ~380m).
  Options: go down 0.5mm and re-swatch, or keep needles and accept the
  larger fabric (the lace is forgiving; the divisibility still holds).
```

Pure gauge arithmetic over the pattern's own declarations — units doing
double duty as the swatch calculator every knitter does by hand.

## 6. Roadmap slices

- **v1 — the tech editor in the compiler:** stitch algebra, sizes, checked
  callouts, divisibility, schematic conformance, charts + PDF, yardage.
  (Everything in the macro spec + §2's assertion/measurement/marker
  ergonomics.)
- **v1.5 — colorwork & lace depth:** Fair Isle floats (§3.4), chart-first
  authoring (draw the chart, derive the text), lace charts with `nupp`/
  double-yo extensions to the algebra.
- **v2 — the knitting experience:** companion + row-counter device (§3.5),
  substitution tooling (§5), Ravelry publishing integration, designer
  grading helpers (grade-rule declarations rather than hand-tupled sizes —
  ledgered in the macro spec).
- **Explicitly later (macro-spec ledger stands):** brioche and short-rows
  (non-row-local algebra), machine-knitting output, crochet (separate
  macro).

## 7. Relations

Macro spec (the base); `check` (all-sizes proofs are its static-discharge
rung); `view`/`schema` (companion); `board`/`display`/`driver` (device);
`units` (gauge/length); `blocks` (chart-first visual editing is literally
the blocks view of the colorwork grammar); `parse` (importing existing
written patterns from standard abbreviation text — the migration funnel for
designers with a back-catalog; ledgered in the macro spec, promoted to
v2-adjacent here because back-catalog import is how designers arrive).

## 8. Ledger additions (beyond the macro spec's)

1. **Grade rules** — declarative grading (`bust step 10cm, ease 5cm`) that
   *generates* the per-size tuples designers currently hand-write.
2. **Take-up factors** — per-stitch-pattern yardage multipliers (cables eat
   yarn); shipped defaults + designer overrides.
3. **Companion device BOM** — one blessed cheap build (ESP32 + e-paper +
   encoder) so "make the row counter" is a shopping list.
4. **Ravelry integration depth** — PDF-only vs. API metadata sync.
5. **Chart-first authoring** — §6 v1.5; interacts with `blocks`.
6. **Pattern-import fidelity** (`parse`) — how much real published prose
   parses without hand-fixing; measure on a corpus before promising.

## 9. Non-goals

Crochet (different algebra — own macro someday); garment *design*
automation (fit is human judgment; we check arithmetic, not aesthetics);
machine-knitting formats in v1; a yarn-inventory/stash app.

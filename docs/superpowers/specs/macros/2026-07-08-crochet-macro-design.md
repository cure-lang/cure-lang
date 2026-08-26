# `crochet` — Crochet Patterns as Checked Programs

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog / knit ledger §10.1, promoted). Built as a `macro` (§5) — zero
compiler special-casing; hiding principles (§3) are law here as everywhere.
Sibling of [`knit`](2026-07-08-knit-macro-design.md): **same checking
discipline, a richer state.** Explicitly *not* bolted onto the knit algebra
(that spec's ledger §10.1 forbids it, correctly).

---

## 1. Purpose & positioning

Crochet patterns are programs, and — like knitting patterns — they ship as
prose and are debugged with the hook in your hand at round 14, when the circle
you wanted flat has turned into a taco. This macro gives crochet the compile
error it has never had.

The key structural fact, and why crochet is a *separate* macro from `knit`:
a knitter holds a whole row of live loops on the needle, so knit's state is a
single running **stitch count** (`Nat`). A crocheter holds exactly **one** live
loop on the hook and anchors each new stitch into a *specific position* in the
fabric below. So crochet's state is not a count — it is the **sequence of
workable positions** across the current row's top (stitches, chain-spaces,
posts). A row is a length-refined fold `Vec(Position, n) -> Vec(Position, m)`.

This is a *better* fit for Cure's dependent kernel than knit was, not a worse
one: the state is a length-indexed vector with `Fin`-indexed anchor positions —
exactly the landed `Vector`/`Bounded` machinery
([[stdlib-dependent-expansion]]). Knit is the degenerate case where every
position is a plain stitch and the traversal is contiguous — so **everything
knit checks, crochet checks at the floor, unchanged**, and the richer state
buys three things knit has no analogue for (§3, §5).

The user writes a pattern that reads like a published pattern. Cure checks
every round balances, every repeat divides, every anchor exists, and — the
flagship — that the piece will actually **lie flat (or curve the way you
declared)**, in every size, and generates chart, count tables, yarn estimate,
and PDF from the one source.

## 2. Surface

A `crochet` block. Standard abbreviations *are* the vocabulary; a crocheter
reads it cold. The canonical crochet program — an amigurumi ball, worked in a
spiral:

```cure
crochet LittleBall spiral
  hook 3.5mm, yarn worsted
  form sphere                        # declares the 3D target (§5)

  round 1: 6 sc in magic ring              — 6 sts
  round 2: inc around                      — 12 sts
  round 3: (sc, inc) around                — 18 sts
  round 4: (sc 2, inc) around              — 24 sts
  rounds 5 to 8: sc around                 — 24 sts
  round 9: (sc 2, dec) around              — 18 sts
  round 10: (sc, dec) around               — 12 sts
  round 11: dec around                     — 6 sts
  finish: pull through remaining 6, weave in
```

And a flat coaster — joined rounds, taller stitch, a disc:

```cure
crochet Coaster joined
  hook 4mm, yarn cotton_dk
  form disc

  round 1: 12 dc in magic ring, join       — 12 sts
  round 2: ch 3, dc in same st, (2 dc in next) around, join   — 24 sts
  round 3: ch 3, (dc, 2 dc in next) around, join              — 36 sts
```

- **Spiral vs. joined** is declared up front, like knit's `flat`/
  `in_the_round`, and it changes the round-boundary semantics: `spiral`
  (amigurumi — no join, no turning chain, a marker tracks the round start)
  vs. `joined` (motifs — each round closes with a slip stitch and opens with
  a standing/turning chain). Getting this wrong by hand produces a visible
  seam jog or a missed join; here it is a declaration, not a discipline.
- **`form disc | sphere | cone | tube | flat`** declares the intended
  geometry (§5) — the schematic, in three dimensions. Omit it for flat rows
  where shaping is explicit.
- **`sc`, `hdc`, `dc`, `tr`** are the basic stitches; `inc`, `dec` (`sc2tog`
  etc.), `sl st`, `ch`, `skip`, `2 dc in next`, `3 dc in same st` are the
  shaping and grouping forms; `around` is `repeat to end` for the round;
  `(…) around` and `* n` are the repeat combinators.
- **Per-size values** use knit's published convention `24 (30, 36)` against a
  `sizes` line; repetition speaks English (`rounds 5 to 8`, `rep rounds 2 and
  3`) per the corpus surface-idiom rule — no `..`, no dashes in source.
- **`— n sts` callouts are checked assertions** (knit vertical §2.1, inherited
  wholesale): the number every crocheter already writes at a round's end is
  verified.
- **`us` / `uk`** may be declared (default `us`): US `sc` = UK `dc`, US `dc` =
  UK `tr`, and so on down the ladder. A pattern that silently means different
  stitches under the reader's convention is a real wild-corpus bug; here the
  vocabulary and stitch **heights** (§5) rebind unambiguously from one word.

## 3. The stitch algebra — positions, not just a count

Every operation has a **(consumes, produces)** arity, exactly as in knit —
`consumes` is how many positions it works out of the row below, `produces` is
how many positions it adds to the row being made:

| Operation | Consumes | Produces | Note |
|---|---|---|---|
| `sc`, `hdc`, `dc`, `tr` | 1 | 1 | the plain stitches; differ only in **height** (§5) |
| `inc` / `2 sc in next` | 1 | 2 | increase — n stitches in one position |
| `3 dc in same st` | 1 | 3 | shell increase |
| `dec` / `sc2tog` | 2 | 1 | decrease — n positions worked together |
| `sl st` | 1 | 1 | slip stitch — height 0 (joins, travel) |
| `ch` | 0 | 1 (space) | a chain — a *chain-space* position, not a stitch |
| `skip` | 1 | 0 | skip a position (mesh, lace); it is still consumed |
| `n st in magic ring` | 0 | n | round-zero, circular (the `cast_on`) |
| `into ch-k sp` | 1 (a space) | per stitch | anchor into a chain-space, not a stitch |

A round's arity is the sum of its stitches'; `(…) around` and `* n` multiply,
exactly as in knit. **The central refinement is knit's, generalized to the
position vector:** the positions a round *consumes* must be exactly the
previous round's *produced* vector — no position left unworked, none
over-worked. For plain fabric every position is a stitch and this collapses to
knit's single-count balance (`consumed == previous produced`); the vector only
becomes load-bearing when spaces and skips enter.

Three checks fall out, two shared with knit and one new:

- **Balance** (= knit): `round 3` above consumes 12, produces 18; the `— 18
  sts` callout is verified. Every count is a literal or a size parameter, so
  discharge is pure computation (hiding principle 3) — the crocheter sees no
  types.
- **Divisibility** (= knit): `(sc 2, inc) around` is 3 positions wide and must
  divide the round's count; `(…) around` over a count not divisible by the
  repeat width is E291, the classic "it didn't come out even."
- **Anchor validity** (new — generalizes knit's marker tracking): `into ch-2
  sp` requires a chain-space to *exist* at that position in the state vector;
  `into 3rd ch from hook` requires the foundation chain to be long enough;
  a front-post `dc` requires a post below. Knit's `sm`-requires-a-marker
  (E223) is the `Nat`-state special case of this `Vec(Position,_)` check.

## 4. Parametric sizing

Identical to knit (§4): the `sizes` line is the index set, every per-size tuple
is a function of it, and **every declared size is instantiated and checked** —
balance, divisibility, anchors, and the form check (§5) must hold for S *and*
M *and* L. Adding a size *is* requesting its proof; a failure names the size,
the round, and the counts. The industry failure knit kills — grading one size
and eyeballing the rest — is the same in crochet, and dies the same way.

## 5. Shaping — the form-aware circle law (the flagship)

This is crochet's equivalent of knit's schematic conformance (`shape 96 -> 72
over 24 rows`), but it is genuinely **three-dimensional**, and it is the single
most common thing crocheters get wrong.

A flat circle lies flat only when each round adds stitches at the rate the
circumference grows — and that rate is **stitch-height dependent**:

| Stitch | Increase / round for a flat disc |
|---|---|
| `sc` | +6 |
| `hdc` | +8 |
| `dc` | +12 |
| `tr` | +16 |

Too many increases and the edge ruffles; too few and it cups into a bowl.
`form` declares which of these behaviours you *want*, and the checker verifies
the increase schedule against it:

- **`form disc`** — every round increases at exactly the stitch's flat rate.
  Deviation is E292 ("your circle won't lie flat").
- **`form sphere` / `ball`** — flat-rate increases for the crown, straight
  rounds, then a **mirror-image** decrease schedule; the checker verifies the
  decrease half mirrors the increase half (asymmetry is E297), which is what
  makes a ball round instead of lumpy.
- **`form cone`** — a constant, *sub-flat* increase (fewer than the flat rate,
  evenly spaced); the checker verifies the cadence is constant and below the
  ruffle threshold.
- **`form tube`** — no increases after the base; any stray increase is flagged.

Because every count is a literal per size, this is **static discharge** —
`proved by construction — 0 runs` for almost every pattern. The `LittleBall`
above: `sc` sphere, crown increases 6/round to 24 (flat-rate ✓), holds rounds
5–8, decreases 6/round back to 6 — a mirror of the increase (✓). Mis-write
round 3 as `(sc, sc, inc) around` (only +4 where sc-flat wants +6):

```
error[E292]: this circle won't lie flat (single crochet, form disc)
  --> coaster.cure:8
   |
 8 |   round 3: (sc 2, inc) around              — 24 sts
   |
  A flat single-crochet circle needs +6 stitches per round; round 3 adds
  only +4 (18 → 22, not 24). Too few increases cup the fabric into a bowl.
  Use (sc, inc) around for +6, or declare `form cone` if a cup is what you
  want.
```

`form` also accepts finished measurements through `units` (§9): `form disc
diameter 12cm` cross-checks the round count against gauge, the way knit's
`shape 48cm -> 36cm` does.

## 6. Generated artifacts

One source of truth, several renderings (knit §6, same machinery):

- **Symbol charts** — the round/row symbol diagram (Craft Yarn Council
  crochet symbols), generated from the written instructions with correct
  spiral-vs-joined layout (concentric for joined rounds, offset spiral for
  amigurumi). Round-trip both directions, checked (§8).
- **Per-size stitch-count tables** — count at every round for every size.
- **Yarn estimate** — from hook/gauge plus total stitch count and per-stitch
  yarn take-up (dc eats more than sc; §10.7), per size.
- **Printable pattern PDF** — abbreviation key (US/UK aware), form schematic
  with measurements at gauge, charts, written instructions, count tables. The
  amigurumi companion / device crossover from the knit vertical (§3.5) applies
  verbatim — a round counter that shows the instruction *and* the checked
  count.

## 7. Errors — explainers in crocheter vocabulary (E290–E299)

Per parent §4, no kernel vocabulary surfaces; the macro's `explain` owns the
shapes. Template as everywhere: what you wrote → why the fabric forbids it →
what to write instead.

```
error[E290]: stitch counts don't balance between rounds 9 and 10 (size M)
  --> bear.cure:14
   |
14 |   round 10: (sc, dec) around               — 12 sts
   |
  round 9 produces 18 stitches, but (sc, dec) is 3 wide and works 6 repeats
  = 18 consumed, 12 produced — the callout says 12 ✓, but round 9 above ends
  at 20, not 18. The mismatch is upstream: round 9's decreases.
```

```
error[E293]: nothing to work into here
  --> shawl.cure:22
   |
22 |   row 7: (dc in ch-2 sp, ch 2) to end
   |               ^^^^^^^^^
  Row 6 made no chain-2 spaces — it is solid double crochet. `into ch-2 sp`
  needs a space below it. Did you mean `dc in next dc`, or is row 6 missing
  its `ch 2`s?
```

```
error[E294]: turning chain doesn't match the stitch
  --> coaster.cure:9
   |
 9 |   round 3: ch 1, (dc, 2 dc in next) around, join
   |            ^^^^
  A round of double crochet turns with ch 3 (dc is 3 chains tall); ch 1 will
  pull the edge in. Use ch 3, or work the round in single crochet.
```

Others in the block: E291 (repeat doesn't divide the round), E292 (circle
won't lie flat — §5), E295 (`— n sts` callout wrong), E296 (spiral/joined
misuse — a `join` inside a `spiral`, or a joined round missing its close),
E297 (form asymmetry / unreachable shaping target). E298–E299 reserved.

## 8. `check` integration

`crochet` ships property templates per parent §7.5:

- **Per-size balance + form** — every round balances, every repeat divides,
  every anchor exists, and the form schedule (§5) holds, every size. Almost
  entirely **static discharge**: `proved by construction — n instantiations,
  0 runs`. The prop exists so the guarantee is *visible* in `cure test`.
- **Chart ↔ written round-trip** — render to symbol chart, read back, compare,
  both directions, including spiral offset layout.
- **Gauge arithmetic** — finished measurements from hook/gauge (disc diameter,
  amigurumi height) recompute consistently under unit round-trips.

## 9. Relations

- **`knit`** (sibling) — shares the vertical (personas, tech-editor economic
  wedge, companion device, PDF/Ravelry publishing, `parse` import funnel).
  The two macros share *nothing algebraic* (different state) but *everything
  ergonomic*; the knit-vertical scope doc's §2 principles are law here too.
- **`units`** — hook size, gauge, and `form … diameter 12cm` are units facts;
  cm/inch and sts-per-10cm conversions reuse the units machinery.
- **`parse`** — importing written crochet patterns ("Rnd 3: *sc, 2 sc in next;
  rep from * around (18)") is a `parse` grammar over the abbreviation
  vocabulary, US/UK-tagged; high-value on-ramp, real wild-corpus ambiguity —
  ledgered (§10.5), not v1.
- **`check`** — §8; Antigen's generator/oracle machinery, reused.
- **`view` / `schema` / `board` / `display`** — the amigurumi round-counter
  companion and e-paper device, exactly as knit vertical §3.5.
- **`blocks`** — a symbol-chart grid editor as an alternative visual input
  surface, one line here.

## 10. Open decisions (ledger)

1. **The full fabric graph** — the position-vector state (§3) covers the
   dominant cases: spirals, plain rows, filet/mesh, basic shells, granny
   squares worked into the previous round's chain-spaces. It does **not**
   cleanly cover stitches that reach into *arbitrary earlier rows* — spike
   stitches, overlay/tapestry crochet, deep post stitches, Bavarian/Catherine-
   wheel motifs. The general case needs each stitch to carry its parent anchor
   as a graph edge (the row is no longer the right abstraction), and it is the
   explicit v2 — parallel to knit's brioche/short-rows carve-out. Ledgered so
   nobody forces the general graph into the vector model prematurely.
2. **Tunisian crochet** — a genuine hybrid: the forward pass holds *all* loops
   on the hook and the return pass works them off, so its state is a full row
   of live loops — **knit's `Nat` state, not crochet's vector**. It is
   arguably closer to `knit` than to `crochet`. Options: a `tunisian` mode in
   this macro that swaps in the single-count algebra, a shared sub-algebra
   both macros import, or its own small macro. Undecided; noted so the
   surface doesn't accidentally assume one-loop-on-hook everywhere.
3. **Post / relief stitches** (`fpdc`/`bpdc`) — need the position to carry
   stitch *identity* (a post to grab), a modest extension of `Position`;
   in-vector (works into the round below) so v1-reachable, but the surface and
   the E293 anchor check need the post case designed. Cabling and basketweave
   ride on this.
4. **Colorwork** — tapestry (carry colors, work over the float) and
   intarsia-style color changes; color as a per-stitch attribute for charts
   lands early (as in knit §10.2), the carried-float structural check waits on
   §10.1's graph work.
5. **Pattern import fidelity** (`parse`, §9) — what fraction of the wild
   written corpus parses clean vs. needs hand-fixup; US/UK auto-detection
   heuristics; import should emit the `crochet` surface (round-trip
   discipline).
6. **Chart symbol standard** — Craft Yarn Council vs. Japanese (JIS) crochet
   symbols; pick one canonical v1 set, isolate in the renderer, themes later.
7. **Yarn take-up model** — per-stitch-height consumption factors (a `tr` eats
   far more than a `sc`); shipped defaults + designer overrides; error bar?
8. **Amigurumi-specific gauge** — amigurumi has no blocked gauge; the relevant
   fact is "tight enough that stuffing doesn't show." Whether `form sphere`
   should warn on a hook-to-yarn ratio that reads as loose is a soft,
   ledgered check.

## 11. Non-goals

- **Not the knit algebra** — separate state, separate macro (§1); no shared
  count machinery beyond the ergonomic surface.
- **No general fabric-graph shaping in v1** — §10.1; spike/overlay/deep-post
  work is v2.
- **No garment/toy *design* automation** — the macro checks patterns; it
  does not draft or design them. "Generate an amigurumi cat from a photo" is a
  different product. `crochet` is the tech editor, not the designer.
- **No freeform / sculptural crochet** — patterns worked by eye without a
  round structure have nothing to check and are out of scope, as knit's
  non-goals put freeform knitting.
- **No yarn-stash / queue app** — pattern-adjacent, welcome to consume the
  generated artifacts, not language work.

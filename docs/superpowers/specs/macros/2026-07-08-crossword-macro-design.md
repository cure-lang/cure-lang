# `crossword` — Constructor-Grade Puzzle Building

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #65, promoted); built as a `macro` (§5) — zero compiler
special-casing. This macro is the **poster child for the locked SMT trust
boundary as a product**: the fill solver may generate anything; only what the
simple checked verifier accepts ever reaches a puzzle file.

---

## 1. Purpose

Crossword construction is a real, serious hobbyist community — indie puzzle
publishing is thriving, and constructors already live by rules that *are*
refinements: symmetry, minimum word length, no unchecked squares, no duplicate
answers. `crossword` makes the grid discipline a set of compile-time checks in
constructor vocabulary, and makes the fill pipeline the project's
solver-generates/kernel-verifies trust pattern made tangible: an untrusted
search engine proposes fills, and simple, checked code verifies every one
before it becomes a puzzle. Per the hiding principles (parent §3, LAW), the
constructor declares a grid and word lists; the macro manufactures the
indexed slot structure, the verification obligations, and the export code.
No type, goal, or solver artifact is ever surfaced.

## 2. Surface

A `grid` declaration states dimensions, style, symmetry, the block pattern,
and theme entries. **Slots are derived from the grid, never hand-declared**
(hiding principle 1) — the macro computes every Across and Down slot from
the block pattern, numbers them by the standard convention, and checks the
discipline cell-by-cell at compile time:

```cure
crossword Tuesday
  grid 15 x 15
    style :american                 # every white cell checked both ways
    symmetry :rotational            # or :mirror — verified cell-by-cell
    blocks
      "...#.....#....."
      "...#.....#....."
      # … 15 rows; symmetry of THIS pattern is what gets checked
    min_word 3                      # {n: Int | n >= 3} — the standard rule

  theme
    across 17 = "RAINCHECK"         # pinned to a numbered slot
    across 57 = "SNOWDRIFT"         # placement symmetry checked (§ below)

  words
    allow  Std.Words.Ranked         # ranked dictionary — the fill quality axis
    allow  "my-seed-list.dict" rank 60
    deny   Std.Words.Breakfast      # profanity / breakfast-test layer
```

Compile-time grid discipline (all by computation over the declared pattern —
concrete literals, the domain where every obligation reduces away):

- **Symmetry** — `:rotational` requires `block(r, c) == block(H-1-r, W-1-c)`
  for every cell; `:mirror` the vertical-axis analogue. Checked cell-by-cell;
  a violation names the offending cell (§7).
- **Minimum word length** — every derived slot's length satisfies
  `{n: Int | n >= 3}`. Two-letter slots are the canonical rookie grid bug.
- **No unchecked squares** — every white cell lies in both an Across and a
  Down slot (coverage — the standard American rule). `style :cryptic` relaxes
  this to the usual alternating-checked convention; the style is declared,
  never inferred.
- **Theme placement symmetry** — theme entries pinned to positions must
  themselves sit symmetrically (17-Across's slot maps onto 57-Across's under
  the declared symmetry) and fit their slots exactly, length-checked.

## 3. Solver-generates, checker-verifies

The fill pipeline is the locked SMT trust boundary, productized:

1. **The solver generates.** A search engine (constraint propagation,
   backtracking, whatever) fills the derived slots from the ranked word
   lists, holding theme entries fixed. The solver is **untrusted and
   swappable** — bring your own, tune it, replace it; nothing about puzzle
   correctness depends on it. A better solver finds *nicer* fills, never
   *more correct* ones.
2. **The checker verifies.** Every candidate fill passes through simple,
   checked verification code before acceptance:
   - every slot's word appears in the declared allow lists (and no deny list),
   - every crossing cell is consistent (the Across and Down words agree on
     the shared letter),
   - no answer appears twice in the grid,
   - theme entries are intact at their pinned positions.

   This verifier is short, total, and boring by design — it is the guarantee.
   Its verdict is what "this is a valid fill" *means*; the solver's opinion
   means nothing.

A fill the solver loves but the verifier rejects is discarded with a
constructor-vocabulary report of which check failed and where. This is
exactly the architecture the kernel uses for SMT (parent §7.5, "Certificate
elevation"): solvers may generate; everything generated is checked by
trusted, simple code. Here the pattern is visible enough to teach — the docs
should say so out loud.

## 4. Uniqueness honesty

"This puzzle has exactly one solution" needs honest handling. For a filled
grid, *existence* is free: the solver's own fill is definitionally a
solution, re-verified by §3's checker. (For crosswords, solver-experience
uniqueness really lives in the clues; what constructors care about here is
**no alternative fill of the same block pattern under the same word list**.)
Uniqueness-under-wordlist gets the `check` ladder's vocabulary (check spec
§2), reported per grid:

- **Minis (≤ 7×7): `proved`.** The fill space is small enough to enumerate
  exhaustively; the checked verifier confirms no second fill exists. This is
  a real, kernel-grade verdict — the enumeration is checked code, not solver
  attestation.
- **Full-size grids: `lint (solver-attested)`.** A second solver search for
  an alternative fill that comes back empty is evidence, not proof — the
  solver is untrusted, so its "none found" is exactly as trustworthy as a Z3
  lint (parent §3, principle 3). Reported honestly as lint-grade confidence,
  **never as proved**. A found alternative, by contrast, is a *verified*
  counterexample (the checker confirms it) and is reported as such.

Two-tier reporting mirrors `check`'s ladder deliberately — same words, same
honesty rule: rungs never inflate, and a solver failure demotes, never lies.

## 5. Clue discipline

- **Coverage** — every derived slot has exactly one clue. "15-Across has no
  clue" is the canonical explainer (§7); an extra clue for a slot that
  doesn't exist is the dual error.
- **Length displays** — clue/answer length annotations (the `(9)` in cryptic
  style, enumeration displays generally) are computed from the slot, never
  typed by hand, so they cannot be wrong.
- **Duplicate answers** — detected across the whole grid, including theme
  entries; a duplicate names both slots.
- **Word-list layering** — `allow`/`deny` lists are declared and ordered;
  deny wins. The breakfast-test layer is just a shipped deny list — swap or
  extend it; the mechanism is not opinionated, the default list is.

## 6. Generated artifacts

From one accepted grid + clue set:

- **`.puz` and `.ipuz` export** — the interchange formats the solving
  ecosystem actually uses.
- **Print PDF** — grid + numbered clue columns, publication layout.
- **Solving web UI** — one line: `view Tuesday` renders a playable puzzle on
  the web trio's `view` runtime.
- **Constructor stats** — word count, average answer length, block count,
  and a fill-quality score computed from the declared ranking (Scrabble-ish;
  scoring model ledgered §10).

## 7. Explainers

Registered per parent §4; the raw kernel never speaks. Representative:

```
error[E1xx]: 15-Across has no clue
  --> tuesday.cure:31
  Every slot needs exactly one clue. 15-Across is "RAINCHECK" (9).

error[E1xx]: grid is not rotationally symmetric
  --> tuesday.cure:8
  Cell (3,7) is a block but its rotational partner (11,7) is white.
  Make both blocks or both white — or declare symmetry :mirror if
  that's what you meant.

error[E1xx]: slot at (3,7) is 2 letters
  --> tuesday.cure:8
  American grids need 3+ letter answers. Add a block to close the
  slot, or open a crossing to extend it.

error[E1xx]: duplicate answer ERA
  --> tuesday.cure:8
  ERA fills both 22-Across and 48-Down. A published grid uses each
  answer once — refill one of the slots (deny-listing ERA for this
  grid forces the solver away from it).
```

## 8. `check`

`crossword` ships templates on the `check` ladder (check spec §6):

- **Grid rules discharge statically.** Symmetry, min-length, and coverage
  are theorems of the declared pattern — reported
  `proved by construction — grid discipline; 0 runs`. The parent's "tests
  you don't have to run" moment, in a domain where users already know the
  rules by heart.
- **Fill verification is the runtime template.** Every accepted fill re-runs
  §3's checker as a template prop — the verifier is the regression net for
  the whole solver pipeline, and a solver swap cannot silently break
  correctness.
- **Round-trip** — `import(export(puzzle)) == Ok(puzzle)` for `.puz`/`.ipuz`,
  the `codec` round-trip template pointed at puzzle files.
- Uniqueness verdicts (§4) report through the same runner with the
  ladder's vocabulary: `proved` for exhaustively-checked minis,
  lint-grade attestation otherwise.

## 9. Relations

- **`check`** — supplies the trust pattern and the ladder vocabulary this
  macro reports in; templates above.
- **`view`** — the one-line solving UI (§6).
- **`parse`** — clue file import (`.xd`, plain-text clue lists) is a `parse`
  grammar; ledgered (§10).
- **The `prompt` idea** — LLM-assisted clue *drafting* as an adapter: the
  model proposes candidate clues, the constructor picks and edits, the
  macro never auto-publishes a machine clue. Same shape as the solver
  boundary — generators generate, humans/checkers decide. Ledgered (§10).

## 10. Open decisions (ledger)

1. **Cryptic support** — different grid conventions *and* a clue grammar
   (wordplay annotations, enumerations). `style :cryptic` covers the grid;
   the clue grammar is probably a sibling macro sharing this one's grid
   core — decide when a cryptic constructor shows up.
2. **Word-list licensing & packaging** — shipped ranked dictionaries have
   licensing terms; pin list versions per puzzle (reproducible fills), and
   settle the package format for community lists.
3. **Fill-quality scoring model** — Scrabble-ish letter rarity vs. pure
   rank-average vs. crossing-freshness; constructors argue about this, so
   make it pluggable and ship one defensible default.
4. **Solver interface** — bring-your-own vs. a shipped default search;
   either way the interface is "candidate fill in, verifier verdict out",
   and the shipped one must be honest about being untrusted like any other.
5. **Collaborative construction** — two constructors on one grid (shared
   fill sessions, clue division). Attractive; needs the toolchain's story
   first; not v1.
6. **Clue file import formats** (§9 `parse`) — which formats, and whether
   import merges or replaces existing clues.

## 11. Non-goals

- **No automatic clue writing as a core feature** — the `prompt` adapter
  drafts; a human always selects. A puzzle whose clues no human chose is
  not this macro's product.
- **No solving-engine competitiveness** — the shipped solver only needs to
  fill hobbyist grids acceptably; speed records belong to dedicated fill
  software, which the solver interface (§10.4) welcomes in.
- **No other puzzle types** — sudoku, acrostics, spelling bees live in the
  backlog's broader `puzzle` space; this macro stays a crossword tool.

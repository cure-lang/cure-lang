# `fold` — Origami Crease Patterns with Compile-Time Flat-Foldability

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #61, promoted). Built as a `macro` (§5) — zero compiler
special-casing; hiding principles (§3) are law here as everywhere.

---

## 1. Purpose & positioning

A crease pattern is a program whose interpreter is a sheet of paper — and one
with *published theorems about its bug class*: a pattern folds flat only if
every interior vertex satisfies **Maekawa's theorem** and **Kawasaki's
theorem**. Both are pure arithmetic over declared geometry — every coordinate
a literal, every angle computed from literals — so per hiding principle 3
every obligation discharges by computation: no solver, no proof term, no
hole. The parent's §1 thesis at its most photogenic: a compile error that
cites a geometry theorem by name.

Today a designer checks these conditions by eye, or discovers the violation
with creased paper in hand — the vertex that "won't lie down" after an hour
of pre-creasing. `fold` makes that vertex a compile error before any paper
exists, and generates the crease-pattern SVG, per-step diagrams, and plotter
cut/score files from the one checked source of truth.

## 2. Surface

A `pattern` block declares vertices (coordinates), creases (vertex pairs
with a mountain/valley assignment), and optionally a grid. Faces are
**derived** — the planar subdivision of the paper by its creases — never
declared.

```cure
pattern WaterbombBase
  paper 150mm square

  vertex c at %[75, 75]                    # the single interior vertex
  crease c -- corner(:nw)   mountain
  crease c -- corner(:ne)   mountain
  crease c -- corner(:se)   mountain
  crease c -- corner(:sw)   mountain
  crease c -- edge(:w, 75)  valley
  crease c -- edge(:e, 75)  valley
```

Four mountains, two valleys, angles 45°/90° alternating — both theorems hold
at `c` and the pattern compiles. Flip one diagonal to `valley` and it does
not (§7).

- **Grid conventions — box pleating is first-class.** Modern representational
  design is dominated by box pleating: creases on a square grid, at
  0°/45°/90° only. `grid 16` switches coordinates to grid units and installs
  alignment refinements — vertices become `{x: Int | 0 <= x and x <= 16}`,
  crease directions must lie in the 0/45/90 set (a crease from `%[4, 4]` to
  `%[7, 5]` is rejected as "not a grid direction"). On-grid, all theorem
  arithmetic is exact integers.
- **Off-grid patterns** use `mm` coordinates directly; the theorems are still
  checked exactly (§3, the no-floats checker).
- **Named sub-patterns** are reusable declarations — a bird base is written
  once and instantiated with `use BirdBase`, creases and sequence imported.
  Instantiation re-runs all checks on the composed pattern: a sub-pattern
  that folds flat alone can still create a violating vertex where its
  creases meet yours, and that is what gets caught.
- **Units** are degrees and millimetres (units macro, parent §6.6);
  `paper` declares the sheet. The theorems are angle-based, hence
  **scale-independent** — resizing the paper never changes a verdict.

## 3. The theorems — Maekawa & Kawasaki

The headline. At every **interior** vertex (creases ending on the paper edge
are exempt — the boundary absorbs their imbalance):

- **Maekawa's theorem** — mountain and valley creases meeting at the vertex
  differ in count by exactly two: `|M − V| == 2` (corollary: even degree).
  Pure counting — a refinement over two integers the elaborator computes
  from the declarations.
- **Kawasaki's theorem** — the angles around the vertex alternate to
  balance: odd-indexed angles sum to 180°, as do even-indexed. A Kawasaki
  failure means the *geometry* cannot fold flat under any assignment; a
  Maekawa-only failure means the geometry is right and the mountain/valley
  assignment is wrong. The two errors are distinguished because the fixes
  differ (§7).

Both discharge by computation. On a grid, angles are exact multiples of 45°
and the sums are integer arithmetic. Off-grid the checker still touches no
floating point or trig: Kawasaki is equivalent to the composed reflections
across the crease lines being the identity, and reflection matrices over
rational coordinates are rational — an exact closure check. Maekawa is
integer counting everywhere. No solver, no epsilon, no "tolerance" knob.

## 4. The honesty boundary — local vs. global flat-foldability

Load-bearing. Maekawa + Kawasaki are **necessary** conditions — together
they characterize *local* flat-foldability (each vertex folds flat in
isolation). **Global** flat-foldability — a valid layer ordering for the
whole sheet, no face forced through another — is NP-hard. No per-vertex
arithmetic settles it, and `fold` does not pretend otherwise. The v1
contract, stated in every report and artifact:

> **locally flat-foldable — layer ordering not verified**

- The local theorems are checked statically, always, reported as proved with
  the interior-vertex count (§8).
- A **layer-ordering search** may additionally run: a search/SAT-style
  procedure over face orderings that, when it finds one, *attests* global
  flat-foldability. Per the locked solver trust pattern this is **lint-grade
  attestation** — advisory, outside any proof claim, reported as
  `attested (layer ordering found)`, never `proved`. A timeout or disabled
  search leaves the local verdict intact; nothing fails.
- The two tiers reuse `check`'s ladder vocabulary (parent §7.5): *proved by
  construction* for the local theorems, *attested* for layer ordering — no
  rung between them to blur.

A designer always knows which claim they hold. "Locally flat-foldable"
already kills the dominant error class; the honest label for the rest is a
feature, not a hedge.

## 5. Fold sequences

A pattern says what the paper looks like unfolded; a `sequence` says how to
get there. Steps are ordered, each checked against the state prior steps
established — **typestate over the diagram sequence**:

```cure
  sequence
    step 1 "fold in half":       valley along c -- edge(:w, 75), c -- edge(:e, 75)
    step 2 "collapse the base":  mountain along c -- corner(:nw), c -- corner(:se)
    step 3 "collapse the base":  mountain along c -- corner(:ne), c -- corner(:sw)
```

- A step folding along a crease **not declared** in the pattern is a compile
  error — the sequence cannot invent geometry.
- A step may only reference vertices and landmarks **established by prior
  steps** (a landmark created by step 4's fold does not exist in step 3).
  Same machinery as the driver macro's attach protocol: the diagram state
  is an index; out-of-order references are inexpressible.
- **Sequence completeness:** every crease is either used by some step or
  explicitly marked `decorative` (pre-crease guides, reference creases). An
  unused, unmarked crease is an error — a missing step or a stray
  declaration, both bugs in a published diagram.

## 6. Generated artifacts

One source of truth, several renderings:

- **Crease-pattern SVG** — standard diagramming line styles: valley dashed,
  mountain dash-dot, paper edge solid; grids rendered faintly. The image
  every designer publishes, generated, always in sync.
- **Per-step diagrams** — one SVG per `sequence` step, the step's creases
  drawn against the state left by prior steps. The checked sequence *is* the
  diagram source; "the diagrams disagree with the crease pattern" becomes
  inexpressible to ship.
- **Cut/score export** for plotters and cutting machines (Cricut/Silhouette,
  laser scoring). Score lines and cut lines are **different types** — a
  crease exports as a score, the paper boundary as a cut, and the export
  path cannot conflate them: a machine cannot be told to cut a fold line.
  Driving such a machine from a Cure board program is the same `gpio`/plotter
  world as the rest of the parent catalog — and that one sentence is all the
  hardware tie this macro needs.

## 7. Errors — explainers in folder vocabulary

Per parent §4, no kernel vocabulary ever surfaces; the macro's `explain`
block owns the failure shapes. (Error-code allocation pending in the
explainer registry — E18x used illustratively.)

```
error[E250]: vertex at (30, 40) breaks Maekawa's theorem
  --> crane.cure:14
   |
14 |   crease v3 -- v7 mountain
   |
  5 mountains and 2 valleys meet here — Maekawa needs the difference to be
  exactly 2 for the vertex to fold flat. Flip one crease at this vertex from
  mountain to valley (any one restores 4/3).
```

```
error[E251]: vertex at (60, 60) breaks Kawasaki's theorem
  --> crane.cure:21
  the alternating angles around this vertex sum to 172°, not 180° — this
  vertex won't fold flat with any mountain/valley assignment. The geometry
  itself is off: move the vertex or a crease endpoint by 8° worth
  (e.g. v9 to (60, 74)).
```

Template as everywhere: what you wrote → why the paper forbids it → what to
write instead, in creases and degrees, never in types. Maekawa errors suggest
an assignment flip; Kawasaki errors say the geometry itself is wrong and no
flip will help.

## 8. `check` integration

`fold` ships property templates per parent §7.5:

- **Local theorems** — Maekawa and Kawasaki at every interior vertex. Pure
  static discharge:
  `✓ locally_flat_foldable  proved by construction — 23 interior vertices; 0 runs`,
  with §4's honesty label attached verbatim; the prop exists so the
  guarantee is visible in `cure test` output.
- **Perturbation templates** — generated negative tests: jitter one crease
  endpoint or flip one assignment in a valid pattern; require rejection
  *with the right theorem named at the right vertex*. The error-message
  quality test — Antigen's antibody pattern, aimed at the explainers.
- **Sequence replay** — every step's preconditions hold (creases declared,
  landmarks established, completeness satisfied). Static; finite literal
  data.
- **Layer-ordering attestation** (when enabled) reports on the `attested`
  rung only, per §4 — the two-tier claim, mechanically enforced.

## 9. Relations

- **`knit`** ([`2026-07-08-knit-macro-design.md`](2026-07-08-knit-macro-design.md))
  and the prospective quilt macro — the craft family: declared geometry
  with arithmetic invariants, checked per-literal, artifacts from one source;
  `fold` is the same shape with named theorems where knit has stitch balance.
- **`blocks`** — visual crease editing (draw the pattern, get the `pattern`
  block) rides the block/visual-editing surface; one line here.
- **`units`** (parent §6.6) — degrees and mm, `paper` sizes, cm/inch export
  conversions.
- **`check`** — §8; generator/oracle machinery is Antigen's, reused.

## 10. Open decisions (ledger)

1. **Layer-ordering attestation scope** — search strategy (SAT encoding vs.
   backtracking over face stacks), time budget, whether a found ordering is
   exported (useful — it is the folding order); all lint-grade per §4.
2. **Curved creases** — **out.** Developable-surface differential geometry,
   not vertex arithmetic; Maekawa/Kawasaki do not apply. A different macro
   if ever; ledgered so nobody bolts it on.
3. **Tessellations** — repeat units with boundary-condition checks (a unit's
   edge creases must meet its translated neighbour's compatibly). Attractive
   v1.5: small repeat machinery, same arithmetic at the seam vertices.
4. **Simulation/preview** — Origami Simulator-style spring-mass preview.
   Recommendation: **export** to the existing external tools (they accept
   crease-pattern SVG with standard line styles) rather than build a physics
   view in-language; revisit only if the export loop proves too slow.
5. **Rigid-origami checks** — rigid foldability (flat panels, hinge-only
   motion) is a different condition set; relevant to the engineering crowd.
   A possible second theorem family, not v1.
6. **Angle grids beyond 45°** — classic bases (the bird base included) live
   on 22.5° multiples, not the box-pleating grid. `grid 8 angles 22.5deg`
   vs. plain off-grid exact coordinates — the checker handles both; the
   question is which alignment refinements to offer.
7. **Constructible-coordinate exactness** — fold constructions can produce
   nested square roots. V1 requires rational coordinates (where §3's
   reflection check is exact); a quadratic-extension coordinate type later.

## 11. Non-goals

- **No fold-physics simulation in-language** — preview is an export target
  (§10.4); paper mechanics is not language work.
- **No curved-crease design** — different mathematics entirely (§10.2).
- **No automated design** — TreeMaker-style "given this base tree, compute a
  crease pattern" is a design synthesizer, a separate product someday. `fold`
  checks the pattern you designed; it is the tech editor, not the designer.

# Metastatic's meta-slot blind spot — design

**Date:** 2026-07-15
**Status:** design for review (no implementation)
**Related:** the six irregular-tuple shapes (separate, smaller gap — see §3); `lib/cure/meta_ast/conformance.ex` (the detector built for component (1)); the migrator→MetaAST rework (downstream consumer, specified as a phase in §8).

## 1. Summary

Metastatic's generic AST traversal descends only the **children** slot of a
canonical `{type, meta, children}` node. It never walks the **meta** slot. Cure's
surface AST stores a large fraction of its most important subtrees *in meta* —
every parameter's type, every function's parameter list and return type, every
match arm's pattern, and more. Those subtrees are invisible to every consumer
built on stock Metastatic traversal (RAG index, MCP, the migrator, any future
tool). Empirically that is **~2,600 hidden nodes across the 48-module stdlib**.

This is distinct from — and much larger than — the six irregular tuple *shapes*
(§3). A node can be perfectly shape-conformant and still hide its entire type
structure in meta; `param` and `function_def` both do exactly that.

The question this spec answers: **can we fix our side rather than change the
Metastatic dependency, and is an Elixir source rewriter the right mechanism?**
Short answer: yes to the first; the rewriter earns its keep *only* for the
full representation refactor (Option C), and even there its leverage is at the
construction sites, not the read sites. Cheaper adapter options (A, B) resolve
every consumer we can currently name without any rewrite. The real decision is
whether we pay to eliminate a standing walker-drift trap or accept adapter
discipline forever.

## 2. The blind spot — mechanism and evidence

### 2.1 Mechanism

`Metastatic.AST.do_traverse/4` (`deps/metastatic/lib/metastatic/ast.ex:730`)
matches `{type, meta, children} when is_atom(type) and is_list(meta)`, applies
the pre hook, recurses **only via `traverse_children` on the third slot**,
reconstructs `{type, meta, new_children}`, then applies the post hook. The meta
slot is copied through untouched — never walked. `prewalk/2,3`, `postwalk/2,3`,
and `traverse/4` all delegate here (`ast.ex:800, 824, 842`), so **every**
Metastatic walker shares the blind spot. There is no per-walker escape.

### 2.2 The two representative nodes (confirmed against the live parser)

```
function_def  = {:function_def, meta, [body_expr]}
    meta keys:   [:return_type, :name, :params, :visibility, :arity, :line, :col]
    :return_type → a {:variable,…} NODE
    :params      → a LIST of {:param,…} NODES
    children     → [body] only

param         = {:param, [type: {:variable,…}], "x"}
    meta keys:   [:type]
    :type        → a NODE
    children     → the name string "x" (a leaf)
```

Both are **structurally canonical 3-tuples** — atom tag, keyword meta, third
slot. Stock Metastatic descends `function_def`'s body and `param`'s name string,
and stops. It never sees the parameter list, the parameter types, the return
type. The entire signature/type layer of every function is dark.

### 2.3 Scan of the stdlib (48 modules)

Meta keys whose value hides a canonical node, by `(parent_tag, key)` and count
(`scratchpad/metascan2.exs` — a total-descent walk that records each meta value
containing a node):

| parent · key | count |
|---|---|
| `param :type` | 999 |
| `function_def :params` | 535 |
| `function_def :return_type` | 526 |
| `match_arm :pattern` | 366 |
| `container :decorator` | 54 |
| `lambda :params` | 31 |
| `implementation :for_type` | 18 |
| `indexed_type :indices` / `:params` / `:decorator` | 11 |
| `function_call :callee` | 9 |
| `function_def :constraints` | 7 |
| **total** | **~2,600** |

This is not a corner case. It is the signature, type-annotation, and
pattern-matching surface of essentially every definition Cure has.

## 3. Relationship to the six irregular shapes (a separate, smaller gap)

The detector in `lib/cure/meta_ast/conformance.ex` flags two **completeness**
defects (INV-A/INV-B) — a canonical-guard walker cannot reach a subterm hidden in
either a non-canonical atom-headed tuple (`:bad_shape`) or a children slot that is
a bare node instead of a list (`:node_child`). Six shapes trip these, measured
across the full first-party corpus (`lib/std` + `examples` + oracle probes +
fixtures — the tripwire's shrinking allowlist):

| Shape | Kind | Items | Files | Fix |
|---|---|---|---|---|
| `gadt_ctor` | `node_child` | 179 | 78 | wrap the bare `arrow_chain` child in a list |
| `group` | `bad_shape` | 47 | 47 | normalize 2-tuple → canonical 3-tuple |
| `builtin` | `bad_shape` | 10 | 10 | normalize 2-tuple → canonical 3-tuple |
| `named_implicit_pat` | `bad_shape` | 10 | 10 | normalize 4-tuple → canonical 3-tuple |
| `named_dom` | `bad_shape` | 8 | 8 | normalize `{tag, name, inner}` → canonical 3-tuple |
| `forced_pattern` | `node_child` | 8 | 8 | wrap the bare child in a list |
| **Total** | | **262** | | **6 producer edits** |

The 262 occurrences reduce to **6 producer edits** — one per shape, at the site
that emits it. Each edit deletes the corresponding allowlist bucket; the allowlist
reaching `[]` is the definition of done. (`arrow_chain` no longer appears as its
own `bad_shape` shape: every occurrence is a `gadt_ctor`'s bare `arrow_chain`
child, re-attributed to `node_child :gadt_ctor` once the children-list invariant
was added.)

These are **orthogonal** to the blind spot:

- Fixing the six shapes (normalize to 3-tuples) makes them *reachable* once
  they sit in a children slot — but does nothing for the 2,600 nodes that are
  reachable-in-principle yet parked in meta.
- Fixing the blind spot (meta→children, or a meta-aware walker) does nothing for
  a malformed 2-tuple.

Both must be addressed for full conformance, but they are independent work. The
detector already covers the shape gap (component (1)); this spec is about the
meta gap.

## 4. Why the compiler's safety net does not cover the meta fix

For the six shapes, flipping a construction site produces Elixir
unreachable-clause warnings and pattern-match failures at every stale consumer —
the compiler hands you the worklist. **The meta fix has no such net.** A reader
does `Keyword.get(meta, :type)` or `meta[:type]`; after the type moves to a
child, that call returns `nil` — a valid value, no warning, no crash at the read
site. The breakage surfaces later and elsewhere (a `nil` where a node was
expected), or not at all until a specific path runs. These meta keys are read
throughout `lib/cure/**` — via `Keyword.get`, `Keyword.fetch!`, and pattern
destructuring under many local names (`meta`, `p_meta`, …), so there is no single
grep that enumerates them and no compile-time list to work down — and many of the
reads sit on the elaborator hot path.

This asymmetry is the whole reason a source rewriter is worth discussing: the
change is mechanical and repetitive, and the compiler will not find the sites
for you. It is also why the conformance detector matters as a **green gate** — a
detector extended to also flag "canonical node hidden in meta" gives the mass
change a red→green signal that the compiler alone cannot.

## 5. Fix options

Two axes: **our side vs. Metastatic side**, and **adapter vs. representation
change**. The user's stated preference is our-side; this section foregrounds A/B/C
and treats D as contrast.

### Option A — Cure-side meta-aware traversal (adapter, internal consumers)

Add `Cure.MetaAST.prewalk/postwalk/traverse` that descend meta *values* as well
as children (the detector's `walk_meta_values/3` already prototypes exactly this
descent). Internal tools — the migrator above all — call the Cure wrapper instead
of `Metastatic.AST.prewalk`.

- **Cost:** one module, no representation change, no elaborator risk, no rewriter.
- **Serves:** every internal Cure tool that we control.
- **Does not serve:** external raw-Metastatic consumers (RAG/MCP indexing that
  calls stock Metastatic on exported AST).
- **Caveat:** correctness now depends on every author remembering to use the
  Cure wrapper. Anyone who reaches for stock `Metastatic.prewalk` silently gets
  the blind spot back. This is the standing walker-drift trap (§6).

### Option B — boundary canonicalization (adapter, external consumers)

At the one choke point where Cure exports AST to Metastatic consumers (the
RAG/MCP upsert / serialization boundary), run a generic structural transform
`Cure.MetaAST.to_conformant/1` that lifts every meta value containing a node
into the children slot under a wrapper node (e.g. `param`'s `:type` becomes a
child `{:param_type, meta, [type_node]}`; keys carrying only primitives stay in
meta). Internal representation is untouched.

- **Cost:** one transform function (a rewriting cousin of the detector's walk),
  no internal changes, no rewriter.
- **Serves:** external raw-Metastatic consumers — they receive a tree stock
  traversal fully descends.
- **Does not serve:** anything that round-trips the *internal* form (the migrator
  reprints internal AST; it needs A, or an inverse of B).
- **Caveat:** the exported form differs from the internal form. Two shapes to
  keep straight; the printer must not be fed the canonicalized form.

A + B together resolve every consumer we can currently name, for the price of two
functions and zero representation change.

### Option C — representation refactor: move subtrees meta→children (the principled fix)

Change the parser (and any other constructor) so type/param/pattern subtrees are
built into the **children** slot from the start, and migrate every reader. After
this, the internal AST simply *is* conformant: stock Metastatic, the Cure
wrapper, external consumers, and any future tool all work uniformly, with no
adapter and no discipline to remember.

**The invariant this establishes.** The target is *not* empty meta. Meta
legitimately holds non-structural scalars — names, line/col, scope, visibility,
arity, and (as QTT lands) grades and erasure/implicit flags. The rule is narrower
and exact:

> **No canonical node may appear inside a meta value.** Every subterm lives in
> children; scalar annotations stay in meta.

This is exactly the predicate the extended conformance detector enforces (§6):
green iff the invariant holds. It is also a convention Cure *already follows* in
places — `pattern_match` is `{:pattern_match, [line:, col:], [scrutinee, arm1,
…]}`, meta scalars only, every subterm in children. The refactor brings the
stragglers into line with a node that is already right.

Why dependent typing makes this the correct direction (rather than a reason to
change Metastatic): the meta/children split is the standard annotations-vs-
structure division every homogeneous AST uses (Elixir's `{form, meta, args}`,
unist, estree). The dividing line is *"is this a subterm?"* — and in a dependent
language **types are terms** (`Vec n a` mentions the value `n`), so a type
annotation is unambiguously a subterm and belongs in children. Cure filed terms
under metadata; that is a category error dependent typing makes sharper, not
murkier.

**Concrete before/after** (the three largest offenders):

```
# current — subterm mis-filed as metadata
param        = {:param,        [type: T], "x"}
function_def = {:function_def, [return_type: T, name: "f", params: [P1,P2],
                                visibility:, arity:, line:, col:], [body]}
match_arm    = {:match_arm,    [pattern: Pat], [body]}

# target — subterms in children, scalars stay in meta
param        = {:param,        [name: "x", line:, col:], [ {:param_type, m, [T]} ]}
function_def = {:function_def, [name: "f", visibility:, arity:, line:, col:],
                 [ {:params, m, [P1, P2]}, {:return_type, m, [T]},
                   {:constraints, m, [...]}, {:body, m, [e]} ]}
match_arm    = {:match_arm,    [line:, col:], [ {:pattern, m, [Pat]}, {:body, m, [e]} ]}
```

### C's sub-fork: how named roles are represented in children — **C2 chosen**

Metastatic's children is a flat positional list, so a node's named roles (params
vs. return-type vs. body) are not first-class. Three shapes resolve this:

- **C1 — positional children.** Roles by position/convention. Leanest, most
  fragile; every consumer memorizes positions.
- **C2 — wrapper-node children (CHOSEN).** Each role becomes a typed child node
  whose tag names the role (`{:return_type, m, [T]}`, `{:params, m, […]}`). Fully
  conformant to *today's* Metastatic, self-describing, drift-proof. Cost:
  verbosity and "scan children for the role" access, both absorbed by thin
  Cure-side accessors (`Cure.MetaAST.child(node, :return_type)`). It emits the
  *same* wrapper shape Option B produces, so B and C converge (B is C applied at
  the boundary), and it extends the already-correct `pattern_match`.
- **C3 — labeled children inside Metastatic.** Teach traversal that children may
  be a keyword list of named sub-nodes it walks. Best ergonomics (keyed access +
  traversal), but changes the shared substrate's traversal contract and every
  consumer assuming children-is-a-list. The literal "Metastatic conforms to us"
  option; rejected here because it destabilizes the shared substrate for a gain
  (lean nodes + keyed access) that Cure-side accessors recover under C2.

**Decision:** C2. If Metastatic ever gains consumers beyond Cure, C2 is
decisively right (their children-is-a-list assumption is preserved). Even
treating Metastatic as Cure's private substrate, C2 keeps the trusted traversal
contract stable and pushes the only real cost (role access) into a trivial
accessor — the better place for it than Metastatic's core.

**The rewriter, with C2 fixed.** Details in §6. In short:

- **Construction sites** (parser, a handful of builders) are few, localized, and
  deterministic — a Sourceror-based rewrite emits the wrapper-child shape safely.
- **Read sites** are the hard part: a purely syntactic rewriter cannot always
  know that a given `meta[:type]` belongs to a `param` (it lacks the runtime node
  type), so it cannot blindly rewrite them. Read-site migration is therefore
  rewriter-*assisted* (transform the unambiguous patterns to the new accessor)
  plus grep-guided manual work, with the **behavioral test suite** catching stale
  readers (nil regressions) and the **extended detector** confirming the shape
  end-state.

- **Cost:** largest blast radius; touches the elaborator hot path (K-adjacent
  risk); silent-read hazard mitigated only by test coverage + detector.
- **Benefit:** eliminates the walker-drift trap permanently. No adapter, no
  discipline, one representation.
- **Sequencing:** do it **incrementally, one node type at a time**, gated by the
  extended detector, each step compiler+test-verified. `param :type` (999) is
  the highest-value first target; `function_def :params`/`:return_type` next.
  Big-bang is not required and not advised.

### Option D — Metastatic descends meta values (contrast; not our side)

Add an opt-in flag to `Metastatic.AST.traverse` to walk meta values. Smallest
possible change in lines, fixes all consumers at once — but it changes the shared
dependency, and it changes traversal semantics for *every* Metastatic user, not
just Cure. Listed for completeness; out of scope given the our-side preference,
though worth a conversation with the Metastatic owner if the trap in §6 is judged
unacceptable and C is judged too expensive.

### Rejected — per-key registry

A table of "these meta keys hold nodes, descend them." Rejected: it is the
walker-drift pattern the project treats as critical (a new meta key that holds a
node is silently skipped until someone updates the table; nothing fails closed).
Every option above is **structural** — it keys on "the value contains a node,"
never on a hard-coded key list — and so is drift-proof by construction.

## 6. The Elixir source rewriter, examined

The user's intuition — "a source rewriter would earn its keep if we fix our
side" — is correct, with one important scoping.

**Where it clearly helps (construction).** Moving `{:param, [type: t], name}` →
`{:param, [name: name], [{:param_type, m, [t]}]}` (the C2 wrapper shape) at the
parser build sites is a mechanical, semantics-preserving AST edit. Sourceror can
do this reliably: match the construction pattern, restructure the tuple, preserve
formatting.

**Where it is limited (reads).** A read site is `Keyword.get(meta, :type)` /
`meta[:type]` / a pattern `{:param, meta, name}` followed by `meta[:type]`. A
syntactic rewriter sees the variable `meta`; it does not know the runtime node is
a `param`. It can transform the *pattern-matched* cases (where the node tag is
visible in the same clause) but not the general `meta[:type]` reached through a
helper. So read-site migration is: rewriter for the unambiguous cases, manual for
the rest, with two nets — the behavioral suite (a stale reader yields `nil` →
some test fails) and the extended detector (shape end-state is provably
conformant).

**Why the detector is the linchpin.** Extend `Cure.MetaAST.Conformance` with a
second predicate: *no canonical node appears inside any meta value*. This is
additive — the detector as built enforces only the *shape* gate (it treats
`{:param, [type: T], "x"}` as conformant, because it is a canonical 3-tuple; it
descends meta values only to find shape violations nested deeper, never recording
that a node lives in meta). The new check reuses the existing `hides_node?/1`
helper: at each canonical node, any meta value that hides a canonical node emits a
violation tagged `kind: :node_in_meta`, distinct from the shape gate's
`kind: :bad_shape`. This is the red→green gate the compiler cannot provide for a
silent-read change.

**How the gate is introduced (it cannot be a day-one hard assertion).** The
`:node_in_meta` predicate is red across all ~2,600 sites today, and the
`:bad_shape` predicate is red across the ~66 six-shape sites — so neither
tripwire can assert "zero violations" against today's corpus without red-lighting
the suite before any refactor exists (and tests are immutable once green). Both
are therefore introduced as a **shrinking allowlist**: the tripwire asserts zero
violations only for the node types (or shapes) already migrated, and each
refactor step removes one entry from the allowlist as it goes green. So each C
step is: rewrite construction → migrate reads → drop that node type from the
`:node_in_meta` allowlist → detector confirms its meta is node-free → full suite
green → commit. The allowlist reaching empty is the definition of done.

**Honest verdict on the rewriter.** It is a genuine force multiplier for
construction and for the regular read patterns, and the detector makes the whole
operation verifiable. It is *not* a push-button codemod that flips the
representation unattended — the read layer needs human judgment and test coverage.
If we choose C, build the rewriter; if we choose A+B, the rewriter has nothing to
do.

## 7. Recommendation

1. **Now, to unblock consumers:** ship **A + B**. Two structural functions, no
   representation change, no rewriter, no elaborator risk. This makes the
   migrator (via A) and any external index (via B) see the full AST immediately.
   Lowest-risk, and it honors "if it's just semantics, prefer the lower-risk
   option."

2. **File C as the principled end-state**, to be executed **incrementally,
   rewriter-assisted, detector-gated**, starting with `param :type`. Its
   justification is not the named consumers (A+B already serve them) — it is
   **eliminating the standing walker-drift trap**: with A+B, any future code that
   reaches for stock `Metastatic.prewalk` silently mishandles the signature layer
   forever, and nothing warns. Given how seriously this project treats
   walker-drift (fail-closed walkers, structural detection, the core-walker-drift
   audit), that trap is a real liability, not mere aesthetics. C removes it.

3. **The decision to actually do C** is the one genuine fork, and it is the
   owner's: pay a large, elaborator-touching, incrementally-staged refactor to
   remove the trap, versus accept permanent adapter discipline. This spec does
   not pre-decide it; A+B are valuable and shippable regardless.

## 8. Phase: rework `Cure.Migrate` onto MetaAST traversal

This is the downstream consumer that motivated the whole initiative. It is
specified here as an explicit phase, sequenced **after** Option C.

### 8.1 Motivating defect (verified)

The migration facility (`lib/cure/migrate/**`, landed 2026-07-10, still unmerged)
does **not** traverse via Metastatic. `Cure.Migrate.fold_rules/2` hands the whole
AST to each rule's `detect_and_rewrite/2`; every rule hand-rolls its own recursive
walker. Two consequences, both confirmed against the live code:

- **`UppercaseTypeVar`** is hand-taught the meta layout — `rewrite_signature/4`
  reads `Keyword.get(meta, :params)` / `:return_type` and rewrites the type
  expressions in place. It works, but only because a human coded descent into each
  meta slot, and it took **five same-day follow-up fixes** (`9ccd04c9`,
  `58f976d9`, `69e143cd`, `610dd492`, `5ec6edb3`) to get the meta/children split
  right — propagate the rename into the body, freshen against body names, rename
  the implicit binder, handle proto/interface/impl heads, reuse a head var's
  rename across methods. Every one of those bugs is a subterm scattered between
  meta and children.
- **`ModuleRename`** was **not** taught that layout: its generic clause recurses
  children only. Verified live — running the `Std.Eq → Std.Equatable` rule on
  ```
  fn f(x: Std.Eq.T) -> Std.Eq.T = Std.Eq.eq(x)
  ```
  yields
  ```
  fn f(x: Std.Eq.T) -> Std.Eq.T = Std.Equatable.eq(x)
  ```
  — the body call renamed, **both signature occurrences (in meta) left pointing at
  the renamed-away module**, and the rule reports success. A half-migrated,
  non-compiling file with a clean bill of health.

This is the blind spot expressed in the one tool whose entire job is correct AST
rewriting — and the two rules disagree with each other about whether the signature
layer even exists.

### 8.2 Principle: retire the traversal, not the transformations

A rule bundles two separable things:

1. a **transformation** — *what* to rewrite (`Std.Eq → Std.Equatable`, lowercase a
   free type var). Inherently per-rule; stays handwritten. This is the rule's
   reason to exist.
2. a **traversal** — *how to reach every node* so the transformation lands
   everywhere. Should be generic and shared across all rules.

The defect is that meta-blindness forces every rule to hand-code #2 as well as #1:
stock `prewalk` never yields the meta-borne type nodes, so a rule must hand-write
descent into `:params`/`:type`/`:return_type` — or, like `ModuleRename`, silently
skip them. This phase retires the **hand-coded traversal** and rebuilds each rule
as *generic walk + local transform*. The transformations are unchanged. The rule
of thumb is exact: **handwrite the transformation, never the traversal.**

### 8.3 Hard ordering dependency: this phase is downstream of Option C

This rework **cannot precede** the C2 representation refactor. Stock
`prewalk`/`traverse` never enter meta, so a rule rebuilt on the generic walk
*today* would visit the `param` node but never be handed the `Std.Eq.T` type var
inside its `:type` meta. Rebuilding on the generic walk before subterms move to
children makes rules **more** broken, not less. Therefore:

> **Option C moves subterms meta→children first; only then do the rules collapse
> onto the generic walk.** The representation fix is what *enables* MetaAST-based
> migration — it is not a substitute for it.

The coupling runs both ways, which pins the timing precisely. The current rules
read the old shape directly (`Keyword.get(meta, :params)`); the moment a C step
relocates a slot, those reads break. So each C step that moves a slot must update
or rebuild every rule that reads it — and the conformance tripwire's shrinking
allowlist is the sequencing mechanism: shrink a bucket → fix the rule that
depended on it → green. C and the rule-rebuild advance **in lockstep, node type by
node type**, not as two independent projects.

### 8.4 Per-rule outcome (honest — not every rule becomes a one-liner)

- **`ModuleRename`** essentially does: `prewalk` + "rename if this node is a
  qualified reference to a renamed module." No per-slot descent; correct for
  signatures and bodies uniformly, by construction.
- **`UppercaseTypeVar`** stays **scope-aware**: it must gather every type var in a
  signature, build one rename map, freshen collisions, and thread that map through
  the body. With children-based shape this becomes **generic `traverse/4` + a
  scoped accumulator** (Metastatic's `traverse` carries an accumulator for exactly
  this) instead of hand-rolled descent plus a `var_names_deep` that has to grovel
  through both meta and children. A genuine simplification — one uniform descent,
  no meta special-casing — that removes the class of bug behind its five fixes,
  but not "delete the rule."

### 8.5 Build on Metastatic's own traversal, not a Cure-only walker

Rebuild the rules on **Metastatic's `prewalk`/`traverse`**, not a fresh
Cure-internal walker. The point of conforming to Metastatic is that "the migrator
can reach a node" and "RAG/MCP can reach a node" become the **same** guarantee —
enforced by the **same** traversal and the **same** conformance tripwire. A
parallel Cure-only walker would reintroduce a second traversal that can drift out
of sync, the exact failure mode this initiative exists to kill. (Option A's
Cure-side meta-aware wrapper is a *bridge* for the pre-C world; once C lands the
wrapper and stock Metastatic coincide, and the rules should target stock
traversal.)

### 8.6 Exit criteria

- Every migration rule reaches nodes through generic Metastatic traversal; no rule
  hand-codes descent into a meta slot.
- Every rename-class rule rewrites references in signature positions —
  regression-pinned by the `fn f(x: Std.Eq.T) -> Std.Eq.T = Std.Eq.eq(x)` case
  above, which must migrate all three occurrences (today it migrates one).
- The `:node_in_meta` allowlist is empty for every node type any rule touches (C
  complete for those types).

## 9. Open questions

- **Consumer inventory.** Exactly which tools consume Cure AST through stock
  Metastatic today (RAG index? MCP? anything else)? This determines whether B is
  even needed now, and how urgent the trap in §6 is. A+B are sized to the answer.
- **B's inverse.** Does any consumer need to round-trip B's output back to
  internal form? If yes, B needs a documented inverse; if no (consumers are
  read-only indexes), it does not.
- **Detector extension scope.** Should the meta-hidden-node tripwire live in the
  same `Cure.MetaAST.Conformance` module (a second violation class) or a sibling?
  (Recommend same module, distinct `kind:` on each violation — one detector, two
  gates.)

## 10. Scope / non-goals

- **In scope:** the meta-slot blind spot, the our-side fix options, the rewriter's
  role, and the migrator→MetaAST rework as a sequenced downstream phase (§8). The
  detector already built for component (1).
- **Out of scope here:** the six-shape normalization (its own follow-up); any
  change to the Metastatic dependency (Option D, noted only for contrast).
- **Non-goal:** a big-bang representation flip. C, if chosen, is incremental and
  gated.

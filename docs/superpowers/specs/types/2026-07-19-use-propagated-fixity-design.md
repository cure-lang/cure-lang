# `use`-Propagated Fixity Design

**Goal:** Make operator fixity (precedence groups + `infix`/`prefix`/`postfix`
declarations) propagate through `use`, uniformly for user modules and the
stdlib, with `@prelude` as the mechanism that makes the core operators ambient.

**Architecture:** A module's parse-time fixity table is the union of its own
fixity declarations, the fixity of every module in its transitive `use`-closure,
and the fixity of every `@prelude` provider. Extraction of a module's own
declarations is *table-independent*, so no dependency-ordered parsing is
required — only `use`-graph reachability, resolved on demand by module name
(the same `Paths`/`:cure_source_roots` resolution `Cure.Elab.Program` already
performs for `use` imports — no project-wide `DepGraph.scan` result is
threaded into `Parser.parse` today; see Component 2) plus a cheap per-module
scanner. Operator *protection* stops being a privileged
built-in list and becomes a single invariant: within any one module's assembled
table, each operator lexeme has at most one fixity.

**Tech stack:** Elixir; `Cure.Compiler.Parser` and friends. All changes live in
the compiler/parser and elaboration layers — **`lib/cure/core/**` (the TCB) is
untouched.**

## Global Constraints

- Zero TCB change. Nothing under `lib/cure/core/**` is modified.
- Fixity is a *syntactic* property, resolved at parse time. It must not depend
  on elaboration, type-checking, or name resolution.
- Fixity extraction for a module must never fail because that module's function
  bodies fail to parse — declarations are inert and extracted independently.
- Overloading (multiple `fn <op>` definitions) is orthogonal to fixity and never
  produces a fixity conflict.
- Full gate (`mix test`) green before merge; commits authored as the user only,
  no co-sign trailer.

---

## Background: current state

- `BuiltinFixity.table()` is the memoized parse of `lib/std/operators.cure`
  only. It is the single ambient fixity table.
- The parser seeds each module's Pratt table from `BuiltinFixity.table()` and
  layers the module's *own* `infix`/`precedencegroup` decls on top via
  `BuiltinFixity.extend/2`. `use`d modules contribute **nothing** to fixity.
- Therefore an operator declared outside `operators.cure` is usable only inside
  its own defining module, and is invisible to any importer.
- `Program.check_no_builtin_rebind/1` rejects a user module that redeclares the
  fixity of any operator present in the built-in table, exempting
  `Std.Operators` itself. This is a location-based privileged-list rule.

## The unified model

For a module `M`:

```
fixity(M) = own(M)
          ∪ ⋃ { own(X) : X ∈ use_reach(M) }
          ∪ ⋃ { own(X) : X ∈ ⋃_{P ∈ prelude_providers} (use_reach(P) ∪ {P}) }
```

- `own(X)` — the fixity declarations textually present in module `X`.
- `use_reach(M)` — every module reachable from `M` over `use` edges
  (transitive; cycles included).
- `prelude_providers` — modules carrying `@prelude` (already identified by
  `DepGraph`). Marking `Std.Operators` `@prelude` places the core operators into
  every module's table by this clause — the same clause a user's `use Foo`
  triggers. There is no separate "built-in" path. The third term therefore
  closes each prelude provider's *own* `use`-reachability too (`use_reach(P)`,
  not just `own(P)`) — a prelude provider is treated exactly as if every
  module had an implicit `use P`, and an implicit `use` propagates
  transitively like any other, per the middle term. Flattening only `own(P)`
  here (dropping `P`'s own `use`-closure) would silently under-propagate the
  moment a prelude provider itself `use`s a module that declares operators it
  relies on — `Std.Operators` today declares no `use`, so this is currently
  vacuous, but the design explicitly anticipates further prelude providers
  (Edge cases), so the formula must not bake in that coincidence.

Both precedence groups and operator declarations are ordinary nodes in each
module's AST, so groups travel with the operators that reference them; no
separate group-propagation logic is needed.

## Key enabler: fixity extraction is table-independent

`infix`/`prefix`/`postfix`/`precedencegroup` are inert declaration syntax whose
parse does **not** consult the fixity table. Extracting `own(X)` therefore needs
neither a seeded table nor a *fully successful* parse of `X`'s function bodies —
only that the declaration nodes themselves land in the result even when
surrounding statements don't. This is not a new capability: it is the same
mechanism `Parser.parse/2` already uses today to harvest `{:macro_def, ...}`
nodes (the "Phase 1 (harvest)" pass in `lib/cure/compiler/parser.ex`) — a full
`parse_program` pass, seeded with the always-available `BuiltinFixity.table()`
(never an empty table; an empty table is reserved for the one-time
`operators.cure` bootstrap, which is safe only because that file has no
operator-using expressions), with per-statement `synchronize_to_statement`
recovery so one broken statement doesn't stop later declarations in the same
file from being collected. `own(X)` reuses exactly this pass; see Component 1.
This removes the hard problem (dependency-ordered two-phase parsing, bootstrap,
cycle handling) for extracting `own(X)` itself — but `fixity(M)` is only as
complete as the `use`-graph reachability it unions over, and that reachability
is *not* automatically as tolerant of misparses. See Component 2 for the gap
this opens in `DepGraph` and what closes it.

## Components

### 1. Per-module fixity scanner — `own(X)`

A function that, given module `X`'s source (or tokens), returns its fixity
declaration nodes. Implementation: run the *harvest pass* `Parser.parse/2`
already performs today — seeded with `BuiltinFixity.table()`, with
`synchronize_to_statement` recovering past any statement whose expressions
reference not-yet-known operators — and collect the resulting
`{:fixity, ...}` / `{:precedencegroup, ...}` nodes, exactly as the harvest pass
already collects `{:macro_def, ...}` nodes today. This is *not* a hand-rolled
scanner that identifies and skips top-level item boundaries without parsing
them; it is a full statement-by-statement parse with per-statement error
recovery, reusing machinery already proven correct for the analogous
macro-harvest problem. It never seeds an empty table for a general module —
only the one-time `operators.cure` bootstrap does that, and only because that
file has no operator-using expressions to misparse; seeding an empty table for
an arbitrary module would misparse every built-in operator too (`+`, `|>`,
`==`, …), not just not-yet-propagated ones. Source location reuses today's
resolution: `Paths` for the stdlib, `:cure_source_roots` / `user_source_path`
for user modules.

**Caching scope, corrected from an earlier draft of this section:** "memoized
per module (persistent-term, keyed by module name), like `prelude_macros`" is
*not* safe as a blanket rule, because `prelude_macros` is safe to cache
unconditionally only because it is restricted to the fixed, in-tree stdlib
(`Path.wildcard(Path.expand("../../std/*.cure", __DIR__))`) — never a user
module. `own(X)` must run over arbitrary modules in `use_reach(M)`, including
user modules whose source changes across an incremental-compile/dev-loop
session within the same running VM. `Program.cached_module_interface/2`
(`lib/cure/elab/program.ex`, ~line 1648) already documents and enforces the
correct scoping rule for exactly this situation: "ONLY shipped stdlib paths
are cached. User and temp-file modules stay per-generation, so a fresh
generation still observes changed source... Caching by path regardless of
provenance would reintroduce exactly that hole." `own/1`'s persistent-term
cache must follow the same provenance check (unconditional cache for stdlib
paths; per-generation / non-persistent-term caching, or explicit invalidation
on recompile, for user and temp-file modules) — not a bare "keyed by module
name" cache that would go stale the moment a user edits a `use`d module's
fixity declarations mid-session.

### 2. `use`-closure fixity resolver — `fixity(M)`

Given `M`'s `use` list and the `@prelude` provider set, compute `use_reach(M)`
by an on-demand, name-based BFS — **not** by consulting a precomputed
`Cure.Compiler.DepGraph`: resolve each `use` target to a path (the same
`Paths` / `:cure_source_roots` / `user_source_path` resolution Component 1
uses for `own(X)`, and that `Cure.Elab.Program.import_source_path/1` already
performs for ordinary `use` imports), harvest that target's own `use` list
alongside `own/1` in the same pass, and recurse. This distinction matters:
`Cure.Compiler.DepGraph.scan/2` requires a predetermined compile-set file
list and is invoked only by the CLI/`Cure.Project`/stdlib-preload bulk-scan
paths (`cli.ex`, `project.ex`, `preload.ex`) to compute compile *order* —
that result is never threaded into `Parser.parse` or `Cure.Elab.Program`'s
per-module elaboration (`module_slice_env`, `elaborate/1`), both of which
already resolve `use` targets one at a time by name and must keep doing so
for `use_reach(M)`. The one piece with no name-based answer is discovering an
arbitrary *user* `@prelude` provider (Edge cases) — that genuinely requires
the project-wide scan `DepGraph` already performs, so the CLI/`Cure.Project`
driver must thread its `prelude_provider?` set down into each subsequent
`compile_file`/`Parser.parse` call as an option; a bare `Parser.parse` call
with no such option falls back to the compiler-bundled prelude set only, per
the single-file edge case. Union `own/1` over the reach plus prelude plus
`own(M)`. Memoized per module, under the *same* provenance-scoped caching
rule Component 1 corrects for `own/1` — `fixity(M)` is built directly from
`own/1` calls over `use_reach(M)`, so an unconditional "keyed by module name"
persistent-term cache here would reintroduce exactly the staleness hole
Component 1 rules out, one level up: a stdlib module's `fixity(M)` may be
cached unconditionally, but a user module's must stay per-generation (or be
invalidated on recompile) so an edit to `M` itself, or to any module in
`use_reach(M)`, is observed. Cycles need no special handling beyond
reachability (union is idempotent).

**Precondition this depends on, not yet true today:** `DepGraph.scan_file/1`
currently discovers a file's `use` edges, `@prelude` flag, and module identity
by calling `Cure.Compiler.parse_source/2`, which fails the *entire* file
(`parse_error: e`, `module: nil`, `order_deps: []`, `closure_deps: []` —
dropped from the `modules` map entirely, so nothing that `use`s it can even
resolve the name) whenever `Parser.parse/2` records *any* error, including one
`synchronize_to_statement` already recovered from. That all-or-nothing
contract is harmless under today's model — every legal operator is either
built-in or declared by the module itself, both resolvable in a standalone
parse — but it is exactly wrong for the case this feature legalizes: a module
`B` that `use`s `A` and writes an expression using an operator only `A`
declares. A standalone, table-naive parse of `B` (which is what
`DepGraph.scan_file` performs — it has no access to `fixity(B)`, since
computing that is the whole point) will produce a genuine parse error on that
expression, and `B` — including its own textually-earlier `use A` edge —
vanishes from the graph, corrupting `use_reach`/`prelude_providers` for every
module that (transitively) depends on it. `DepGraph.scan_file`'s
`use`/`@prelude`/module-identity extraction must therefore be hardened to the
same statement-level-recovery tolerance `own/1` (Component 1) relies on —
e.g. by driving it off the same harvest pass directly, rather than requiring
`parse_source`'s `{:ok, ast}` — before the CLI/`Cure.Project` compile-order
scan, and the *prelude-provider* discovery it performs (Component 2), can be
trusted for any program that actually exercises `use`-propagated fixity. This
is in scope for this change, not a pre-existing concern to defer: although
`use_reach(M)` itself resolves modules on demand rather than through
`DepGraph.scan_file` (Component 2), a file this bug drops from `DepGraph`'s
`modules` map is a file the CLI/`Cure.Project` driver never compiles at all
(they iterate `DepGraph.order/1`'s output), and a dropped `@prelude` provider
is one `prelude_providers` silently loses — both real regressions a
`use`-propagated-fixity program can now trigger.

### 3. Parser hook

When the parser begins module `M`:

1. **Scan** `M`'s own `use` declarations, wherever they occur in the file —
   `use` is not restricted to a leading "header" region of a module, so this
   is the same whole-file, harvest-style collection `own/1` performs for
   fixity nodes (and what `DepGraph.collect_uses/1` already does today via a
   full-AST walk), not a scan that stops after some leading prefix.
2. **Assemble** `fixity(M)` via the resolver. A conflict here (Component 5) is
   a **hard, whole-module** parse error, raised before step 3 begins — unlike
   the per-statement `synchronize_to_statement` recovery Components 1–2 rely
   on to extract declarations past a misparsing body, a conflicting-fixity
   declaration is not something later statements can be parsed around, since
   every subsequent statement in `M` would need to pick one of the two
   groups to even attempt parsing. This does not violate the Global
   Constraint that fixity extraction "must never fail because that module's
   function bodies fail to parse" — a conflict is a defect in the
   *declarations themselves* (assembled before any body is parsed), not a
   body-parse failure.
3. **Body parse** the rest of `M` seeded with `fixity(M)`.

`BuiltinFixity` degenerates to "the third term of the `fixity(M)` formula" —
`own/1` unioned over the transitive `use`-closure of `prelude_providers` (not
just the providers' own declarations; see "The unified model") — providing
the bootstrap table for the use-scan/expression-free cases and for a
single-file parse with no surrounding source universe (see Edge cases).

### 4. `@prelude` on the operators module

Mark `Std.Operators` `@prelude` so it enters `prelude_providers`. This is the
change that keeps the core operators ambient under the new model — via the
general union, not a special case.

### 5. Conflict detection replaces `check_no_builtin_rebind`

While assembling `fixity(M)`, if two declarations bind the same lexeme (same
fixity slot — infix/prefix/postfix) to **different** groups, that is a hard
error naming the conflicting lexeme (and, where available, the contributing
modules). Consequences:

- A prelude operator sits in every table, so redeclaring `+`'s group always
  conflicts → rejected everywhere (recovers today's behavior with no list).
- Two `use`d modules declaring `<?>` with different precedence conflict *in the
  importer* → rejected there (Haskell's "conflicting fixity" semantics).
- An **identical** redeclaration (same group) is a silent no-op, not an error.
- `Std.Operators` declaring its own operators is not a conflict (sole source).
- A `precedencegroup` **name** is not module-scoped, and `FixityTable.add_group/3`
  registers by name with last-write-wins (`Map.put`) — no conflict signal
  today. The same rule applies one level down from operators: if two
  declarations reaching `fixity(M)` — `M`'s own and/or any drawn from
  `use_reach(M)` — declare a `precedencegroup` of the same name with a
  **different** body (`assoc`/`higher_than`/`lower_than`), that is the same
  class of conflict as a same-lexeme/different-group operator redeclaration
  (which likewise is not restricted to two *used* modules — see the opening
  paragraph above) and must be rejected the same way; an identical body is a
  no-op. Before
  this change a group-name collision could not arise (a module's table was
  built from the built-in groups plus only its own declarations); the
  transitive union this design introduces is what first makes it reachable,
  so it is in scope here, not a pre-existing gap deferred to later work.

Error tag: keep `:builtin_operator_not_overloadable`? No — generalize to a new
tag `:conflicting_operator_fixity` carrying `{lexeme, group_a, group_b}`.
`operator_flip_test.exs` asserts this old tag at **three** call sites, all of
which move to the new tag (and, since the conflict is now raised during parse
rather than `Cure.Elab.Program.elaborate/1`'s declaration check, the assertion
shape each test uses to observe it): "rebinding a builtin syntactic operator
is rejected" (`|>`), "redeclaring the fixity of any stdlib operator is
rejected by location" (`+`), and "redeclaring the Melquiades envelope operator
is rejected" (`✉`) — the third is not a Unicode-specific edge case, just
another instance of the same lexeme-conflict path, but the harness pins on
`:builtin_operator_not_overloadable` no less than the other two, so it breaks
identically once `check_no_builtin_rebind` is deleted (Migration) and must be
updated alongside them, not just the first. The group-name conflict above
gets its own tag, `:conflicting_precedence_group`, carrying
`{name, body_a, body_b}` — it is not folded into
`:conflicting_operator_fixity`, since the payload shape differs (a group body
vs. two group *names*) and the offending declaration is a `precedencegroup`
node, not a `fixity` node.

## Overloading vs fixity (explicit)

Fixity attaches to the operator **symbol**, not to any typed overload. Defining
additional `fn <op>(...)` implementations of different types is overloading; it
carries no fixity declaration and can never conflict. All overloads of a symbol
share the single declared precedence. This matches both Haskell and Swift and is
why the conflict check keys on fixity *declarations* only, never on function
definitions.

## Decisions (locked)

1. **Transitivity** — full transitive `use`-closure. Over-approximating fixity
   is safe: extra entries only shape parse trees; an operator not semantically
   imported is still rejected at elaboration (`no_operator_meaning`).
2. **Cycles** — merged by union via reachability; no strict topo order needed.
3. **One fixity per lexeme per slot** — within a single fixity slot
   (infix/prefix/postfix — see Component 5), different-group redeclaration of
   the same lexeme is a hard error; identical redeclaration is a no-op;
   function overloads never conflict and share the precedence. The same
   lexeme may carry independent fixities in *different* slots without
   conflict (e.g. `-` as both `prefix` and `infix`, for unary and binary
   minus) — this decision does not collapse the three slots into one
   namespace.

## Edge cases

- **Single-file parse, no source universe** (e.g. an isolated parser test):
  `use_reach` resolves only the modules whose sources are locatable; unresolved
  `use` targets contribute nothing (as today). "`own(M)` is always available" is
  trivially true (`M` is the file being parsed). "Prelude providers are always
  available" is true only for the *compiler-bundled* set (`Std.Operators` and
  any other stdlib module marked `@prelude`), because those are located via a
  fixed Elixir-compile-time path (`BuiltinFixity`'s `@stdlib_source_dir`),
  independent of the project's source universe — exactly like today. Nothing
  in this design restricts `@prelude` to stdlib-owned modules (Component 4
  reuses the existing, already-general decorator); a *user* module marked
  `@prelude` is only discoverable by scanning the project's source universe
  (`DepGraph`'s `prelude_provider?` detection), so in a genuinely
  universe-free single-file parse a user `@prelude` module's operators do
  *not* bind, unlike the compiler-bundled ones. This preserves current
  single-file behavior for the compiler-bundled prelude only.
- **Operator present, its group absent** (an imported operator whose group's
  module was not reached): the lexeme is unranked/incomparable, the existing
  `incomparable?` path applies. This is reachable, not merely a defensive
  corner case: nothing in this design (or today's `check_no_precedence_cycle`,
  which already tolerates `higher_than`/`lower_than` references to undeclared
  group names as bare leaf nodes) requires a module's `infix ... : Group`
  declaration to be backed by a `precedencegroup Group` that the *importer*
  transitively reaches. Full transitive closure guarantees that whenever an
  operator's declaring module is reached, so is *that module's own*
  `precedencegroup` for it — it does not guarantee every group name any
  reached module happens to reference (e.g. in a stray `higher_than`) is
  itself resolvable. The parser degrades gracefully (`incomparable?`) either
  way rather than crashing.
- **Prelude bootstrap, generalized beyond `Std.Operators`**: Component 3's
  "degenerates to" note redefines `BuiltinFixity` as the third term of the
  `fixity(M)` formula — `own/1` unioned over the transitive `use`-closure of
  `prelude_providers` (`use_reach(P) ∪ {P}` for each `P`, per "The unified
  model" correction), not merely `own/1` applied to the providers themselves.
  That makes computing `own(X)` for *any* `X` in that closure self-referential
  on its face: the harvest pass for `X` (Component 1) is seeded with
  `BuiltinFixity.table()`, which is itself defined in terms of `own(X)`
  whenever `X` is in the closure being computed. Today this is a non-issue
  only because there is exactly one prelude provider (`Std.Operators`) that
  declares no `use` of its own, so the closure is the single file
  `operators.cure`, and `BuiltinFixity.compute` breaks that one-file cycle
  with a re-entrancy guard (`Process.put(:cure_building_fixity_table, true)`)
  seeding an *empty* table. The same guard generalizes to the whole closure:
  while `own(X)` is being computed for any `X` currently in progress
  (whether `X` is a prelude provider itself or a module reached through one),
  seed the harvest pass with an empty (or partial/stale) table rather than
  recursing into `BuiltinFixity.table()`. This is safe by the exact
  table-independence property Component 1 already relies on — the seed table
  only shapes how `X`'s *expression bodies* parse (via
  `synchronize_to_statement` recovery), never whether `X`'s own
  `{:fixity, ...}`/`{:precedencegroup, ...}` declaration nodes are extracted,
  since declaration parsing never consults the table. `own(Std.Operators)`
  scanning `operators.cure` with an empty table, exactly as
  `BuiltinFixity.compute` does today, is the special case of this general
  rule where the closure happens to be the single sole-provider file.

## Migration

- `BuiltinFixity.table/0` itself is reimplemented, not left as today's
  single-file `operators.cure` parse: it becomes the third term of the
  `fixity(M)` formula (Component 3's "degenerates to" note; the bootstrap
  re-entrancy guard generalized in the Edge Cases "Prelude bootstrap"
  discussion) — `own/1` unioned over the transitive `use`-closure of
  `prelude_providers`. This is the most central migration step of this
  change (every other component reads `BuiltinFixity.table()` as its
  fallback/bootstrap seed) and is called out explicitly here so it is not
  left implicit in the components/edge-cases prose above. `table/0`'s own
  `:persistent_term` memoization — today unconditional, with no
  invalidation, on the stated premise that "the stdlib is fixed for a
  compiler build" — is a third sibling of the caching claim Component 1
  corrects and Component 2 repeats: that premise holds only while
  `prelude_providers` is stdlib-only, but the Edge Cases "Prelude bootstrap"
  discussion is explicit that a *user* module can be `@prelude`, so once one
  exists, `table/0` is unioning `own/1` over a closure that can include user
  source. `table/0` must carry the same provenance-scoped caching rule
  Components 1–2 use, not keep the old unconditional cache — otherwise
  editing a user `@prelude` module (or anything in its `use`-closure)
  mid-session leaves every other module's bootstrap seed silently stale.
- **Revert the half-built whole-stdlib scan.** The uncommitted plan to make
  `BuiltinFixity.table()` scan every `lib/std/*.cure` is wrong under this model
  (it would make stdlib operators ambient regardless of `use`) and is dropped.
  The already-committed augmented-assignment removal and `builtin`-keyword
  retirement stay.
- `FixityTable.declares?/2` (added in the retirement commit) is retained; the
  resolver and conflict check use it plus per-slot group lookups.
- `@prelude` is added to `lib/std/operators.cure`.
- `cli.ex`/`project.ex` already run `DepGraph.scan(files)` to compute compile
  *order*, discarding the resulting graph once `order/1` is called
  (`compile_one`/`compile_all_files` then call `Cure.Compiler.compile_file`
  per path with no graph in scope). They must additionally extract that
  scan's `prelude_provider?` modules and thread them into each subsequent
  `compile_file`/`Parser.parse` call (as a new option), or a *user*-declared
  `@prelude` module (Edge cases) never actually reaches other files' tables —
  the compiler-bundled prelude works either way (Component 1's fixed
  `@stdlib_source_dir` path), so this gap would stay invisible until a
  project actually adds a user `@prelude` module.
- `Cure.Elab.Program.check_no_precedence_cycle/1` currently assembles its
  table as `BuiltinFixity.extend(BuiltinFixity.table(), ast)` — built-in plus
  the module's own declarations only, a sibling of `check_no_builtin_rebind`
  that the conflict-detection section above does not mention. It must be
  repointed at `fixity(M)` so a precedence cycle closed through a `use`d
  module's group (neither built-in nor local to `M`) is still caught; left
  as-is it silently stops covering exactly the new source of precedence
  groups this change introduces.
- `Cure.Compiler.Printer` defaults to `BuiltinFixity.table()`
  (`printer.ex:63`, `:1706`) whenever no `:fixity` option is supplied. Any
  caller reprinting a module that uses a `use`-propagated operator must
  thread `fixity(M)` through that option, or the operator silently degrades
  to `:unknown` precedence in the printed output.
- `check_no_builtin_rebind/1`'s call site in `Cure.Elab.Program.check_declarations/1`
  is **deleted, not repointed** — unlike `check_no_precedence_cycle/1` above.
  These two existing checks are structurally similar (both elaboration-time
  functions in `program.ex` operating on a `BuiltinFixity.extend`-built
  table) but this design treats them differently, for a reason the two
  Migration bullets should not leave implicit: a same-lexeme different-group
  conflict (Component 5) must be resolved *before* `fixity(M)` is even usable
  to parse `M`'s body — so it is raised at parse time, during table assembly
  itself (Component 2/3), not deferred to elaboration. A precedence-group
  cycle, by contrast, does not block table assembly — the table degrades
  gracefully (`incomparable?`, per the "operator present, its group absent"
  edge case) — so `check_no_precedence_cycle` stays a separate elaboration-time
  well-formedness pass and is merely repointed at `fixity(M)`. Component 5's
  conflict error therefore has no elaboration-time counterpart left to keep in
  sync.

## Testing

- **Scanner**: `own/1` extracts fixity decls from a module whose function bodies
  reference not-yet-known operators without failing.
- **Propagation**: user module `A` declares `infix <?> : G`; module `B` that
  `use A` parses `x <?> y` with `<?>`'s precedence; a module that does **not**
  `use A` fails to parse `x <?> y` as an operator (or elaborates to
  `no_operator_meaning`, per how an unknown infix lexeme is handled).
- **Transitivity**: `A` declares, `B use A`, `C use B` — `C` sees `<?>`.
- **Conflict**: `use`-ing two modules that declare `<?>` in different groups is
  rejected in the importer with `:conflicting_operator_fixity`.
- **Transitive conflict**: the conflict is not limited to direct siblings —
  `C use B1` (`B1 use D1`, `D1` declares `<?> : G1`) and `C use B2` (`B2 use
  D2`, `D2` declares `<?> : G2`) is rejected in `C` even though `B1`/`B2`/`D1`/
  `D2` never directly `use` each other, proving the conflict check operates
  over the full transitive union (Decision 1), not just `M`'s direct `use`
  list.
- **Group-name conflict**: `use`-ing two modules that each declare a
  `precedencegroup` of the *same name* with different `higher_than`/`assoc`
  bodies is rejected in the importer with `:conflicting_precedence_group`,
  proving the conflict rule (Component 5) covers group identity, not just
  operator lexemes.
- **DepGraph resilience**: `DepGraph.scan(["B.cure", "A.cure"])` where `A`
  declares `infix <?> : G` and `B` (`use A`) writes `x <?> y` in a function
  body still records `B`'s module identity, its `use A` order-edge, and any
  `@prelude` flag — proving `DepGraph.scan_file` no longer treats `B`'s
  not-yet-resolvable operator as a whole-file parse failure (the Component 2
  precondition).
- **Cross-module precedence cycle**: `A` declares `precedencegroup Ga
  higher_than: [Gb]`; a `use A` module `B` declares `precedencegroup Gb
  higher_than: [Ga]` — rejected by `check_no_precedence_cycle` operating on
  `fixity(B)`, proving that check was repointed off the builtin+own(M)-only
  table it uses today.
- **Prelude provider's own use-closure propagates**: a prelude provider `P`
  (marked `@prelude`) that itself `use`s a module `H` declaring `infix <?> :
  G` makes `<?>` available in a module `M` that neither `use`s `P` nor `H`
  directly — proving the third term of the `fixity(M)` formula closes over
  `use_reach(P)`, not just `own(P)` (the "unified model" correction).
- **Prelude still protected**: redeclaring `+`/`|>` group in any user module is
  rejected (now as a conflict).
- **Overload is not a conflict**: adding `fn <?>` of a second type alongside an
  existing declaration parses and elaborates.
- **Idempotent redeclare**: declaring `<?>` with the same group as an imported
  declaration is accepted.
- **Single-file fallback**: parsing an isolated single-file module (no
  surrounding source universe / no `DepGraph` scan) still binds core/prelude
  operators (`+`, `|>`, …) via `own(M)` plus the compiler-bundled prelude set.
- **User `@prelude` reaches sibling files via the driver**: a small project
  compiled through `cli.ex`/`Cure.Project` (not a bare single-file
  `Parser.parse`) containing a user module `P` marked `@prelude` that declares
  `infix <?> : G`, and a sibling module `M` with no `use P`, parses `x <?> y`
  in `M` — proving the `prelude_provider?` threading Migration adds to
  `compile_one`/`compile_all_files` actually reaches `Parser.parse`, not just
  the compiler-bundled prelude the single-file fallback test above covers.
- **Group-absent degrade**: a reached module's operator is present while its
  declared group is not (e.g. its `infix` references a group name the
  importer never separately reaches) — parses as `incomparable?` rather than
  crashing, per the hardened "Operator present, its group absent" edge case.
- Full `mix test` gate green.

## Rollback

The change is confined to the parser/elaboration layer, plus the thin
driver-level plumbing Migration calls out in `cli.ex`/`project.ex`/`Printer`
that carries a `fixity(M)`/`prelude_provider?` value between them — no new
persistent state or on-disk format. Reverting the fixity resolver + parser
hook + `@prelude` marker + conflict check + the `DepGraph.scan_file`
misparse-tolerance hardening (Component 2's precondition) + the
`cli.ex`/`project.ex` `prelude_provider?` threading (Migration) restores the
location-based rule and today's all-or-nothing `DepGraph` parse contract. No
TCB or on-disk-format changes to reverse.

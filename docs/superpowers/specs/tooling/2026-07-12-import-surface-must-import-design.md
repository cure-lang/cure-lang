# Import Surface & Must-Import Semantics — Design (PARTIALLY LANDED / PARKED)

> **Status.** The model is settled and two mechanics are **landed green**
> (`d65cf2f`): brace grouping and direct-owner-wins. The remaining surface —
> `exposing (…)`, the "did you mean to expose this?" diagnostic, and
> last-segment qualifiers — is **designed here and PARKED** (not scheduled).
> Operator settled the model 2026-07-12 by comparing to Swift/Elm/Haskell/Idris.
>
> Sibling spec: [`2026-07-12-user-module-import-resolution-design.md`](2026-07-12-user-module-import-resolution-design.md)
> covers cross-module *resolution* of `use`d **user** modules (Failure C). This
> spec covers the import **surface syntax and name-visibility semantics**; the
> two are complementary and share the `Env.import_modules` machinery.

## 1. The model: must-import

A name from module `M` is referenceable only after `use M`. There is **no
globally-addressable qualified access** — you cannot write `Std.String.length`
without importing `Std.String`, even though the BEAM substrate would make it
"free." This matches **all four** reference languages the operator chose as the
yardstick — Swift, Elm, Haskell, Idris — none of which allow a qualified
reference to an un-imported module. Only Elixir/Rust are globally-addressable,
and we deliberately do **not** follow them.

Rationale for must-import over globally-addressable: it is more explicit (naming
a module never spookily pulls it into the env/build), it matches the typed-FP
tradition, and it avoids the invasive "load-and-re-key a module on qualified
mention" machinery.

## 2. Consumer-side surface (what you write to import)

Keyword stays `use`. The complete set of forms:

```cure
use Std.List                         -- import all of List's own names, unqualified
use Std.List exposing (map, filter)  -- import ONLY these names, unqualified
use Std.{List, Core}                 -- grouping sugar: one full `use` per element
```

- **No `as`** and **no qualified-only import mode.** Operator decision: allowing
  qualified/aliased imports "creates code that's much harder to read between
  different people based on preferences." One canonical way to reach a name.
- **Author-side visibility already exists** via the `local` keyword (marks a
  top-level item module-private). Do **not** rebuild it. The consumer-side
  `exposing` here is naturally bounded by it — you can only expose what the
  author did not mark `local`.

### 2.1 `exposing` is Elm-style (unlisted names stay qualified-reachable)

`use M exposing (a, b)` brings **only** `a`, `b` into unqualified scope. Every
other name of `M` is **still reachable qualified** (`M.other` / full path) —
the list governs the unqualified *shortcut*, not membership. This is Elm's
model, chosen over Haskell's "unlisted names are entirely gone."

Consequences, by situation:

1. **Calling an exposed function whose signature mentions an unexposed type —
   no friction.** The whole module slice is still merged into the importer's
   env; `exposing` only filters which names get a bare key. So an exposed
   `map`'s reference to an unexposed `List` resolves by its (qualified) key with
   no help from the caller. **You need nothing extra to call the function.**
2. **Writing an unexposed type name in your own source** — reachable via the
   qualified escape hatch (`M.T`) or by adding it to the list. Never blocked,
   worst case verbose.
3. **Destructuring an unexposed ADT a function returns** — the one real friction
   point: pattern-matching needs the constructors, and a qualified constructor
   in a pattern is awkward. Fix: expose them (see §2.2). This is the *good* kind
   of friction — constructor visibility is pay-for-what-you-use.

### 2.2 Constructors follow the type; `(..)` is the opt-in

A constructor is just another name: if it is not in the `exposing` list it stays
qualified-only and never enters unqualified scope. Exposing a **type name alone
does not** drag its constructors in. Three item shapes the parser must accept:

```cure
use Std.Vector exposing (map)          -- plain name; NO constructors
use Std.Vector exposing (Vector(..))   -- the type AND all its constructors
use Std.Vector exposing (VCons, VNil)  -- specific bare constructor names
```

**This is the headline benefit.** It makes constructor collisions
opt-in-avoidable without renaming:

```cure
use Std.List   exposing (cons, map)   -- List's `cons` earns the bare spelling
use Std.Vector exposing (map)          -- Vector's cons stays Vector.cons

fn f() = cons(1, empty)               -- ✅ unambiguously List's cons
fn g() = Vector.cons(1, vempty)       -- Vector's cons, qualified, no clash
```

No `vcons`. You pick which `cons` is bare by what you expose; the other stays
qualified. (Note: even without `exposing`, the collision machinery already
prevents a *silent* clash — it re-keys both and makes bare `cons` an
`ambiguous_name` error, forcing qualification. So renaming was never strictly
required; `exposing` upgrades the outcome from "neither is bare, qualify both"
to "one is bare, the other qualified.")

### 2.3 The "did you mean to expose this?" diagnostic (no auto-import)

When an **unqualified** name is unresolved but **is** provided by an
already-imported module the consumer did not expose, emit a targeted error
rather than failing generically or auto-importing:

```
error: `Ok` is not in scope
  `Ok` is a constructor of `Std.Result`, which `Std.Parse` re-exports but you
  did not expose.
  fix: add it to the import — `use Std.Parse exposing (parse, Result(..))`
```

**Auto-importing the mentioned type is explicitly rejected:** "the mentioned
type" is not one type (`parse : String -> Result(Map(K, List(V)), E)` would pull
in a crowd), it can silently introduce `ambiguous_name` collisions the user
never wrote, it undoes the "one explicit way" property, and none of the four
reference languages do it. The diagnostic is cheaper, teaches, and leaves the
namespace under the user's control. It is easy to compute — on an unresolved
bare name, consult `Env.import_modules` + each module's owned/re-exported names
for a provider and suggest it (with `Type(..)` when the name is a constructor).

## 3. Qualifier resolution: last segment OR full path — nothing partial

A module has **exactly two** qualifiers: its **last path segment** and its
**full path**. No intermediate suffixes.

```cure
-- module is Std.Signal.Graph.Flow, `Flow` is the MODULE (not a nested type)
connect(g)                          -- ✅ unqualified (in scope, no collision)
Flow.connect(g)                     -- ✅ last segment  (canonical short qualifier)
Std.Signal.Graph.Flow.connect(g)    -- ✅ full path      (unambiguous fallback)
Graph.Flow.connect(g)               -- ❌ partial suffix — NOT a qualifier
Signal.Graph.Flow.connect(g)        -- ❌ partial suffix — NOT a qualifier
```

Why last-segment-or-full and nothing between: partial suffixes are neither the
name nor the address — a middle ground that multiplies spellings for one call,
the exact preference-divergence `as` was dropped to avoid. The short name is
*derived* (the last segment), not a user-chosen alias, so two people writing
`Flow.connect` always mean the same module — consistent with rejecting `as`.

**Collision consequence follows naturally.** If both `Std.Signal.Graph.Flow`
and `Std.Data.Flow` are imported and both provide `connect`, then `Flow.connect`
is ambiguous, and the **only** disambiguator is the full path
(`Std.Signal.Graph.Flow.connect` vs `Std.Data.Flow.connect`) — because
`Graph.Flow`/`Data.Flow` do not exist as qualifiers. Short-or-full, never
partial. Resolver stays trivial: a qualifier `Q.name` matches an imported module
iff `Q` equals its **full id** or its **last segment** — no suffix search.

**Parser/type coexistence.** A type named `Flow` and last-segment qualifier
`Flow` for module `…Flow` coexist: bare `Flow` (no trailing member) is the type;
`Flow.connect` (trailing `.member`) is qualified module access. The parser
already splits on exactly that — a trailing `.name` marks qualified access.

## 4. What is LANDED (`d65cf2f`, branch `autopilot/kernel-parity-batch`)

Fixed ImportTest Failures A + B. See memory `import-machinery-must-import-landed`.

- **Grouping.** `imports/1` (`lib/cure/elab/program.ex`) expands `:items` →
  one `source.item` per brace element (was reading only `:source`).
- **Direct-owner-wins.** A directly-imported module's OWN name wins the
  unqualified spelling over a name reachable only via another module's
  **transitive re-export** (`use Std.List` + `use Std.Core` → bare `map` is
  Std.List's own, not the Std.Option `map` Core re-exports). Mechanism: inert
  `Env.import_modules` (MapSet of direct-import module-ids = explicit `use` +
  auto-prelude), set by `shadow_resolved_imports`, unioned by `merge_env`, added
  to `@merged_env_keys`. `Resolution.prefer_direct/2` restricts
  `resolve_bare_shadowed`/`ambiguous_modules` to direct owners when any match is
  direct. The kernel never reads the field.
- ImportMixed's qualified `Std.String.length` now imports `Std.String`
  (must-import) and resolves via the re-keyed collision key.

### Landed-work TRAP (do not repeat)

Do **not** gate `resolve_qualified(:value)`'s bare fallback on `import_modules`.
It was tried and regressed 4 tests (ResolutionTest's synthetic env has no
import_modules; all 3 Std.Functor HKT cross-module tests hit `:unknown_global`)
because that fallback serves instance-delegate resolution where the set isn't
reliably populated. The latent soundness gap (`Std.String.length` with only
`Std.List` imported bare-falls-back to List.length) stays reach-pinned; a proper
fix needs `import_modules` populated in every resolve_qualified context.

## 5. What is PARKED (this spec's build queue)

1. **`exposing (…)` parser** — contextual `exposing` keyword after the module
   path → `:exposing` meta. Three item shapes: plain name, `Type(..)`, bare
   constructor. (`use M.{…}` grouping stays `:items`; the two are distinct.)
2. **`exposing` semantics** — non-exposed owned names of an exposing-filtered
   module get their qualified-only (`Mod#name`) key, keeping bare keys only for
   listed names (+ constructors when `(..)`/listed). Reuses `rekey_module_env`.
   Requires threading per-source exposing lists (today `imports/1` returns a
   flat source list, dropping exposing info).
3. **"did you mean to expose this?" diagnostic** (§2.3).
4. **Last-segment qualifier resolution** (§3) — `resolve_qualified` matches full
   id **or** last segment of an imported module; ambiguous last segment → error
   pointing at the full paths.

## 6. Parked variant (not adopted)

An explicit `unqualified Std.Signal.Graph.Flow` keyword (Rust/Java-style leaf
binding, canonical last-segment name) was discussed as a **robustness** variant
of §3: it pins the short name's meaning at the import line, so a later
`use …Data.Flow` cannot retroactively make an existing `Flow.connect` ambiguous.
**Not adopted** — automatic last-segment qualifiers are lower-ceremony and the
fragility is a clear compile error, not silent breakage. If deep namespaces
(`Std.Signal.Graph.*`) proliferate and one-name-per-line imports feel heavy,
revisit it as a deliberate opt-in — with the canonical last-segment rule, never
arbitrary aliases.

# Forced disambiguation of ambiguous bare names (`Self.S` / `Nat.S`) — design

Status: SPEC (not implemented)
Date: 2026-07-10
Supersedes part of: [`2026-07-04-local-type-shadowing-design.md`](2026-07-04-local-type-shadowing-design.md) (R1, and its "qualifying defs" non-goal)
Depends on: [`2026-07-09-migration-facility-design.md`](2026-07-09-migration-facility-design.md) (rule registry, warn-now → error-later policy)

## 1. Problem

Today, when a module declares a name that a `use`d module also provides, the
local declaration **silently wins**. From `lib/cure/elab/resolution.ex` and the
R1 requirement of the shadowing spec:

```cure
mod Demo
  use Std.Nat            # brings Nat, Z, S

  type Peano = Z | S(Peano)

  fn f(p: Peano) -> Peano = S(p)   # which S? silently: the local one.
```

Bare `S` resolves to the local constructor with no diagnostic. The imported
`Std.Nat.S` is still reachable, but only as `Std.Nat.S`. The reader of `f` has
no way to know, from the body alone, which `S` is meant — they must scan the
module header, the local declarations, and know the precedence rule.

This is a *silent-precedence* footgun. The precedence rule ("local beats
import") is invisible at the use site, and it is the one place where Cure
resolves an ambiguity by fiat rather than by asking.

Note the asymmetry that already exists: **import-vs-import** ambiguity is
already a hard error (R7 / `Resolution.ambiguous_modules/2`). Only
**local-vs-import** silently resolves. The rule is not uniform.

### 1.1 What we want instead

A bare name with ≥2 distinct in-scope meanings is **ambiguous, and the compiler
says so**. The author qualifies:

- `Self.S` — the constructor this module declares.
- `Nat.S` — the one imported from `Std.Nat`.

## 2. Prior art (checked, not recalled)

| Language | Local top-level decl vs. import | Escape hatch |
|---|---|---|
| **Haskell (GHC)** | `Ambiguous occurrence 'S'` — a hard **error at the use site**. Applies to the implicit `Prelude` too. | `M.S` (module's own name), `Data.Nat.S`, or `import … hiding (S)` |
| **Rust** | Error `E0255`: a definition clashing with an import in the same namespace | `Self::S`, `crate::S`, `use … as` |
| **Elixir** (host) | Local def wins over `import` silently; two `import`s clashing is an error | full `Mod.fun()` |
| **Agda** | Ambiguous-name error — *except constructors*, which are disambiguated by expected type | qualified name, `renaming` |
| **Idris 2** | Ambiguity is resolved **by type** (try each candidate, error iff ≠1 elaborates) | `%hide`, qualified name |
| **Lean 4** | Tries each interpretation; error iff ≠1 elaborates | `_root_.S`, `open … hiding` |
| **OCaml / SML** | Last binding silently wins | — |

Two coherent designs exist:

- **(A) Syntactic ambiguity ⇒ qualify.** Haskell, Rust. Predictable, cheap,
  gives exact errors.
- **(B) Type-directed disambiguation.** Agda (constructors), Idris 2, Lean 4.
  Ergonomic, but needs *backtracking elaboration*; it is a well-known source of
  slow compiles and inscrutable "ambiguous elaboration" errors in Idris.

**Cure has already ruled out (B)**: the shadowing spec's §7 non-goals say
"Agda-style ambiguous-constructor type-directed disambiguation … Constructors
remain a one-name→one-family map per resolution scope; ambiguity is an error."
Cure's elaborator is bidirectional and does not backtrack. So (A) is the only
design consistent with the locked decisions, and it is what this spec adopts.

**Forward-compatibility argument.** A program that qualifies its ambiguous names
is valid under *both* (A) and (B). So adopting (A) now forecloses nothing: if
Cure ever grows type-directed disambiguation, the error of R8 simply softens
into "error only when type-directed resolution yields ≠1 candidate", and every
already-migrated program keeps compiling unchanged. Qualification is a monotone
move.

## 3. Decision

Generalize R7 (import-vs-import ⇒ error) to cover local-vs-import, making the
rule uniform:

> **A bare name that has ≥2 distinct in-scope meanings must be qualified.**

There is no longer an implicit "local wins" precedence. `Self.` names the
current module.

## 4. Requirements (continuing the shadowing spec's numbering)

R8. **Uniform ambiguity rule.** A bare name `N` used in type, expression, or
    pattern position is *ambiguous* when the in-scope environment offers ≥2
    **distinct** entities under `N` — whether they come from (local decl +
    import), (import + import), or (local decl + ≥1 imports). Ambiguity is
    computed **per namespace** (family / constructor / def) and **per name**,
    exactly as the existing re-key machinery already does: a local `type Nat =
    Zero | Suc` makes `Nat` ambiguous but leaves `Z`/`S` unambiguous (R2 is
    preserved).

    *"Distinct" excludes the same entity reached twice* — a re-export, an alias,
    or the same module `use`d twice is not ambiguity (this is R7's existing
    carve-out, unchanged).

R9. **`Self.` qualifier.** `Self.N` resolves to the entity named `N` **declared
    by the current module**, and to nothing else. If the current module declares
    no `N`, `Self.N` is an error — it never falls back to an import. The
    module's own name (`Demo.N`) is accepted as an equivalent spelling.

R10. **Lazy diagnosis, at the use site.** *Declaring* a colliding name is silent
    and legal. The diagnostic fires only where a **bare** ambiguous name is
    *used*. A module may shadow `Nat` and never mention bare `Nat`; that must
    compile clean. (Haskell's rule. Eager, declaration-site diagnosis would
    punish the overwhelmingly common "I import a big module and redefine one
    name I never use ambiguously" case.)

R11. **Lexical binders are untouched.** Function parameters, `let` bindings,
    pattern variables, and type-parameter binders shadow *silently*, as in every
    language in the table above. This spec governs **module-scope** names only.
    `fn f(nat: Nat) -> …` does not warn. R11 is the load-bearing scope limit:
    without it, this rule would fire on every program ever written.

R12. **Staged rollout (warn now, error later).** Ambiguous bare use is:
    - **Phase 1** — a warning, `W089`, and resolves **exactly as today**
      (local declaration wins; import-vs-import stays the existing hard error).
      Phase 1 is therefore *strictly additive*: no currently-green program
      changes meaning or stops compiling.
    - **Phase 2** — an error, under `--strict` and then by default at the next
      edition boundary, per the migration facility's per-rule maturity policy.

R13. **Mechanical, semantics-preserving migration.** Because Phase 1 resolves
    ambiguity deterministically, `cure migrate` can rewrite every bare ambiguous
    name to *the qualified form it already resolves to* — bare `S` → `Self.S`
    when the local wins, `Nat.S` when the (unique) import wins. This rewrite
    **cannot change program meaning**. That property is what makes Phase 2 safe.

R14. **No runtime, no TCB, no codegen change.** Runtime constructor tags stay
    bare (the AtomVM invariant, shadowing spec §3.5). This is a surface-syntax
    and E-layer-resolution change only. `lib/cure/core/*` is untouched.

## 5. Prerequisites (P0)

**Two independent bugs. Both must land before R8, or the escape hatch this spec
forces people onto does not exist — and, worse, silently lies.** Found by source
read on 2026-07-10; P0.2 was corroborated by an independent audit of
`resolution.ex` the same day.

### 5.1 P0.1 — the qualifier is currently unchecked

`Resolution.resolve_qualified/3` (`lib/cure/elab/resolution.ex:209-232`) tries
the re-keyed `:"Mod#Name"` key first and then falls back to the **bare atom**:

```elixir
try_keys(env, [rekey_atom(mod, String.to_atom(last)), String.to_atom(last)], :value)
#                                                     ^^^^^^^^^^^^^^^^^^^^^ unchecked fallback
```

The fallback is load-bearing — an *unshadowed* import keeps its bare key, so
`Std.Nat.Z` must be able to reach `:Z`. But the fallback never verifies that
`mod` is the module that actually **owns** the bare name. Consequently:

```cure
use Std.Nat
fn f() -> Nat = Bogus.Module.Z    # resolves to Std.Nat.Z. No error.
```

Any module prefix whatsoever resolves an unshadowed bare name. A qualifier that
is not checked is decoration, and `Self.S` would "work" today only by this
accident — as would `Garbage.S`.

**Fix.** Gate the bare fallback on ownership. The data already exists:
`Resolution.classify/2` is handed a `family_owners` map. Extend it to defs and
constructors, persist it on the E-layer resolution table (§3.3 of the shadowing
spec — it already lives there, outside the core `Env`), and require:

- `Mod.N` → the bare key **only if** `owner(N) == Mod`; otherwise
  `{:qualifier_not_owner, Mod, N, actual_owner}`.
- `Self.N` → the bare key **only if** `N` is declared by the current module.

This is a bug fix independent of R8 and can be tested and landed first.

### 5.2 P0.2 — constructor-name collisions are never detected

**The motivating example in this spec does not work today, and fails silently.**

`Program.shadow_resolved_imports/1` computes collisions over exactly two
namespaces — family names and def names:

```elixir
%{losers: losers, ambiguous: ambiguous} = Resolution.classify(family_owners, local)
%{losers: def_losers}                   = Resolution.classify(def_owners, local_defs)
owner_mods = MapSet.union(MapSet.new(Map.keys(losers)), MapSet.new(Map.keys(def_losers)))
```

`rekey_module_env/5` is then applied only to modules in `owner_mods`. Its
`shadowed_ctor_names` argument (`local_ctors`) is therefore *only ever consulted
for a module that already lost a family-name or def-name collision*. A module
whose sole collision is a **constructor** name is never re-keyed at all.
`Resolution.ambiguous_modules/2` has the same blind spot — it scans `families`
and `defs`, never `ctors` (`resolution.ex:310`).

Consequence, for the exact case this spec exists to fix:

```cure
use Std.Nat                  # brings Nat, Z, S
type Peano = Z | S(Peano)    # family names Peano vs Nat — NO family collision
```

1. `Std.Nat` is not a loser, so it is never re-keyed. No `:"Std.Nat#S"` key is
   ever created.
2. The local declaration reaches `Inductive.declare/3`, whose `Map.put` on
   `env.ctors` **silently overwrites** the imported `S`.
3. Because of P0.1's unchecked bare fallback, `resolve_qualified(env,
   "Std.Nat.S", :value)` misses `:"Std.Nat#S"` and falls through to the bare
   `:S` — **which is now the local constructor.**

So `Nat.S` today does not merely fail to reach the import; it resolves, without
diagnostic, to the *wrong* constructor. R9's escape hatch is unimplementable
until this is fixed, and R8's warning would be actively harmful — it would tell
users to write a qualified form that silently means something else.

Note the interaction: P0.1 alone is a laxity, P0.2 alone is data loss. Composed,
they produce *silent misresolution of an explicitly qualified name*, which is
strictly worse than either. Fix both, and prefer fixing P0.2 first — with
ownership checked (P0.1), the missing `:"Std.Nat#S"` key would at least become a
loud `{:qualifier_not_owner, …}` rather than a wrong answer.

**Fix.** Extend collision classification to a third namespace. `classify/2` is
already shape-generic (it takes a `%{name => MapSet.t(owner)}` map and a local
set, and is called twice with different namespaces); pass it `ctor_owners` built
the same way `family_owners`/`def_owners` are, and union the resulting losers
into `owner_mods`. Extend `ambiguous_modules/2` to scan `ctors`. The existing
`rekey_module_env/5` already accepts `shadowed_ctor_names` and does the right
thing once its module is actually in `owner_mods` — the re-key transform itself
is not at fault and needs no change.

**Scope note.** This also fixes the import-vs-import variant (two imported
modules exporting the same constructor name from different families), which is
today an equally silent clobber and which R7 was *supposed* to have covered.

## 6. Surface syntax: `Self`

`Self` is parsed as a **contextual module qualifier**: the token `Self`
immediately followed by `.` and a name. It is *not* added to the reserved-word
set, so an existing user type named `Self` keeps working in type position, and
no migration rule is needed for the keyword itself.

**Known future interaction.** Rust and Swift use `Self` for *the implementing
type* inside a trait/protocol. Cure has `interface`/`implementation` (the Idris 2
pair), which today names the implementing type via the interface's own type
parameter, not `Self`. If Cure later wants `Self`-as-implementing-type, the two
uses are still syntactically separable (`Self.` in qualifier position vs. bare
`Self` in type position), but it is worth deciding deliberately rather than
discovering the clash. Alternatives considered and rejected:

- **Lean's `_root_.`** — names the root namespace, not the current module; wrong
  concept, and Cure's modules are flat so there is no root/current distinction
  to draw.
- **Module's own name only** (Haskell's `Demo.S`) — works, and R9 accepts it,
  but it is verbose and forces a rename cascade when a module is renamed.
  `Self.` is the shorter, rename-stable spelling. Both are supported.

## 7. Scope: which namespaces

Applies to every module-scope namespace where the re-key machinery already
operates:

- **Type constructors (families)** — yes.
- **Data constructors** — yes. This is the motivating `S` case.
- **Top-level defs (functions)** — yes. *This extends the shadowing spec's §7
  non-goal ("Qualifying `defs`… out of scope").* That non-goal was written
  before `Resolution.rekey_defs/4` and `ambiguous_modules/2` landed (the K12
  Approach-B rekey extension); the machinery now exists, and the classic
  motivating case — a local `map` against an imported `map` — is a def, not a
  type. Including defs is what makes the rule feel principled rather than
  arbitrary.
- **Interfaces** — yes, same rule, same machinery.

**Open (§11):** record field accessors.

## 8. Ergonomics: how an author silences the warning

Three ways, in order of preference:

1. **Don't import the clashing name.** Cure already has selective import:
   `use Std.Nat.{Nat}` brings the type but not `Z`/`S`. This is the right fix
   when you never wanted the imported constructors.
2. **Qualify at the use site** — `Self.S` / `Nat.S`. Right when you genuinely
   use both.
3. **Run `cure migrate`** — does (2) mechanically, everywhere (R13).

Cure has an allow-list selective import but **no `hiding` form**. `hiding` is
the more ergonomic fix when a module exports thirty names and you clash with
one. Adding `use Std.Nat hiding {S}` is a natural companion; it is **not** a
blocker for this spec (selective import covers the same ground, verbosely) and
is deferred to §11.

### 8.1 The auto-prelude

Cure has an auto-prelude (`lib/cure/stdlib/preload.ex`). If the prelude injects
names into scope, then under R8 a user defining `map` warns at every bare `map`.
That is precisely GHC's behavior with the implicit `Prelude`, and it is
considered correct there — but GHC also gives `import Prelude hiding (map)` and
`-XNoImplicitPrelude` as escapes.

**Decision:** treat the auto-prelude as an ordinary import for the purposes of
R8, *conditional on* an opt-out existing. Before Phase 2, either `hiding` (§11)
or a `no_prelude` module attribute must ship. Phase 1's warning is harmless
either way and will tell us empirically how noisy this is across the stdlib and
the test corpus — **measure this before committing to Phase 2.**

## 9. Diagnostics (W089)

The warning must be *actionable without thinking*: name every candidate, its
origin, and the exact string to paste.

```
warning: ambiguous unqualified name `S` (W089)
  ┌─ src/demo.cure:7:31
  │
7 │   fn f(p: Peano) -> Peano = S(p)
  │                             ^
  │
  = `Self.S`    constructor of `Peano`, declared at src/demo.cure:4:16
  = `Nat.S`     constructor of `Nat`, imported by `use Std.Nat` at src/demo.cure:2:3
  = resolved as `Self.S` (a local declaration currently takes precedence)
  = this becomes an error in a future release
  = fix automatically with `cure migrate`, or drop the import: `use Std.Nat.{Nat}`
```

Requirements on the diagnostic:
- **Every** candidate is listed with its origin module and declaration site.
- The **chosen** resolution is stated explicitly (Phase 1 only) — the reader must
  never have to know the precedence rule.
- The suggested fixes are *copy-pasteable strings*, not prose.

Two new diagnostics accompany P0:
- `E0xx qualifier is not the owner of this name` — `Bogus.Z` where `Z` is owned
  by `Std.Nat`. Message names the actual owner.
- `E0xx module declares no such name` — `Self.Z` where the module declares no `Z`.

W-code `W089` is the next free code (`W081`, `W082`, `W086`, `W088` are taken).

## 10. Non-goals

- **Type-directed disambiguation** (Agda/Idris/Lean). Explicitly out, per the
  shadowing spec's §7. See §2 for why adopting (A) does not foreclose it.
- **Nested module namespaces.** Cure modules are flat; `Mod#Name` handles one
  level.
- **Changing lexical shadowing.** R11.
- **Changing runtime tags or the TCB.** R14.
- **`hiding` imports.** Desirable companion; deferred (§11).

## 11. Open questions

1. **Auto-prelude noise.** Measure the W089 count across `lib/std/**` and the
   test corpus in Phase 1 before deciding whether the prelude participates in
   R8. If the count is large and mostly `Self.`-resolving, that is a signal that
   `hiding` / `no_prelude` must land first. *This is the single fact that should
   gate Phase 2.*
2. **`hiding` syntax.** `use Std.Nat hiding {S}` vs. `use Std.Nat.{Nat}` (today's
   allow-list) being deemed sufficient.
3. **Record field accessors** — are they a namespace that can collide? If
   accessors are ordinary defs, they fall out of §7 for free.
4. **`Self` as the implementing type** in a future `interface` surface (§6).
5. **Per-rule `--strict` graduation** vs. one global switch — inherited open
   question from the migration facility spec §7; W089 is a third client and a
   good forcing function for that decision.

## 12. Test strategy (TDD)

Red tests first, per the project's discipline. Layered:

**P0.1 (independent, lands first)**
- `Bogus.Z` with `use Std.Nat` ⇒ `:qualifier_not_owner`, *not* silent success.
- `Self.Z` with no local `Z` ⇒ `:no_such_local_name`.
- `Std.Nat.Z` (correct owner, unshadowed) ⇒ still resolves. **Regression guard
  for the load-bearing fallback.**

**P0.2 (independent, lands first — and before P0.1, per §5.2)**
- `use Std.Nat` + `type Peano = Z | S(Peano)` ⇒ `Nat.S` resolves to
  `Std.Nat`'s constructor, **not** the local one. *This is the test that fails
  most loudly today: it currently returns the wrong constructor with no
  diagnostic.* Assert on the resulting Core, not on `{:ok, _}`.
- Same program ⇒ the imported `S` is still present in the env under some key
  (guards against the silent `Map.put` clobber).
- Two imported modules exporting `Ok` from different families, no local
  declaration ⇒ bare `Ok` is `{:ambiguous_name, …}` (R7 was supposed to cover
  this and does not).
- A local ctor colliding with an import whose *family name also* collides ⇒
  unchanged behavior (regression guard: this is the path that works today).

**R8 / R9 (Phase 1)**
- Local ctor `S` + imported `S`, bare use ⇒ exactly one `W089`, and the program
  still elaborates to the *local* `S` (byte-identical Core to today).
- Local `Nat` + imported `Nat`, local ctors named `Zero`/`Suc`: bare `Nat` warns;
  bare `Z`/`S` do **not** (R2 preserved, per-name scoping).
- `Self.S` and `Nat.S` both elaborate, to *different* constructors. Assert the
  resulting Core differs — this is the test that proves qualification is real
  and not decoration.
- Same module `use`d twice, or re-exported ⇒ **no** warning (R8's "distinct"
  carve-out; guards against over-detection).
- Declared-but-never-bare-used collision ⇒ **no** warning (R10, laziness).
- `fn f(nat: Nat)` and `let s = …` shadowing globals ⇒ **no** warning (R11).
- Local def `map` + imported `map` ⇒ `W089` (§7, defs included).

**R6 regression (inherited)**
- Full suite green; the oracle replay green; no Core diff on any currently-green
  program. Phase 1 must be provably additive: **assert emitted Core is
  byte-identical** before/after, over the whole test corpus.

**R13**
- `cure migrate` on a W089-dirty file ⇒ zero W089 afterwards, **and** the
  post-migration Core is byte-identical to the pre-migration Core. This is the
  property that licenses Phase 2.

## 13. Risk + layer summary

- **Primary layer E** — `lib/cure/elab/resolution.ex` (ownership map, `Self`
  resolution, ambiguity set), `lib/cure/elab/elaborator.ex` +
  `lib/cure/elab/declarations.ex` (bare-name lookup consults the ambiguity set
  *before* falling through — the same anchor-point the shadowing spec §3.3 calls
  out), `lib/cure/compiler/parser.ex` (contextual `Self.` qualifier).
- **No soundness surface.** The kernel checks the same Core it always did; only
  *which* key a surface name resolves to changes, entirely before the kernel
  sees a term. A bug here yields a wrong-name error or a wrong-but-well-typed
  program — never an unsound one. (Contrast: a bug in the *ambiguity* direction
  can only make the compiler *more* conservative.)
- **Chief risk: noise.** Over-firing on the auto-prelude or on re-exports would
  make Phase 1 unusable and Phase 2 impossible. Mitigations: R8's "distinct
  entity" carve-out; R10's laziness; R11's lexical-binder exemption; and the
  §11.1 measurement gate before Phase 2.
- **Secondary risk: `Self` collision** with a future interface surface (§6) —
  cheap to avoid now, expensive later.
- **Phase 1 is reversible.** It emits a warning and changes no resolution. If
  the measurement in §11.1 says the rule is too noisy, we delete the warning and
  keep P0 (which is a straight bug fix).

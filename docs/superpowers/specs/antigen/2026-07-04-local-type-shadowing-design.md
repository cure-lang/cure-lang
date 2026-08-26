# Local type shadowing (types + constructors) with qualified escape hatch — design

**Date:** 2026-07-04
**Layer:** E (elaborator, `lib/cure/elab/*`) + a contained C-layer touch (codegen runtime tags). **Kernel/TCB (`lib/cure/core/*`) is NOT modified.**
**Status:** design approved (Approach B). This spec is the source of truth for the implementation plan.

## 1. Problem

A module may declare its own type whose name collides with an imported (or auto-imported) family. Value/function shadowing already works (local defs win, last-writer in the `defs` map). **Type + constructor shadowing does not fully work:** a local `type Nat = Zero | Suc(Nat)` shadows correctly in *declarations and signatures*, but the `match` exhaustiveness/coverage checker still resolves the scrutinee's family to the imported namesake's constructor set, producing `{:error, {:missing_branch, :S}}`.

### 1.1 Reproduction (confirmed)

```
mod ExplicitShadow
  use Std.Nat                       # imports family Nat = Z | S
  type Nat = Zero | Suc(Nat)        # local shadow
  fn add(a: Nat, b: Nat) -> Nat = match a
    Zero() -> b
    Suc(m) -> Suc(add(m, b))
end
```
`Cure.Elab.Program.elaborate/1` → `{:error, {:missing_branch, :S}}`.

The auto-prelude case (no explicit `use`) already works, because `program.ex`'s
`auto_prelude_imports/1` skips auto-importing `Std.Nat` when the module declares
its own `type Nat` (collision-avoidance keyed on `declared_type_names`). That
skip does **not** cover an explicit `use`, nor import-vs-import collisions.

### 1.2 Root cause (confirmed by source read)

The registry keys families and constructors by **bare atom**, and imports flatten
in with **zero provenance**:
- `program.ex` `import_source_env/2` elaborates each imported module's
  declarations into a fresh flat `Env` and `merge_env`s it under bare keys
  (`Std.Nat` → family `:Nat`, ctors `:Z`, `:S`).
- `Inductive.declare/3` (inductive.ex:183) does `Map.put(families, :Nat, …)` and,
  per ctor, `Map.put(ctor_to_family, cname, :Nat)`.
- `Inductive.ctors_of(env, :Nat)` (inductive.ex:275) returns **every** ctor whose
  `ctor_to_family[name] == :Nat`.

So after `use Std.Nat` registers `Z,S → :Nat` and the local `type Nat` registers
`Zero,Suc → :Nat` (overwriting `families[:Nat]` but **not** disowning `Z,S`), the
`ctor_to_family` map holds all four `{Zero,Suc,Z,S} → :Nat`. Coverage
(`elaborator.ex` `elaborate_rematch_branches`, line ~1293, and the sibling path
~1816) iterates `ctors_of(dname)` and demands a branch for each of the four →
`{:missing_branch, :S}`. **The imported constructors are never disowned from the
shadowed family's key.**

### 1.3 Faithfulness note (checked against upstream clones)

Idris2 (`Core/Name.idr`) keys definitions by namespaced `NS : Namespace -> Name ->
Name` (+ `Resolved Int`); Agda (`Syntax/Abstract/Name.hs`) uses `QName{qnameModule,
qnameName}` + a unique `NameId`. **Fully-qualified naming is the faithful
representation.** We deliberately adopt the *behavior-faithful* Approach B (below),
not the *representation-faithful* Approach A, because the operator's requirements
are purely about observable shadowing semantics and B keeps the TCB and the AtomVM
runtime value format untouched. What A would additionally buy — Agda-style
ambiguous same-named constructors disambiguated by expected type, self-describing
Core terms, nested namespaces — is explicitly out of scope (§7).

## 2. Requirements (observable behavior)

R1. **Per-name shadowing of both types and constructors.** A local `type Nat = Z |
    S` fully shadows imported `Nat` including its `Z`/`S` constructors: unqualified
    `Nat`/`Z`/`S` all resolve to the local family; the imported `Nat` is
    unreachable *unqualified*.
R2. **Non-shadowed imported names stay visible.** With local `type Nat = Zero |
    Suc`, unqualified `Nat` → local; unqualified `Z`/`S` (not redeclared locally)
    → still the imported `Std.Nat` constructors.
R3. **Qualified escape hatch always works:** `Std.Nat` in a type slot → the
    imported type; `Std.Nat.Z` in an expression/pattern → the imported
    constructor — regardless of any local shadow.
R4. **Module==typename collapse.** When a module `M`'s last path segment equals a
    type it declares (module `Std.Nat` declares `type Nat`), `Std.Nat` in a type
    slot resolves to that `Nat` type directly — the user need not write
    `Std.Nat.Nat`.
R5. **Shadow-aware diagnostics.** Using a shadowed constructor where the in-scope
    family is the local one yields a targeted error naming the shadowed origin and
    the correct qualified form — not a generic `{:foreign_ctor,_}` /
    `{:missing_branch,_}`.
R6. **No regression.** Every currently-green program elaborates unchanged; the
    non-collision path is byte-for-byte identical. The 2843/0 suite and the oracle
    replay stay green.
R7. **Import-vs-import ambiguity is a hard error, not silent clobber.** When ≥2
    *distinct* imported modules provide the same family name and no local
    declaration shadows it, unqualified use of that name is a compile error
    listing the qualified alternatives (§3.4); both remain reachable qualified.
    "Distinct" excludes the same module reached twice (see R6/§3.1) — that is
    not ambiguity, it is a no-op re-import.

## 3. Approach B — resolution layer over bare atoms

The registry stays bare-atom keyed. A resolution layer in the elaborator maps
surface names → registry keys with shadowing precedence, and collisions trigger a
targeted re-keying of the shadowed import(s).

### 3.1 Collision detection

After the imported `Env` is built and the local declarations' family names are
known (both available in `program.ex check_ast/1` before/at
`elaborate_declarations`), compute the multiset of **family names** contributed by
(a) each imported module and (b) the local module. A **collision** is any family
name provided by ≥2 distinct sources. Detection covers **both** local-vs-import
**and** import-vs-import.

**"Distinct sources" means distinct resolved module identities (canonical dotted
path), deduplicated *before* counting — not raw entries in the import list and
not per-transitively-reached copy.** This dedup is required, not optional,
because the ubiquitous case already exercises it today: `program.ex
auto_prelude_imports/1` excludes a prelude module only for self-reference or a
*local* same-named type declaration — it does **not** check whether the module
also appears in the explicit `use` list. So any module with no local `Nat` that
writes `use Std.Nat` already has `"Std.Nat"` in `auto_prelude_imports(ast) ++
imports(ast)` twice (auto-prelude + explicit), and `import_env`'s `seen`
MapSet is not threaded across sibling top-level imports, so both copies are
independently resolved. Separately, `priv/std/vector.cure` itself does `use
Std.Nat`, so a program combining `use Std.Vector` + `use Std.Nat` reaches
family `Nat` via two import paths — a real diamond dependency in the stdlib
today, not a hypothetical. Both cases already elaborate cleanly under today's
idempotent `merge_env` (Map.merge of identical content is a no-op). Collision
detection MUST recognize "same resolved module, reached N times" as **one**
source contributing `N`'s family once — never triggering re-keying or the
R7 ambiguity error — or it regresses R6 on the single most common import
pattern in the suite. Only genuinely distinct modules (different canonical
dotted path) providing the same family name count toward a collision.

**Interaction with the auto-prelude skip.** `program.ex auto_prelude_imports/1`
today *skips* auto-importing `Std.Bool`/`Std.Nat` when the module declares a
same-named type, so no collision arises for the auto case. The general mechanism
here can subsume that skip: prefer to **stop skipping** and let auto-imported
families collide + re-key like any other, so the qualified escape hatch (`Std.Nat.Z`)
works uniformly even when the type was only auto-imported. If the plan instead
retains the skip (lowest-risk), then reaching an auto-prelude type's shadowed
constructor requires an explicit `use Std.Nat` — acceptable, but the plan must
state which choice it takes and keep the existing auto-prelude tests green either
way. The re-keying path must be validated against **explicit `use`** regardless.

### 3.2 Re-keying the shadowed families (the core transform)

For each colliding family name `N`:
- **Winner of the unqualified name `N`:** the local declaration if the local
  module declares `type N`; else — if exactly one import provides `N` — that
  import; else (≥2 imports, no local) `N` is **unqualified-ambiguous** (§3.4).
- **Losers** (every import providing `N` that is not the winner) are **re-keyed**:
  the family key `:N` becomes the qualified atom `:"<Module>#N"` (e.g.
  `:"Std.Nat#Nat"`), and each of its constructors `:C` becomes `:"<Module>#C"`
  (e.g. `:"Std.Nat#Z"`). The re-key is applied to that imported module's slice of
  the `Env`:
  - `families`: move `:N` → `:"<Module>#N"` (family record's `name` field updated).
  - `ctors`: move each `:C` → `:"<Module>#C"` (ctor record's `name` field updated
    — see §3.5 for the runtime-tag caveat).
  - `ctor_to_family`: repoint each re-keyed ctor to the re-keyed family.
  - `defs`: rewrite the imported module's Core terms so every occurrence of a
    re-keyed atom is substituted, across **all three** bare-atom positions
    `lib/cure/core/term.ex` defines (a literal walk must hit each): `{:data, :N,
    params, indices}`, `{:ctor, :C, args}`, **and** a `:case` branch tag —
    `:case` branches are `{cname, arity, body}` tuples where `cname` is a bare
    constructor atom, *not* wrapped in `{:ctor, …}` (see `term.ex` `shift/3`,
    `subst/3`). Missing the branch-tag position would silently leave a
    re-keyed module's own pattern matches tagged with the old bare name,
    reintroducing the exact coverage bug this spec fixes, only inside the
    losing import instead of the local module.
- **Constructor-name collisions within a re-keyed family are harmless**: local `Z`
  and re-keyed `:"Std.Nat#Z"` are distinct keys; both may exist.

Because the winner keeps the bare key `:N` and its bare ctor keys, and everything
else in the program already references bare keys, **no non-colliding term changes**.
The disown is automatic: after re-keying, `ctor_to_family` maps `Zero,Suc → :Nat`
(local) and `Std.Nat#Z, Std.Nat#S → :"Std.Nat#Nat"`, so `ctors_of(:Nat)` returns
exactly `{Zero,Suc}` and coverage passes.

### 3.3 Resolution table

Alongside re-keying, build a **resolution table** recording, per module, the
mapping from qualified surface paths to registry keys:
- `"Std.Nat"` (as a type) → the `Nat` type key from module `Std.Nat`
  (`:"Std.Nat#Nat"` when re-keyed, else `:Nat`) — this is R4's collapse.
- `"Std.Nat.Z"` → the ctor key (`:"Std.Nat#Z"` when re-keyed, else `:Z`).
- `"Std.Nat.Nat"` → same as `"Std.Nat"` (both spellings accepted).

The table also retains **shadowed-but-present** names (which bare surface name is
now only reachable qualified, and from which module) to power R5's diagnostics,
and, separately, **ambiguous** names (a bare name provided by ≥2 distinct
non-winning imports with no local declaration, plus the list of candidate
modules) to power R7's diagnostic (§3.4). Both sets must be consulted by the
*ordinary* bare-name resolution path — `resolve_index_name` for types
(`declarations.ex`), and the bare-`{:variable,…}`/`constructor_pattern`
lookups for values/patterns (`elaborator.ex`) — **before** it falls through to
today's plain lookup. Without this, an ambiguous `N` (re-keyed off the bare
atom on both sides, since neither import is a winner) would simply be
*absent* from `families`/`ctors` and fall through to the existing
unbound-global/unknown-constructor path, producing a generic "not found"
error instead of `{:ambiguous_name,…}` — the same anchor-point mistake §5
identifies and fixes for the shadowed-constructor case.

The table is threaded into elaboration. It lives in the E-layer (NOT in the core
`Env` struct) — e.g. carried on the elaboration context/`names` environment or a
sibling structure passed to `elaborate_expr_typed` / declaration elaboration —
so `lib/cure/core/*` is untouched.

### 3.4 Unqualified ambiguity

If ≥2 imports provide family `N` and the local module does not declare `N`, bare
`N` (and any bare ctor name provided by >1 of them) is ambiguous. Using it
unqualified is an error: `{:ambiguous_name, N, [Module1, Module2]}` with a message
listing the qualified forms. Both families are still reachable via their qualified
paths. (This case is rare today — the stdlib has no duplicate family names — but
detection must not silently let one import clobber another.)

### 3.5 Runtime constructor tags stay bare (AtomVM invariant)

The BEAM/AtomVM value representation tags a constructor by its **bare** name
(`Zero`, `Suc`, `Z`, `S`). Qualified keys are elaborator/registry-internal only.
Codegen (`lib/cure/compiler/codegen.ex`) must emit the **bare** tag even for a
re-keyed constructor: strip the `"<Module>#"` prefix from a ctor atom of the form
`:"Mod#C"` → `C` when producing the runtime tag. This is the only C-layer touch and
is exercised **only** on the escape-hatch path (a re-keyed ctor actually used).
Structural tag collisions across distinct families are safe: type safety is
enforced entirely at compile time, and BEAM ADTs routinely share tags across types.

### 3.6 Qualified reference resolution in the elaborator

**Two distinct AST shapes carry a qualified name, and both must be
intercepted — they are not interchangeable.**

**(a) No-call reference** (`Std.Nat` alone, no parens — the shape a
*nullary* type reference takes in a type slot, e.g. R4's own example; `Nat`
itself has no parameters) parses as nested `{:attribute_access, [attribute:
seg], [base]}` chains (`Std.Nat` → `attribute_access("Nat", var "Std")`). The
dependent elaborator currently handles `attribute_access` for σ-tuple
projection (`p.1`/`p.2`) and, in `elaborator.ex`'s expression/pattern path
only (`record_projection/5`), single-constructor record field access
(`obj.field`); `declarations.ex`'s type-slot path (`idx_to_core`) handles only
`.1`/`.2` and errors `{:bad_projection, _}` on anything else — there is
currently no type-slot handling of a dotted module/type path at all. Note a
qualified reference to a *parameterized/indexed* family (e.g.
`Std.Vector(Nat)`, mirroring the existing `Vector(a: Type) indices (n: Nat)`
declaration in `priv/std/vector.cure`) is **not** this shape — like a
constructor application, it is parsed as a call, so it falls under (b)
instead (see the third call site there, `idx_to_core`'s own `function_call`
clause). A type-slot qualified reference is shape (a) only when the
referenced family is nullary.

**(b) Call-syntax reference** (`Std.Nat.Z(x)` or `Std.Nat.Z()` — and every
constructor in this codebase and in this spec's own examples is written with
explicit call parens, including nullary ones: `Zero()`, `None()`, `Z()`) is
**flattened by the parser itself, before elaboration ever sees it**: `parse_call`
in `lib/cure/compiler/parser.ex` calls `extract_call_name/1` (line ~658),
which for an `attribute_access`-shaped callee calls `extract_dotted_path/1`
(line ~674) and joins the segments with `.` into a single **string**, so
`Std.Nat.Z(x)` parses directly as `{:function_call, [name: "Std.Nat.Z"], [x]}`
— **no `attribute_access` node survives**. Consequently:
- `constructor_pattern/1` (`elaborator.ex` ~3174), which does `cname =
  meta |> Keyword.fetch!(:name) |> String.to_atom()`, would turn a qualified
  pattern into the atom `:"Std.Nat.Z"` (dot-separated, from the parser) —
  which matches neither the bare key `:Z` nor the re-keyed registry key
  `:"Std.Nat#Z"` (hash-separated, from §3.2). Looked up as-is, it is simply
  unknown.
- `elaborate_named_call/5` (`elaborator.ex` line 171), which does the same
  `String.to_atom(name)` before `Inductive.get_ctor(env, atom)`, has the
  identical problem for a qualified constructor used as an *expression*
  (`Std.Nat.Z(x)` on the right of `=`, in a call, etc.).
- `idx_to_core`'s own `{:function_call, fmeta, args}` clause (`declarations.ex`
  line ~726), which does `name = Keyword.fetch!(fmeta, :name); atom =
  String.to_atom(name)`, has the identical problem for a qualified
  *parameterized* type reference in a type slot (`Std.Vector(Nat)`, mirroring
  the existing `Vector(a: Type) indices (n: Nat)` declaration in
  `priv/std/vector.cure`) — this is the one type-slot case that is call
  syntax, not shape (a).
- All three call sites above must, **before** falling back to a plain-atom
  registry lookup, check whether `name` contains a `.` and — if so — look it
  up **directly** (as the full dotted string, e.g. `"Std.Nat.Z"`) in the
  resolution table (§3.3), which is already keyed by exactly these
  full dotted-path strings — no further splitting is needed, the table does
  that bookkeeping once at collision-detection time (§3.1/§3.2). Only a
  resolution-table miss falls back to `String.to_atom(name)`/
  `Inductive.get_ctor`. This is the primary implementation site for R3's
  escape hatch and for R5's pattern diagnostics (§5) — **not** the
  `attribute_access` extension in (a), which only ever fires for the
  no-parens (nullary-reference) case.

For all three call sites, **when the flattened dotted path resolves in the
resolution table** to a type or constructor key:
- In a **type slot** (`declarations.ex`): a nullary reference (shape (a),
  `idx_to_core`'s `attribute_access` clause) `Std.Nat` / `Std.Nat.Nat` →
  `{:data, <key>, [], []}`; a parameterized reference (shape (b),
  `idx_to_core`'s `function_call` clause) `Std.Vector(Nat)` → `{:data, <key>,
  params, indices}` built from the call's own args exactly as the existing
  bare-name case already does.
- In an **expression / pattern position** (`elaborator.ex`, shape (b) via
  `constructor_pattern`/`elaborate_named_call`, or shape (a) for a bare
  parenless value reference if the grammar permits one): `Std.Nat.Z` → the
  constructor reference/pattern for `<ctor key>`.
- A dotted path that does **not** resolve to a type/ctor falls through to the
  existing behavior unchanged for its call site — the `attribute_access`
  clauses fall through to tuple-projection/attribute/`{:bad_projection,_}`
  behavior; the three `function_call`-shaped clauses fall through to their
  existing plain-atom `Inductive.get_ctor`/global lookup (no regression
  either way).

## 4. Worked examples

| Program | Unqualified resolves | Escape hatch |
|---|---|---|
| `use Std.Nat` (Z\|S) + local `Nat = Zero\|Suc` | `Nat`,`Zero`,`Suc` → local; `Z`,`S` → imported (R2) | `Std.Nat` → imported type; `Std.Nat.Z` → imported ctor |
| `use Std.Nat` (Z\|S) + local `Nat = Z\|S` | `Nat`,`Z`,`S` → local (imported fully shadowed, R1) | `Std.Nat.Z` → imported ctor (still reachable, R3) |
| `use Std.Nat` only, no local `Nat` | `Nat`,`Z`,`S` → imported (unchanged) | `Std.Nat.Z` also works |
| `use A` + `use B`, both define `Nat`, no local | bare `Nat` → `{:ambiguous_name,…}` (R7, mechanism §3.4) | `A.Nat` / `B.Nat` each resolve |

## 5. Diagnostics (R5)

The resolver retains, per bare surface name, whether it is *shadowed* (present in
an import but not the unqualified winner) and its origin module + sibling ctor set.

**Anchor point.** After re-keying (§3.2), a shadowed constructor's bare atom
(`:Z`) is *moved off* the registry entirely — it is not merely misfiled to the
wrong family. So a bare pattern `Z()` on a scrutinee of the local `Nat = Zero |
Suc` does **not** reach `Inductive.ctor_family(sig, cname) != dname`
(`{:foreign_ctor,_}`); it fails the *earlier* gate, `Inductive.get_ctor(env,
cname) == nil`, in both `partition_arms` (`elaborator.ex` ~2778) and
`partition_rematch_arms` (~1267), which today produces
`{:unknown_pattern_constructor, cname}`. **This is the error the shadow-aware
diagnostic must intercept** — not `{:foreign_ctor,_}`. Concretely, right
before raising `{:unknown_pattern_constructor, cname}`, check the resolution
table's shadowed-but-present list for `cname`; if present, raise instead:

`{:shadowed_ctor, ctor: :Z, shadowed_module: "Std.Nat", local_family: :Nat,
  local_ctors: [:Zero, :Suc], hint: "Std.Nat.Z"}`
rendered as: *"`Z` is a constructor of `Std.Nat`, which is shadowed here by the
local `Nat` (constructors `Zero`, `Suc`). Write `Std.Nat.Z` to use the shadowed
constructor."*

A constructor that is genuinely unknown (never declared, anywhere) still
raises the unchanged `{:unknown_pattern_constructor,_}` (R6). `{:foreign_ctor,
cname}` also stays reachable and unchanged: it now fires when `cname` exists
in the registry (under its own bare or re-keyed name, found via the table) but
names a *different, non-shadowed* family than the scrutinee's — the ordinary
cross-family mismatch this error already covers.

Note there is deliberately no separate "missing branch that is actually a
shadow artifact" case: `ctors_of(dname)` (the source of `{:missing_branch,_}`)
only ever enumerates `dname`'s own, already-disowned constructor set (§3.2) —
a shadowed constructor cannot appear there post-re-key, so it cannot surface
as a `{:missing_branch,_}`. Every shadow-related diagnostic is caught earlier,
at the unknown-constructor gate above.

## 6. Test strategy (TDD, differential oracle)

Each behavior is pinned by a paired `.cure`/`.idr` oracle probe (faithful
transliteration, `%default total`, no `module` line) plus a focused elaborator
unit test. Red-first: the repro (P-a) is currently `{:missing_branch, :S}`.

Oracle cluster `shadow` (new), probes:
- **shadow01** — R1-partial repro: `use Std.Nat` + local `Nat = Zero|Suc`, match
  `Zero`/`Suc`. Cure currently rejects; Idris accepts (local shadows). Target:
  `same` (accept).
- **shadow02** — R1 full: local `Nat = Z|S` shadowing same-named imported ctors;
  construct + match locally. Target `same`.
- **shadow03** — R2: local `Nat = Zero|Suc`; a function using unqualified `Z`/`S`
  still refers to imported `Std.Nat`. Target `same` (both accept, both resolve to
  imported).
- **shadow04** — R3 escape hatch: after a local shadow, `Std.Nat.Z` /
  `Std.Nat` used explicitly. `Nat` is nullary, so this probe exercises two of
  the three call sites in §3.6 — `constructor_pattern` and
  `elaborate_named_call` (§3.6(b); the parameterized-type `idx_to_core`
  `function_call` site is not reachable via `Nat` and is not this probe's
  concern) — plus the nullary type-slot site (§3.6(a), `idx_to_core`'s
  `attribute_access` clause). Assert all three, separately:
  `Std.Nat.Z()` in **pattern** position (`constructor_pattern`); building a
  value with `Std.Nat.S(Std.Nat.Z())` in **expression** position
  (`elaborate_named_call`); and `Std.Nat` / `Std.Nat.Nat` in a **type slot**.
  A probe that exercises only one path could pass while another is still
  broken. Target `same` for each.
- **shadow05** — R4 collapse: `Std.Nat` in a type slot (no `.Nat`). Target `same`.
- **shadow06** — R5 diagnostic: match a shadowed ctor on the wrong family; assert
  the specific `:shadowed_ctor` error (Cure-only unit assertion; Idris side is a
  parallel type error — relation `cure_stricter`/documented, or an idris probe that
  also errors → `same` on *reject*, with the reason pinned to the message).
- **shadow07** — R7 ambiguity (mechanism §3.4): two *distinct* imports both
  defining `Nat`, no local, bare use → `{:ambiguous_name,…}`. Must use two
  genuinely distinct modules (e.g. scratch stdlib-shaped sources `Std.Foo` /
  `Std.Bar` each declaring `type Nat`) — not the same module reached twice via
  auto-prelude + explicit `use`, or via a diamond such as `use Std.Vector` +
  `use Std.Nat` (`priv/std/vector.cure` itself does `use Std.Nat`), both of
  which are the same source deduplicated per §3.1 and must NOT trigger this
  error. (Constructed with a scratch second stdlib-style module since none
  exists today; relation documents the deliberate reject.)

Unit tests (behavioral, immutable once green):
- `test/cure/elab/type_shadowing_test.exs` — the R1–R5 cases at
  `Program.elaborate/1` granularity, asserting `{:ok,_}` / specific error tuples.
- Extend `test/cure/elab/auto_prelude_test.exs` only if a new auto-prelude
  interaction surfaces (auto-prelude collision-avoidance must remain green).

Gate (run once, alone — never concurrent suites):
1. New unit + oracle probes green.
2. `mix test test/oracle_replay_test.exs` green (no other probe regressed).
3. Full suite `mix test` green (2843/0 baseline or higher).
4. Codegen sanity for the escape-hatch path: a program using `Std.Nat.Z` compiles
   and the emitted constructor tag is bare `Z` (assert on the generated forms; a
   host run is sufficient — no hardware needed for this invariant).

## 7. Non-goals

- **Fully-qualified internal naming (Approach A).** Not adopted; see §1.3.
- **Agda-style ambiguous-constructor type-directed disambiguation.** Constructors
  remain a one-name→one-family map per resolution scope; ambiguity is an error
  (§3.4), not resolved by expected type.
- **Nested / sub-module namespaces.** Cure modules are flat; `Module#Name` handles
  one level. No arbitrary nesting.
- **Qualifying `defs` (functions).** Function/value shadowing already works
  (last-writer-wins); this spec does not change it. Only families + constructors
  gain the resolution layer. (If a function name genuinely needs qualified access
  it can be added later on the same table; out of scope here.)
- **No kernel/TCB change.** `lib/cure/core/*` is not modified.

## 8. Risk + layer summary

- **Primary layer E** (`lib/cure/elab/program.ex` collision detection + re-key +
  table; `lib/cure/elab/elaborator.ex` + `lib/cure/elab/declarations.ex` qualified
  resolution + diagnostics). No soundness surface — the kernel still checks the
  same Core it always did; only *which* family key a name resolves to changes,
  entirely before the kernel sees a term.
- **Contained C touch** (`lib/cure/compiler/codegen.ex`) — strip `Mod#` prefix for
  runtime tags; escape-hatch path only.
- **Chief risks (two, opposite directions):**
  1. *Under-detection* — a missed collision silently reverting to clobber.
     Mitigated by detecting *all* family-name collisions (import-vs-import
     included) with a simple set-comparison, and by shadow07/shadow0x probes.
  2. *Over-detection* — flagging the same module reached twice (auto-prelude +
     explicit `use`, or a diamond like `use Std.Vector` + `use Std.Nat`) as a
     false collision. This is the higher-probability risk in practice, since
     it hits the single most common import pattern rather than an edge case
     (§3.1). Mitigated by deduplicating on resolved module identity *before*
     counting sources.
  3. *Wrong intercept point* — routing qualified-name resolution only through
     `attribute_access` would silently no-op for every constructor written
     with call syntax (the universal convention here) and for any qualified
     *parameterized* type reference, since the parser flattens
     `Mod.Sub.Name(...)` into a plain dotted-string function-call name before
     `attribute_access` ever exists (§3.6). Mitigated by wiring the
     resolution-table lookup into all three affected call sites directly —
     `constructor_pattern`, `elaborate_named_call`, and `idx_to_core`'s
     `function_call` clause — not only into `attribute_access`.
  4. *Diagnostics never firing* — both R5's `:shadowed_ctor` and R7's
     `:ambiguous_name` describe a name that, post-re-keying, is simply
     *absent* from the bare-atom registry. If the ordinary bare-name lookup
     paths (pattern/expression/type-slot) aren't each explicitly taught to
     check the resolution table's shadowed/ambiguous sets *before* falling
     through to their existing not-found error, both diagnostics silently
     degrade to a generic `{:unknown_pattern_constructor,_}` / unbound-global
     error instead of firing. Mitigated by the anchor-point call-site list in
     §5 (R5) and §3.3 (R7).
  The re-key term-rewrite is a bounded pure atom substitution over one
  module's `defs` — including `:case` branch tags, a bare-atom position
  distinct from `{:ctor,…}` (§3.2) — unit-tested directly.
- **Regression guard:** non-collision path is a no-op; R6 asserted by the full
  suite + replay.

# Phase 5 (C2) — U0 characterization and inventory

**Scope.** `docs/PATH_TO_LEAN4.md` §8 Phase 5 = **C2, universe polymorphism**.
Its gate is the completion criteria in §21 of
[`2026-07-20-agda-style-universe-polymorphism-design.md`](superpowers/specs/types/2026-07-20-agda-style-universe-polymorphism-design.md).
That spec's mandatory sequence is U0–U7 (§18); **this document is U0**.

**U0 gate (spec §18):** "characterization tests fail for the intended missing
behavior; existing suite remains green." This document is the checked
inventory (U0 items 2 and 4); the characterization tests are
`test/cure/core/universe_polymorphism_characterization_test.exs`.

**Status:** U0 in progress. No kernel semantics changed by this phase slice.

---

## 1. What exists today

`Cure.Core.Universe` is a 34-line module holding a **fixed three-level
hierarchy**:

```elixir
@ceiling 2
def ceiling, do: @ceiling
def max(l1, l2), do: Kernel.max(l1, l2)
def le?(l1, l2), do: l1 <= l2
def succ(level) when level + 1 <= @ceiling, do: {:ok, level + 1}
def succ(_level), do: {:error, :universe_ceiling}
```

Every universe level in Core is a **plain Elixir integer in `0..2`**. There is
no `UniverseLevel` type, no canonical maximum-plus normal form, no level
variables, no level metavariables, no `TypeLimit`, and no `universe_zero` /
`universe_succ` / `universe_max` primitives. `grep -rn "UniverseLevel" lib/`
returns **zero** matches.

### 1.1 The surface misreading (measured, not inferred)

The Lean-4-parity corpus pins `g9-universe-level-binder` as `:accept` because
"`{l: UniverseLevel}` parses and elaborates". It does parse — but it does **not**
do what it says. `parse_type_arrow_dispatch/2`'s simple-type arm calls
`type_variable/1`, which produces a bare `{:variable, [scope: :local, …], name}`
with no kind metadata. `UniverseLevel` is therefore an **ordinary type variable
named `"UniverseLevel"`**, and `TypeN` is an ordinary type variable named
`"Type37"`. Nothing distinguishes them from `a` or `b`.

Measured through the real pipeline (`cure check` / `compile_and_load`):

| Source | Result | Meaning |
|---|---|---|
| `fn id({a: Type37}, x: a) -> a = x` alone | **accepted** | `Type37` is a variable, so `a` ranges over it as a plain type |
| `fn id({a: Type37}, x: a) -> a = x` + `id(n)` at `Int` | **rejected** | but with `{:conversion_failure, {:type, 0}, {:global, :Type37}}` — `Type37` resolves to an unresolved *global*, not a sort |
| `fn id({a: TypeLimit}, x: a) -> a = x` | **accepted** | `TypeLimit` is an ordinary type variable |
| `fn id({a: Type(0)}, x: a) -> a = x` | **accepted** | `Type(0)` is an ordinary *application* |
| `fn id({l: UniverseLevel}, {a: Type}, x: a) -> a = x` | **accepted** | `UniverseLevel` is an ordinary type variable |

So the binder is not merely *unproven* arbitrary-level polymorphism — it is
**misread**. `TypeN` is the sharpest case: it is not even a type variable that
unifies with a sort, it is an **unresolved global**, so a definition written at
`Type37` fails with a conversion failure against `{:global, :Type37}` rather
than a level error. That is stronger than the scorecard's current "surface
binders alone are not proof of arbitrary-level kernel polymorphism" caveat.

**Consequence for the corpus.** These are *accepted* programs, so a `:reject`
pin is the wrong instrument — `compile_and_load` genuinely accepts them. The
pins therefore stay `:accept` for the three that compile, and the defect is
recorded in each pin's title and in the scorecard, which is the only place the
corpus can carry a caveat. See §5.

### 1.2 What the kernel actually enforces

The ceiling is real and load-bearing in four places:

| Site | Behaviour |
|---|---|
| `Term.term?/1` | `{:type, level}` valid only for `0 <= level <= 2` |
| `Value.value?/1` | `{:vtype, level}` valid only for `0 <= level <= 2` |
| `Kernel.infer/2` (`{:type, level}`) | `Universe.succ/1` → `{:error, :universe_ceiling}` past 2 |
| `Kernel.check_family_level/1` | family declared at `> 2` → `{:error, :universe_ceiling}` |

`Kernel.subtype?/3`'s sort clause is `Universe.le?(l1, l2)` — integer `<=`.
`Kernel.infer/2`'s Π rule is `{:vtype, Universe.max(l1, l2)}` — integer `max`.
There is **no** `piSort` / rigid-level-dependency classification, so
`(l : UniverseLevel) -> Type(l)` has no sort today.

### 1.3 Declaration-time level search (to be deleted)

`Cure.Elab.Declarations` mirrors `@ceiling 2` and implements exactly the
retry loop spec §11.1 says to delete:

```elixir
defp declare_at_min_level(env, name, ctors, level) when level <= @ceiling do
  …
  {:error, :universe_level} -> declare_at_min_level(env, name, ctors, level + 1)
end
defp declare_at_min_level(_env, _name, _ctors, _level), do: {:error, :universe_ceiling}
```

Three near-identical copies exist: `declare_at_min_level/4`,
`declare_indexed_at_min_level/6`, `declare_opaque_at_min_level/5`. Each searches
`0, 1, 2` for the first level the two-universe rule accepts.

---

## 2. Inventory: every `{:type, integer}` / `{:vtype, integer}` producer

Producers are the sites that **construct** a universe node. They are the U2
migration surface. Grouped by trust tier.

### 2.1 Trusted kernel (`lib/cure/core/`)

| File | Site | Role |
|---|---|---|
| `term.ex:311` | `to_external({:type, l})` | serialization — needs a version bump |
| `serialize.ex:21,200` | `enc`/`build_node("type", …)` | S-expression codec — needs a new tag |
| `eval.ex:31` | `eval({:type, level})` → `{:vtype, level}` | NbE |
| `quote.ex:42` | `reify({:vtype, level})` → `{:type, level}` | read-back |
| `printer.ex:28-29` | `print({:type, n})` | display |
| `kernel.ex:65` | `{:vtype, l+1}` from `Universe.succ` | universe formation |
| `kernel.ex:138,1430` | `{:vtype, Universe.max(l1,l2)}` | Π join |
| `kernel.ex:2407` | `Universe.le?` | cumulativity |
| `kernel.ex:1346` | `Universe.succ` in `infer_type_value_sort` | motive sorting |
| `builtins.ex:219,268,447,464,489` | `{:type, 0}` in seeded Pi/family telescopes | floor |
| `proof_wire.ex:117` | `code({:type, level})` guarded by `@ceiling` | proof wire |
| `validator.ex:270` | `violation(:level_expr, {:type, l})` | **already flags integer levels** |

`validator.ex:270` is notable: the validator already has a
`level_expr` clause whose message is "universe level is an integer, not a
level-expression (K7)". The migration's target representation is already
anticipated by the audit layer.

### 2.2 Untrusted elaborator (`lib/cure/elab/`)

| File | Site | Role |
|---|---|---|
| `elaborator.ex:996` | `elaborate_expr_typed("Type")` → `{:type, 0}`, `{:vtype, 1}` | surface `Type` |
| `elaborator.ex:16042` | `elaborate_expr("Type")` → `{:type, 0}` | surface `Type` (untyped path) |
| `declarations.ex:454` | `result_sort = {:type, 0}` / `{:type, @ceiling}` | typealias placeholder |
| `declarations.ex:517` | `wrap_binders(…, {:type, level})` | alias result sort |
| `declarations.ex:1488` | `signature_return_core(nil, …)` → `{:type, 0}` | omitted return |
| `declarations.ex:2478` | `{:type, 0}` param telescope entry | bare type param |
| `declarations.ex:3319` | `idx_to_core("Type")` → `{:type, 0}` | type-position `Type` |
| `equation.ex:574` | `equality_terms(_, {:type, 0}, …)` | equality at `Type0` |
| `unify.ex:423` | `do_unify_struct({:type, l}, {:type, l})` | **syntactic** level equality |
| `union.ex:199` | `member_key({:type, l})` → `"Type" <> int` | union keying |
| `proof_display.ex:8-9` | `format({:type, n})` | display |

`unify.ex:423` is a correctness hazard for U2: it decides level equality by
**Elixir term equality on integers**, which the spec (§6.4) explicitly forbids
("Atom comparison uses ordinary Core definitional equality … It does not use
Elixir term equality as a substitute for conversion").

### 2.3 Antigen (`lib/antigen/`)

21 generator/assay files construct `{:type, n}`. The universe vertical itself is
`lib/antigen/generators/universes.ex`, whose 9 coverage cells are all
**ceiling-shaped** and must be replaced (U7):

| Cell | What it pins | Fate under U0–U7 |
|---|---|---|
| `:type_in_type` | `Type0 : Type0` rejects | **survives** (§21.2) |
| `:ceiling_def` | a def annotated *at* `Type2` rejects | **deleted** — no ceiling |
| `:cumulativity` | `Nat` at `Type1` | survives, generalized |
| `:stratification` | `Type0 : Type1` | survives |
| `:ctor_field_pos` / `_neg` | two-universe rule | survives, generalized |
| `:indexed_ctor_pos` / `_neg` | result-index check | unaffected |
| `:family_ceiling` | family at `ceiling+1` rejects | **deleted** — no ceiling |

`lib/antigen/generators/malformed.ex:81` also hard-codes
`{:type, 2}` as "universe ceiling (Type 2 has no sort)".

---

## 3. Inventory: every Core walker (the soundness-critical list)

Spec §7.2: "Every generic Core traversal must descend into level atoms …
Treating a level as an inert leaf would permit scope escape and is a
**soundness bug**." The following table classifies each walker by how it will
behave when `{:type, sort_index}` gains atom subterms.

### 3.1 Explicit, level-aware today (safe — needs a level-atom clause)

| Walker | Location | Note |
|---|---|---|
| `Term.shift/3` | `term.ex` | `{:type, _}` returns as-is; must shift atoms |
| `Term.subst/3` | `term.ex` | same |
| `Term.closed?/1` | `term.ex` | `has_free_var?` catch-all recurses tuples — **already safe** |
| `Term.to_external` / `from_external` | `term.ex` | needs a new tag |
| `Serialize.enc` / `build_node` | `serialize.ex` | needs a new tag |
| `Validator` | `validator.ex` | has `level_expr` clause already |
| `ProofSnapshot.scan!` | `proof_snapshot.ex:209` | `{:type, _level}` → `:ok`; must descend |
| `ProofWire.code` | `proof_wire.ex:117` | guarded by `@ceiling` |
| `Audit.Refs.walk` | `audit/refs.ex:64` | `{:type, _}` → `acc`; must descend |
| `Kernel.occurs_index?` | `kernel.ex` | catch-all `_ -> false` — **fail-open on atoms** |
| `Kernel.strongly_rigid_occurs?` | `kernel.ex` | ctor/data-only descent; atoms unreachable |
| `Kernel.replace_branch_vars` | `kernel.ex` | `other -> other` catch-all — **fail-open on atoms** |
| `Kernel.subst_params` | `kernel.ex` | `other -> other` catch-all — **fail-open on atoms** |
| `Elab.Unify.escapes?` | `unify.ex:587` | `{:type, _}` → `false` |

### 3.2 Catch-all tuple walkers (fail-open — the §7.2 hazard)

These recurse over `Tuple.to_list/1` and would traverse a level atom's
*representation* without knowing it is a level. They are not wrong today
(levels are integers), but after U2 they are the exact failure mode the spec
names:

| Walker | Location |
|---|---|
| `ModulePipeline.Closure.collect/2` | `closure.ex:103` |
| `ModulePipeline.Interface.mentioned_globals/1` | `interface.ex:343` |
| `MetaAST.Conformance.walk/4`, `to_conformant/1`, `hides_node?/1` | `conformance.ex:174,252,370` |
| `MetaAST.MetadataLint.walk/3` | `metadata_lint.ex:91` |
| `MetaAST.Metadata.strip_diagnostics/1` | `metadata.ex:72` |
| `ModulePipeline.Cycle` | `cycle.ex:79,100` |
| `ModulePipeline.Expansion.collect_variables/2` | `expansion.ex:165` |

**U0 finding:** the migration cannot be done by changing `Term` alone. Every
row in §3.2 must gain an explicit level-atom clause in the same commit as the
representation change, or a level variable can escape its binder scope
silently. This is the single largest risk in U2 and the reason U0 exists.

---

## 4. Inventory: serialization and hash versions

Spec §15 requires the universe representation version to be included in:
checked Core artifact hashes, totality certificates, module interface hashes,
incremental semantic hashes, bundled stdlib artifacts, macro quasiquote/Core
captures, Antigen corpus schema and dedup keys, exported protobuf schemas.

Measured current state:

| Artifact | Version carrier | Action |
|---|---|---|
| Core S-expression codec | **none** — `Serialize` has no version tag | add `(sort …)` / level tags; old `(type n)` decodes only in a compatibility path |
| `Term.to_external` | **none** | add a version field |
| `ModuleInterface` | `@schema_version 8` (`module_interface.ex:25`) | **bump to 9** |
| Totality certificates | `Certificate.summary_version()` | audit + bump |
| Antigen corpus | schema in `lib/antigen/` | regenerate seeds (U7) |
| protobuf export | `lib/cure/export_types/protobuf.ex` | audit |

---

## 5. Corpus and scorecard corrections required by U0

These are **truthfulness** corrections, not reach changes. Per
`PATH_TO_LEAN4_PLAN.md` §2.1 a flipped pin is the review — here the review is
"the pin was measuring a misreading".

**Measured outcome.** All four surface forms except the `Type37`-with-use are
*accepted* by `compile_and_load`, so `:reject` is the wrong pin value for them —
the corpus would be recording a rejection that does not happen. The pins
therefore keep their `:accept` value and carry the defect in their **titles**,
with the scorecard as the place the caveat lives.

| Pin | Value | Recorded behaviour |
|---|---|---|
| `g9-universe-level-binder` | `:accept` | renamed to "…is misread as an ordinary type variable and ACCEPTED" |
| `g9-typen-misread-as-level-zero` | `:reject` | **new** — the only one that fails, with `{:conversion_failure, {:type, 0}, {:global, :Type37}}`, i.e. `Type37` is an unresolved global, not a sort |
| `g9-typelimit-misread-as-variable` | `:accept` | **new** — `TypeLimit` is an ordinary variable |
| `g9-type-application-misread` | `:accept` | **new** — `Type(0)` is an ordinary application |
| `g9-fixed-universe-type` | `:accept` | unchanged (`{a: Type}` at level 0 is correct) |

The scorecard's G9 bullet must be rewritten from "universe work not changed.
Surface binders alone are not proof of arbitrary-level kernel polymorphism" to
record the misreading explicitly, and to state that the `:accept` pins above are
**not** evidence of level polymorphism.

**U4 gate:** when `TypeN` becomes a real sort, `g9-typen-misread-as-level-zero`
flips to `:accept` (the definition then compiles because the level is real), and
the three misread titles are replaced by their correct titles. That diff is the
U4 review.

---

## 6. U0 characterization matrix (what the tests must assert)

Per spec §19, mapped to what U0 can observe **without** changing semantics.
Each row becomes a test that fails today for the intended reason.

### 19.1 Level algebra — *cannot be tested yet*

`UniverseLevel` does not exist. U0 records the absence as an explicit
`@tag :u1` pending test rather than a passing stub.

### 19.2 Kernel positives — all fail today

| Spec row | Expected | Today |
|---|---|---|
| `Type(a) : Type(succ a)` for open `a` | accept | no open levels exist |
| `Type37 : Type38` without 38 successor nodes | accept | **rejected** (`:universe_ceiling`) |
| `Type(a)` accepted at `Type(max a b)` | accept | n/a |
| `Pi(A:Type(a)).Type(b)` at finite max | accept | integer max, no variables |
| `(l:UniverseLevel) -> Type(l)` at `TypeLimit` | accept | no `TypeLimit`, no `piSort` |
| finite sorts below every `TypeLimitN` | accept | no `TypeLimit` |
| limit cumulativity by closed index | accept | n/a |
| polymorphic `List`/`Sigma`/`Equivalent` | accept | **all pinned at `Type0`** (`builtins.ex:447,464,489`) |
| use-site level inference | accept | no level metas |
| ctor fields determine least family level | accept | retry loop, not constraints |

### 19.3 Kernel negatives — the antibodies that must survive

| Spec row | Today |
|---|---|
| `Type(a)` rejected at `Type(a)` | holds for integers (`Type0 : Type0` rejects) — must hold for variables |
| `TypeLimitN` rejected at itself | n/a today |
| `TypeLimitN` rejected below every finite sort | n/a |
| unrelated open levels do not compare | n/a — no open levels |
| `a + 1 <= a` rejected | n/a |
| non-`UniverseLevel` term rejected as a `Type` index | **fails** — `Type(0)` is an ordinary application |
| out-of-scope level atom rejected | n/a |
| noncanonical serialized level rejected | n/a |
| level meta marker rejected at Core boundary | n/a |
| ctor field sort > family sort rejected | holds |
| uncertified fn in a level atom never unfolds | n/a |

### 19.4–19.6

Elaborator, erasure and Antigen rows are U4/U6/U7 gates. U0 records them as
pending with the inventory rows above as their input.

---

## 7. What U0 changes

**Nothing in `lib/`.** U0 is characterization + inventory. The only source
changes are:

1. This document.
2. `test/cure/core/universe_polymorphism_characterization_test.exs` — red
   tests for the intended missing behaviour, tagged so they can be enabled
   phase by phase.
3. The `g9` corpus pins and scorecard correction (§5), which record today's
   behaviour **truthfully** rather than changing it.

The existing suite stays green (U0 gate).

## 8. U1 entry criteria (next slice)

U1 is "implement `Cure.Core.UniverseLevel` with canonical construction,
equality, ordering, substitution, shifting, validation, and printing" with the
gate "focused UniverseLevel tests and property tests green; **no kernel
semantics changed**".

U1 can start as soon as this inventory is reviewed, because it adds a new
module and does not touch `Term`. The `{:level_nf, constant, [{atom, offset}]}`
representation, the §6.3 operation list and the §6.2 canonicalization rules are
all specified; the open question U1 must answer is the **atom ordering key**
("atoms are sorted by canonical serialized term order"), which requires
`Serialize.encode/1` to be stable on the terms that can appear as atoms — a
dependency on §4's codec work.

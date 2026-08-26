# `primitive` type declarations for the machine base types

**Status:** Approved (design), ready for planning.
**Date:** 2026-07-10
**Batch:** Std hygiene (2 of 2; follows
`2026-07-10-group-decorator-placement-design`, and adopts its above-`mod`
`@group` form for the new modules).

## Problem

`Int`, `Float`, and `Binary` are the three irreducible machine base types. In
the dependent pipeline they resolve through **hardcoded name-magic** in the
elaborator:

```elixir
# lib/cure/elab/declarations.ex
defp primitive_type("Int"),    do: {:int_type}
defp primitive_type("Float"),  do: {:float_type}
defp primitive_type("Binary"), do: {:binary_type}
defp primitive_type(_),        do: nil
```

They have **no declaration anywhere in Std**. A user browsing `lib/std/` finds
`Bool`, `Nat`, `Bounded` — all real, documented, inspectable declarations — but
no `Int`, no `Float`, no `Binary`. The base types the language leans on hardest
are invisible. We want them declared in Std so they can be read, documented, and
inspected like every other type, while still resolving to their primitive Core
nodes (`{:int_type}` / `{:float_type}` / `{:binary_type}`) — not to some new
family or postulate.

### Why not `opaque` or `@extern` (the mechanisms first considered)

- **`opaque type Binary`** creates a *new postulate family* with its own atom,
  resolving to `{:data, :Binary, [], []}`. That is a *different type* from the
  kernel primitive `{:binary_type}`, severed from everything keyed on the
  primitive node — the bitwise/arithmetic delta-globals, literals, and base-type
  conversion rules. It would produce two incompatible "Binary"s. `opaque` is for
  *carrying* an inert payload, not for *being* a machine type.
- **`@extern`** is a function-to-Erlang FFI path; it cannot declare a type.

Neither fits. The mechanism that *does* fit already exists in the tree:
`Std.Bounded` is `@builtin(:bounded) type Bounded indices (n: Nat)` — a visible
Std declaration carrying a marker that wires it to kernel-special semantics.
`Int`/`Float`/`Binary` simply lack their analogue.

## Design

### 1. Surface — a new `primitive` keyword + `@builtin(:tag)` marker

A new statement keyword `primitive`, always paired with an `@builtin(:tag)`
decorator naming the Core node it maps to:

```cure
@group(:core)
mod Std.Int
  @builtin(:int) primitive Int

@group(:core)
mod Std.Float
  @builtin(:float) primitive Float

@group(:core)
mod Std.Binary                       # existing module GAINS the declaration
  @builtin(:binary) primitive Binary
  fn to_binary(...) ...              # existing bridge fns stay
```

`primitive Name` declares an **irreducible machine base type**: no constructors,
not an inductive (distinct from a constructor-less `type`, which is an *empty*
inductive), not a postulate (distinct from `opaque`, a fresh value-carrying
family). The `@builtin(:tag)` names the target node. Exactly three tags are
legal — `:int → {:int_type}`, `:float → {:float_type}`, `:binary →
{:binary_type}`; any other tag on a `primitive` declaration is a declaration
error.

### 2. Wiring — marker-keyed (the three-part `Bool`/`Nat`/`Sigma` pattern)

Resolution keys off the `@builtin` marker, mirroring how `Std.Bool` /`Std.Nat` /
`Std.Sigma` are already seeded-plus-declared-plus-preluded:

- **Seed (the floor).** `Cure.Core.Builtins.seed/1-2` registers the three
  primitive-type bindings (`Int → {:int_type}`, `Float → {:float_type}`,
  `Binary → {:binary_type}`) into every `env0`. This is what actually makes bare
  `x: Int` resolve in *every* context — including the self-compilation of
  `Std.Int` itself, and minimal/synthetic envs. It **replaces** the hardcoded
  `primitive_type/1` clauses. The primitive registry lives on the env alongside
  the existing `builtins` map (`inductive.ex:224-242`,
  `register_builtin`/`builtin`), or a sibling map keyed the same way — the plan
  picks whichever is the smaller change; the behaviour is identical.
- **Declaration (canonical + inspectable).** `@builtin(:int) primitive Int` in
  `Std.Int` is the documented, user-facing source of truth. On elaboration it
  registers/confirms the same binding via its marker; the seeded floor and the
  declaration's marker **must agree** (a look-alike that disagrees is rejected —
  the same consistency contract `Bool`/`Nat` already carry, `program.ex:162-164`
  / `240`).
- **Auto-prelude.** `Std.Int` / `Std.Float` / `Std.Binary` join `@auto_prelude`
  (`program.ex:234`) and `@auto_prelude_types` (`program.ex:240`) so the
  declarations are in scope in every module without `use`, keeping the marker in
  effect and the types discoverable. All three dependent-elaborate cleanly today
  (verified: `Std.Binary` and its `use Std.Bounded` dependency both elaborate
  with no error), so they meet the auto-prelude gate.

`resolve_index_name/2` (`declarations.ex:1287-1289`) then consults the env's
primitive bindings instead of calling `primitive_type/1`, which is **deleted**.

### 3. Std.Binary — wholesale prelude (chosen), with the trade-off noted

Auto-preluding all of `Std.Binary` makes `to_binary` / `from_binary` and `Char`
(its `typealias Char = Bounded(1114112)`) universally available in every module,
alongside the `Binary` type. This is chosen deliberately: those are core
string-surface operations and universal `Char` availability directly serves the
ongoing `Std.String` work (#29). The type itself would resolve via the seed
regardless; preluding the module is what brings the bridge functions along.
(Confirmed at spec review: wholesale, not type-only.)

## Interaction with the sibling spec

The new `Std.Int` / `Std.Float` modules are authored with `@group(:core)` in the
**above-`mod`** position defined by the group-placement spec, so they are born in
the canonical form and never need migration.

## Testing

- **Surface / parse** — `@builtin(:int) primitive Int` parses to a primitive
  declaration carrying the `:int` tag; `primitive` with no `@builtin`, or with an
  unknown tag, is rejected.
- **Resolution** — in a module with *no* imports, `fn f(x: Int) -> Int = x`
  elaborates with type `{:pi, {:int_type}, {:int_type}}` (and the float/binary
  analogues), proving the seed floor resolves bare names without `use`. This is
  the behaviour `primitive_type/1` provided; it must survive its deletion.
- **Marker agreement** — a `primitive` declaration whose `@builtin` tag
  contradicts the seeded node is rejected (consistency contract).
- **Inspection** — `Std.Int` / `Std.Float` appear as real modules; `Binary`,
  `Int`, `Float` are present as declared types a tool/query over the env can
  see (not merely name-magic).
- **Auto-prelude** — a bare module (no `use`) can name `Binary` and call
  `to_binary` / use `Char` (per §3 wholesale choice).
- **Regression** — full suite + Antigen green. No change to the kernel Core
  nodes themselves (they already exist from #2/#3); this spec only changes how
  the *surface names* resolve to them, so the risk surface is the elaborator +
  seeding, not the TCB. If the plan touches `lib/cure/core/*` (e.g. the seed
  lives there), that edit gets the standard TCB gate: red-green + an Antigen
  antibody + full Antigen suite.

## Out of scope

- New operations on `Int` / `Float` (arithmetic already exists as delta-globals;
  fleshing out method surfaces is separate).
- `Binary` literals / byte_size / bit-syntax — the deferred fast-follow in
  `2026-07-10-length-indexed-binary-design`.
- `Char` / `String` restructuring — they already have Std homes
  (`typealias Char`, `String = List(Char)`); untouched here beyond `Char`
  becoming universally available as a side-effect of §3.
- Deleting the classic pipeline (#18) — this is groundwork toward the whole
  stdlib compiling on the dependent pipeline, not that rip-out.

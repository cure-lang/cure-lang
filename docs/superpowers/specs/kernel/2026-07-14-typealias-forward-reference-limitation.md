# Typealias forward-reference limitation — Design note

**Date:** 2026-07-14.
**Status:** resolved 2026-07-17 — explicit aliases participate in the header pass.
**Scope:** the elaborator's type-header pre-pass and the transparent `lift module`
declaration ordering that consumes it.

## 1. Summary

Forward-referencing an explicit **type alias** now works. The type-header
pre-pass registers a body-less alias definition containing its erased
type-parameter telescope and a conservative universe. The normal declaration
pass installs checked bodies, then a dependency-ordered completion pass
re-elaborates aliases from their completed dependencies so final universe levels
are exact. A kernel-driven certification sweep makes the completed chains
available to conversion before function bodies are checked.

This is **out of scope** for the transparent BEAM / macro work, and it does
**not** need fixing for that work: the transparent `lift module` path already
orders the enclosing unit's declarations first, so an alias a lifted module
references is always bound before the lifted module elaborates.

## 2. The limitation

The two-pass elaborator (`Cure.Elab.Program.elaborate_declarations/3`,
`lib/cure/elab/program.ex:1517`) runs a **header pre-pass** before any
constructor body is elaborated:

- `declare_type_headers/2` (`program.ex:1534`) → `Declarations.declare_header/2`
  (`lib/cure/elab/declarations.ex:224`) registers the *header* (name +
  parameter/index telescopes, empty constructor list) of every ctor-bearing
  family up front. That is what allows a field type to name a sibling declared
  later, or a mutually-recursive partner — standard `data`-block scoping.

The pre-pass is deliberately narrow. Its own contract (`declarations.ex:217-222`)
states that only the ctor-bearing enum / record / indexed families need it,
because *their bodies* are what reference siblings; and:

> Everything else — **aliases**, opaque carriers, interfaces, primitives,
> functions — is returned unchanged; their forward-reference cases are out of
> scope for this pass and handled (or rejected) in the main pass exactly as
> before.

Concretely, `declare_header/2` for a `:type_annotation` node
(`declarations.ex:260`) registers a header **only** when the right-hand side is a
single-variant enum; a genuine alias (`type MyNat = Nat`) "binds a nullary def,
not a ctor-bearing family, so it is left to the main pass" (`declarations.ex:256`).

Result: an alias is not visible until the main pass reaches its declaration in
source order. Elaborating a use of the alias before that point is either an
unresolved-type error or a mis-resolution — the alias has no forward-reference
protection an inductive would get.

### Failing shape (illustrative)

```
# A lifted/independent unit whose body refers to `Message` …
fn handle(m: Message) -> State = ...

# … while `Message` is only declared afterwards, as an alias:
type Message = Tick
```

Were these elaborated in this order, `handle`'s signature would resolve
`Message` against an environment that has not yet bound the alias. An inductive
in `Message`'s place would survive (its header is pre-declared); an alias does
not.

## 3. Why it is out of scope here

This is general elaborator behaviour that predates the macro / transparent-BEAM
work and is independent of it. It is a property of how aliases are registered,
not of macro expansion, `lift module`, or `beam_ops`. Nothing in the transparent
BEAM plan changes the pre-pass or the alias registration path, and fixing it
would be a change to the elaborator's scoping model (an untrusted-layer change,
still TCB-delta-zero, but a distinct piece of work with its own design and
tests). It is therefore recorded as an accepted limitation rather than folded
into any macro slice.

## 4. Why the lifted-module case does not need it fixed

A lifted module produced by a transparent macro is not free-floating: it is
generated *inside* an enclosing compilation unit whose declarations **lexically
precede** it in the source. `LiftModule.inherit_scope/2`
(`lib/cure/compiler/lift_module.ex:41`) makes that lexical order explicit in the
generated declaration stream:

```elixir
# Inherited declarations come FIRST: they lexically precede the lifted module
# in the source, and the template's own declarations refer to them (a
# `typealias Message = Tick` needs `Tick` already bound — unlike an inductive,
# a type alias has no forward-reference pre-pass).
declarations = inherited ++ request.declarations
```

Because the enclosing unit's declarations are prepended to the lifted unit's own
declarations, any alias the lifted module references is already bound by the
time the lifted module's declarations elaborate. The forward-reference case
never arises for lifted modules — the ordering sidesteps it entirely, without
depending on the pre-pass covering aliases.

Name shadowing is handled in the same function: an inherited declaration whose
name is also defined inside the lifted module (`taken_names/1`,
`lift_module.ex:60`) is dropped from the inherited set, so the lifted module's
own definition wins and no duplicate binding is introduced.

## 5. What a real fix would require (not obligated)

Should forward-referencing an alias ever need to work in the *general* case
(outside the lifted-module ordering), the change is to extend the header
pre-pass to register alias headers too:

- In `Declarations.declare_header/2`, add a clause that registers a genuine
  `type A = <rhs>` alias's name as a type-level binding before the main pass,
  mirroring how single-variant enums are pre-declared today.
- The alias's RHS may itself forward-reference; registering only the *name*
  (deferring RHS elaboration to the main pass) matches the inductive header
  treatment and avoids ordering hazards.
- Add differential tests: an alias used before its declaration at module scope
  (currently rejected) should elaborate identically to the same program with the
  alias moved earlier.

This was implemented as a general elaborator improvement. Explicit `typealias`
nodes carry a parser metadata marker so the header pass cannot confuse them with
the deliberately ambiguous single-constructor spelling `type X = Y`. Alias
cycles are rejected before certification; unknown targets retain their ordinary
unresolved-name error.

## 6. Verification

The lifted-module ordering is the operative guarantee and is exercised by the
transparent object suites (a `lift module` whose callbacks reference an
enclosing-unit alias elaborates through the ordinary checker). No new test is
required for *this note*; it records existing behaviour. If §5 is ever taken up,
its differential tests become the red fixtures for that separate work.

## 7. References

- `lib/cure/elab/program.ex:1512-1541` — two-pass elaboration + header pre-pass.
- `lib/cure/elab/declarations.ex:205-270` — `declare_header/2` contract; aliases
  explicitly out of the pre-pass (`:217-222`, `:256`).
- `lib/cure/compiler/lift_module.ex:41-58` — `inherit_scope/2`; inherited
  declarations prepended so aliases are bound before the lifted module.
- Pre-pass origin: commit `de77530f` (Elaborator: type-header pre-pass for
  forward/mutual type declarations).

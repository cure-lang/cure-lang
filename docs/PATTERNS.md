# Cure Pattern Matching Reference
This document is the authoritative reference for Cure's pattern
matching. It covers every pattern shape accepted by `match`, `let`,
multi-clause function heads, comprehension generators, and `try ...
catch` clauses.

## Pattern elaboration and Erlang mapping

There is no separate classic pattern compiler. `Cure.Elab.Elaborator`
checks every pattern form through one dependent path, preserving narrowed
bindings, constructor identities, equality constraints, and source spans.
After kernel validation and evidence erasure, `Cure.Elab.Emit` lowers the
runtime pattern to Erlang abstract forms. The table below describes that final
shape for compiler-output and Elixir-side tooling.

- `{:variable, _, "_"}` lowers to `{:var, L, :_}` (wildcard).
- `{:variable, _, name}` on first occurrence lowers to
  `{:var, L, :V_name}` and adds `name` to the scope. On a repeat it
  lowers to a fresh variable and emits an equality guard against the
  original binding.
- `{:pin, _, [{:variable, _, name}]}` lowers to a fresh variable plus
  an equality guard against the pre-existing binding for `name`. If
  `name` is unbound at that point, elaboration fails with the structured
  unbound-pin diagnostic.
- `{:literal, [subtype: :integer], n}` lowers to `{:integer, L, n}`.
  Similarly for `:float`, `:symbol`, `:boolean`, `:null`, and `:char`.
  Strings elaborate as `List(Char)` patterns; byte literals lower through
  `Std.Binary`.
- `{:tuple, _, elems}` recurses into every child as a pattern and
  lowers to `{:tuple, L, forms}`.
- `{:list, [cons: true], [head, tail]}` lowers to
  `{:cons, L, head_form, tail_form}`.
- `{:list, _, elems}` (without `cons`) lowers to the Erlang cons
  chain `{:cons, L, e1, {:cons, L, e2, ... {nil, L}}}`.
- `{:map, _, pairs}` lowers to a map pattern. **Each field uses
  `map_field_exact`**, so the pattern requires the key to be present
  in the subject.
- `{:function_call, [record: true, name: T], fields}` lowers to a
  map pattern with `__struct__ := :t` plus one `map_field_exact`
  entry per field. Field-punning shorthand (bare `{:variable, _,
  name}` inside `fields`) expands to `name: name`. Unspecified fields
  are ignored (open matching).
- `{:function_call, [name: Tag], args}` with a PascalCase `Tag` is an
  ADT constructor pattern. It lowers to a tagged tuple
  `{:tuple, L, [{:atom, L, tag} | child_forms]}`, recursing into each
  argument as a pattern.
- `{:unary_op, [operator: :-], [literal]}` in a pattern compiles to
  the negated literal (so `-5` matches the integer `-5`).

## Binding and scope

Pattern variables are introduced into the enclosing scope and become
available to:

- The arm's `when` guard (and to any injected pin/repeat guards).
- The arm's body.
- The rest of the block (for `let` destructuring).

In multi-clause functions each clause starts from a fresh empty
scope, so names can be reused freely across clauses.

## Map keys in pattern position

Map keys in a pattern must be literal atoms. A bare identifier at a
map-key position is permitted as an abbreviation: `%{x, y}` expands to
`%{x: x, y: y}`. Any non-atom-literal, non-identifier expression
triggers the general type-mismatch diagnostic `E093`.

## Record fields

Record patterns resolve against the record's declared schema when the
type is known. Referring to a field that is not in the schema, or
supplying a sub-pattern whose type is incompatible with the declared
field type, emits `E022` as an error.

## Exhaustiveness

A missing reachable constructor -- at the top level of the scrutinee
or at a tuple element position -- is rejected under `E118` (Pattern
Coverage). This is a compile-time error: it blocks compilation. There
is no separate flat/nested pass; both cases are reported under the
same code.

## Injected guards

Dependent pattern elaboration records equality constraints when a pattern
uses:

- `^x` (pin operator).
- A variable that occurs more than once in the same pattern.

These are conjoined with the user-written `when` clause via
`andalso` before being emitted into the Erlang abstract form.

## What is not supported

- Range patterns (`1..10 -> ...`). Compile-time rejected.
- Bitstring patterns with sized or typed segment specifiers (`x::16`,
  `x::float`, `x::utf8`, ...). The parser accepts the full `<<...>>`
  specifier-chain grammar, but the elaborator only lowers plain 8-bit
  byte segments plus a single trailing unsized tail (`rest::binary`);
  anything richer is rejected under `E093`. See `docs/BINARIES.md`.

See `docs/LANGUAGE_SPEC.md` §"Pattern Matching" for the surface
syntax, `examples/destructuring.cure`, `examples/json_tree.cure`,
and `examples/pattern_guards.cure` for end-to-end programs, and
`Std.Match` for stdlib helpers.

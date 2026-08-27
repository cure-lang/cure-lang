# Binaries

Reference guide for Cure's binary literal and pattern syntax.
Introduced in v0.20.0 (segment AST, codegen, printer) and extended in
v0.21.0 (type-checker bindings). The dependent-pipeline rewrite that
removed the classic checker/codegen (see `CHANGELOG.md`) narrowed what
the elaborator actually lowers: today only plain byte segments and a
single trailing unsized tail elaborate successfully, in both
construction and pattern position. The richer specifier grammar below
still parses, but a sized or typed segment is rejected as unsupported
rather than silently mislowered.

## Syntax

A binary literal is written between `<<` and `>>`, with segments
separated by commas. Every segment has the shape:

```
value [:: specifier_chain]
```

The specifier chain is a hyphen-joined list of specifiers (mirroring
Elixir's grammar) and is accepted by the parser:

- **Type**: `integer`, `float`, `bits`, `bitstring`, `bytes`, `binary`,
  `utf8`, `utf16`, `utf32`.
- **Signedness**: `signed`, `unsigned`.
- **Endianness**: `big`, `little`, `native`.
- **Size**: `size(expr)`. A bare integer specifier is shorthand for
  `size(<integer>)`.
- **Unit**: `unit(n)`.

## What actually elaborates

The elaborator only lowers two segment shapes:

- A **plain segment** with no specifier chain: a bare literal integer
  (0-255) or a bare variable/`_`, each consuming exactly one byte.
- A single **trailing unsized tail** (`rest::binary`, `::bytes`,
  `::bitstring`, or `::bits`, with no `size`), binding the remaining
  bytes as a `Bitstring`.

Any other segment -- a size (`x::16`), a numeric type other than a
plain byte (`x::float`), a text type (`x::utf8`), explicit signedness,
endianness, or `unit(n)` -- is rejected under `E093` ("Binary segment
form is not supported") in both binary literals and binary patterns.
This applies uniformly to `match` arms, multi-clause function heads,
and `let` destructuring.

## Examples

```cure
fn first_byte(buf: Binary) -> Int =
  match buf
    <<b, _rest::binary>> -> b
    <<>> -> 0
    _ -> 0
```

## Pattern positions

Binary patterns work in every destructuring position:

1. `match` arms.
2. Multi-clause function heads: `fn parse(buf: Bitstring) -> Int | <<a, _rest::binary>> -> a | <<>> -> 0`.
3. `let` bindings: `let <<tag, body::binary>> = buf`.

A binary comprehension generator (`for <<b <- buf>>`) is supported for
a single bare, unsized, untyped binder; sized or typed generator
segments are rejected the same way as sized/typed match segments.

## Type-checker semantics

A plain byte segment's bound variable has type `Int`; a trailing
unsized tail's bound variable has type `Bitstring`. There is no
byte-size refinement propagation for the tail today.

## Exhaustiveness

Binary matches desugar to guarded byte-offset reads (length and
per-byte equality checks) rather than an inductive case split over
enumerated shapes, so they are open by construction. There is no
per-shape coverage checker or witness synthesis; a binary `match`
without a trailing wildcard/variable catch-all is rejected outright
under `E119` ("Binary match needs a catch-all").

## Codegen

Binary patterns lower to guarded `byte_size`/`byte_at`/`drop_bytes`
calls over `Std.Binary` rather than to Erlang bit-syntax match
instructions directly; construction of a plain-byte literal lowers to
`Std.Binary.of_bytes/1` over the segment values.

See also: `docs/PATTERNS.md` for the broader destructuring
reference and `docs/LANGUAGE_SPEC.md` for the full grammar.

# Cure Standard Library Reference

The standard library is self-hosted: every module below is written in Cure
itself under `lib/std/` and compiled by `mix cure.compile_stdlib` (or
`cure stdlib`). Each compiled module produces a loadable `:"Std.<Name>"`
BEAM module; external calls use `@extern(:module, :fun, arity)` to punch
through to `:erlang`, OTP, or the dedicated `Cure.*.Builtins` helpers in
`lib/cure/stdlib/`.

## Viewing the stdlib

- **On the web** -- [cure-lang.org/stdlib](https://cure-lang.org/stdlib) renders every `Std.*` module from the same `.cure` sources, grouped by topic. A single module page lives at `/stdlib/<Module>` with a GitHub "View source" link and anchored entries for every public function / type / protocol.
- **Locally** -- `cure doc` produces the same layout under `_build/cure/doc/`. The tree is self-contained (HTML + one CSS + one JS file) so the output can be zipped up or served from any static host. See [`docs/DOC.md`](DOC.md) for the configuration reference.
- **In the REPL** -- `:doc Std.List.map` pulls the `##` comments and renders them as ANSI using `Cure.REPL.Markdown`.

Module and API documentation is authored in the `##` comments beside the
declarations in `lib/std/*.cure`. The generated module pages are authoritative;
this page is the orientation guide and topic map. Examples embedded in source
comments are checked by `mix cure.check.docs` and the stdlib compiler.

The documentation below is organised by topic:

- [Core utilities](#core-utilities)  -- `Std.Core`, `Std.Io`, `Std.Show`,
  `Std.System`, `Std.Test`.
- [Containers and data](#containers-and-data)  -- `Std.List`, `Std.Map`,
  `Std.Set`, `Std.Bounded`, `Std.Vector`, `Std.Tuple`, `Std.Option`,
  `Std.Result`, `Std.Match`.
- [Interfaces](#interfaces)  -- `Std.Equatable`, `Std.Comparable`,
  `Std.Show`, `Std.Semigroup`, `Std.Functor`.
- [Value-shaped modules](#value-shaped-modules)  -- `Std.String`,
  `Std.Math`, `Std.Regex`, `Std.Json`, `Std.Time`.
- [Types and proofs](#types-and-proofs)  -- `Std.Equivalent`,
  `Std.Proof`.
- [Concurrency and OTP](#concurrency-and-otp)  -- `Std.Actor`,
  `Std.Fsm`, `Std.Process`, `Std.Supervisor`, `Std.App`.
- [Lazy evaluation and randomness](#lazy-evaluation-and-randomness)  --
  `Std.Iter`, `Std.Gen`.
- [Replicated data types](#replicated-data-types)  -- `Std.CRDT`.

All source line references point at `lib/std/<module>.cure`.

## Module groups and selective preload

Every stdlib module carries a single module-level decorator near the top
of its source that assigns it to a group:

```cure path=null start=null
@group(:collections)
```

The compiler lowers `@group(:g)` to a `-group([:g]).` BEAM attribute, so
the tag is inert metadata rather than an exported function.

`Cure.Stdlib.Preload` scans `lib/std/*.cure` at Elixir compile time
(tracked via `@external_resource`), builds a static
`%{module => group}` map, and exposes it through
`Cure.Stdlib.Preload.module_groups/0`. The REPL, host applications,
and test fixtures can then ask for a subset of the library via
`Cure.Stdlib.Preload.stdlib_modules/1` or the identically-named
`:kind` option on `Cure.Stdlib.Preload.preload/1`:

- `:none` (the default everywhere) -- nothing is loaded.
- `:all` -- every stdlib module is preloaded, matching the historical
  behaviour of the CLI entry points (`cure run`, `cure compile`,
  `mix cure.check.examples`).
- a single group atom, or a list of them -- the union of the matching
  modules is loaded.

Known groups and their current membership (also the source of truth
for `Cure.Stdlib.Preload.known_groups/0`):

- `:core` -- foundational types, operators, interfaces, proofs, syntax, and
  primitive homes, including `Std.Core`, `Std.Equivalent`,
  `Std.Equatable`, `Std.Comparable`, `Std.Show`, `Std.Functor`,
  `Std.Semigroup`, and `Std.Proof`.
- `:collections` -- `Std.List`, `Std.Map`, `Std.Set`, `Std.Vector`,
  `Std.Tuple`, `Std.Match`, `Std.NonEmpty`, `Std.Optic`, `Std.Data.Suffix`,
  `Std.Dynamic`, and `Std.Iter`.
- `:text` -- `Std.String`, `Std.Regex`, the `Std.Regex.Syntax` family,
  and `Std.Json`.
- `:numeric` -- `Std.Math` and `Std.Decimal`.
- `:system` -- `Std.Io`, `Std.System`, `Std.Time`, `Std.Measurements`,
  `Std.App`, and `Std.CRDT`.
- `:concurrency` -- the typed `Std.Otp` algebra and its raw boundary,
  plus `Std.Actor`, `Std.ActorBehavior`, `Std.Beam`, `Std.ExitReason`,
  `Std.Fsm`, `Std.Process`, and `Std.Supervisor`.
- `:option` -- `Std.Option`, `Std.Result`.
- `:test` -- `Std.Test`, `Std.Gen`.
- `:network` -- reserved; no `lib/std/*.cure` module currently declares this
  group.

Groups are **selection tags only** — they say *which* modules a `kind:`
pulls in, never in what order. Compile order and load closure are automatic:
the build derives them from the dependency graph (`Cure.Compiler.DepGraph`
— `use` edges order compilation; `use` + qualified-call edges define the
runtime closure), and `preload(kind:)` expands a selection to everything it
needs at runtime, so e.g. selecting `:collections` also loads the `:core`
modules its members call. See
`docs/superpowers/specs/tooling/2026-07-08-auto-import-order-design.md`.

The REPL reads a `.cure.repl.toml` file at startup (project-local
wins over the home-wide fallback) and threads the resolved kind
through `Cure.Stdlib.Preload.preload/1` and
`Cure.REPL.Docs.default_uses/1`. See `docs/REPL.md` for the TOML
shape and worked examples.

## 0.34 module map

This is a curated map for choosing a module; it is deliberately not an API
inventory. Signatures, member descriptions, examples, and source links belong
in the generated module pages so they cannot drift from `lib/std/*.cure`.
Modules added or substantially reshaped by the dependent pipeline include:

- **Primitive and bootstrap homes** -- `Std.Int`, `Std.Float`, `Std.Char`,
  `Std.Atom`, `Std.Binary`, `Std.Bool`, `Std.Unit`, and `Std.Nat`.
- **Interfaces and operators** -- `Std.Equatable`, `Std.Comparable`,
  `Std.Show`, `Std.Semigroup`, `Std.Functor`, `Std.Arithmetic`,
  `Std.Literal`, and `Std.Operators`. `Std.Arithmetic` declares operation
  interfaces, but numeric surface operators still select their primitive
  implementations by operand kind; the callable interface methods are the
  forward-compatible algebra surface.
- **Dependent data** -- `Std.Vector`, `Std.Bounded`, `Std.NonEmpty`,
  `Std.Sigma`, `Std.Tuple`, `Std.Decision`, and `Std.Equivalent`.
- **Proofs and reflection** -- `Std.Proof`, `Std.Proof.Math`, the
  `Std.Proof.Int.*` and linear-arithmetic modules, `Std.Refine`,
  `Std.Telescope`, `Std.Syntax`, and `Std.Syntax.Raw`.
- **Collections and data shape** -- `Std.List`, `Std.Map`, `Std.Set`,
  `Std.Dynamic`, `Std.Data.Suffix`, `Std.Match`, `Std.Optic`, and `Std.Iter`.
- **Text and parsing** -- `Std.String`, `Std.Regex` plus its syntax-parser
  family, and `Std.Json`.
- **Numeric and measurements** -- `Std.Math`, `Std.Decimal`, and
  `Std.Measurements`.
- **Typed BEAM/OTP** -- `Std.Otp`, `Std.Otp.Raw`, `Std.Beam`,
  `Std.ActorBehavior`, `Std.Actor`, `Std.Fsm`, `Std.Process`,
  `Std.Supervisor`, `Std.ExitReason`, and `Std.App`.

## Building the reference

The deployment build runs `cure doc` over `lib/std/*.cure`; the website uses
the same extractor at compile time. Both paths consume only source doc
comments, so a public API change is incomplete until its declaration and its
`##` documentation change together. Run these checks locally:

```sh
mix cure.check.docs
cure doc lib/std -o _build/cure/doc
```

The generated HTML is the complete standard-library reference. This overview
intentionally contains no duplicated function tables.

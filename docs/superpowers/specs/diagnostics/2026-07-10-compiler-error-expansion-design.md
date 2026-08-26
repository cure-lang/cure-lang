# Compiler Error Expansion & Cleanup — Design Spec

> **Status: SUPERSEDED FOR IMPLEMENTATION.** Error quality became a material
> blocker during the 0.34 reflective OTP macro work. The authoritative 0.34
> design is now
> [`2026-07-20-structured-compiler-diagnostics-design.md`](2026-07-20-structured-compiler-diagnostics-design.md).
> This document remains the historical audit that motivated it.

**0.35 integration note (2026-07-17):** this cleanup is the seed of, but not the
complete design for, the shared diagnostic foundation in
[`2026-07-17-cure-native-parser-diagnostics-self-hosting-design.md`](2026-07-17-cure-native-parser-diagnostics-self-hosting-design.md).
On resumption, follow that spec's multi-span, provenance, machine-output, and
typed-hole requirements rather than stopping at this document's original
one-line formatter boundary.

## Motivation

Cure's compiler returns a mix of **payload-carrying** error tuples and
**bare-atom** errors. The bare atoms name a *category* but not the *offending
thing*, so diagnosing a failure means editing the compiler to print the missing
detail, re-running, and reverting — every single time.

Concrete evidence (2026-07-10, stdlib dependent-pipeline survey): five stdlib
modules all failed elaboration with the **identical** top-level error
`{:error, :unknown_global}`. Only after temporarily instrumenting the two
kernel raise sites (`lib/cure/core/kernel.ex` `infer/2` `{:global, name}` and
`check_def/2`) to `IO.inspect` the name did the *actual* causes separate:

| module        | bare error         | real missing name (after instrumentation) | true cause                                    |
|---------------|--------------------|-------------------------------------------|-----------------------------------------------|
| `json.cure`   | `:unknown_global`  | `:String`, then `:Value`                  | missing `use Std.String`; own `Value` type unresolved |
| `iter.cure`   | `:unknown_global`  | `:IterStep`                               | own type referenced before/without registration |
| `set.cure`    | `:unknown_global`  | `:Map`, `:"Std.Map.put"`                  | missing `use Std.Map` + qualified cross-module call gap |
| `access.cure` | `:unknown_global`  | `:Any`                                    | `Any` top type not in scope                    |
| `crdt.cure`   | `:unknown_global`  | `:t`                                       | a type variable leaking as a global            |

Five different root causes, one indistinguishable error. The bare atom cost a
full instrument-run-revert cycle to tell them apart. That cycle is the tax this
spec removes.

## Goals

1. **Every error carries the context needed to act on it** — the offending name,
   a source location where one exists, and (where cheap) an expected-vs-got.
   The reader should not need to instrument the compiler to learn *which* global
   was unknown, *which* definition was duplicated, or *where*.
2. **Uniform shape.** One structured error representation across the elaborator
   and kernel, not the current ad-hoc split between `:bare_atom` and
   `{:tag, payload}`.
3. **A human-facing formatter.** A single renderer turns the structured error
   into a readable diagnostic (offending token, location, hint), so the REPL,
   `mix compile`, and test output all read the same way.
4. **No soundness change.** All of this lives on the *rejection* path. The
   accept path (what the kernel certifies as well-typed) is untouched. This is a
   diagnostics change, not a type-theory change.

## Non-goals

- Rust/Elm-grade multi-span rendering with source snippets and carets. That is a
  later polish layer; this spec stops at "structured payload + one-line
  formatter with a location."
- Changing *which* programs are accepted or rejected. Same accept/reject
  verdicts, better messages.
- Error *recovery* / multiple-errors-per-run. Out of scope; the compiler still
  stops at the first error. (Batch reporting can build on the structured type
  later.)

## Current-state audit (do this first)

Before designing the target shape, enumerate every error return. Sketch of what
the survey already shows:

- **Kernel (`lib/cure/core/*`) — TCB.** Bare atoms dominate:
  `:unknown_global` (×2 sites, drops the name), plus others to enumerate
  (`:not_a_function`, conversion failures, motive failures). These are the
  highest-value fixes because the kernel is where the elaborator's Core output
  actually gets judged, and its errors are the least contextual.
- **Elaborator (`lib/cure/elab/*`) — untrusted.** Mixed. Some already good
  (`{:duplicate_definition, :get_env}`, `{:unsolved_metavariables, :second}`,
  `{:unsupported_index_expr, expr}`); some bare
  (`:match_scrutinee_not_data`, `:unsupported_expression` sometimes with the
  expr, sometimes not).
- **Parser/lexer (`lib/cure/compiler/*`).** Generally have line info already;
  confirm and normalize into the same shape.

Deliverable of the audit: a table of `(module, function, error term, has_name?,
has_location?)` so the expansion work is a checklist, not a hunt.

## Design

### Structured error term

A tagged map (not a bare tuple) so fields are named and optional fields can be
omitted without positional churn:

```elixir
%Cure.Diagnostic{
  code: :unknown_global,        # the stable category atom (unchanged vocabulary)
  name: :Value,                 # the offending symbol, when there is one (else nil)
  meta: [line: 42, ...],        # source location when available (else nil)
  detail: %{...}                # code-specific extras: expected/got, module, etc.
}
```

Rationale for a struct over an expanded tuple like `{:unknown_global, name}`:
the tuple shape is what breaks matchers (see below) and it forces every site to
agree on arity. A struct with a fixed `code` field lets pattern matches key on
`code` while carrying arbitrary extras, and lets old matchers be rewritten
**once** to `%Cure.Diagnostic{code: :unknown_global}` instead of chasing arities.

### Location threading

The kernel operates on Core terms, which today may have dropped the surface
`meta`. Two options, in preference order:

1. **Carry `meta` on the Core `{:global, name}` node** (and other leaf nodes
   that can fail), populated by the elaborator when it emits them. Kernel errors
   then have a location for free. Lower blast radius than it sounds: the meta is
   inert to conversion/normalisation (it is not part of term equality — assert
   this with an Antigen antibody so two terms differing only in meta still
   convert).
2. **Elaborator re-attaches location** by catching the kernel's
   `%Cure.Diagnostic{}` and filling `meta` from the surface node it was checking.
   Keeps the kernel meta-free but only works where the elaborator still has the
   surface node in hand.

Recommend (1) for kernel-origin errors that name a term, (2) as the fallback for
errors raised deep in normalisation where no single surface node maps cleanly.

### Formatter

`Cure.Diagnostic.format/1` → a string:

```
error: unknown global `Value`
  at lib/std/json.cure:56
  hint: `Value` is declared in this module but not yet in scope here;
        if it belongs to another module, add `use Std.<Module>`.
```

Hints are per-`code` and optional. Start with the high-traffic codes
(`:unknown_global`, `:duplicate_definition`, `:match_scrutinee_not_data`).

## Backward-compatibility risk (the real work)

Tests and **Antigen assays match on exact error shapes.** Known matchers that
will break if `:unknown_global` changes shape:

- `lib/antigen/assays/kernel_probe.ex:179` — `matches?(:check_def_unknown, r), do: r == {:error, :unknown_global}`
- `lib/antigen/generators/malformed.ex` — generates `:unknown_global` as an
  expected outcome (multiple sites), `lib/antigen/generators/totality.ex:767`.
- Elaborator/stdlib tests that assert `{:error, :unknown_global}` (e.g.
  `typeclass_tail_elaborates_test.exs` asserts `{:error, :unknown_global}` for
  Show).

**Migration rule:** expand and update matchers in lockstep, per `code`. A single
normalization helper — `Diagnostic.code(result)` returning the category atom —
lets assays assert on the category while ignoring the new payload, so most
matchers become `assert Diagnostic.code(r) == :unknown_global`. Do the helper
first; it makes the rest mechanical and keeps the Antigen vocabulary stable.

## TCB gate

Kernel error sites are in `lib/cure/core/*`. Changing them is TCB-adjacent but
**only on the rejection path** — no accept-path term changes, no new conversions
admitted. Still run the full gate for the touched kernel files: red-green, an
Antigen antibody proving (a) meta on `{:global, …}` does not affect conversion
(two terms differing only in meta still convert), and (b) the expanded errors
still trip the same assays via the normalization helper; then the full Antigen
suite and the full test suite. Because accept/reject verdicts are unchanged, the
oracle fixtures should not move — a moved verdict means the change leaked into
the accept path and must be reverted.

## Suggested phasing

1. **Audit** — enumerate every error return into the `(has_name?, has_location?)`
   table. No code change. (Committable as a doc.)
2. **`Cure.Diagnostic` + `code/1` normalization helper** — introduce the struct
   and the category extractor; no call sites changed yet.
3. **Rewrite Antigen/test matchers** onto `Diagnostic.code/1` while errors are
   still bare (they pass through unchanged) — decouples the matcher migration
   from the payload migration.
4. **Expand elaborator errors** (untrusted, no TCB gate) — start with the bare
   ones (`:match_scrutinee_not_data`, `:unsupported_expression`).
5. **Expand kernel errors** (TCB gate) — `:unknown_global` ×2 first; add name +
   meta.
6. **Formatter + hints** — `format/1`, wire into REPL / `mix compile` / test
   output.

Each phase is independently useful and independently committable; the tax is
paid down fastest by phases 2, 3, and 5's `:unknown_global` case.

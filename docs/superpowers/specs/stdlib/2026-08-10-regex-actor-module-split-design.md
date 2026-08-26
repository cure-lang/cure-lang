# Regex and Actor module-split decision

**Status:** accepted design; implementation is intentionally limited to the
Actor split described below and must remain benchmark-driven.

**Date:** 2026-08-10

## Decision

Do not split `Std.Regex` for elaboration performance now. Split `Std.Actor` only
along the acyclic helper boundaries below, and do not claim that moving source
between modules removes typed-elaboration work.

The post-CharacterLiteral canonical cold baseline is 12.351 seconds:

- `Std.Actor`: 4.821 seconds;
- `Std.Bool`: 1.400 seconds;
- `Std.Fsm`: 0.605 seconds;
- `Std.Regex`: 0.471 seconds.

Regex is no longer a dominant component. Its compile-time syntax implementation
is already separated into `Std.Regex.Syntax.Model`, `.Class`, `.Flags`,
`.Parser`, and `.Emitter`. The remaining 1,443-line runtime module contains a
single dependent chain from `ShapeCode`/`Sem`, through pattern compilation and
evidence, to typed extraction and the public combinators. Splitting that chain
would publish large indexed types across more interfaces and risk making
conversion/interface-loading performance worse for no measured payoff.

## Actor boundary

`Std.Actor` remains both a public macro surface and a 732-line implementation.
The expensive declarations form two cohesive implementation clusters that can
move without creating a reverse dependency on the public macro module.

Create these internal modules:

1. `Std.Actor.Analysis`
   - owns `ReplyInference`, `ReplyTypeInference`, and reply-shape inference;
   - owns handler/query AST normalization helpers;
   - depends only on `Std.Syntax`, `Std.List`, `Std.Option`, and `Std.String`.
2. `Std.Actor.Emit`
   - owns `ActorInitSpec`, initialization derivation, and all
     `emit_actor_*`/GenServer construction helpers;
   - uses `Std.Actor.Analysis` and `Std.ActorBehavior`;
   - never imports `Std.Actor`.
3. `Std.Actor`
   - retains the `actor` and `behavior` syntax families, their expansion entry
     points, and the small orchestration functions that interpret captured
     syntax;
   - uses `Std.Actor.Analysis` and `Std.Actor.Emit` lexically.

The dependency direction is therefore:

```text
Std.Actor -> Std.Actor.Emit -> Std.Actor.Analysis
                         \-> Std.ActorBehavior
```

There is no edge back to `Std.Actor`, so the split introduces no SCC. Helper
definitions receive their new canonical owners once; callers must resolve them
through ordinary `use` imports or explicit qualified references. No alias,
wrapper, duplicate definition, generated-dependency scan, or macro-only runtime
path is permitted.

## Why this split is worthwhile

The primary benefit is change isolation. Edits to syntax-family orchestration
need not invalidate the large emitter interface, while emitter changes have a
smaller semantic publication surface. It also gives profiling stable ownership
labels and makes subsequent shape-directed elaborator work easier to localize.

It is not, by itself, expected to reduce a clean build substantially. The six
dominant Actor functions spend their time in typed elaboration; moving them to
another source file preserves that work. A performance improvement must be
demonstrated by a fresh cold/warm benchmark, not inferred from module size.

## Migration and gates

Migrate in two commits, Analysis before Emit. For each migration:

1. add a focused red test proving the public macro expansion is unchanged;
2. move definitions, deleting them from `Std.Actor` in the same change;
3. assert the canonical dependency graph contains no new SCC;
4. run actor quote goldens and typed actor/compiler suites;
5. run the canonical module-pipeline gate;
6. benchmark all sources and record rebuilt modules and declaration stages;
7. run the complete suite before accepting the second boundary.

The emitted actor-module goldens must remain byte-identical. If moving a helper
changes syntax identity, hygiene, generated identifiers, or emitted BEAM, stop
and fix the canonical ownership issue rather than retaining a compatibility
wrapper.

## Revisit trigger for Regex

Reconsider a runtime Regex split only if a representative post-proof baseline
shows `Std.Regex` above 15% of cold module-check time, or an isolated edit forces
unrelated regex layers to rebuild and costs more than one second. Any future
split should follow the proof architecture (shape, machine, evidence,
extraction, API), preserve an acyclic dependency direction, and measure
interface/conversion cost as well as source elaboration.

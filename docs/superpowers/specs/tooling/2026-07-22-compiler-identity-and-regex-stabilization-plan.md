# Compiler Identity and Dependent Regex Stabilization Plan

**Status:** implementation specification and execution plan

**Date:** 2026-07-22

**Applies to:** module loading, canonical names, dependency graphs, reachability,
totality, emission, macros, dependent local functions, matching, literals,
`Char`, `String`, `Bounded(n)`, large elimination, diagnostics, build isolation,
and the bounded-regex fixture

## 1. Outcome

Make every module, declaration, and global reference carry one canonical
identity from resolution through emission, then stabilize the dependent
language features required by the bounded-regex fixture.

The immediate blocker is:

```text
elaboration succeeds
  -> local `same` is registered as `Module#same`
  -> a closure or emission path asks for bare `:same`
  -> emission cannot find a body
```

The fix is not another emitter fallback. The compiler must establish these
invariants:

1. A source module has one canonical interface per source/dependency hash.
2. A declaration has one canonical key from registration onward.
3. Every ordinary Core global reference contains that canonical key.
4. Lexical visibility and qualified module availability are separate facts.
5. Every closure entry resolves to a body or declared extern before codegen.
6. Every compilation entry point uses one complete dependency graph.
7. Macro-generated syntax uses the ordinary resolver and runtime path.
8. Compiler-boundary failures are rich diagnostics, never raw exceptions.

The bounded-regex fixture is the final acceptance test for this programme, not
the laboratory in which the foundational invariants are discovered.

### Follow-up: foundational module layering and import semantics

After the 0.34 literal and Cure-native JSON migrations, perform a dedicated
module-system design audit. The current bootstrap can expose ambient prelude
interfaces from an older artifact while compiling an earlier foundational
module, and an otherwise reasonable explicit `use Std.List` from `Std.Literal`
can pull later operator/interface dependencies backward into the bootstrap.
This must not remain an order-sensitive convention.

Compare how Swift, Rust, Zig, Idris, and other relevant typed languages define
and load foundational scalar/collection types, inject preludes, own protocol or
trait declarations and implementations, reject or break dependency cycles, and
serialize module interfaces for incremental builds. Specify a Cure layering
model in which:

- canonical type availability is distinct from lexical value imports;
- ambient prelude providers cannot leak stale implementations into an earlier
  bootstrap stage;
- source and cached interfaces obey the same dependency graph;
- foundational aliases such as `String` can be named without importing a later
  convenience module or exposing their representation;
- dependency cycles are diagnosed before elaboration with their exact edge
  provenance; and
- clean and incremental builds produce identical module environments.

Do not solve this audit by adding more filename/order exceptions.

#### One canonical compilation world, not synchronized environment snapshots

The compiler currently permits an elaboration call to carry both an `env` and
a `Context.signature`. Resolution may consult the former while normalization,
conversion, or the kernel consults the latter. This is invalid architecture:
the two snapshots can disagree about an imported definition's body, interface
implementation, canonical identity, or totality certificate.

The literal migration exposed a concrete failure:

```text
Resolve.method_call_checked finds
  Std.Decimal's ExpressibleByDecimalLiteral implementation in `env`

Normalise.nf consults `ctx.signature`
  and sees the implementation as an opaque/uncertified global

Result
  a valid Decimal literal remains a stuck application and is rejected as
  "literal initializer is not a compile-time value"
```

The final model must have three distinct components:

```text
CompilationWorld
  canonical definitions, families, constructors, module interfaces,
  implementations, equations, extern ownership, and certification

LexicalScope
  bare-name bindings, qualified-module availability, direct-import preference,
  and use-site visibility, all pointing into CompilationWorld

LocalContext
  the local dependent telescope and let-bound values only
```

Resolution, elaboration, normalization, conversion, totality, reachability,
and emission must all query the same `CompilationWorld`. `LexicalScope` may
change which canonical keys an authored name can denote, but must never copy,
rekey, or own definition bodies or certificates. `LocalContext` must not retain
an independently mergeable snapshot of global state; if an API carries a world
handle for convenience, it must be the same immutable world identity used by
resolution and every downstream phase.

The temporary 0.34 bridge may replace a stale `Context.signature` with the
current resolved environment immediately before literal normalization. Treat
that operation as a diagnostic compatibility bridge only. It must:

- be isolated behind one named helper rather than open-coded copying;
- assert that every global referenced by the resolved conversion has the same
  canonical definition in both views;
- have a regression where an imported literal implementation and its helper are
  visible and certified during normalization; and
- be removed when `CompilationWorld`, `LexicalScope`, and `LocalContext` are
  separated.

Acceptance properties for the final model:

- it is impossible to construct a phase input where resolution and the kernel
  observe different bodies or certification for one canonical key;
- loading or merging lexical scopes never changes `CompilationWorld` identity;
- clean, cached, incremental, macro-expanded, and REPL elaboration use the same
  world semantics;
- declaration publication produces a new persistent world and all subsequent
  phase inputs refer to that world, rather than requiring pairwise sync calls;
- imported proof and literal-provider normalization is invariant under module
  load order; and
- tests contain no repair of the form `ctx.signature = env` outside the single
  temporary bridge.

## 2. Dependency order

The twenty issue groups form four layers:

```text
identity foundation
  interfaces -> canonical definition keys -> graph -> emission closure
       |                    |                    |
       +--------- macro expansion contract -----+
                            |
dependent-language stabilization
  local functions -> matches -> literals -> Char/String -> Bounded
                            |
proof readiness
  large elimination -> proof-directed probe -> totality/proof closure
                            |
operational readiness
  diagnostics -> isolated gates -> performance -> stabilization gate
                            |
                  dependent regex resumes
```

The MetaM-like tier sits above the corrected resolver. It is not on the critical
path to restoring regex and must not become a second loader or resolver.

## 3. Prior-art findings from local sources

These findings constrain the architecture; Cure does not copy the artifact
formats.

### 3.1 Lean 4: canonical names enter the environment early

Source tree: `/Users/ch/Develop/lean4`.

- `src/Lean/Environment.lean` defines the global environment and
  `importModules`; declarations are keyed by `Lean.Name`, not caller-relative
  aliases recovered by codegen.
- `src/Lean/ResolveName.lean` centralizes global resolution and returns canonical
  declaration candidates while keeping field suffixes separate.
- `src/Lean/Elab/MutualDef.lean` and `src/Lean/Elab/LetRec.lean` assign names and
  declaration ranges while elaborating mutual and local recursive definitions.
- `src/Lean/DeclarationRange.lean` stores ranges by declaration identity.
- `src/Init/Prelude.lean` and `src/Lean/Hygiene.lean` give expansions fresh macro
  scopes and make global resolution available to macro expansion.

Lesson: Core references and declaration metadata share the same canonical key.
Macros may request resolution, but do not manufacture a parallel alias universe.

### 3.2 Agda: interface identity includes source and import hashes

Source tree: `/Users/ch/Develop/agda`.

- `src/full/Agda/Interaction/Imports.hs:getInterface` owns interface loading,
  module-name validation, active import stacks, cycle checks, and visited reuse.
- `src/full/Agda/TypeChecking/Monad/Imports.hs` owns `VisitedModules` and
  transitive imports.
- `src/full/Agda/TypeChecking/Monad/Base.hs` records `iModuleName`, source hash,
  imported-module hashes, and combines them in `iFullHash`.
- `src/full/Agda/TypeChecking/Serialise.hs` serializes an interface instead of
  independently re-elaborating it for each consumer.

Lesson: cache identity is canonical module identity plus source and dependency
identity. A visited module contributes its interface, never an empty environment.

### 3.3 Idris 2: resolved identities survive the whole context

Source tree: `/Users/ch/Develop/Idris2`.

- `src/Core/Context.idr` distinguishes readable names from `Resolved` IDs and
  performs exact context lookup on the latter.
- It records direct `imported` modules separately from `allImported`, which
  avoids repeated TTC loading.
- `src/Idris/ProcessIdr.idr:readModule` consults `allImported`, reads TTC data,
  restores namespace state, and handles Prelude as part of module processing.
- `src/TTImp/ProcessDef.idr` resolves definitions before body, coverage, and
  totality-related processing.

Lesson: source spellings remain metadata; compiler maps and references use
stable resolved identities before downstream analysis.

### 3.4 Racket: binding identity is not textual spelling

Source tree: `/Users/ch/Develop/racket`.

- `racket/src/expander/syntax/binding.rkt` implements identifier equality from
  binding and resolved module-path identity, not symbols alone.
- `expand/context.rkt`, `expand/use-site.rkt`, and `expand/apply-transformer.rkt`
  explicitly manage expansion, definition, and use-site scopes.
- `syntax/api.rkt:syntax-track-origin` preserves origin independently of binding
  identity.

Lesson: `macro_home_source` is legitimate hygiene/provenance metadata, but not a
substitute for dependency discovery or canonical resolution.

## 4. Locked architecture

### 4.1 Canonical definition identity

Use the existing `Cure.Elab.Name` representation:

```text
DefinitionKey = :"Module.Name#definition"
```

An opaque key type may come later. Now, all code must use `Cure.Elab.Name`
constructors/accessors rather than ad-hoc splitting or bare-tail reconstruction.

Every authored, generated, lifted, implementation, dictionary, and extern
declaration receives its key before its signature or body is installed. Forward
references resolve against this predeclared symbol table and are source-order
independent.

Core remains `{:global, key}`, but `key` is canonical for ordinary definitions.
Bare atoms are allowed only for an explicit legacy/kernel primitive allowlist.
Builtin operations continue to resolve through registered definition records.

### 4.2 Canonical module interfaces

The loader owns:

```text
ModuleTable[module_name] = loading(stack) | loaded(interface) | failed(diagnostic)

ModuleInterface = {
  module_name, source_path, source_hash, dependency_hash, interface_hash,
  direct_edges, closure_edges, owned_definitions, exported_definitions,
  externs, type_aliases, interfaces, macro_exports, source_metadata
}
```

There are two distinct views:

- **qualified availability:** loaded modules whose canonical exports can be
  addressed as `Std.Regex.foo`;
- **lexical visibility:** bare candidates introduced by local declarations,
  direct `use`, and ambient Prelude policy.

Loading an interface never itself adds bare names. Transitive dependencies are
usable by canonical Core references without leaking lexical names. This
supersedes the old rule that qualified access itself required `use`; `use` now
means bare-name exposure, while the dependency graph controls availability.

The cache key is `(module_name, source_hash, dependency_hash, compiler_schema)`.
Repeated loading returns the same semantic interface without changing aliases
or visibility. Changed input hashes produce a new generation.

### 4.3 One resolution boundary

```text
resolve_qualified(module_table, "Std.Regex.foo", :value)
  -> {:ok, :"Std.Regex#foo"}

resolve_bare(lexical_scope, "foo", :value)
  -> {:ok, canonical_key} | {:ambiguous, candidates} | :missing
```

Authored syntax, parsed macro output, compiled-macro output, and evaluator
fallback output all enter this boundary.

Delete `env_with_generated_dependencies/2` and its stamped-AST scan after the
migration. Retain `macro_home_source` only for definition-site hygiene,
provenance/expansion traces, and locating the expander interface.

### 4.4 One typed dependency graph

Record edges for:

```text
use_import | qualified_reference | prelude_provider | macro_home |
generated_declaration_owner | interface_provider | extern_owner
```

`use_import` affects lexical visibility. Other edges establish availability,
hashing, compile order, or packaging as appropriate, but do not expose bare
names. The same graph and topological ordering serve incremental, project,
stdlib, bundle, escript, test, and macro compilation. Diagnose missing modules,
duplicates, and cycles before body elaboration. Filename order is irrelevant.

### 4.5 Validated emission closure

Replace “atoms that probably need emission” with:

```text
ClosureEntry = definition(key, body, owner, origin)
             | extern(key, owner, target, origin)

build_emission_closure(env, roots)
  -> {:ok, [ClosureEntry]} | {:error, Diagnostic}
```

`reachable_def_names/2` may temporarily remain as a compatibility projection,
but it returns only canonical existing definitions. Production emitters consume
the validated artifact. Each edge records a predecessor so errors report paths:

```text
RegexFixture#run -> RegexFixture#matches -> RegexFixture#same
```

Emission performs no name guessing. A missing entry reports the originating
Core reference and path, never `ArgumentError`.

## 5. Macro expansion contract

Expansion is recursive and inside-out. Output is scoped, resolved, elaborated,
and kernel-checked by the ordinary K3 path. Generated declarations are
predeclared and published through the same interface machinery as authored ones.

1. Compiled execution and Core-evaluator fallback consume the same syntax packet.
2. Conversion preserves character/string escapes exactly.
3. Both return equivalent metadata-normalized syntax or the same failure class.
4. Siblings receive independent state and disjoint deterministic fresh scopes.
5. Every generated identifier declares definition-site or use-site intent.
6. Provenance is additive metadata and never changes resolution.
7. Generated qualified calls need availability, not a synthetic `use`.
8. Generated code has no macro-specific runtime or emission path.

MetaM is a later client. It receives checked query/publication capabilities, not
raw mutable environment maps, and its output still uses this pipeline.

## 6. Phased implementation plan

Each phase begins with a failing focused test, ends with its gate, and is
committed separately. Do not mix feature work into identity-foundation commits.

### Phase 0 — Freeze and trace the blocker

- Check in the minimal bounded-regex `:same` reproducer.
- Add smaller caller-before-helper and helper-before-caller fixtures.
- Through `dev/trace.ex`, capture registered keys, Core globals, graph edges,
  totality/reachability inputs, closure paths, and emitted names. Do not create a
  second trace utility.
- Record cold/warm time for the fixture and stdlib.
- Assert at the earliest boundary where a noncanonical ordinary global appears.

Exit: the first stage that loses `Module#same` is deterministic and named.

### Phase 1 — Canonical qualified-module resolution

- Make the interface table the sole source for qualified resolution.
- Resolve `Std.Regex.foo` without exposing bare `foo`.
- Make interface loads hash-keyed and idempotent.
- Route authored/generated qualified calls identically.
- Model Prelude providers as ambient edges without direct-import preference.
- Delete `env_with_generated_dependencies/2` and stamped-AST scans.
- Narrow `macro_home_source` to its three legitimate roles.

Regressions: duplicate/diamond loads; transitive qualified calls; qualified-only
does not expose bare names; direct `use` does; transitive dependencies do not;
authored/generated calls produce identical Core; `Char = Bounded(1114112)`
remains definitionally equal under every merge order.

Gate: loader, import, resolution, macro-use, and incremental tests.

### Phase 2 — Canonical definition identity everywhere

- Predeclare every local signature under `Module#name` before bodies.
- Canonicalize local, lifted, implementation, dictionary, generated, and extern
  references at registration/resolution.
- Use the same keys in environments, Core, source metadata, reachability,
  totality, and emission.
- Remove late bare-name guesses and alias recovery.
- Audit/centralize all producers of `{:global, _}`.
- Assert ordinary globals are canonical or explicitly allowed primitives.

Regressions cover helpers before/after callers, mutual recursion, overloads,
imported same-basename names, implementations, and macro-generated callers.

Exit: regex `same` is `RegexModule#same` at every traced stage.

### Phase 3 — Dependency graph completeness

- Record every edge kind from section 4.4.
- Specify each edge's effect on compile order, hashes, visibility, and packaging.
- Migrate all compilation entry points to the shared graph.
- Diagnose missing modules, duplicate identities, and full cycle paths early.
- Include generated and extern owners in packaging closure.

Tests deliberately oppose filename/input and dependency order across clean,
incremental, stdlib, project, bundle, escript, test, macro-home, generated-owner,
qualified-only, missing-module, and cyclic builds.

### Phase 4 — Reachability and code-generation closure

- Implement `build_emission_closure/2` and migrate production emitters.
- Walk all Core through the authoritative traversal substrate.
- Cover local/lifted functions, lambdas, dictionaries, generated and qualified
  calls, proofs, and externs.
- Preserve predecessor paths and macro/source provenance.
- Validate entries before BEAM lowering; make output order deterministic.
- Retire production reliance on `reachable_def_names/2`.

Property: every reachable key resolves to a body or legitimate extern. Mutation
of one body must produce a structured diagnostic naming the key, declaration,
Core reference, and path. No emitter may raise “no such definition”.

### Phase 5 — Macro equivalence and hygiene

- Finish recursive inside-out expansion and K3 re-elaboration.
- Normalize and compare compiled/fallback outputs.
- Preserve escapes exactly and isolate sibling state.
- Validate binding intent for every generated identifier.
- Publish generated declarations through canonical interfaces.
- Preserve expansion provenance for diagnostics, hover, and go-to-definition.

Properties: compiled/fallback equivalence; sibling-order independence; repeated
expansion cannot duplicate/rekey aliases; reflection preserves escapes; authored
and generated equivalents have equivalent Core and closure.

Gate: macro protocol, hygiene, packet, expansion-soundness, and fuzz suites.

### Phase 6 — Dependent local functions

- Lift `where` helpers of arbitrary arity.
- Capture outer parameters, values, erased indices, and quantities.
- Preserve dependent results under abstraction/application.
- Canonicalize lifted keys before body elaboration and reachability.
- Support recursive and mutual helpers independent of order.

Test guards, patterns, proofs, generated helpers, erased captures, and recursion.
Inspect runtime artifacts to ensure erased indices are absent. Gate dependent
codegen, totality, erasure, and relevant Antigen assays.

### Phase 7 — Match, guard, and multi-clause reliability

- Multi-parameter guarded clauses.
- Constructor/literal patterns, including `=` as an ordinary character.
- Nested list/constructor patterns.
- Dependent motives and forced indices.
- Source-order clauses and coverage.
- Type-directed guard equality through `Std.Equatable` where appropriate,
  without weakening dependent elimination.

Test parser, elaborator, kernel, totality, and runtime positives/negatives. Never
relax coverage or equality solely to accept regex.

### Phase 8 — Literal protocols

- Complete natural/integer literal protocol coherence and custom conformances.
- Route negative literals exclusively through the integer protocol.
- Diagnose `Bounded(n)`/`Char` ranges with value, target, range, and span.
- Remove compiler target-type whitelists.
- Load Prelude protocol providers through the graph.

Properties span `Nat`, `Int`, `Char`, bounded domains, and custom types, checking
unique routing, coherence, ranges, and provider-order independence.

### Phase 9 — `Char` and `String` foundation

- Finalize equality, ordering, casing, classification, digit, and hex APIs.
- Keep code-point arithmetic inside `Std.Char`.
- Specify ASCII versus Unicode behavior per operation.
- Specify multi-codepoint Unicode case expansions honestly.
- Test scalar boundaries and invalid inputs.
- Keep externs principled character primitives, never regex hooks.

Compare documented operations with the host Unicode implementation over
generated scalars and pin the Unicode data/version assumption.

### Phase 10 — Indexed `Bounded(n)` robustness

- Preserve it as an indexed inductive.
- Prove compact literals correspond definitionally to `First`/`Next` semantics.
- Complete elimination, coverage, equality, conversion, emission, and erasure.
- Add structural `Bounded(n) -> Bounded(n+m)` and disjoint sum-side injections.
- Expose no unchecked `Nat -> Bounded(n)` conversion.

Properties verify range preservation, sum-side disjointness,
compact/constructor agreement, and erasure. Gate TCB, totality, erasure, and
Antigen.

### Phase 11 — Large elimination and indexed interpretation

- Make `Sem : ShapeCode -> Type` normalize for every constructor.
- Support dependent matching over interpreted shapes.
- Ensure transparent aliases reduce after interface merges.
- Stabilize conversion/unification for nested pairs, choices, options, lists.
- Inspect BEAM erasure of shape indices.

Exit: equivalent alias/import arrangements yield definitionally equal results.

### Phase 12 — Proof-directed data pipeline probe

Before regex, build a small module where an indexed producer returns data plus
erased evidence and a total consumer extracts a typed result solely from that
evidence. Accepted construction makes failure unrepresentable; contextual
remainder evidence mirrors `Encodes`; BEAM inspection proves evidence erasure.
Keep the probe small enough for full Core and closure diagnostic snapshots.

### Phase 13 — Totality and proof-closure reliability

- Use canonical closure for proofs and ordinary functions.
- Include mutual recursion, lifted helpers, generated/qualified calls, and
  quantity-zero dependencies.
- Keep certification stable across repeated and permuted interface loads.
- Diagnose the exact unresolved proof/function and dependency path.

Properties compare closure and certification under declaration/interface merge
permutations.

### Phase 14 — MetaM-like reflective tier

Resume the parked type-aware macro design only after phases 1–5 are green:

- checked declaration/expression reflection;
- controlled type, constructor, interface, and source-context lookup;
- fresh identifiers with explicit scopes;
- structured diagnostics;
- declaration publication through the current interface;
- explicit compile-time effects;
- no runtime interpreter or alternate codegen path.

The API exposes resolver capabilities, not mutable environment maps. Qualified
output never requires macros to emit `use`.

### Phase 15 — Diagnostics hardening

E101 at a caught internal boundary includes, when available: declaration and
canonical key, primary span, bounded failing Core term plus full trace, expected
and inferred types, unresolved global, closure path, macro provenance, and stable
fingerprint.

An unresolved closure entry normally gets its own actionable diagnostic rather
than generic E101. Allocate codes through the existing registry and
producer-fixture process. Fingerprint deduplication retains distinct source and
closure contexts. No raw `ArgumentError`, `KeyError`, or match failure escapes a
supported compile command, and ordinary user errors never become E101.

### Phase 16 — Isolation and performance

- Give integration tests isolated build roots.
- Prevent concurrent Mix/Antigen jobs from deleting shared BEAMs.
- Separate host, stdlib, escript, and test gates.
- Let focused tests reuse valid interfaces instead of rebuilding 131 modules.
- Cache interfaces by source/dependency hash.
- Time parse, graph, interface load, elaboration, certification, closure, emit.
- Split large stdlib modules only when measurements justify an acyclic boundary.
- Check in benchmark commands and tolerant cold/warm baselines for stdlib/regex.

## 7. Foundational property suite

Generate small module/interface models, with shrinking to replayable source:

1. interface load idempotence;
2. environment merge idempotence;
3. merge associativity where conflicts are absent;
4. merge-order invariance of canonical identities;
5. qualified availability does not imply bare visibility;
6. direct `use` exposes bare names; transitive dependencies do not;
7. Prelude ambience does not change direct-import preference;
8. repeated macro expansion cannot duplicate/rekey aliases;
9. resolution is stable under declaration order;
10. every reachable key resolves to a body or legitimate extern;
11. dependency order is independent of filename/input order;
12. compiled/fallback macro execution is equivalent;
13. literal protocol routing is coherent;
14. `Bounded` injections preserve range and side;
15. erased proof/index arguments do not appear in BEAM values;
16. parse/print/reflection preserves identity metadata and literal payloads.

Use public compiler operations where possible; helper-map properties supplement
but do not replace end-to-end laws.

## 8. Test matrix

| Layer | Required evidence |
|---|---|
| parser | spelling, escapes, patterns, provenance |
| resolver | canonical key and visibility decision |
| interface | hashes, exports, edges, idempotence |
| elaborator | canonical Core and dependent type |
| kernel | principled acceptance/rejection |
| totality | complete canonical dependency closure |
| emission | validated closure and BEAM target |
| runtime | expected value; evidence erased |
| diagnostic | registered code, ranges, context, fingerprint |
| property | ordering, merge, engine invariance |

Declaration-order regressions include helpers before/after callers, mutual
recursion, local/imported same basenames, overloads, lifted `where` helpers,
macro-generated callers/callees, qualified generated calls, and extern roots.

## 9. Full stabilization gate

Dependent regex proof work resumes only after one clean run demonstrates:

1. dependency-ordered stdlib build from an empty isolated build root;
2. complete `MIX_ENV=test mix test`;
3. TCB and totality suites;
4. relevant Antigen closure/erasure assays;
5. property suite at CI count with replay artifacts retained;
6. no E101 and no compiler warnings;
7. no bare unresolved keys in Core or emitted closures;
8. no macro-specific module-resolution bridge;
9. Unix/escript smoke test;
10. cold/warm benchmark report without unexplained regression;
11. bounded-regex fixture elaborates, certifies, emits, and runs.

If regex alone then fails, the diagnostic must identify a regex semantic/proof
obligation rather than a missing compiler identity.

## 10. Commit sequence

1. `test(compiler): freeze canonical same emission failure`
2. `refactor(loader): canonicalize qualified module interfaces`
3. `refactor(elab): canonicalize definition identity at registration`
4. `refactor(build): unify compiler dependency graphs`
5. `fix(codegen): validate canonical emission closure`
6. `fix(macros): unify expansion resolution and hygiene`
7. `feat(elab): complete dependent local helpers`
8. `fix(elab): stabilize guarded dependent clauses`
9. `fix(literals): complete protocol-directed literals`
10. `feat(stdlib): finalize char and string semantics`
11. `feat(types): harden indexed bounded operations`
12. `fix(kernel): stabilize indexed interpretation`
13. `test(proofs): add erased evidence pipeline probe`
14. `fix(totality): use canonical proof closure`
15. `feat(macros): add checked reflective elaboration tier`
16. `fix(diagnostics): report canonical closure failures`
17. `test(build): isolate compiler integration gates`
18. `perf(elab): cache and profile module interfaces`
19. `test(regex): restore bounded dependent fixture`

After each commit: focused red/green tests, `git diff --check`, record deliberate
deferrals, never weaken a regression, and never combine a language feature with
a foundational resolver rewrite.

## 11. Required deletions and forbidden fallbacks

Delete `env_with_generated_dependencies/2`, stamped-AST dependency discovery,
late bare-name guessing, alias-dependent emitter recovery, entry-point-specific
sorting, raw missing-definition raises, macro-only resolution/runtime paths, and
shared destructive integration-test build assumptions.

Do not replace them with suffix searches at emission, implicit macro-generated
`use`, source-order retries, regex-specific primitives, unchecked
`Nat -> Bounded(n)`, or E101 wrapping that omits the canonical reference/path.

## 12. Definition of done

Canonical identity is a stable, tested fact at every compiler boundary; the
properties prove merge, ordering, closure, macro, literal, and erasure laws; all
entry points share one graph; diagnostics make invariant failures actionable;
and bounded regex passes the full gate without a macro-resolution bridge or
emitter recovery heuristic.

# Parser-Owned Source Metadata and Semantic Invariance Implementation Plan

> Implement this plan task-by-task. Broad parser span propagation is blocked until Task 7's semantic-invariance gate is green.

**Goal:** Retain exact authored source information through surface elaboration without allowing it to affect compiler verdicts, Core output, erasure, emission, macro identity, or caches; then replace post-parse span inference with parser-owned token ranges.

**Architecture:** Store one typed `Cure.MetaAST.SourceInfo` value under the reserved `:source_info` key. Centralize diagnostic projection and semantic comparison in `Cure.MetaAST.Metadata`. Prove all semantic consumers invariant under recursive source decoration before migrating parser productions, one grammar family at a time, to exact token-owned ranges. Delete the inference bridge only after every reachable family has moved.

**Tech stack:** Elixir, ExUnit, Cure MetaAST/parser/elaborator, existing diagnostic plain/ANSI/JSON/LSP renderers, standard-library and Antigen suites. No new dependency.

## Global constraints

- Preserve compiler accept/reject verdicts, stable diagnostic codes, normalized Core, erasure, and emitted BEAM behavior.
- Keep source information available at surface checking sites; do not globally strip it before elaboration.
- Keep trusted Core span-free. Independently supplied Core remains locationless unless a surface boundary can prove its origin.
- Do not introduce an external AST-to-span side table. Macro copying, capture, substitution, and generation make tuple identity and traversal position unsuitable identities.
- MetaAST subterms can occur inside metadata values. Decoration, traversal, and semantic projection must recurse into them according to `Cure.MetaAST.Conformance`.
- New parser code writes only `:source_info`; it must not dual-write legacy `:span`, `:construct_span`, or role-span keys.
- Never fabricate a span. Missing source information is `nil` or an empty collection; insertion sites use honest zero-width positions.
- Semantic code must not exact-match an entire metadata keyword list. Bind metadata and read named semantic fields after diagnostic fields are ignored.
- Every implementation slice starts with a failing focused test and ends with formatting, warnings-as-errors compilation, focused tests, the verdict corpus, and registry/catalog validation where those runners exist.
- Do not weaken, skip, or replace a failing runner. If the standard-library runner performs a build-only first pass, run it again warm and require the actual test result.
- Commit each task or named sub-slice independently with the proposed commit subject. Do not combine parser-family migrations.

## Known baseline and regression fixture

The mandatory regression fixture is a dependent-pair type whose valid surface node changes only from:

```elixir
{:sigma_type, [binder: "x"], [domain, body]}
```

to:

```elixir
{:sigma_type, [source_info: info, binder: "x"], [domain, body]}
```

At baseline, `Cure.Elab.Declarations.idx_to_core/5` rejects the decorated form because it matches `[binder: bname]` exactly and falls through to `{:unsupported_index_expr, ast}`. The initial audit found 116 literal metadata-list constructions or patterns; the plan must classify pattern positions rather than mechanically rewriting constructions.

## Phase I: Establish semantic invariance

### Task 1: Add the canonical source-information model and recursive semantic projection

**Files:**

- Create `lib/cure/meta_ast/source_info.ex`.
- Create `lib/cure/meta_ast/metadata.ex`.
- Create `test/cure/meta_ast/metadata_test.exs`.
- Modify `lib/cure/compiler/source_spans.ex` only to delegate existing projection calls.

- [ ] Write tests for a `%Cure.MetaAST.SourceInfo{}` containing every specified role: `whole`, `name`, `callee`, `operator`, `operands`, `arguments`, `annotation`, `body`, `pattern`, `guard`, `branches`, `fields`, `opener`, `closer`, and `provenance`.
- [ ] Write recursive projection tests with real AST subterms in metadata values: parameter types, return types, guards, constraints, patterns, and clauses.
- [ ] Prove projection removes `:source_info` and the compatibility keys `:line`, `:col`, `:column`, `:span`, `:construct_span`, `:name_span`, `:callee_span`, `:provenance`, `:source_provenance`, and `:expansion_provenance` at every nested MetaAST node.
- [ ] Prove semantic fields, their values, and their ordering are retained; ordinary structs and opaque payloads remain atomic.
- [ ] Implement `source_info/1`, `put_source_info/2`, `drop_source_info/1`, `strip_diagnostics/1`, `semantic_equal?/2`, and `semantic_key/1` in `Cure.MetaAST.Metadata`.
- [ ] Make `Cure.Compiler.SourceSpans.strip_diagnostic_meta/1` a temporary delegate. Do not change attachment behavior yet.
- [ ] Run:

```sh
MIX_ENV=test mix format --check-formatted
MIX_ENV=test mix compile --warnings-as-errors
MIX_ENV=test mix test test/cure/meta_ast/metadata_test.exs test/cure/meta_ast/conformance_test.exs
```

**Commit:** `feat(meta_ast): centralize source metadata semantics`

### Task 2: Build the recursive sentinel decorator and three-way parity harness

**Files:**

- Create `test/support/meta_ast_source_decorator.ex`.
- Create `test/cure/meta_ast/metadata_invariance_test.exs`.
- Modify `test/test_helper.exs` only if support loading requires it.

- [ ] Implement a test-only decorator that adds distinctive `SourceInfo` values to every conformant surface node, including subterms nested in metadata. Use different sentinel values per node so shallow traversal cannot pass accidentally.
- [ ] For representative Sigma, Pi, refinement, union, record, call, annotation, pattern, and guarded-branch programs, compare three inputs: undecorated, fully decorated, and `Metadata.strip_diagnostics/1` projected.
- [ ] Assert equal accept/reject verdict and stable error category. On success, assert semantic equality of returned surface state and exact equality of normalized Core where the public checking interface exposes it.
- [ ] Add the known Sigma regression first and run it red before changing semantic consumers.
- [ ] Exercise `Cure.Elab.Program.check_ast/1`, `check_ast/2`, and `check_ast_elixir_core/1` as applicable rather than testing only private helpers.
- [ ] Keep diagnostic payload comparison deliberately narrow: ranges may improve, but category and verdict may not drift.
- [ ] Run the focused test and retain the failing Sigma output as the regression evidence.

**Commit:** `test(meta_ast): add recursive source metadata parity harness`

### Task 3: Repair dependent-type lowering without stripping diagnostic context

**Files:**

- Modify `lib/cure/elab/declarations.ex`.
- Extend `test/cure/meta_ast/metadata_invariance_test.exs` and the closest dependent-type elaboration tests.

- [ ] Replace exact Sigma and Pi metadata heads with a bound `meta` variable and explicit reads of `:binder` or `:binders`.
- [ ] Fix every additional exact metadata pattern exposed by the Task 2 cases in this lowering path. Do not add a blanket strip at the entry to elaboration.
- [ ] Add malformed-node tests proving missing required semantic keys are still rejected explicitly after diagnostic metadata is ignored.
- [ ] Require the Sigma, Pi, refinement, and dependent-application three-way parity cases to pass.
- [ ] Run:

```sh
MIX_ENV=test mix test test/cure/meta_ast/metadata_invariance_test.exs
MIX_ENV=test mix test test/cure/elab/declarations_test.exs test/cure/elab/dependent_types_test.exs
MIX_ENV=test mix test test/cure/compiler/source_spans_test.exs
```

Use the actual nearest test paths if the repository names differ; record those resolved paths in the commit message body.

**Commit:** `fix(elab): ignore source metadata in dependent type lowering`

### Task 4: Add a pattern-position metadata lint and classify the repository inventory

**Files:**

- Create `lib/cure/meta_ast/metadata_lint.ex`.
- Create `test/cure/meta_ast/metadata_lint_test.exs`.
- Create `docs/superpowers/specs/parser-source-metadata-pattern-audit.md` if a checked-in classification is needed.

- [ ] Parse compiler source into quoted Elixir and report literal keyword metadata lists only when they occur in pattern position in function heads, `case`, `with`, `receive`, and anonymous-function clauses.
- [ ] Report file, line, node tag where statically recoverable, and the offending pattern.
- [ ] Prove parser construction sites are not false positives.
- [ ] Classify every finding as semantic consumer, diagnostic-only consumer, parser construction, raw-shape validation, or test fixture.
- [ ] Allow temporary semantic findings only through an explicit file-and-line debt list. The list must shrink to zero in Tasks 5 and 6; broad parser propagation remains blocked while it is non-empty.
- [ ] Add a test fixture showing that `{:sigma_type, [binder: binder], children}` is rejected while `{:sigma_type, meta, children}` is accepted.

**Commit:** `test(meta_ast): audit exact semantic metadata patterns`

### Task 5: Make equality, hashing, reflection, formatting, and caches use the canonical projection

**Likely files, confirmed by the audit before editing:**

- `lib/cure/compiler/formatter.ex`
- `lib/cure/compiler/macro_syntax.ex`
- `lib/cure/compiler/macro_validate.ex`
- `lib/cure/compiler/source_spans.ex`
- Macro fuzzing, quoting, incremental compilation, manifest, and cache modules reported by searches for AST equality/hash/key construction.

- [ ] Add focused red tests showing that changing only `SourceInfo` does not change formatter semantic equivalence, macro matching/reflection, validation, deduplication, hashes, manifest identities, or cache keys.
- [ ] Replace every independent list of diagnostic metadata keys with `Cure.MetaAST.Metadata` calls.
- [ ] Route AST-derived equality through `semantic_equal?/2` and AST-derived hashes/keys through `semantic_key/1`.
- [ ] Preserve formatter behavior for source-preserving trivia already governed by its own contract; do not erase trivia merely because diagnostic metadata is ignored.
- [ ] Run formatter, macro syntax, macro validation, quote, fuzz, incremental, and manifest suites discovered by the audit.

**Commit:** `refactor(meta_ast): use canonical semantic projection`

### Task 6: Remove metadata-sensitive patterns from all semantic subsystems

Complete these as three independently reviewable slices. Each slice adds sentinel-decorated cases before replacing patterns.

#### Task 6A: Program and elaboration

- [ ] Audit `Cure.Elab.Program`, `Declarations`, `Elaborator`, resolution, unification, normalization, overload selection, and proof search.
- [ ] Replace exact metadata lists with named semantic-field reads.
- [ ] Prove decoration cannot change resolution candidates, inferred types, constraints, normalized terms, or verdicts.
- [ ] Run focused elaborator, dependent-type, and program suites.

**Commit:** `refactor(elab): make surface metadata semantically inert`

#### Task 6B: Macro transformation and hygiene

- [ ] Audit macro matching, capture, copying, substitution, generation, hygiene, reflection, and expansion-cache identity.
- [ ] Prove authored `SourceInfo` survives copies; generated nodes receive structured provenance without borrowing authored spans.
- [ ] Prove changing source metadata cannot change generated names, expansion shape, hygiene, or cache identity.
- [ ] Run structured macro, actor, FSM, supervisor, application, and macro fuzz suites.

**Commit:** `refactor(macros): make source metadata identity-free`

#### Task 6C: Static checks and trusted boundaries

- [ ] Audit coverage, exhaustiveness, totality, positivity, relevance, erasure, interface generation, code generation, and BEAM emission.
- [ ] Add parity cases for both accepted and rejected programs in each subsystem reached by the surface compiler.
- [ ] Compare exact Core, erasure, interfaces, and emitted forms after removing nondeterministic build metadata already excluded by existing tests.
- [ ] Run kernel, static-analysis, codegen, and BEAM lint suites.

**Commit:** `refactor(core-boundaries): make source metadata semantically inert`

### Task 7: Enforce the semantic-invariance gate

**Files:**

- Extend `test/cure/meta_ast/metadata_invariance_test.exs`.
- Create `test/cure/meta_ast/trusted_boundary_test.exs` if separation improves diagnostics.
- Update the existing verdict corpus fixture and runner only to add coverage, never to change established verdicts.

- [ ] Make the metadata-pattern lint pass with zero semantic debt entries.
- [ ] Add a recursive leak detector over returned Core, certificates, exported interfaces, BEAM forms, and artifact payloads. It must fail on `SourceInfo`, diagnostic spans, provenance frames, or source paths beyond the surface boundary.
- [ ] Run the sentinel decorator over the frozen parser, elaborator, kernel, macros, stdlib, and Antigen verdict corpus. Compare stable category and accept/reject status.
- [ ] Require identical normalized Core, erasure, and emission for accepted baseline/decorated pairs.
- [ ] Require all current diagnostic span tests to remain green; semantic inertness must not be achieved by dropping checking-site context.
- [ ] Run the full gate:

```sh
MIX_ENV=test mix format --check-formatted
MIX_ENV=test mix compile --warnings-as-errors
MIX_ENV=test mix test test/cure/meta_ast test/cure/compiler/source_spans_test.exs
MIX_ENV=test mix test test/cure/elab test/cure/core test/cure/compiler
MIX_ENV=test mix test
```

- [ ] Run the repository's stdlib, examples, and complete Antigen commands exactly as documented in its contributor scripts. Record the commands and outcomes in the design spec.
- [ ] Do not begin Task 8 until every gate above is green.

**Commit:** `test(meta_ast): enforce source metadata invariance`

## Phase II: Move ownership to parser productions

### Task 8: Add token-owned range primitives and compatibility reads

**Files:**

- Create `lib/cure/compiler/parser/range.ex` or the nearest existing parser utility module.
- Modify lexer token/span helpers and parser `expect` helpers only as required.
- Create focused parser range tests.

- [ ] Add red unit tests for `mark(token)`, `through(mark, closing_token)`, `between(first, last)`, and `zero_at(token_or_eof)`.
- [ ] Cover same-line, multiline, Unicode UTF-8 byte/column behavior, synthetic indent/dedent/newline tokens, and EOF insertion positions.
- [ ] Reject or return an explicit error when spans come from different sources; never silently merge them.
- [ ] Introduce `expect_token/2` returning the consumed token and parser state. Retain `expect/2` only as a compatibility wrapper where the token is irrelevant.
- [ ] Make `Metadata.source_info/1` read canonical and legacy shapes during migration. New writes remain canonical-only.
- [ ] Prove no helper scans completed ASTs, searches source text by token spelling, or guesses delimiter width.

**Commit:** `feat(parser): add token-owned source range primitives`

### Task 9: Migrate parser grammar families in vertical slices

Every subtask follows the same acceptance template:

1. add a failing parser producer test asserting the exact `SourceInfo` roles and half-open ranges;
2. add a real compilation failure that consumes one role in its primary/secondary labels;
3. assert fixed-width plain rendering, focused ANSI, JSON, and LSP machine parity;
4. rerun the semantic-invariance gate;
5. remove that family's case from the `SourceSpans.attach/2` migration allowlist and delete its inference helpers;
6. confirm the parser writes no legacy source keys for the migrated nodes.

#### Task 9A: Declarations and annotations

- [ ] Own declaration keyword-through-end `whole`, `name`, `annotation`, and `body` ranges at production time.
- [ ] Cover value/type declarations, signatures, constructors, members, interfaces, namespaces, and visibility forms.
- [ ] Migrate existing annotation/type-application legacy spans rather than preserving dual representations.

**Commit:** `feat(parser): own declaration and annotation ranges`

#### Task 9B: Parameters, calls, and operators

- [ ] Cover explicit, implicit, variadic, typed, and defaulted parameters.
- [ ] Cover call `callee`, ordered `arguments`, exact closer, operator token, and ordered operand ranges.
- [ ] Exercise missing closer/operator diagnostics at honest zero-width insertion sites.

**Commit:** `feat(parser): own parameter call and operator ranges`

#### Task 9C: Patterns, guards, conditions, and branches

- [ ] Cover match patterns, arm arrows, optional guards, bodies, condition expressions, and every authored branch.
- [ ] Preserve sibling ranges so later diagnostics can pair disagreeing branches without reconstructing widths.

**Commit:** `feat(parser): own pattern guard and branch ranges`

#### Task 9D: Records, type applications, and containers

- [ ] Cover record literals/updates, field names and values, type constructors/applications, tuples, lists, maps, and other delimited containers.
- [ ] Assert exact opener and closer ownership, including multiline and nested forms.

**Commit:** `feat(parser): own record type application and container ranges`

#### Task 9E: Macro sections and authored provenance

- [ ] Cover macro invocation, captured authored expressions, definition/template, generated declaration, and parent provenance.
- [ ] Cover actor, FSM, supervisor, and application section boundaries without asking users to edit generated syntax.
- [ ] Use E092 at invocation for generated-only defects while retaining nested provenance in machine data.

**Commit:** `feat(macros): own authored ranges and expansion provenance`

### Task 10: Verify transformations preserve or generate provenance correctly

**Files:** Macro copy/capture/substitution/generation modules identified by Task 6B; focused transformation tests.

- [ ] Prove pure copies retain the complete authored `SourceInfo` unchanged.
- [ ] Prove substitutions retain the substituted authored node's source identity and append parent expansion provenance where required.
- [ ] Prove generated nodes do not claim an authored `whole` range; they identify invocation, template/definition, generated declaration, and parent frames explicitly.
- [ ] Add cross-file provenance tests and JSON/LSP related-information assertions.
- [ ] Run all macro families plus full ExUnit because provenance traverses metadata recursively.

**Commit:** `feat(macros): preserve structured source provenance`

### Task 11: Delete post-parse inference and close the specification

**Files:**

- Delete or reduce `lib/cure/compiler/source_spans.ex` to any still-valid non-inference API, then remove it if unused.
- Modify parser entry points to stop calling `SourceSpans.attach/2`.
- Update both authoritative diagnostic specifications and the source-metadata design spec with evidence.

- [ ] Assert the attachment allowlist is empty, then delete `attach/2`, token-spelling lookup, position lookup, delimiter reconstruction, width guessing, and legacy source-key writes.
- [ ] Search the repository for independent diagnostic-key lists and exact semantic metadata patterns; require zero findings outside deliberate raw-shape fixtures.
- [ ] Search serialized Core, interfaces, artifacts, and diagnostic fixtures for leaked `SourceInfo` or legacy source keys.
- [ ] Run formatting, warnings-as-errors, focused metadata/parser/diagnostic suites, lexer/parser suites, elaborator/kernel suites, macro suites, LSP/CLI suites, complete Antigen, stdlib/examples, and full ExUnit.
- [ ] Compare the final verdict corpus with Task 7's frozen baseline.
- [ ] Measure warm median stdlib and generated-macro compilation against the pre-migration baseline; allow at most 5% wall-time and 10% peak-memory regression.
- [ ] Record exact commands, coverage totals, verdict comparison, leak/lint totals, and performance evidence in the authoritative specifications. Mark this specification implemented only when every gate is satisfied.

**Commit:** `refactor(parser): remove post-parse span inference`

## Definition of done

- `:source_info` is the only source metadata written by new parser code.
- The semantic-pattern lint has zero unwaived findings in semantic code.
- Recursive sentinel decoration changes no compiler verdict, stable category, Core, erasure, emitted form, macro identity, or cache key.
- No trusted Core or artifact contains source metadata.
- Every reachable parser family constructs exact token-owned roles and has producer, exact-range, renderer, machine-parity, and real-path coverage.
- `Cure.Compiler.SourceSpans.attach/2` and all normal-path inference are deleted.
- The frozen verdict corpus is unchanged, all required suites pass, and performance stays within the specified budgets.

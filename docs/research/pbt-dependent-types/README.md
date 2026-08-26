# Research: property-based testing of a dependent type-theory kernel

Reference PDFs gathered while designing the soundness-audit / metatheory-testing
harness for `Cure.Core`. The recurring technique is **"typing rules as
generation rules"** — invert the (bidirectional) type checker to emit well-typed
terms, then assert metatheoretic invariants (subject reduction, conversion
termination, infer/check agreement) on them.

## Copyable structure (build the generator from these)

- **palka-ast11-random-lambda-terms.pdf** — Pałka, Claessen, Russo, Hughes,
  *Testing an Optimising Compiler by Generating Random Lambda Terms* (AST'11,
  DOI 10.1145/1982595.1982615). The original "typing rules → generation rules"
  method; a hand-written type-directed generator that found real GHC bugs. The
  ancestor of both Making Random Judgments (generic goal-directed CLP) and the
  FLOPS'14 uniform-distribution work below.
- **claessen-duregard-palka-flops14-constrained-uniform-data.pdf** — Claessen,
  Duregård, Pałka, *Generating Constrained Random Data with Uniform Distribution*
  (FLOPS'14). The alternative lineage: FEAT size-indexed enumeration + predicate
  inversion + bounded-backtracking near-uniformity. Not goal-directed; useful for
  the enumeration substrate and distribution knobs, not the well-typed-term core.
- **making-random-judgments-esop15.pdf** — Fetscher, Claessen, Pałka, Hughes,
  Findler, *Making Random Judgments: Automatically Generating Well-Typed Terms
  from the Definition of a Type-System* (ESOP'15). Derives the generator
  directly from the typing-rule definition — the closest blueprint.
- **quickchick-foundational-pbt-itp15.pdf** — Paraskevopoulou, Hriţcu, Dénès,
  Lampropoulos, Pierce, *Foundational Property-Based Testing* (ITP'15,
  DOI 10.1007/978-3-319-22102-1_22). The trust layer: a "set of outcomes"
  semantics for generators, letting you prove a generator is sound (only valid
  outputs) and complete (reaches every witness) without probabilistic reasoning.
  Foundation under the POPL'18 derivation mechanism.
- **quickchick-inria-project-proposal.pdf** — a 5-page INRIA project/grant
  proposal ("QuickChick: Property-Based Testing for Coq"). Motivation and
  objectives only, no algorithms. Kept for context; its mechanics live in the
  POPL'18 and ITP'15 papers above.
- **generating-good-generators-inductive-relations-popl18.pdf** — Lampropoulos,
  Paraskevopoulou, Pierce, *Generating Good Generators for Inductive Relations*
  (POPL'18, DOI 10.1145/3158133). The QuickChick derivation mechanism that turns
  an inductive relation (e.g. a typing judgment) into a sound+complete generator
  — the theory behind "derive the generator from the rules."
- **well-typed-not-useless-popl24.pdf** — *Generating Well-Typed Terms That Are
  Not "Useless"* (POPL'24). Makes generated terms actually use their bindings so
  tests aren't trivially passing.
- **hiking-trip-generators-stlc.pdf** — *A Hiking Trip Through the Orders of
  Magnitude: Deriving Efficient Generators for Closed Simply-Typed Lambda Terms
  and Normal Forms*. Efficiency: interleave generation with type inference.

## Dependent-type specifics (frontier + directly on our TCB)

- **generic-bidirectional-typing-dtt.pdf** — *Generic Bidirectional Typing for
  Dependent Type Theories* (2023). The bidirectional rule structure to invert;
  our kernel is already bidirectional (`infer`/`check`).
- **certify-conversion-checker.pdf** — *What does it take to certify a
  conversion checker?* (2025). Directly about a `conv.ex`-style checker — one of
  our trusted components.
- **type-level-pbt.pdf** — *Type-level Property-Based Testing* (TyDe'24).
  PBT with dependent types / state machines.

## Takeaway for Cure

No turnkey **dependent** term generator exists — efficient dependently-typed
generation is an open problem. Copy the *structure* (bidirectional rules →
generator) from Making Random Judgments / Pałka, but start **schema-directed**
(e.g. "generate a recursive fn; assert it certifies iff it terminates";
"generate an indexed family; assert positivity rejects negative occurrences")
and grow toward general type-directed generation as capabilities land.

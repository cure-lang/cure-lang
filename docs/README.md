# Cure Documentation Index

This directory holds the prose documentation for Cure. The generated API
reference lives on [HexDocs](https://hexdocs.pm/cure) and on the website; the
files here are the narrative guides, references, and design notes.

Start with [`GETTING_STARTED.md`](GETTING_STARTED.md) if you are new, then
[`TUTORIAL.md`](TUTORIAL.md). [`GLOSSARY.md`](GLOSSARY.md) defines the terms
used throughout.

## Learning the language

- [`GETTING_STARTED.md`](GETTING_STARTED.md) -- from an empty directory to a
  compiled, running, tested project: toolchain install, stdlib resolution,
  `Cure.toml`, and the `check` / `compile` / `run` / `test` loop.
- [`TUTORIAL.md`](TUTORIAL.md) -- fourteen short chapters across the language.
- [`GLOSSARY.md`](GLOSSARY.md) -- the vocabulary, for newcomers.
- [`LANGUAGE_SPEC.md`](LANGUAGE_SPEC.md) -- syntax, keywords, operators, all
  constructs (the authoritative surface reference).
- [`LANGUAGE.md`](LANGUAGE.md) -- the formal description of the language.
- [`TECHNICAL_OVERVIEW.md`](TECHNICAL_OVERVIEW.md) -- a high-level tour of the
  compiler and runtime.

## The type system and proofs

- [`TYPE_SYSTEM.md`](TYPE_SYSTEM.md) -- dependent bidirectional checking,
  indexed families, quantitative binders, conversion, and erasure.
- [`DEPENDENT_TYPES.md`](DEPENDENT_TYPES.md) -- indexed-family and proof
  programming guide.
- [`PROOFS.md`](PROOFS.md) -- proof authoring: `proof chain`/`because`, `have`,
  `rewrite`, `simplify`, `induction`, generated defining equations.
- [`KERNEL.md`](KERNEL.md) -- the trusted dependent Core kernel.
- [`SOUNDNESS.md`](SOUNDNESS.md) -- the written soundness argument for the
  kernel, mapping each lemma to its executable Antigen assay.
- [`CONFLUENCE.md`](CONFLUENCE.md) -- confluence of the Core reduction relation
  (the Agda `proof/` development).
- [`MATCH.md`](MATCH.md) -- the `match` construct.
- [`PICKUP.md`](PICKUP.md) -- the `pickup` construct.
- [`PATTERNS.md`](PATTERNS.md) -- structural patterns, guards, pins, and
  pattern-valued `let`.
- [`BINARIES.md`](BINARIES.md) -- Erlang-style binary pattern matching.

## Language features

- [`MACROS.md`](MACROS.md) -- `macro` containers, syntax rules and holes,
  `becomes` / `computed by` / `syntax family`, `Std.Syntax`, and self-proving
  `example` / `explain`.
- [`BIND_PIPE.md`](BIND_PIPE.md) -- the binder pipe `|x|>`.
- [`FFI.md`](FFI.md) -- the `@extern` foreign-function interface.
- [`FSM_GUIDE.md`](FSM_GUIDE.md) -- FSM definition, compilation, runtime, and
  verification.
- [`SUPERVISION.md`](SUPERVISION.md) -- typed actors, `sup` containers, and the
  Melquiades Operator.
- [`APP.md`](APP.md) -- `app` containers, `Cure.toml` `[application]` /
  `[release]` sections, and the `cure release` subcommand.
- [`PROTOCOL.md`](PROTOCOL.md) -- session-typed binary protocols.
- [`TEMPORAL.md`](TEMPORAL.md) -- temporal (LTL) properties over FSM graphs.

## Tooling

- [`REPL.md`](REPL.md) -- the interactive session: submission semantics,
  meta-commands, and inspection.
- [`DOC.md`](DOC.md) -- the `cure doc` pipeline, `[doc]` config, placeholder
  interpolation, and the REPL Markdown renderer.
- [`OBSERVABILITY.md`](OBSERVABILITY.md) -- `Cure.OTel`, `cure top`, `cure
  trace`.
- [`JOHN.md`](JOHN.md) -- `mix cure.john`, `cure john`, and the `:john` REPL
  meta-command.
- [`REPLAY.md`](REPLAY.md) -- `cure replay` FSM time-travel.
- [`SNAP.md`](SNAP.md) -- REPL session snapshots (`cure snap`).
- [`STORY.md`](STORY.md) -- the `cure story` narrative architecture generator.
- [`BLESS.md`](BLESS.md) -- the `cure bless` Socratic type-error assistant.
- [`EXPORT_TYPES.md`](EXPORT_TYPES.md) -- cross-language type export
  (`cure export-types`).
- [`PGO.md`](PGO.md) -- profile-guided optimisation.
- [`PLAYGROUND.md`](PLAYGROUND.md) -- the live playground.

## Packages, releases, and the standard library

- [`STDLIB.md`](STDLIB.md) -- the standard-library orientation guide and topic
  map (the generated module pages are authoritative).
- [`PUBLISHING.md`](PUBLISHING.md) -- publishing Cure packages.
- [`PACKAGE_REGISTRY.md`](PACKAGE_REGISTRY.md) -- the package registry design.
- [`PROOF_CARRYING.md`](PROOF_CARRYING.md) -- proof-carrying packages
  (`mix cure.verify`).

## Examples and case studies

- [`ESCROW_EXCHANGE.md`](ESCROW_EXCHANGE.md) -- the multi-currency exchange and
  escrow engine walkthrough.

## Design notes and audits

These are historical or design-stage documents; they are not part of the
learning path.

- [`COMPILER_PERFORMANCE_BASELINES.md`](COMPILER_PERFORMANCE_BASELINES.md) --
  measured cold/warm build baselines (numbers frozen at measurement time).
- [`DEPENDENT_TYPE_SLICES.md`](DEPENDENT_TYPE_SLICES.md) -- the dependent-type
  delivery slices.
- [`DEPENDENT_KERNEL_PEERNESS_ROADMAP.md`](DEPENDENT_KERNEL_PEERNESS_ROADMAP.md)
  -- the kernel peerness roadmap.
- [`STDLIB_DEPENDENT_CLAIMS_AUDIT.md`](STDLIB_DEPENDENT_CLAIMS_AUDIT.md) -- an
  audit of the stdlib's dependent-type claims.
- [`LAUNCH-CHECKLIST-0.34.md`](LAUNCH-CHECKLIST-0.34.md) -- the historical 0.34
  launch checklist (closed; kept as a record).

## Elsewhere

- [`../README.md`](../README.md) -- the project README.
- [`../CHANGELOG.md`](../CHANGELOG.md) -- the release inventory.
- [`../RELEASE.md`](../RELEASE.md) -- the operational release procedure.
- [`../ROADMAP-0.34.md`](../ROADMAP-0.34.md) -- the 0.34 dependent-pipeline
  feature narrative.
- [`../proof/README.md`](../proof/README.md) -- the Agda soundness development.

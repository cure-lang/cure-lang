# Public Documentation Redesign

**Status:** proposed information-architecture and editorial specification

**Date:** 2026-07-27

**Applies to:** `README.md`, public files under `docs/`, ExDoc extras,
`site/priv/pages/`, generated standard-library documentation, documentation
navigation, and the placement of historical engineering material

**Does not change:** Cure language semantics, compiler behavior, command-line
interfaces, or the contents of historical records kept outside public
navigation

## 1. Decision

Cure's public documentation will be reorganized around reader goals rather
than repository history or compiler subsystems. It will have four explicit
reader journeys:

1. **Learn** — install Cure, run a program, understand the language, and finish
   a guided project.
2. **Build** — accomplish focused tasks such as modeling errors, defining an
   interface, expressing an invariant, using OTP, or calling BEAM code.
3. **Reference** — look up syntax, types, patterns, commands, diagnostics, and
   standard-library APIs.
4. **Understand** — study compiler architecture, the dependent kernel,
   erasure, trust, and formal language design.

Release notes, implementation plans, audits, agent reports, and superseded
designs are not part of these journeys. They remain available in an internal
history area but do not appear in primary public navigation.

The target quality is calm, intentional, task-oriented documentation with
strong progressive disclosure. “Apple-quality” means that a reader sees the
result first, can complete the common path without understanding the
implementation, and encounters detail only when it becomes useful. It does
not mean copying Apple's terminology or visual style.

## 2. Why the current documentation must change

The current corpus is factually richer than it was before the dependent
compiler work, but its organization still reflects incremental accumulation:

- the README opens with compiler architecture and MetaAST before showing what
  a Cure program does;
- many pages begin with release-version history instead of a reader outcome;
- tutorial, reference, architecture, and changelog material are mixed within
  the same files;
- the website and repository maintain overlapping explanations independently;
- generated API information is manually repeated in prose inventories;
- obsolete or deferred implementation plans appear in ExDoc beside supported
  user guides;
- large formal documents contain hand-maintained tables of contents,
  glossaries, test suites, implementation sketches, style guides, and future
  syntax in one file;
- internal completion reports and audit loops occupy the repository root.

The scale makes local copy-editing insufficient:

| Surface | Approximate size at survey time |
|---|---:|
| Root Markdown | 14 files, 43,000 words |
| Top-level `docs/` | 36 files, 60,000 words |
| Website guide pages | 13 files, 31,000 words |
| `docs/superpowers/plans/` | 111 files, 504,000 words |
| `docs/MATCH.md` | 11,700 words, 196 headings |
| `docs/PICKUP.md` | 8,800 words, 155 headings |
| Website roadmap | 9,600 words |

The engineering-plan corpus is useful history. The problem is not that it
exists; the problem is that public and internal material lack a strong
boundary.

## 3. Editorial principles

Every public page must follow these principles.

### 3.1 Lead with the outcome

The opening must answer what the reader can accomplish and why it matters.
Architecture, release provenance, and implementation ownership come later or
move to contributor documentation.

### 3.2 Show before explaining

A concept guide begins with a small, complete example and its observable
result. Explanations then name the ideas the reader has already seen.

Code examples intended for users must, where practical:

- be complete enough to run or clearly identify omitted context;
- use current canonical imports and syntax;
- include the command that exercises them;
- show expected output or the type-checking result;
- be validated by a documentation example test rather than copied by hand
  without coverage.

### 3.3 One page, one reader question

A page may cover supporting concepts, but it must have one primary job. A
Getting Started page is not also the complete CLI, LSP, MCP, package, release,
and embedding reference.

### 3.4 Progressive disclosure

The common path comes first. Edge cases, formal rules, runtime representation,
and contributor details follow in clearly named sections or separate pages.

### 3.5 One canonical explanation

The repository and website must not maintain independent long-form copies of
the same language or type-system guide. Website pages should be generated from,
include, or briefly introduce canonical sources.

### 3.6 Evergreen prose is not release history

Supported behavior is described in the present tense without version badges.
The changelog owns when a feature landed. A guide mentions a version only when
compatibility or migration genuinely depends on it.

### 3.7 Generate inventories

Function lists, command lists, diagnostic catalogs, keyword lists, and
standard-library API signatures should be generated from their authoritative
registries or source comments. Hand-written prose should explain how to choose
and use an API, not mirror a database.

### 3.8 Use a restrained voice

Prefer short, direct sentences and descriptive headings. Avoid slogans,
release-title flourishes, claims of completeness, “everything-at-once”
language, and internal component names unless the reader is explicitly in the
Understand journey.

## 4. Target information architecture

### 4.1 Learn

- Welcome to Cure
- Install Cure
- A tour of the language
- Build your first Cure project
- Introduction to dependent programming

### 4.2 Build

- Model data with records and ADTs
- Handle failure with `Result`
- Work with structural patterns
- Define and use interfaces
- Enforce an invariant with a type
- Write and consume proofs
- Build an actor, FSM, and supervised application
- Call Erlang, Elixir, and AtomVM code
- Test, document, package, and release a project

### 4.3 Reference

- Language reference
- Type-system reference
- Pattern reference
- Binary syntax reference
- CLI reference
- Configuration reference
- Diagnostic catalog
- Generated standard-library API

### 4.4 Understand

- Compiler architecture
- Dependent kernel
- Elaboration and canonical modules
- Quantitative erasure and runtime representation
- Trust model and proof checking
- Normative language specifications

### 4.5 History

History is accessible but not mixed into the primary learning hierarchy:

- release notes and changelog;
- completed roadmaps;
- superseded designs;
- audits;
- implementation plans;
- automated-agent completion reports.

## 5. File-level redesign

### 5.1 `README.md`

Rewrite the README as the product landing page. Target 800–1,200 words.

Required sequence:

1. a two-sentence statement of what Cure is and what makes it useful;
2. one complete, differentiating Cure program;
3. the command to run it;
4. its visible output or checked result;
5. three short explanations of what the example demonstrates;
6. the shortest supported installation path;
7. three capability paths: dependent data, BEAM/OTP programs, and ordinary
   functional programming;
8. links to Getting Started, the tutorial, reference, and project status.

The opening example should demonstrate why Cure exists, not merely that it has
functions and arithmetic. A small indexed-data or typed-state example is
preferred, provided a newcomer can understand its behavior before learning the
type theory.

Move out of the README:

- compiler pipeline and MetaAST details → compiler architecture;
- the Elixir module inventory → contributor architecture;
- the standard-library function inventory → generated stdlib reference;
- the long example-project inventory → a curated examples gallery;
- release history → changelog/releases;
- detailed REPL bindings → REPL reference.

### 5.2 Getting Started

`site/priv/pages/getting-started.md` becomes a short success path:

1. prerequisites;
2. installation;
3. create or copy a complete program;
4. `cure check`;
5. `cure run`;
6. expected output;
7. three next destinations.

CLI catalogs, editor setup, MCP, embedding from Elixir, stdlib inventory, and
release packaging move to focused pages. Repository URLs must come from one
project setting rather than being copied into prose.

### 5.3 Tutorial

Replace `docs/TUTORIAL.md` with one coherent project developed incrementally:

1. create and run the project;
2. define an ADT and record;
3. transform values with functions and patterns;
4. handle failure with canonical `Std.Result`;
5. define and consume an interface;
6. express one useful invariant in a type;
7. use a typed hole to finish an implementation;
8. test and package the result.

Every chapter starts from the previous working state and ends with a command
and result. Removed features never receive tutorial chapters. Binary parsing,
FSMs, supervision, proof authoring, and documentation generation become
separate Build guides.

### 5.4 Language guide and language reference

Create two distinct artifacts:

- a short, example-led language tour for learners;
- one canonical exhaustive language reference.

`docs/LANGUAGE_SPEC.md` is the likely canonical reference source.
`site/priv/pages/language-guide.md` should not remain an independently edited
near-copy. The reference should be organized by the grammar readers look up,
not by the dates features arrived.

### 5.5 Type and proof documentation

Assign non-overlapping responsibilities:

- `docs/DEPENDENT_TYPES.md` — practical dependent-programming guide;
- `docs/TYPE_SYSTEM.md` — concise semantic reference;
- `docs/PROOFS.md` — task-oriented proof authoring and consumption;
- `docs/KERNEL.md` — compiler-contributor architecture;
- `docs/GLOSSARY.md` — alphabetical lookup.

The website type-system page should introduce and link to these canonical
roles rather than restating all of them. Move the long type-theory primer out
of the kernel architecture document. The glossary should use compact examples
and ordinary alphabetical navigation rather than “telescope-sorted” ordering.

### 5.6 `match`, `pickup`, and patterns

Reduce `docs/MATCH.md` and `docs/PICKUP.md` to normative cores:

- syntax and grammar;
- static semantics;
- evaluation behavior;
- exhaustiveness/reachability;
- diagnostics;
- representative conformance examples.

Move formal proofs, implementation sketches, duplicated glossaries,
hand-written acceptance suites, style advice, migration walkthroughs,
anti-pattern catalogs, and reserved future syntax into separately named
internal or companion documents.

`docs/PATTERNS.md` should be the practical pattern reference. It should lead
with Cure patterns and examples; Erlang abstract-form lowering belongs in an
Understand/compiler-lowering page.

### 5.7 Standard library

Turn `docs/STDLIB.md` into a curated selection guide:

- where the generated API reference lives;
- canonical import behavior;
- which module to choose for common jobs;
- a small number of composed examples;
- stability and runtime notes that cannot be generated from signatures.

Module/function inventories and signatures remain in `.cure` doc comments and
generated pages. Documentation CI must fail when a curated link points to a
missing module.

### 5.8 Tooling

Split `site/priv/pages/tooling.md` into:

- CLI reference;
- editor and LSP integration;
- diagnostics and explanations;
- compiler integrations (MCP, events, profiling);
- deferred optimizer status, if it needs a public page at all.

Remove chronological “v0.x additions” sections. Generate command syntax from
CLI command definitions and the diagnostic catalog from
`Cure.Diagnostic.Registry`.

### 5.9 Roadmap

The public roadmap contains only:

- **Now** — actively landing;
- **Next** — committed near-term work;
- **Later** — directional work without implied scheduling.

Completed releases link to the changelog or release archive. The roadmap is
not a second changelog.

### 5.10 Feature guides

Pages such as REPL, package publishing, observability, protocols, snapshots,
and export tooling should be rewritten from version-led announcements into
task-led guides:

- what this feature is for;
- the shortest successful example;
- common workflows;
- configuration/reference;
- failure modes;
- related pages.

Implementation module names belong only in an Architecture section.

## 6. Public versus internal placement

Remove historical and deferred engineering documents from ExDoc extras,
including:

- dependent-kernel peerness roadmap;
- dependent-type slice plan;
- stdlib dependent-claims audit;
- classic-AST type-directed cloning prototype;
- PGO design until a supported optimizer returns.

Move them under a clearly labeled internal history tree, for example:

```text
docs/internals/
  architecture/
  designs/
  history/
  reports/
```

Move root `AUTOPILOT-*` reports and `AUDIT-LOOP.md` into the reports/history
area. Preserve git history; do not delete useful evidence merely to make the
tree look smaller.

`docs/superpowers/` remains the engineering design corpus. Its master indexes
should make clear that these documents are implementation inputs, not user
guides.

## 7. Source-of-truth and generation rules

The redesign must eliminate manual duplication:

- public website prose and ExDoc prose share canonical Markdown sources or
  generated includes;
- CLI reference derives syntax from command definitions;
- diagnostics derive codes and summaries from the diagnostic registry;
- stdlib reference derives from `.cure` declarations and doc comments;
- keyword/operator tables derive from edition/fixity definitions;
- version and repository links derive from project metadata;
- examples used in public docs are registered and checked by CI.

Generated content must be visibly generated and must not be edited at the
output location.

## 8. Quality gates

The redesign is complete only when all of the following hold:

1. A new reader can install Cure and run a complete program by following one
   page without branching into reference material.
2. The README presents runnable Cure code and its result before compiler
   architecture.
3. The tutorial contains no removed, deferred, or historical feature chapter.
4. Each public page states one primary reader outcome.
5. No long-form language or type-system explanation is independently
   maintained in both `docs/` and `site/priv/pages/`.
6. Public navigation contains no superseded implementation plan or resolved
   audit.
7. The roadmap contains no completed-release encyclopedia.
8. The stdlib overview does not manually mirror the generated API inventory.
9. Every runnable public Cure example is compiled or checked in CI, and
   examples with expected results are executed.
10. Internal module names and data structures appear only where the declared
    audience is compiler contributors.
11. Navigation labels use reader language rather than release names or
    internal subsystem names.
12. Links, anchors, code fences, front matter, and generated documentation
    build without new warnings.

## 9. Implementation sequence

Execute the work in this order:

1. establish the directory taxonomy and navigation;
2. rewrite README and Getting Started;
3. replace the tutorial with the coherent project;
4. establish canonical-source/include generation for website and ExDoc;
5. split language tour from language reference;
6. assign and rewrite the type/proof/kernel/glossary roles;
7. reduce `match` and `pickup`, and refocus the pattern reference;
8. replace manual stdlib inventory with the curated guide;
9. split tooling and reduce the roadmap;
10. rewrite remaining feature guides to the shared template;
11. relocate historical/internal material;
12. run a final voice, correctness, link, and executable-example audit.

Do not begin with a global wording pass. Rewriting sentences before fixing
ownership and duplication will polish material that should be moved, generated,
or deleted.

## 10. Non-goals

- Redesigning the website's visual CSS or component system.
- Changing Cure syntax to make documentation examples simpler.
- Deleting historical engineering evidence.
- Promising a package manager, installer, hosted playground, or optimizer that
  is not currently supported.
- Turning every internal design into public educational content.
- Using word count alone as a quality metric; concision must preserve the
  information the intended reader needs.

## 11. Open implementation decisions

The implementation pass must decide:

1. whether canonical public Markdown lives under `docs/` and is included by
   the website, or lives in a neutral content directory consumed by both;
2. whether the formal `match` and `pickup` cores remain ExDoc extras or move to
   a language-design reference area;
3. how runnable snippets declare their source file, imports, command, and
   expected result for CI;
4. whether release pages are generated from `CHANGELOG.md` or remain separate
   curated posts;
5. which existing pages can be redirected rather than preserved as duplicate
   content.

These choices must preserve stable external links where practical, using
redirects or compatibility stubs when pages move.

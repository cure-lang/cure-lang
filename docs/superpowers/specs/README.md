# Cure specification catalogue

The specifications are grouped by the subsystem or design concern they govern.
The filenames retain their historical dates and names so existing plans and
commit history remain recognizable.

| Directory | Scope |
| --- | --- |
| `antigen/` | Antigen corpus, assays, generators, fuzzing, and soundness infrastructure |
| `beam/` | BEAM, OTP, process algebra, ports, and runtime representation |
| `diagnostics/` | Compiler diagnostics and error-rendering design |
| `effects/` | Effect discipline, effect typing, deferred effects, and stackless Flow effects |
| `ir/` | Cure IRs, Flow machine semantics, JSON interchange, Lean verification, and LowCure |
| `kernel/` | Dependent kernel, conversion, reduction, termination, and trust-boundary design |
| `language/` | Surface syntax, parsing, names, literals, tuples, and language ergonomics |
| `macros/` | Compile-time macro facility and macro-specific designs |
| `ownership/` | Ownership, uniqueness, usage, borrowing, and transfer rules |
| `roadmap/` | Parity, migration, value-surface, and staged implementation roadmaps |
| `stdlib/` | Standard-library and library-derived language designs |
| `tooling/` | Elaborator tooling, imports, migration tooling, module loading, and development workflows |
| `types/` | Type constructors, indexed types, type classes, universes, ADTs, and overloads |

Cross-cutting specifications should link to the authoritative directory rather
than recreating a copy in another category. The macro directory is the
precedent for this organization; it remains the home for macro specifications,
including BEAM macro expansion designs.

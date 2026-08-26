# Cure v0.13.0 Roadmap

v0.12.0 established all major subsystems. v0.13.0 deepens them from
"working foundation" to "production ready" and closes the remaining
gaps with the legacy Erlang implementation (~17,000 lines still unported,
primarily the type optimizer at 7,200 lines and 5 LSP modules at ~3,100 lines).

## Theme: Depth Over Breadth

Every subsystem in v0.12 works. Most are shallow. v0.13 makes them deep:
dependent types that actually verify, protocols that work across modules,
an LSP that edits code for you, an optimizer that makes code measurably faster.

---

## Phase 1 -- Dependent Type Verification [DONE]

Constrained function signatures stored in type env. Call-site verification
via SMT. Counterexample extraction. Std.Vector stdlib module.

### 1a -- Checker Integration
- Extend `Cure.Types.Checker` to recognize dependent function signatures
- When a function declares `when n > 0`, generate a VC at every call site
- Wire VCs through `Cure.SMT.Solver.prove_implication/4`
- Emit type errors when VCs cannot be proven

### 1b -- Type-Level Arithmetic
- Extend `Cure.SMT.Translator` to translate type-level `+`, `-`, `*` in
  return types: `Vector(T, m + n)`
- Track value parameters through function calls and let bindings

### 1c -- Dependent Parser
Legacy: `cure_dependent_parser.erl` (229 lines)
- Parse value parameter annotations: `fn f(v: Vector(T, n: Nat))`
- Distinguish type params (`T`) from value params (`n: Nat`)

### 1d -- SMT Counterexample Extraction
- When `prove_implication` returns `:sat`, use `Cure.SMT.Parser.parse_model/1`
  to extract the counterexample and include it in the error message:
  "Cannot prove n > 0; counterexample: n = 0"

### 1e -- Std.Vector
- Length-indexed vector stdlib module using dependent types
- `empty() -> Vector(T, 0)`, `cons(x, v: Vector(T, n)) -> Vector(T, n + 1)`
- `safe_head(v: Vector(T, n)) -> T when n > 0`

**Estimated**: ~800 lines across checker, translator, parser, stdlib

---

## Phase 2 -- Cross-Module Protocol Registry [DONE]

ETS-backed global registry. Impls registered during codegen. has_impl?/lookup_impl APIs.

### 2a -- Global Protocol Registry
- ETS-backed registry started in `Cure.Application`
- When a module with `impl` is compiled, register the implementation
- When resolving a protocol call, check local dispatch first, then registry

### 2b -- Where Constraints
- Type checker validates `where Show(T)` constraints at call sites
- Verify the constraint is satisfied by checking the registry

### 2c -- Cross-Module Derive
- Wire `Cure.Types.Derive` into the codegen pipeline
- `@derive(Show)` on a record generates and registers an implementation

**Estimated**: ~500 lines

---

## Phase 3 -- LSP Production Features [DONE]

textDocument/definition, textDocument/documentSymbol, textDocument/codeAction.
Quick fixes for non-exhaustive matches and did-you-mean suggestions.

### 3a -- Go-to-Definition
- Track definition locations in `Cure.LSP.Symbols`
- Resolve identifier at cursor position to source location
- `textDocument/definition` response with file URI and range

### 3b -- Type Holes
Legacy: `cure_lsp_type_holes.erl` (839 lines)
- Recognize `_` in type annotations as a hole
- Infer the type that would fill the hole
- Report as LSP hint diagnostics

### 3c -- Code Actions
Legacy: `cure_lsp_code_actions.erl` (740 lines)
- Quick fix: add missing match arms (from exhaustiveness warnings)
- Quick fix: add missing import (from unresolved function call)
- Quick fix: "did you mean?" typo correction (from error suggestions)

### 3d -- Incremental Compilation
- Cache parsed AST per document URI + version
- Only re-check functions that changed
- Debounce diagnostic publication

### 3e -- SMT Feedback
Legacy: `cure_lsp_smt.erl` (525 lines)
- Show refinement type info on hover
- Display counterexamples inline when subtype proofs fail

**Estimated**: ~1,500 lines across 4-5 modules

---

## Phase 4 -- Advanced Optimizer [DONE]

Function inlining (small pure functions) + guard simplification (algebraic rules).
5 optimizer passes: inline, constant_fold, dead_code, pipe_inline, guard_simplify.

### 4a -- Function Inlining
- Identify small, pure functions (body <= 3 AST nodes, no side effects)
- Inline at call sites during optimization pass
- Respect recursion (never inline recursive functions)

### 4b -- Type-directed cloning experiment
- Clone functions for concrete call-site type shapes
- Redirect eligible calls to the clone
- This was experimental optimizer scaffolding, not full monomorphisation

### 4c -- Guard Optimizer
Legacy: `cure_guard_optimizer.erl` (358 lines)
- Algebraic simplification: `x > 0 and x > 0` -> `x > 0`
- Merge overlapping guards across clauses
- Eliminate redundant guards that are implied by patterns

### 4d -- Pattern-Aware SMT Encoding
Legacy: `cure_pattern_encoder.erl` (339 lines)
- Encode pattern match structure as SMT constraints
- Use for more precise exhaustiveness: "these 5 integer literals cover all
  values in range 0..4" (currently reports non-exhaustive)

### 4e -- Pipe Chain Optimizer (deep)
Legacy: `cure_pipe_optimizer.erl` (354 lines)
- Analyze pipe chains for Result-type propagation
- Eliminate Ok wrapping/unwrapping when all functions are provably infallible
- Inline direct function calls for chains under 5 stages

**Estimated**: ~1,200 lines across 5 modules

---

## Phase 5 -- FSM Actions & Monitoring [DONE]

Transition guards and actions compiled into gen_statem handle_event clauses.
health_check/1 API on FSM Runtime.

### 5a -- Action Compiler
Legacy: `cure_action_compiler.erl` (695 lines), `cure_fsm_action_compiler.erl` (127 lines)
- Parse `do` blocks on transitions: `Red --timer--> Green do count = count + 1`
- Compile action expressions to BEAM code within `handle_event` clauses
- Action has access to current state data and can return modified data

### 5b -- FSM Guard Codegen
Legacy: `cure_guard_codegen.erl` (654 lines), `cure_guard_compiler.erl` (586 lines)
- Compile guard expressions on transitions to BEAM guard sequences
- `Red --timer when count > 0--> Green`

### 5c -- OTP Monitoring
Legacy: `cure_fsm_monitor.erl` (397 lines)
- Supervisor-compatible FSM processes
- Health check API (last event time, transition count, error count)
- Automatic restart tracking

**Estimated**: ~800 lines

---

## Phase 6 -- Error Reporting [DONE]

CLI uses format_with_source for source-annotated errors. Error catalog with
5 codes (E001-E005). `cure explain E001` command.

### 6a -- CLI Integration
- `cure compile` and `cure check` use `format_with_source` when source is available
- Show source line + caret for parse errors and type errors
- Append "did you mean?" suggestions for unresolved names

### 6b -- LSP Integration
- Include source context in diagnostic messages
- Wire suggestions into code action quick fixes
- Color output for terminal (ANSI escapes, detect TTY)

### 6c -- Structured Error Catalog
- Assign error codes: E001 type mismatch, E002 unbound variable, etc.
- `cure explain E001` command showing detailed explanation + examples

**Estimated**: ~300 lines

---

## Phase 7 -- Stdlib Completion [DONE]

Std.Map (14 fns), Std.Set (11 fns), Std.Option (10 fns), Std.Functor (1 fn).
17 stdlib modules total, ~200 functions.

---

## Phase 8 -- Package Management (deferred to v0.14)

### Missing from legacy
- `Std.Vector` -- length-indexed vectors (depends on Phase 1)
- `Std.Rec` -- record creation/update helpers (`make`, `update`, `fields`)
- `Std.Typeclasses` -- meta-module re-exporting Eq/Ord/Show
- `Std.Functor` -- functor protocol (map over any container)

### New modules (not in legacy)
- `Std.Map` -- map operations (put, get, delete, merge, keys, values)
- `Std.Set` -- set operations via maps (add, remove, member, union, intersection)
- `Std.Option` -- separate from Std.Core (like Std.Result)

**Estimated**: ~500 lines of .cure code

---

## Phase 8 -- Package Management & Distribution

### 8a -- Cure.toml Project File
- Project metadata: name, version, dependencies
- Stdlib path configuration
- Compiler options (optimize, type-check by default)

### 8b -- Dependency Resolution
- Fetch dependencies from git URLs or local paths
- Compile dependencies before main project
- Add dependency BEAM files to code path

### 8c -- Hex.pm Integration (stretch goal)
- Publish Cure packages as Hex packages
- Mix-compatible dependency specification

**Estimated**: ~600 lines

---

## Suggested Implementation Order

1. **Phase 1** (dependent type verification) -- the language's raison d'etre
2. **Phase 2** (cross-module protocols) -- unblocks real-world multi-module use
3. **Phase 6** (error reporting wiring) -- small effort, big DX improvement
4. **Phase 3** (LSP production) -- critical for adoption
5. **Phase 5** (FSM actions) -- makes FSMs useful for real protocols
6. **Phase 4** (advanced optimizer) -- performance; can be incremental
7. **Phase 7** (stdlib completion) -- ongoing
8. **Phase 8** (package management) -- stretch goal for v0.13; may slip to v0.14

## Total Estimated Work

~6,200 lines of new Elixir code across ~25 modules. This closes nearly all
remaining gaps with the legacy implementation and adds capabilities (package
management, structured error catalog) that the legacy never had.

## Legacy Coverage After v0.13

With v0.13, the only significant unported legacy code will be:
- `cure_type_optimizer.erl` (7,196 lines) -- the bulk is optimizer experiments and
  profile-guided optimization, which Phase 4 covers the essential subset of
- Runtime interpreter (`cure_runtime.erl`, 970 lines) -- not needed since
  Cure compiles to BEAM bytecode directly
- Native show/string helpers -- replaced by Cure stdlib + @extern FFI

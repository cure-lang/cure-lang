# Cure v0.14.0 Roadmap

v0.13 deepened every subsystem. v0.14 shifts from reimplementing the legacy
to building capabilities it never had, plus the single most impactful
remaining legacy feature (type holes).

## Theme: Real-World Readiness

A language is real-world ready when programs can have dependencies, the type
system follows values through function calls, and the editor tells you what
types it inferred before you even ask.

---

## Phase 1 -- Package Management

**Why first**: without dependency resolution, every Cure program is a single
file or a manually orchestrated collection. This is the biggest adoption
blocker.

### 1a -- Cure.toml Project File
- TOML-based project configuration (name, version, stdlib_path, compiler opts)
- Parsed at `cure compile` / `cure run` time
- Example:
  ```toml
  [project]
  name = "my_app"
  version = "0.1.0"

  [dependencies]
  http_client = { git = "https://github.com/user/http_client.cure", tag = "v1.0" }
  utils = { path = "../shared/utils" }

  [compiler]
  type_check = true
  optimize = true
  ```

### 1b -- Dependency Resolution
- `cure deps.get`: clone/fetch dependency sources
- Topological sort of dependency graph (detect cycles)
- Compile dependencies before main project
- Add dependency `.beam` files to code path

### 1c -- Stdlib as a Built-in Dependency
- The standard library is treated as an implicit dependency
- `cure stdlib` compiles it once; projects reference the compiled output
- No need to recompile stdlib for every project

### 1d -- cure init
- `cure init my_project`: scaffold a new project with Cure.toml, lib/, test/
- Generate a hello-world `lib/main.cure`

**Estimated**: ~600 lines (TOML parser can use an Elixir library, or a
minimal hand-rolled parser for the subset we need)

---

## Phase 2 -- Deep Dependent Type Tracking

**Why second**: v0.13 verifies constraints at call sites with literal
arguments only. Real programs pass variables, and the type system must
track value knowledge through bindings and function returns.

### 2a -- Value Tracking Through Let Bindings
- When `let n = length(v)` and `length` returns `:int`, track that `n`
  is bound to `length(v)` -- not just type `:int` but the expression
- When `safe_head(v)` requires `n > 0`, look up `n` in the environment
  and check if the tracked expression proves the constraint

### 2b -- Refinement Propagation Through Function Calls
- When calling `fn f(x: Int) -> Int when x > 0`, the return value carries
  the refinement `{:refinement, :int, "result", result > 0}`
- Subsequent uses of the result can assume the refinement holds
- Chain: `let y = abs(x); safe_divide(100, y)` -- abs returns non-negative,
  but we need non-zero; the system should report the gap precisely

### 2c -- Path-Sensitive Refinement
- In `if x > 0 then safe_head(v) else default`, the then-branch knows
  `x > 0` and the else-branch knows `not (x > 0)`
- Guards on multi-clause functions already do this (v0.13 Phase 5);
  extend to if/else and match arms

### 2d -- SMT Context Accumulation
- Maintain a stack of known constraints as the checker descends into
  expressions
- At each call site, assert all accumulated constraints before checking
  the function's precondition
- `Cure.SMT.Solver.check_with_context(constraint, context_constraints)`

**Estimated**: ~800 lines across checker, env, solver

---

## Phase 3 -- LSP Type Holes

**Why third**: the single most valuable remaining legacy feature (839 lines
in `cure_lsp_type_holes.erl`). Type holes make the type system interactive.

### 3a -- Parser Support
- Recognize `_` in type annotation positions as a type hole
- `fn foo(x: _) -> _` parses with hole markers in the AST
- `let y: _ = expr` also supported

### 3b -- Hole Inference
- During type checking, when a hole is encountered, infer the type that
  would make the program well-typed
- For parameter holes: infer from how the parameter is used in the body
- For return type holes: infer from the body expression type
- For let annotation holes: infer from the bound expression

### 3c -- LSP Reporting
- Report inferred types as LSP hint diagnostics (severity 4)
- Show on hover: "Type hole: inferred Int"
- Code action: "Fill type hole with Int"

### 3d -- Interactive Workflow
- Write `fn foo(x: _) -> _ = x + 1`
- LSP immediately shows: parameter `x` is `Int`, return type is `Int`
- Accept the suggestion to fill in the types

**Estimated**: ~500 lines across parser, checker, LSP server

---

## Phase 4 -- LSP Incremental Compilation

### 4a -- AST Cache
- Cache parsed AST per document URI + version number
- On `didChange`, only reparse if the version changed
- Store in the `ast_cache` field already present on the server state

### 4b -- Incremental Type Checking
- Track which functions changed between versions (diff AST)
- Only re-check changed functions and their callers
- Keep a dependency graph of function -> function calls

### 4c -- Debounced Diagnostics
- Buffer rapid keystroke changes (100ms debounce)
- Only publish diagnostics after the buffer settles
- Reduces Z3 invocations during active typing

**Estimated**: ~400 lines

---

## Phase 5 -- Cross-Module Protocol Dispatch

v0.13 added the global protocol registry. v0.14 uses it for actual
cross-module function calls.

### 5a -- Codegen: Registry-Aware Call Resolution
- When an unqualified call doesn't match local functions, imports, or
  variables, check the protocol registry
- If a matching protocol method exists, emit a remote call to the
  registered module's dispatch function

### 5b -- Runtime Fallback
- If the registry has no entry at compile time (module not yet compiled),
  generate a runtime lookup via `ProtocolRegistry.lookup_impl` + `apply`
- This handles cases where compilation order doesn't guarantee visibility

### 5c -- Where Constraint Enforcement
- Type checker reads `:constraints` from function meta
- For each `where Show(T)` constraint, verify the argument type has
  a registered Show impl
- Emit a type error if the constraint cannot be satisfied

**Estimated**: ~400 lines

---

## Phase 6 -- Testing Infrastructure

### 6a -- cure test Command
- `cure test` compiles and runs `.cure` test files
- Test modules use assertions: `fn test_add() = assert(add(1, 2) == 3)`
- Report pass/fail counts

### 6b -- Std.Test Module
- `assert(condition)`: raise on false
- `assert_eq(a, b)`: structural equality check
- `assert_match(pattern, value)`: pattern match assertion

**Estimated**: ~300 lines

---

## Suggested Implementation Order

1. **Phase 1** (package management) -- adoption blocker
2. **Phase 5** (cross-module protocol dispatch) -- uses v0.13 registry
3. **Phase 3** (type holes) -- highest DX impact
4. **Phase 2** (deep dependent types) -- the hard one; benefits from 1-3
5. **Phase 4** (incremental LSP) -- performance; can be done in parallel
6. **Phase 6** (test infrastructure) -- enables testing Cure programs in Cure

## Total Estimated Work

~3,000 lines of new Elixir code across ~15 modules. This is smaller than
v0.13 (~1,500 lines) because the focus is on connecting existing subsystems
rather than building new ones.

## Legacy Coverage After v0.14

After v0.14, the only unported legacy code will be:
- `cure_type_optimizer.erl` (7,196 lines) -- optimizer experiments and PGO,
  diminishing returns vs the function inliner added in v0.13
- `cure_runtime.erl` (970 lines) -- bytecode interpreter, not needed
- Native helpers (697 lines) -- replaced by stdlib + FFI

The Cure rewrite will be functionally complete.

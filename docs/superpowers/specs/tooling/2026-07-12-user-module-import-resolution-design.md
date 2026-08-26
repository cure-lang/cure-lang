# User-Module Import Resolution — Design (PARKED)

> **Status: PARKED.** Design captured mid-#18-green-up so the work isn't lost;
> not scheduled. Resume after the rip-out suite is green. Owner decision on
> record: "We need to close the completeness gap, but first we should continue."

## Problem

The dependent pipeline (sole compiler post-#18) resolves `use` **only for
`Std.*` modules**. A `use SomeUserModule` followed by an unqualified call to one
of its functions is rejected with `{:codegen_error, :unknown_global}`.

This is **not a soundness gap** — it fails *closed* (an unresolved name is
rejected, never miscompiled). It is a **completeness gap**: multi-file Cure
programs that `use` a sibling user module cannot be compiled through the
dependent front-end alone.

### Why it exists (root cause)

The two pipelines resolved cross-module calls by different mechanisms:

- **Classic (deleted in `07b65ed`):** `resolve_import/3` in the old
  `compiler/codegen.ex` consulted the *loaded BEAM module's*
  `module_info(:exports)` and matched on **name/arity only**. It never needed
  types — it emitted a remote call to a `{fn, arity}` that provably existed in a
  loaded module.
- **Dependent (current):** to *type-check* a cross-module call it needs the
  callee's **type signature**, and BEAM modules carry no Cure types. It recovers
  signatures by **re-elaborating the callee's source**. `import_source_path/1`
  (`lib/cure/elab/program.ex:1046`) only knows where `Std.*` sources live
  (`Cure.Stdlib.Paths.source_dir()`); anything else returns `:not_stdlib` →
  `import_source_env(:not_stdlib, _)` (program.ex:989) → `{:ok, Env.empty()}`,
  i.e. imports nothing.

So the rip-out did not break a working typed feature — the classic mechanism was
untyped and cannot be reused. Typed user-module import resolution was **never
built**; the rip-out merely exposed the hole.

### What it affects

- `test/cure/compiler/multi_file_link_test.exs` — compiles a user module, `use`s
  it from another; asserts `{:ok, %{modules: …}}`. Currently
  `{:compile_failed, {:codegen_error, :unknown_global}}`.
- `test/cure/compiler/unresolved_import_warning_test.exs` — `use Ghost` (missing)
  + an unqualified call; asserts a `W088 :unresolved_import` warning via
  `{:error, {:beam_lint_error, _lint, warnings}}`.
- Multi-file *user* projects compiled purely through the dependent front-end.
  (The phase1/phase35 build flow already works: it compiles files separately and
  links via packbeam with qualified/remote calls; cross-module **emit** already
  works via `Program.import_origins/1` → remote calls. Only the *unqualified `use`
  + re-elaborate-for-types* path is missing.)

Both tests additionally assert **stale classic behaviors** (a beam-import-table
remote call; the `W088` fallback that lived in the deleted classic codegen) that
must be re-specified against the post-fix contract — see Testing.

The **REPL** was in this bucket too but has been removed from it: `evaluate/2`
now **inlines** session definitions as local functions instead of `use
Repl.Session` (commit `390011a`), so it needs no cross-user-module resolution.

## Goal

`use MyModule` locates `my_module.cure` on the project's source path, elaborates
it for its signatures, and merges its env into the importer — the exact treatment
`Std.*` gets today, generalized to user modules — so unqualified calls resolve and
type-check, and emit lowers them to remote calls (already working).

Non-goals: no change to the kernel/TCB; no change to the emit path (remote calls
already correct); no separate-compilation caching (see Open Questions).

## Design

### Core change: generalize `import_source_path/1`

Today (`program.ex:1046`) it hard-codes the `["Std", name]` shape. Generalize to
consult an ordered list of **source roots**, Std first, then project roots:

```
import_source_path(source, source_roots) →
  for each root in [stdlib_dir | project_roots]:
    candidate = Path.join(root, module_rel_path(source))   # "My.Mod" → "my/mod.cure" (or per project layout)
    if File.exists?(candidate): return {:ok, source, candidate}
  {:error, {:unresolved_module_source, source, tried_paths}}
```

`:not_stdlib` disappears as a resolution outcome; a module that resolves nowhere
becomes an explicit `{:error, {:unresolved_module_source, …}}` rather than a
silent fail-open to `Env.empty()`. **This is the leniency fix** the rip-out audit
flagged separately (garbage/`use Std.Nonexistent` currently "compiles"): once
resolution can *fail*, a missing `use` target is a real error.

### Threading the project source roots

`Cure.Elab.Program.check_ast/2` currently ignores `opts` (program.ex:34:
`check_ast(ast, _opts)`). Thread `:source_roots` (a list of absolute dirs)
through:

- `Cure.Compiler.compile_and_load/2` and the project/CLI compile entry accept a
  `:source_roots` opt (default: the directory of the file being compiled, plus
  any `-I`/config roots), and pass it into `check_ast/2` and
  `check_ast_with_locals/2`.
- `check_ast/2` stores it and hands it to the import-resolution helpers
  (`imports/1` → `import_source_path/2` → `import_source_env/2`). Default `[]`
  preserves today's Std-only behavior for every existing single-file call site
  (so no current test moves unless it opts in).

### Recursion, cycles, ordering

`import_source_env/2` already recurses (it re-elaborates the imported source,
which itself has `use`s) and threads a `seen` set (program.ex:989+). User modules
join the same recursion:

- **Cycle guard:** the existing `seen` set must key on the *resolved source path*
  (not just the module name) and short-circuit a module already on the stack —
  mutual `use` between user modules must not loop. Emit a diagnostic
  (`W0xx :import_cycle`) rather than hanging; a cycle is legal for *types* if the
  signatures don't depend circularly, but v1 may reject it and defer.
- **Determinism:** resolution order follows import-BFS, matching
  `import_origins/1`'s "first owner in import-BFS order wins" (program.ex:476), so
  `import_origins` and the resolver agree on which module owns a name (they must —
  emit uses `import_origins` to pick the remote target).

### Selective imports (fold in the one genuine bug)

While here, fix the brace-group import bug the ImportTest diagnosis found:
`imports/1` (program.ex:736) drops `:items`, so `use Ns.{A, B}` imports nothing.

```
defp imports({:import, meta, _}) when is_list(meta) do
  source = Keyword.fetch!(meta, :source)
  case Keyword.get(meta, :items, []) do
    []    -> [source]
    items -> Enum.map(items, &(source <> "." <> &1))
  end
end
```

This is independent of user-module resolution (it's a plain dropped-field bug) but
lives in the same function and should land together. NOTE: it only advances
`use Std.{List, Core}` from `:unknown_global` to an `ambiguous_name`/goal-directed
wall — greening those ImportTest rows *also* needs the goal-directed implicit
solving gap (tracked separately; not part of this spec).

## Testing

Strict red-green, behavioral. New file
`test/cure/compiler/user_module_import_test.exs`:

1. **Resolves a sibling user module.** Write `lib_a.cure` (`mod LibA` with
   `fn ping() -> Int = 7`) and `lib_user.cure` (`use LibA` + `fn go() -> Int =
   ping()`) to a temp dir; compile with `source_roots: [tmp]`; assert `go/0`
   returns `7`. RED first (`:unknown_global`), GREEN after.
2. **Unresolvable module is a hard error.** `use Ghost` with no `ghost.cure` on
   any root → `{:error, {:unresolved_module_source, :"Cure.Ghost", _tried}}`
   (replaces today's silent fail-open).
3. **Mutual `use` terminates.** Two user modules that `use` each other for types
   → resolves or a clean `:import_cycle` diagnostic, never a hang (assert with a
   timeout).
4. **Selective brace import.** `use Ns.{A, B}` brings names from both.

Re-specify the two stale tests to the new contract:
- `multi_file_link_test` — drop the classic beam-import-table assertion; assert
  the linked call resolves + runs (compile both under one `source_roots`).
- `unresolved_import_warning_test` — the `W088` fallback is gone; either assert
  the new `{:error, {:unresolved_module_source, …}}` or, if a lint-warning path is
  restored, re-pin it. Decide when the resolver lands.

Full suite once at the gate (one build at a time).

## Constraints (carried)

- Layer **E/P** only — `lib/cure/elab/program.ex` (+ compile-entry opt plumbing in
  `lib/cure/compiler.ex` and the CLI). **No TCB change.**
- Ghost-writer commits `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`,
  no co-sign. Explicit-pathspec staging. One `mix` build at a time.

## Open questions (resolve at resume)

1. **Module → path mapping.** `"My.Mod"` → `my/mod.cure`? `my.mod.cure`?
   lowercased? Match whatever the project/CLI already assumes for output layout;
   confirm against the CLI directory-compile before coding.
2. **Re-elaboration cost / caching.** v1 re-elaborates each imported source per
   importer. Fine for correctness; a per-run memo keyed on resolved path is an
   obvious optimization but out of scope for v1.
3. **Cycle policy.** Reject mutual user-module `use` in v1, or support it for
   type-only dependencies? Lean reject-with-diagnostic first.
4. **Interaction with `import_origins/1`.** Confirm both walk imports identically
   so the owner chosen for a name's *type* (resolver) equals the owner chosen for
   its *remote-call target* (emit). A mismatch would type-check against one module
   and call another.

## Related

- Rip-out ledger / `ripout-tail-decisions` memory.
- Import diagnosis (this session): the dominant ImportTest blocker is the
  goal-directed implicit-solving gap, NOT imports — tracked separately.
- `dependent-emit-crossmodule-gap` memory (emit-side remote calls, already fixed).

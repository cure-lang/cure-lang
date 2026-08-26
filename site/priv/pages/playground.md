%{
  title: "Playground",
  description: "Browser-based checking and evaluation through Cure's dependent compiler.",
  order: 13
}
---

## Current status

The Playground now uses the same dependent compiler pipeline as ordinary Cure
builds. Editor updates run through `Cure.Compiler.compile_string/2`, while the
Run action uses `Cure.Compiler.compile_and_load/2` before invoking `main/0` in a
resource-limited process.

The supported interactive surfaces are:

- `cure repl` for checked local exploration;
- `cure check <file>` for dependent elaboration without emission;
- `cure run <file>` for checked compilation and `main/0` execution;
- editor/LSP integrations for structured diagnostics and holes.

## Compiler and isolation boundary

Both paths use the canonical module loader, stdlib/prelude discovery, structured
diagnostics, Core validation, and validated emission path. The application
warms the verified stdlib generation during startup so the first browser request
does not pay the complete preload cost.

Evaluation retains process isolation, output capture, a bounded process heap,
and a two-second execution deadline. These are useful resource controls, not a
security boundary: a public deployment still needs operating-system or
container isolation.

## Historical implementation

The v0.27/v0.28 site provided the debounced editor, Makeup highlighting, and
sandboxed evaluator. The current implementation keeps that interface while
replacing its deleted classic checker and emitter with the dependent compiler.

## Related

- [REPL](/repl)
- [Tooling](/tooling)
- [Type System](/type-system)
- [Roadmap](/roadmap)

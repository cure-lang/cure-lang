# SP3 Slice B: Generated Macro Use-Site Assembly

## Goal

Turn typed Core fillers from Slice A into complete use-site token streams and
run those streams through the real parser expansion entry point.

## Scope

- Add assembly helpers to `Cure.Compiler.MacroFuzz` for a parsed syntax rule.
- Preserve the rule keyword and literal segments in order, replacing each hole
  by its generated filler.
- Support the scalar surface encodings available in Slice A (`Nat` and `Bd`);
  return an explicit unsupported-surface error for other generated terms.
- Verify every assembled stream is fully consumed by
  `Parser.expand_example/2` and produces a non-sentinel expansion.

## Invariants

- Use the parser's own expansion path; do not duplicate segment matching.
- Generated terms remain kernel-checked by Slice A before assembly.
- No trusted Core changes.

## Verification

- A generated `Nat` use-site expands through a one-hole `becomes` rule for
  multiple deterministic samples.
- Unsupported surface encodings are reported.
- Focused compiler tests and formatting pass.


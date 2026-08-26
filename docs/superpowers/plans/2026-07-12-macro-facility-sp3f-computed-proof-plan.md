# SP3 Slice F: Generated Proof for Computed Rules

## Goal

Extend the live generated expansion gate from template rules to Tier-3
`computed by` rules now that deferred execution and typed input records exist.

## Scope

- Generate supported hole fillers for computed rules.
- Parse the generated use-site into a deferred `computed_use` node.
- Execute it through `MacroExpand.expand/2`, then run the same elaborator/kernel
  proof check and shrink path as template rules.
- Include computed rules in proof manifests.

## Invariants

- Computed output remains untrusted and is re-elaborated before acceptance.
- Execution failures are reported as proof failures, never as skipped coverage.
- No trusted Core changes.

## Verification

- A computed identity elab passes generated inputs.
- A computed elab producing an ill-typed reflected literal is rejected by the
  generated gate.
- Existing computed macro tests remain green.


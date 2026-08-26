# SP3 Slice E: Proof Manifest and Cache

## Goal

Make generated macro proof work observable and avoid repeating identical
successful or failing proof runs for the same macro definition and environment.

## Scope

- Record one manifest entry per syntax rule with hole categories, draw budget,
  and pass/fail status.
- Cache the complete proof result and manifest by a definition/environment
  fingerprint.
- Expose a testable manifest API that reports whether a result came from cache.

## Invariants

- Cache hits return the exact stored result; they never turn a failure into a
  pass or reduce the proof budget.
- Any macro AST or environment change produces a different key.
- No Antigen seed/corpus banking and no trusted Core changes.

## Verification

- Multi-rule manifests list every syntax rule.
- The second identical lookup reports a cache hit and returns the same result.
- A changed rule misses the cache.


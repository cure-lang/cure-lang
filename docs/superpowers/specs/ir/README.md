# Intermediate-representation specification family

## Authority hierarchy

1. [`2026-07-21-multiple-irs-architecture-design.md`](2026-07-21-multiple-irs-architecture-design.md)
   owns the complete IR sequence and the responsibilities of each layer.
2. [`2026-07-21-lean-verified-middle-end-design.md`](2026-07-21-lean-verified-middle-end-design.md)
   owns the Lean implementation boundary, validation, proof structure, and
   host integration.
3. [`2026-07-21-cure-core-json-schema.md`](2026-07-21-cure-core-json-schema.md)
   and `cure-core-0.1.schema.json` own the serialized input contract.
4. [`2026-07-21-cure-flow-machine-semantics.md`](2026-07-21-cure-flow-machine-semantics.md)
   owns Flow transition semantics and ownership-preserving suspension.
5. [`2026-07-21-lean-core-erlang-proof-boundary.md`](2026-07-21-lean-core-erlang-proof-boundary.md)
   owns the verified Core Erlang target boundary.
6. [`2026-07-21-lowcure-restricted-ir-design.md`](2026-07-21-lowcure-restricted-ir-design.md)
   owns the restricted ownership-aware C/Rust/Wasm/MCU target profile.

These are subsidiary specifications, not competing IR architectures. Changes
to the sequence belong in `multiple-irs`; changes to Lean proof obligations
belong in `lean-verified-middle-end`; target-specific rules belong in the
relevant subsidiary document.

`2026-07-14-backend-decoupling-cureir-design.md` is parked historical context.
It should be consulted for motivation, but it does not override the 2026-07-21
pipeline.

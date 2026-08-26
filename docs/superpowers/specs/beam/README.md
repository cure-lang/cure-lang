# BEAM and OTP specification family

- `2026-07-09-typed-beam-process-algebra-design.md` defines the original typed
  process algebra.
- `2026-07-10-checked-beam-concurrency-design.md` is the later concurrency and
  linear-resource correction; its supersession statements govern conflicts with
  the earlier process-algebra document.
- `2026-07-14-otp-conformance-fixes-design.md` records conformance repairs to
  the typed OTP surface.
- `2026-07-19-typed-beam-representation-design.md` owns foreign boundary
  representation and encoding/decoding.
- `2026-07-19-typed-actor-behavior-design.md` owns actors and their shared
  behavior substrate.
- `2026-07-19-typed-fsm-as-constrained-actor-design.md` owns FSM lowering as a
  constrained actor.
- `2026-07-13-cure-port-interactive-design.md` is an independent Core Erlang
  porting tool design, not part of the actor/FSM runtime contract.

# cure_pool — the verified core (pure Cure)

This half of `cure_pool` is a pure Cure project: `Cure.toml`, `lib/`, `test/`,
and nothing else. It is where the pool's **compile-time guarantees** live.

## The guarantees

| Guarantee | Enforced by | Fixture that must fail |
|---|---|---|
| no over-checkout | `Pool(S(n), m)` argument type | `negative/checkout_empty.cure` |
| no double-return | `@linear` lease | `negative/double_return.cure` |
| no leak | `@linear` lease | `negative/dropped_lease.cure` |

## Run it

```bash
# The scripted, verified walk: checkout -> run -> checkin, counts in the type.
cure run lib/main.cure

# Positive tests.
cure test

# The proof: every fixture that MUST fail to compile, and does.
./negative/run_negative.sh

# The worker FSM's graph, verified at compile time.
cure run lib/worker_fsm.cure
```

## Layout

```text
Cure.toml
lib/pool_core.cure     Pool(avail,in_use) + linear Lease + checkout/checkin
lib/worker_fsm.cure    Std.Fsm: Idle/Reserved/Active/Returning graph
lib/main.cure          main/0: the scripted verified walk
test/pool_test.cure    positive tests
negative/              MUST-FAIL fixtures + the driver that asserts it
```

See `../README.md` for the full story and `../docs/POOL.md` for the design
notes verified against the compiler.

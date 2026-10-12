# cure_pool — a safe linear resource pool in Cure

**The compiler proves your pool can't leak, double-free, or over-checkout.**

This is the flagship end-to-end example for Cure's *verified concurrency*
niche: dependent types plus first-class OTP, applied to the one problem every
Erlang/Elixir system has — a pool of checked-out resources.

In a conventional pool (poolboy and friends) a worker can be checked out twice,
forgotten, used after its checkout has been returned, or lost when a client
crashes. Those are *runtime* failures you discover in production. Here they are
**compile errors**, and the example ships the fixtures that prove it.

## The two guarantees, and how to see them

### 1. No over-checkout — the count is a *type*, not a counter

A pool is `Pool(avail, in_use)`, a pair of `Nat` indices:

```text
type Pool indices (avail: Nat, in_use: Nat)
  mk_pool : (capacity: Int) -> Pool(avail, in_use)

## checkout is only defined on a NON-EMPTY pool: the index S(n) is the proof.
fn checkout(n: Nat, m: Nat, k: Nat, worker: Int, p: Pool(S(n), m)) -> %[Lease(k), Pool(n, S(m))]
```

Checking out moves a slot in the **type**: `Pool(2,0) → Pool(1,1)`. Checking a
pool out when it is empty has no `S(n)` to match, so it does not type-check:

```console
$ ./negative/run_negative.sh
ok    checkout_empty: rejected with E093
```

### 2. No double-return and no leak — the lease is *linear*

A `Lease` is a `@linear` capability. The kernel proves it is consumed exactly
once on every path:

```console
$ ./negative/run_negative.sh
ok    double_return: rejected with E117   # used twice  -> use-after-free
ok    dropped_lease: rejected with E117   # never used  -> leak
```

`E117 LINEAR VALUE MAY BE USED MORE THAN ONCE` is the double-return /
use-after-free bug. `E117 LINEAR VALUE IS NOT USED` is the "checked out and
forgot to return it" bug. Both are rejected before any code runs.

### 3. Crashes don't strand slots — the runtime half

Types cover programs that type-check. A live system also has to survive
*untyped* events: a client dying mid-lease, a worker crashing, a node
disconnecting. The Elixir-hosted runtime monitors every checkout and reclaims
the slot the instant the holder goes away, so `available + in_use` is invariant
across the crash:

```console
$ cd elixir && mix test
...
  * test a client that dies mid-lease has its slot reclaimed
  * test a crashed worker is replaced, keeping capacity constant
  * test many concurrent holders crashing never leak a slot
```

## Layout

```text
cure_pool/
├── cure/                        # PURE CURE CORE -- the verified half
│   ├── Cure.toml
│   ├── lib/
│   │   ├── pool_core.cure        # Pool(avail,in_use) + linear Lease + checkout/checkin
│   │   ├── worker_fsm.cure       # Std.Fsm: Idle/Reserved/Active/Returning graph
│   │   └── main.cure             # main/0: the scripted verified walk
│   ├── test/pool_test.cure       # positive tests (cure test)
│   └── negative/                 # MUST-FAIL fixtures + the driver that asserts it
│       ├── checkout_empty.cure
│       ├── double_return.cure
│       ├── dropped_lease.cure
│       └── run_negative.sh
│
├── elixir/                      # ELIXIR-HOSTED RUNTIME -- the live half
│   ├── cure_src/worker_fsm.cure  # the FSM, compiled to a raw BEAM atom
│   ├── lib/cure_pool/pool.ex     # supervised slot registry + crash reclaim
│   ├── lib/cure_pool.ex          # facade
│   └── test/
│       ├── pool_test.exs         # checkout/checkin, exhaustion, double-return guard
│       └── crash_reclaim_test.exs# the crash-reclaim guarantee
│
└── docs/POOL.md                 # design notes, verified against the compiler
```

## Run it

### The verified core (pure Cure)

```bash
cd cure

# The scripted, verified walk: checkout -> run -> checkin, counts in the type.
cure run lib/main.cure

# Positive tests.
cure test

# The proof: every fixture that MUST fail to compile, and does.
./negative/run_negative.sh

# The worker FSM's graph, verified at compile time.
cure run lib/worker_fsm.cure
```

`cure run lib/main.cure` prints:

```text
cure_pool -- a safe linear resource pool in Cure

checkout -> run(3) -> checkin on a 2-slot pool
10

the pool's counts are a TYPE, not a counter:
  Pool(2,0)  all free
  Pool(1,1)  one checked out   (checkout)
  Pool(2,0)  all free again     (checkin)
```

### The live runtime (Elixir-hosted)

```bash
cd elixir
mix deps.get
mix test
```

## The FSM

Each worker's lifecycle is a compile-time-verified state machine:

```text
Idle --Reserve(client)--> Reserved --Activate(key)--> Active
Active --Return--> Returning --Reclaim--> Idle
Active --Timeout--> Returning
```

The `Timeout` edge is the safety net: a client that checks a worker out and
then vanishes does not strand it. The graph is checked while it compiles —
reachability, deadlock-freedom, and payload consistency. Delete a transition
and re-run `cure run lib/worker_fsm.cure` to watch the compiler reject it with
`fsm_deadlocked_state`.

## What this demonstrates about Cure

- **Dependent types on a real problem.** `Pool(avail, in_use)` is the indexed
  family from `Std.Vector`, applied to resource counting. The count is not a
  field someone can forget to decrement; it is the type.
- **Linear capabilities.** `Lease` uses the same `{0,1,ω}` usage accounting that
  guards `@linear from : Reply(r)` in every generated OTP `handle_call`. The
  compiler's "used exactly once" rule is what turns double-return and leaks
  into type errors.
- **Typed FSM as a transparent macro.** `fsm Worker with WorkerData` is ordinary
  `Std.Fsm` syntax, expanded to a checked `gen_statem`, verified at compile
  time. There is no FSM-specific compiler object.
- **OTP interop.** The compiled FSM is a standard BEAM `gen_statem` the Elixir
  side drives by its atom; supervision, monitoring, and crash recovery are
  ordinary OTP.

## Honest notes on the toolchain

This example was built against Cure 0.34.3 and is deliberately candid about
where the compiler's edges are — a language whose value is *"the compiler
proves things"* is only as credible as its honesty about what it does and does
not yet prove. `docs/POOL.md` records each of these with the reproduction:

- `cure check` does not reliably validate an `fsm` declaration; `cure run` on a
  single file does. The FSM here is validated that way.
- A macro-generated submodule cannot be called from project-mode Cure code, so
  the *live* process half is hosted in Elixir and drives the FSM by its raw
  BEAM atom — the same pattern `examples/cure_moneta` and
  `examples/cure_exchange` use.
- A cross-file annotation on a nested indexed type is rejected by a
  definitional-equality bug, so the core's types are written once (in
  `Pool.Core`) and callers rely on inference. The types are still checked; they
  are just not repeated at every binding.
- Inline `##` comments are not allowed inside a function body.

None of these affect the guarantees above: every one of them was reproduced
end-to-end before this example claimed it.

## Where to go next

- Replace the placeholder worker with the compiled `WorkerFsm` process, so each
  slot's lifecycle is the verified state machine end to end.
- Add a `Lease`-indexed `Effect` so the checkout/checkin cycle can be written
  in direct style.
- Lift the slot count into the pool process's own type, so a pool of capacity
  `n` can only be asked for `n` checkouts at the type level.

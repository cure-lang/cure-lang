# cure_pool — the live runtime (Elixir-hosted)

This half of `cure_pool` runs the pool as a supervised OTP process and proves
the **crash-reclaim guarantee**: a client or worker dying mid-lease does not
strand a slot.

The Cure FSM that models each worker's lifecycle is compiled from
`cure_src/worker_fsm.cure` to the raw BEAM module `:"Cure.Main.WorkerFsm"` and
is verified at Cure compile time.

## Run it

```bash
mix deps.get
mix test
```

## Layout

```text
cure_src/worker_fsm.cure        the FSM, compiled to a raw BEAM atom
lib/cure_pool/pool.ex           supervised slot registry + crash reclaim
lib/cure_pool/application.ex    the OTP application
lib/cure_pool.ex                facade
test/pool_test.exs              checkout/checkin, exhaustion, double-return guard
test/crash_reclaim_test.exs     the crash-reclaim guarantee
```

See `../README.md` for the full story and `../docs/POOL.md` for the design
notes verified against the compiler.

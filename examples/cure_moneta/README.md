# cure_moneta

A money and ledger library written in Cure. The example focuses on ADTs,
records, dependent data, and checked foreign calls. Its process
surface uses the transparent standard-library macros rather than a bespoke
FSM compiler.

## Quick start

```bash
cd examples/cure_moneta
mix deps.get
mix test
```

## Domain model

```text
type Currency = EUR | USD | GBP | JPY | CHF | OMR

rec Money
  amount: Int
  currency: Currency
  fractional_units: Int

rec Ledger
  accounts: List(Account)
```

The ledger operations are pure and return `Result` values. Currency rendering,
functional record updates, and the float FFI are all ordinary Cure declarations.

## Transparent process floor

`cure_src/transaction.cure` declares a transparent FSM module:

```cure
use Std.Fsm

fsm Transaction with Int
  Idle --create--> Pending
  Pending --submit--> Awaiting
  Awaiting --confirm--> Settled
  Awaiting --reject--> Failed
    update 0
  Failed --retry--> Pending
    update 0
  Awaiting --on_timer--> Failed
    update 0
  * --cancel--> Cancelled
```

The transition rows are checked macro data and dispatch is generated as ordinary
Cure declarations. The bare module name is owned by top-level `Main`, producing
`Cure.Main.Transaction`; source does not author the emitter's `Cure.` prefix.

## Layout

```text
cure_src/moneta.cure       domain types and ledger operations
cure_src/transaction.cure  transparent FSM floor
lib/cure_moneta.ex         Elixir-facing facade
test/cure_moneta_test.exs  domain and interop tests
```

# cure_exchange (Elixir + Cure FSM)

A multi-currency exchange and escrow engine where **only the state graph is
written in Cure**; money, the ledger, quote/timer orchestration, bank-webhook
simulation, and the multi-step refund rollback are all Elixir. Structured
like [`examples/cure_turnstile`](../../cure_turnstile) and
[`examples/cure_moneta`](../../cure_moneta): a single `.cure` file compiled
by a custom Mix task, driven from Elixir through its raw BEAM module name.
See [`../cure`](../cure) for the sibling project written entirely in Cure.

## The scenario

```text
                        [ Created ]
                             |
                             | LockFunds(amount, quote_id)
                             v
                     [ FundsReserved ]
                      /             \
        QuoteExpired /               \ CounterpartyMatched(trade_id)
                    v                 v
               [ Cancelled ]      [ ExecutingSwap ]
                                   /            \
                  BankConfirmed   /              \ SettleTimeout / BankFailed
                                 v                v
                           [ Completed ]     [ Refunding ]
                                                  |
                                                  | RefundCompleted
                                                  v
                                             [ Refunded ]
```

`TradeWorker` owns one trade end to end: it starts the compiled FSM, reserves
the escrow hold, starts a rate-lock timer, and reacts to whichever of
"counterparty matched" / "quote expired" happens first. Once matched, it
starts a simulated bank webhook timer *and* a settlement safety-net timer,
and reacts to whichever of "bank webhook" / "settle timeout" happens first --
capturing the hold on confirmation, or rolling it back on failure or timeout.

## Layout

```text
cure_src/escrow_fsm.cure              the state graph, and only the state graph
lib/mix/tasks/compile_cure.ex         compiles cure_src/*.cure via Cure.Compiler.compile_file
lib/cure_exchange/money.ex            Money struct, arithmetic, FX conversion
lib/cure_exchange/ledger.ex           GenServer: reserve/capture/release accounts
lib/cure_exchange/quote_service.ex    rate-lock quote generation
lib/cure_exchange/trade_worker.ex     GenServer: owns one trade's FSM, timers, webhook, rollback
lib/cure_exchange/trade_supervisor.ex DynamicSupervisor, one TradeWorker per trade
lib/cure_exchange/application.ex      starts Ledger + TradeSupervisor
lib/cure_exchange.ex                  the public facade
test/cure_exchange_test.exs           raw FSM tests + TradeWorker/CureExchange integration tests
```

## Quick start

```bash
cd examples/cure_exchange/elixir
mix deps.get
mix test
```

```elixir
iex -S mix

CureExchange.open_account(1, "Alice", 1_000_000, :usd)   # USD 10,000.00
{:ok, pid, quote_id} = CureExchange.open_trade(1, :usd, 10_000, bank_delay_ms: 50)
CureExchange.match_counterparty(pid, :"T-1")
# wait a beat for the simulated webhook...
CureExchange.status(pid)
# => %{state: :Completed, data: %{amount: 10000, quote_id: ^quote_id, trade_id: :"T-1", attempts: 0}}
CureExchange.balance(1)
# => {:ok, %CureExchange.Money{amount: 990000, currency: :usd}}
```

## The FSM, and only the FSM

`cure_src/escrow_fsm.cure` declares nothing but the state graph:

```cure
use Std.Fsm

rec EscrowData
  amount: Int
  quote_id: Atom
  trade_id: Atom
  attempts: Int

fsm EscrowFsm with EscrowData
  terminal Cancelled
  terminal Completed
  terminal Refunded

  Created --LockFunds(amount: Int, quote_id: Atom)--> FundsReserved
    when amount > 0
    update EscrowData{data | amount: amount, quote_id: quote_id}
  FundsReserved --QuoteExpired--> Cancelled
  FundsReserved --CounterpartyMatched(trade_id: Atom)--> ExecutingSwap
    update EscrowData{data | trade_id: trade_id}
  ExecutingSwap --BankConfirmed--> Completed
  ExecutingSwap --SettleTimeout--> Refunding
    update EscrowData{data | attempts: data.attempts + 1}
  ExecutingSwap --BankFailed--> Refunding
  Refunding --RefundCompleted--> Refunded
```

`quote_id`/`trade_id` are `Atom`, not `String`: they are opaque handles the
graph never inspects, and an `Atom` crosses the Cure/Elixir boundary as a
bare atom with no wrapping. A Cure `String` is a nominal type that erases to
`{String, code_points}` (see `docs/FFI.md`); a plain Elixir binary or
charlist does not satisfy that shape, and this project has no reason to pay
that conversion cost for a value neither side ever reads the contents of.

`compile_cure` compiles this one file with `Cure.Compiler.compile_file/2` --
a single-file compile, not the project/directory-mode `cure compile <dir>`
the escript CLI uses for `cure test`. That distinction matters: see
[`../cure`'s README](../cure/README.md#known-limitations-found-while-building-this-example)
for a project-mode limitation this same compiler build has with `fsm`
declarations, which this project's structure (following `cure_turnstile` and
`cure_moneta`) never encounters in the first place.

## Wire format

The compiled module (`:"Cure.Main.EscrowFsm"`) is an ordinary `gen_statem`.
Confirmed by starting it directly and inspecting `:sys.get_state/1` after
each cast (see `test/cure_exchange_test.exs`'s raw FSM tests):

- **States** are plain atoms: `:Created`, `:FundsReserved`, `:ExecutingSwap`,
  `:Cancelled`, `:Completed`, `:Refunding`, `:Refunded`.
- **Data** is a positional record tuple: `{:EscrowData, amount, quote_id,
  trade_id, attempts}`.
- **Events** are `:EventName` for payload-less events (`:QuoteExpired`,
  `:BankConfirmed`, `:SettleTimeout`, `:BankFailed`, `:RefundCompleted`) and
  `{:EventName, ...fields}` for the two payload-bearing ones:
  `{:LockFunds, amount, quote_id}`, `{:CounterpartyMatched, trade_id}`.

`TradeWorker` drives the FSM with plain `:gen_statem.cast/2` calls using
exactly these shapes.

## Timers and webhooks are just messages

A rate-lock expiry and a bank webhook are, from the FSM's point of view,
both just an event that shows up some time after `LockFunds`. `TradeWorker`
models both literally that way: `Process.send_after/3` schedules an
ordinary message to itself, and `handle_info/2` turns it into a
`:gen_statem.cast/2`. Before applying the corresponding *side effect*
(releasing or capturing the ledger hold), it re-reads the FSM's actual
current state with `:sys.get_state/1` -- a timer that fires after the state
has already moved on is confirmed to be a no-op before any money moves,
exactly mirroring the graph's own safe fallback for an event with no
matching row (`test/cure_exchange_test.exs` has a race test for this: a
counterparty match that lands right before the quote-expiry timer fires).

## The multi-step refund rollback

On `BankFailed` or `SettleTimeout`, `TradeWorker.refund/1`: releases the
hold back to the account's available balance in `CureExchange.Ledger`,
records that the refund happened, and only then casts `RefundCompleted` to
the FSM -- the state transition is the last thing that happens, after the
money has actually moved, not the first.

## What it demonstrates

- **A real escrow state graph, entirely in Cure** -- typed event payloads, a
  guard, three terminal states, verified at compile time by the same
  `Std.Fsm` machinery documented in `docs/FSM_GUIDE.md`.
- **OTP actor lifecycle end to end** -- a `DynamicSupervisor` of
  `:transient` `TradeWorker`s, each of which starts, links to, and drives a
  Cure-compiled `gen_statem` child; `Process.send_after/3` /
  `Process.cancel_timer/1` for both the rate-lock and the settlement
  safety net; `:sys.get_state/1` used defensively before every side effect.
- **A clean language boundary** -- the FSM never imports money, a ledger, or
  a clock; Elixir never re-implements the state graph. Each side owns
  exactly what it is good at.

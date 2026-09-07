# Escrew&Exchange project

This guide explores a multi-currency escrow and exchange engine implemented in two distinct ways:

1. **Pure Cure Project** (`examples/cure_exchange/cure`) — The domain model, double-entry hold ledger, state transition logic, FSM graph verification, and scenario playback are written entirely in Cure with no Elixir wrappers.
2. **Elixir + Cure FSM Hybrid** (`examples/cure_exchange/elixir`) — The state transition graph is written and type-checked in Cure, while process lifecycle, rate-lock timers, simulated bank webhooks, and OTP supervision are orchestrated in Elixir.

Both projects model the same escrow state machine and guarantee financial invariants, illustrating how Cure can be used as a standalone language or embedded into an existing Elixir/OTP application.

---

## 1. The Escrow Scenario & State Graph

An escrow trade reserves funds when a buyer locks a rate quote. The trade then proceeds along one of two main pathways: counterparty matching and settlement, or cancellation due to quote expiration. If bank settlement fails or times out, the engine performs an automated refund.

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

### States and Events

* **States**: `Created`, `FundsReserved`, `ExecutingSwap`, `Cancelled`, `Completed`, `Refunding`, `Refunded`.
  * Terminal states: `Cancelled`, `Completed`, `Refunded`.
* **Events**:
  * `LockFunds(amount, quote_id)`: Reserves available account balance into an escrow hold. Requires `amount > 0`.
  * `QuoteExpired`: Rates locked for the trade timed out before a counterparty was matched; unwinds the hold.
  * `CounterpartyMatched(trade_id)`: Binds a matching trade and begins simulated bank settlement.
  * `BankConfirmed`: Bank completed the fiat transfer; captures the held funds (payout).
  * `BankFailed` / `SettleTimeout`: Bank rejected the settlement or failed to respond within the deadline; initiates a refund.
  * `RefundCompleted`: Money has been returned to the buyer's balance; marks the FSM as refunded.

---

## 2. Pure Cure Implementation (`examples/cure_exchange/cure`)

The pure Cure project demonstrates how to structure a complete domain application with `Cure.toml`, standard library modules, algebraic data types, record operations, FFI bindings, and transition functions.

### Directory Structure

```text
examples/cure_exchange/cure/
├── Cure.toml                            # Project manifest
├── lib/
│   ├── money.cure                       # Exchange.Money (Currency ADT, Money record, FX conversion)
│   ├── ledger.cure                      # Exchange.Ledger (Account & Ledger records, hold lifecycle)
│   ├── escrow_fsm.cure                  # Exchange.EscrowFsm (State/Event ADTs + total transition/3)
│   ├── escrow_fsm_dsl_reference.cure    # Exchange.EscrowFsmDslReference (Std.Fsm macro DSL)
│   ├── escrow.cure                      # Exchange.Escrow (FSM transition walk + ledger side effects)
│   ├── otp_demo.cure                    # Exchange.OtpDemo (Std.Otp process identity demo)
│   └── main.cure                        # Exchange.Demo (main/0 entry point)
└── test/                                # Std.Test unit test suite
    ├── escrow_fsm_test.cure
    ├── escrow_test.cure
    ├── ledger_test.cure
    ├── money_test.cure
    └── otp_demo_test.cure
```

### Double-Entry Hold Ledger (`lib/ledger.cure`)

To prevent double-spending, accounts maintain two separate amounts: `balance` (available to spend) and `held` (locked in active escrows).

```text
mod Exchange.Ledger
  use Std.Result
  use Exchange.Money

  rec Account
    id: Int
    owner: String
    balance: Exchange.Money.Money
    held: Exchange.Money.Money

  rec Ledger
    accounts: List(Account)
```

The escrow hold lifecycle is governed by three total operations:

1. `reserve(ledger, account_id, amount)`: Moves `amount` from `balance` into `held` (`LockFunds`).
2. `capture(ledger, account_id, amount)`: Debits `held` entirely when a trade completes (`BankConfirmed`).
3. `release(ledger, account_id, amount)`: Moves `held` back into `balance` on cancellation or refund (`RefundCompleted`).

```text
  ## Move amount from available balance into hold
  fn reserve(ledger: Ledger, id: Int, amount: Exchange.Money.Money) -> Result(Ledger, String) =
    match find_account(ledger.accounts, id)
      Error(e) -> ledger_error(e)
      Ok(account) ->
        match Exchange.Money.subtract(account.balance, amount)
          Error(e) -> ledger_error(e)
          Ok(new_balance) ->
            match Exchange.Money.add(account.held, amount)
              Error(e) -> ledger_error(e)
              Ok(new_held) ->
                ledger_ok(update_account(ledger, Account{account | balance: new_balance, held: new_held}))
```

### Pure FSM Transition Function (`lib/escrow_fsm.cure`)

`Exchange.EscrowFsm` models transitions using a `match` expression over state and event ADTs. Unhandled state/event combinations return `Keep(data)` instead of crashing, ensuring stray webhooks or delayed timers are safely ignored.

```text
mod Exchange.EscrowFsm
  use Std.Fsm

  rec EscrowData
    amount: Int
    quote_id: String
    trade_id: String
    history: List(String)

  type EscrowState =
    | Created
    | FundsReserved
    | ExecutingSwap
    | Cancelled
    | Completed
    | Refunding
    | Refunded

  type EscrowEvent =
    | LockFunds(Int, String)
    | QuoteExpired
    | CounterpartyMatched(String)
    | BankConfirmed
    | SettleTimeout
    | BankFailed
    | RefundCompleted

  fn transition(state: EscrowState, event: EscrowEvent, data: EscrowData) -> FsmAction(EscrowState, EscrowData) =
    match state
      Created() -> match event
        LockFunds(amount, quote_id) ->
          pickup
            amount > 0 -> Next(FundsReserved(), record(EscrowData{data | amount: amount, quote_id: quote_id}, event))
            else       -> Keep(data)
        _ -> Keep(data)
      FundsReserved() -> match event
        QuoteExpired() -> Next(Cancelled(), record(data, event))
        CounterpartyMatched(trade_id) -> Next(ExecutingSwap(), record(EscrowData{data | trade_id: trade_id}, event))
        _ -> Keep(data)
      ExecutingSwap() -> match event
        BankConfirmed() -> Next(Completed(), record(data, event))
        SettleTimeout() -> Next(Refunding(), record(data, event))
        BankFailed() -> Next(Refunding(), record(data, event))
        _ -> Keep(data)
      Refunding() -> match event
        RefundCompleted() -> Next(Refunded(), record(data, event))
        _ -> Keep(data)
      Cancelled() -> Keep(data)
      Completed() -> Keep(data)
      Refunded() -> Keep(data)
```

### Declarative Graph Verification (`lib/escrow_fsm_dsl_reference.cure`)

In addition to hand-written transitions, the project includes `Exchange.EscrowFsmDslReference`, which uses Cure's `Std.Fsm` macro DSL. When compiled, the compiler automatically verifies graph properties (reachability, deadlock-freedom, and payload consistency):

```text
mod Exchange.EscrowFsmDslReference
  use Std.Fsm

  rec EscrowData
    amount: Int
    quote_id: String
    trade_id: String

  fsm Escrow with EscrowData
    terminal Cancelled
    terminal Completed
    terminal Refunded

    Created --LockFunds(amount: Int, quote_id: String)--> FundsReserved
      when amount > 0
      update EscrowData{data | amount: amount, quote_id: quote_id}
    FundsReserved --QuoteExpired--> Cancelled
    FundsReserved --CounterpartyMatched(trade_id: String)--> ExecutingSwap
      update EscrowData{data | trade_id: trade_id}
    ExecutingSwap --BankConfirmed--> Completed
    ExecutingSwap --SettleTimeout--> Refunding
    ExecutingSwap --BankFailed--> Refunding
    Refunding --RefundCompleted--> Refunded
```

### Running the Pure Cure Project

Run the main runner script or test suite using the `cure` CLI:

```bash
cd examples/cure_exchange/cure

# Execute the 4 trade scenarios
cure run lib/main.cure

# Verify compile-time FSM graph validation
cure run lib/escrow_fsm_dsl_reference.cure

# Run unit tests
cure test
```

Output of `cure run lib/main.cure`:

```text
cure_exchange -- a multi-currency escrow engine in Cure

happy path       : Completed  balance=USD 9900.00  held=USD 0.00
quote expired    : Cancelled  balance=USD 10000.00  held=USD 0.00
bank failed      : Refunded  balance=USD 10000.00  held=USD 0.00
settle timed out : Refunded  balance=USD 10000.00  held=USD 0.00
```

---

## 3. Elixir + Cure FSM Hybrid (`examples/cure_exchange/elixir`)

The hybrid project places the state graph definition inside Cure (`cure_src/escrow_fsm.cure`) and delegates process orchestration, OTP supervision, timers, webhooks, and ledger management to Elixir.

### Directory Structure

```text
examples/cure_exchange/elixir/
├── mix.exs                             # Mix configuration
├── cure_src/
│   └── escrow_fsm.cure                 # Pure Cure state machine definition
├── lib/
│   ├── mix/tasks/compile_cure.ex       # Custom Mix task compiling cure_src/*.cure
│   └── cure_exchange/
│       ├── money.ex                    # Elixir Money struct & FX helper
│       ├── ledger.ex                   # GenServer managing account balances & holds
│       ├── quote_service.ex            # Rate quote generator
│       ├── trade_worker.ex             # GenServer driving FSM & timers
│       ├── trade_supervisor.ex         # DynamicSupervisor for trade workers
│       ├── application.ex              # Root application supervisor
│       └── cure_exchange.ex            # Public facade
└── test/
    └── cure_exchange_test.exs          # BEAM wire-format tests & integration suite
```

### The Embedded FSM (`cure_src/escrow_fsm.cure`)

The state machine is defined using `Std.Fsm`. Note that identifiers like `quote_id` and `trade_id` use `Atom` to cross the BEAM boundary cleanly without String allocation overhead.

```text
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

### Custom Mix Compiler (`lib/mix/tasks/compile_cure.ex`)

A custom Mix task invokes `Cure.Compiler.compile_file/2` during `mix compile`, compiling `cure_src/escrow_fsm.cure` directly into `_build/dev/lib/cure/ebin/Cure.Main.EscrowFsm.beam`.

```elixir
defmodule Mix.Tasks.Compile.Cure do
  use Mix.Task

  @impl Mix.Task
  def run(_args) do
    Mix.shell().info("Compiling Cure files in cure_src/...")
    # Calls Cure.Compiler.compile_file on cure_src/escrow_fsm.cure
    # ...
  end
end
```

### BEAM Wire Format Integration (`lib/cure_exchange/trade_worker.ex`)

Elixir interacts with the compiled Cure module (`:"Cure.Main.EscrowFsm"`) as a standard Erlang `:gen_statem` process:

* **States**: Plain Erlang atoms (`:Created`, `:FundsReserved`, `:ExecutingSwap`, `:Cancelled`, `:Completed`, `:Refunding`, `:Refunded`).
* **Data**: Positional record tuple `{:EscrowData, amount, quote_id, trade_id, attempts}`.
* **Events**: Single atoms (`:QuoteExpired`, `:BankConfirmed`) or tuples (`{:LockFunds, amount, quote_id}`, `{:CounterpartyMatched, trade_id}`).

`TradeWorker` spawns the FSM, issues `:gen_statem.cast/2` commands, and checks state with `:sys.get_state/1` before applying ledger side effects:

```elixir
defmodule CureExchange.TradeWorker do
  use GenServer
  alias CureExchange.Ledger

  @escrow_fsm :"Cure.Main.EscrowFsm"

  def init(opts) do
    account_id = Keyword.fetch!(opts, :account_id)
    hold = Money.new(Keyword.fetch!(opts, :amount), Keyword.fetch!(opts, :currency))
    quote_id = Keyword.fetch!(opts, :quote_id)

    with :ok <- Ledger.reserve(account_id, hold),
         {:ok, fsm} <- apply(@escrow_fsm, :start_link, [{:EscrowData, 0, :none, :none, 0}]) do
      :gen_statem.cast(fsm, {:LockFunds, hold.amount, quote_id})
      quote_timer = Process.send_after(self(), :quote_expired, Keyword.fetch!(opts, :quote_ttl_ms))

      {:ok, %__MODULE__{fsm: fsm, account_id: account_id, hold: hold, quote_timer: quote_timer, ...}}
    end
  end

  def handle_info(:quote_expired, state) do
    if fsm_state(state) == :FundsReserved do
      :gen_statem.cast(state.fsm, :QuoteExpired)
      Ledger.release(state.account_id, state.hold)
    end
    {:noreply, %{state | quote_timer: nil}}
  end

  # Multi-step refund rollback pattern
  defp refund(state) do
    :ok = Ledger.release(state.account_id, state.hold)
    :gen_statem.cast(state.fsm, :RefundCompleted)
  end

  defp fsm_state(state) do
    {name, _data} = :sys.get_state(state.fsm)
    name
  end
end
```

### Running the Hybrid Project

```bash
cd examples/cure_exchange/elixir

# Install dependencies and run test suite
mix deps.get
mix test
```

Interactive shell session (`iex -S mix`):

```elixir
# Open account with USD 10,000.00 balance
CureExchange.open_account(1, "Alice", 1_000_000, :usd)

# Open a trade reserving USD 100.00
{:ok, pid, quote_id} = CureExchange.open_trade(1, :usd, 10_000, bank_delay_ms: 50)

# Match counterparty
CureExchange.match_counterparty(pid, :"T-1")

# Check trade status
CureExchange.status(pid)
# => %{state: :Completed, data: %{amount: 10000, quote_id: ^quote_id, trade_id: :"T-1", attempts: 0}}

# Check remaining available balance
CureExchange.balance(1)
# => {:ok, %CureExchange.Money{amount: 990000, currency: :usd}}
```

---

## 4. Comparison Summary

| Aspect | Pure Cure (`examples/cure_exchange/cure`) | Elixir + Cure FSM (`examples/cure_exchange/elixir`) |
| :--- | :--- | :--- |
| **Primary Domain Logic** | Pure Cure (`Exchange.Money`, `Exchange.Ledger`, `Exchange.Escrow`) | Elixir (`CureExchange.Money`, `CureExchange.Ledger`, `CureExchange.TradeWorker`) |
| **State Machine** | Transition function & `Std.Fsm` reference | Embedded `Std.Fsm` compiled to `:"Cure.Main.EscrowFsm"` |
| **Concurrency / Process Model** | Direct state folds (`Exchange.Escrow.play/5`) | `:gen_statem` driven by Elixir `GenServer` & `DynamicSupervisor` |
| **Build & Toolchain** | Native `cure` CLI (`cure run`, `cure test`) | `mix compile` via custom Mix task (`Compile.Cure`) |
| **Key Advantage** | End-to-end type safety and zero host runtime overhead | Seamless integration with existing Elixir/OTP infrastructure |

---

## 5. Summary & Key Takeaways

* **Formally Verified Graphs**: Cure's `Std.Fsm` compiler extension catches invalid transitions, deadlock states, and missing terminal states at compile time.
* **Double-Entry Safety**: Separating `balance` and `held` prevents double-spends and ensures total refund safety.
* **Interoperability**: Cure state machines compile directly into standard BEAM `:gen_statem` processes that Elixir code can inspect, spawn, and supervise using familiar OTP primitives.

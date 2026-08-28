# cure_exchange (pure Cure)

A multi-currency exchange and escrow engine, written entirely in Cure with no
Elixir wrapper -- `Cure.toml`, `lib/`, `test/`, and nothing else, in the same
spirit as [`examples/cure_calc`](../../cure_calc). It is the pure-Cure half of
the `cure_exchange` pair; see [`../elixir`](../elixir) for the sibling project
where only the FSM is written in Cure and everything else is Elixir.

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

A quote is locked (reserving funds), then either the rate lock expires, or a
counterparty is matched and the bank is asked to settle. Settlement either
confirms, or fails/times out and the hold is unwound as a refund.

## Layout

```text
Cure.toml                            project manifest
lib/money.cure                       mod Exchange.Money        -- Currency, Money, FX conversion
lib/ledger.cure                      mod Exchange.Ledger       -- reserve/capture/release accounts
lib/escrow_fsm.cure                  mod Exchange.EscrowFsm    -- EscrowState/EscrowEvent + transition/3
lib/escrow_fsm_dsl_reference.cure    mod Exchange.EscrowFsmDslReference -- the real `Std.Fsm` DSL, standalone
lib/escrow.cure                      mod Exchange.Escrow       -- plays events through transition/3 + the ledger
lib/otp_demo.cure                    mod Exchange.OtpDemo      -- a small Std.Otp process-identity demo
lib/main.cure                        mod Exchange.Demo         -- main/0, the entry point
test/*.cure                          Std.Test coverage for every module above
```

## Commands

Run from this directory, with the `cure` escript on `PATH`:

```bash
cure run lib/main.cure                     # play all four scenarios, print the results
cure run lib/escrow_fsm_dsl_reference.cure # verify the real Std.Fsm DSL declaration's graph
cure test                                  # run every test_* function under test/
cure check lib/escrow.cure                 # type-check one file (see the limitation below for escrow_fsm*.cure)
```

`cure run lib/main.cure` prints:

```text
cure_exchange -- a multi-currency escrow engine in Cure

happy path       : Completed  balance=USD 9900.00  held=USD 0.00
quote expired    : Cancelled  balance=USD 10000.00  held=USD 0.00
bank failed      : Refunded  balance=USD 10000.00  held=USD 0.00
settle timed out : Refunded  balance=USD 10000.00  held=USD 0.00
```

## What it demonstrates

- **A real escrow state graph** -- 7 states, 7 events, a guard (`amount > 0`
  on `LockFunds`), 3 terminal states, all reachable and deadlock-free.
- **The `Std.Fsm` transition-graph DSL** -- `lib/escrow_fsm_dsl_reference.cure`
  declares the exact same graph using `use Std.Fsm; fsm Escrow with
  EscrowData ...` (typed event payloads, `when`, `terminal`), which is what
  actually exercises the compiler's compile-time graph verification
  (reachability, deadlock-freedom, duplicate-transition and
  payload-consistency checks) described in `docs/FSM_GUIDE.md`.
- **A total hand-written mirror** -- `Exchange.EscrowFsm.transition/3` is the
  same graph as an ordinary `match`-based function returning `Std.Fsm`'s own
  `FsmAction`/`Keep`/`Next` vocabulary. Every test in this project exercises
  this version; see "Known limitations" for why.
- **Stray-event safety** -- any event with no matching row (a duplicate
  webhook, a timer that fires after the state has already moved on) is a
  no-op (`Keep`), never a crash; `test/escrow_fsm_test.cure` asserts this
  directly.
- **`Result`-typed ledger effects** -- `reserve`/`capture`/`release` model the
  escrow hold lifecycle without ever risking a double-spend: funds move from
  `balance` to `held` on lock, and from `held` to either gone (`capture`) or
  back to `balance` (`release`), never both.
- **A little FFI** -- `Exchange.Money`'s float-rate conversion talks to
  `:erlang` directly (no Elixir/Mix step exists in this project to host a
  helper module), and its own header comment documents a real FFI pitfall
  this project hit and fixed (see below).

## Known limitations (found while building this example)

This example was written against a specific, actively-developed build of the
`cure` compiler, and two of its rough edges directly shaped this project's
layout. Both are pre-existing compiler behavior, not bugs introduced by this
example -- they are documented here so the duplication above doesn't look
like an accident.

1. **A macro-generated submodule cannot be called from project-mode code.**
   In *project-mode* compilation (`cure compile <dir>`, and therefore `cure
   test`), a module that calls another module's `fsm`- or `actor`-generated
   API (`.start`, `.send`, even the pure `.decide`) fails with an internal
   `missing_module` resolution error -- reproduced with both `fsm` and
   `actor`, same-file and cross-file, even against the officially scaffolded
   `cure new --fsm` template. Declaring the macro on its own, and never
   calling its generated API from elsewhere in a directory-mode build,
   compiles fine. This is why `Exchange.EscrowFsm.transition/3` is
   hand-written rather than being `Exchange.EscrowFsmDslReference.Escrow`'s
   generated `decide/3` called directly: that call is exactly the pattern
   that fails under `cure test`.

2. **`cure check` does not currently validate an `fsm` declaration.** Even the
   two-state, two-edge graph generated by `cure new --fsm` fails `cure check`
   with a generic macro-expansion-rejected error, with or without a
   `Cure.toml` in scope. The graph verification logic itself does work --
   `cure run` on a file whose *only* content is the `fsm` declaration plus a
   trivial `main/0` correctly reports a graph error for a deliberately broken
   graph (e.g. a missing `terminal`) and cleanly succeeds for a valid one.
   `lib/escrow_fsm_dsl_reference.cure`'s header comment explains how to use
   `cure run` (not `cure check`) to validate it, and why its `fsm` declaration
   lives in its own module rather than alongside `Exchange.EscrowFsm`'s
   hand-written `EscrowState`/`EscrowEvent` (their constructors collide
   otherwise: unlike an ordinary nested `mod`, this build does not
   independently namespace a macro's generated constructors from the rest of
   their enclosing module).

3. **`Std.Otp.spawn` is rejected outside a managed actor/FSM/supervisor
   declaration** ("unavailable in dependent code"), and a *self-recursive*
   `Effect`-returning function -- the natural shape of an actor's own receive
   loop -- is unreliable in this build. Combined with limitation 1 (no way to
   reliably start a project-local `fsm`/`actor` module from this project's own
   code), a live, spawned OTP process demonstration isn't reliably reachable
   from `cure test` here. `Exchange.OtpDemo` sticks to what is reliable:
   `self()` and a typed `tell` to it. The live, timer-driven, multi-process
   version of this same escrow scenario is exactly what
   [`../elixir`](../elixir) is for -- Elixir's own OTP tooling does not share
   any of these constraints, since it drives the compiled Cure FSM module
   through its raw BEAM atom rather than through Cure's own module resolver.

4. **An `@extern` return type of `String` for a function that actually
   returns a raw charlist (e.g. `:erlang.integer_to_list/1`) type-checks but
   crashes at run time** the first time the result is concatenated --
   `docs/FFI.md` calls this out explicitly. `Exchange.Money` originally
   declared exactly this extern (copying `examples/cure_moneta`'s own
   `int_to_string`, which has the same latent issue) before being fixed to
   use `Std.Io.int_to_string`, which wraps the charlist correctly via
   `Std.String.from_characters`. If you add your own integer-to-string FFI
   here, wrap it the same way.

## Where to go next

- Add a fourth currency and a real rate table instead of a single hard-coded
  spot rate per call.
- Extend `EscrowData.history` (already tracked by `transition/3`) into an
  assertion helper so tests can check the exact event sequence, not just the
  final state.
- Compare this project's hand-written `transition/3` against
  `Exchange.EscrowFsmDslReference.Escrow`'s generated `decide/3` once
  limitation 1 above is fixed upstream -- they should be behaviorally
  identical.

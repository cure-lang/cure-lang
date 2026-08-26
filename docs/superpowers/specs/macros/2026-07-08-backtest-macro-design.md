# `backtest` — Trading-Strategy Backtesting Where Look-Ahead Is a Type Error

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #93, promoted); built as a `macro` (§5), zero compiler
special-casing. The four hiding principles (§3) are law: no user ever sees an
index or a kernel error.

---

## 1. Purpose

Half of hobbyist backtests are fiction, and the fictions are always the same
three: the strategy peeked at a bar that hadn't printed yet (look-ahead
bias), it traded for free (zero costs), or it was tuned on the data it was
graded on (leakage/overfitting). `backtest` attacks all three in that order
of confidence: look-ahead is **inexpressible** by type, zero-cost runs are
**a compile error**, leakage across train/test splits is **inexpressible at
the split boundary** — while overfitting itself gets only an honest lint,
because nothing detects overfitting reliably and this macro does not
pretend otherwise.

The brand is skepticism: every other backtesting tool sells returns; this one
sells the list of ways your returns are fake, minus the ones the compiler has
already removed. Users declare indicators, rules, and cost models; the
elaborator manufactures the causally-indexed types (hiding principle 1).

## 2. Surface

A **strategy is a flow program over bar streams**: indicators are pure signal
derivations, entries/exits are guarded events, sizing is a refinement-bounded
value. A `backtest` block binds a strategy to data, costs, and capital.

Worked example — moving-average cross with a max-drawdown guard:

```cure
use Trade.Backtest

strategy MaCross
  input px = bars(daily)                    # Signal of Bar, causally indexed
  let fast = px.close |> sma(10)            # bars, not days — see §6
  let slow = px.close |> sma(50)

  entry long when fast crosses_above slow
  exit       when fast crosses_below slow
  exit       when drawdown > 15pct          # portfolio-level guard event

  size   fraction(0.5)                      # {f: Float | 0.0 < f and f <= 1.0} of equity
  leverage max 1.0                          # refinement bound, checked (§9)

backtest MaCrossDaily
  strategy MaCross
  data     prices.spy from 2015-01-01 to 2024-12-31   # a `schema` table, §5
  capital  10_000usd
  costs                                     # mandatory — §4
    fee      1bp per_trade
    spread   0.5bp
    slippage 1bp
  fills next_bar_open                       # the default; stated here anyway
```

- **`input`** binds the price stream; the instrument is bound in the
  `backtest` block, so strategies are data-source-agnostic.
- **Indicators** (`sma`, `ema`, `rsi`, `crosses_above`, …) are ordinary flow
  combinators — pure, windowed, causally indexed; a user-written indicator
  inherits the causality discipline automatically, there being nothing else
  to inherit.
- **`entry`/`exit`** are guarded events; **`size`**/**`leverage`** carry
  refinements (§9); **`backtest`** binds strategy + data range + cost model
  + capital and runs on the deterministic engine (§7).

## 3. Look-ahead bias as a type error — the headline

A decision at bar *t* may read bars ≤ *t*. That sentence is the entire
semantics of honest backtesting — and it is exactly the Safe-FRP causality
index `flow` already carries (parent §6.4). The same theorem that forbids an
instantaneous feedback loop in `flow`, a screaming self-referential patch in
`synth`, and a step-order dependence in `sim` also forbids a trading rule at
*t* reading `close[t+1]`. **Backtesting is the fourth audience for one
theorem** — the macro adds no machinery, only vocabulary.

Concretely: `px.close` at decision time *t* denotes the close of the *last
completed* bar. `px.close |> shift(-1)` — tomorrow's close — is not a value a
guard at *t* can consume; the index does not unify, and the program does not
compile. Look-ahead bias — the bug that silently, flatteringly invalidates
half of hobbyist backtests — is **inexpressible, not detected**: no linter
pass, no runtime assertion, no audit, because the ill-typed program never ran.

The subtle variants fall out of the same index: a window-*centered* smoother
is future-facing and cannot feed a guard; a signal normalized by the whole
period's max is future-facing at every point before the end and rejected the
same way. What survives the type checker could, by construction, have been
executed with the information available at the time.

## 4. Honest-costs discipline

**A backtest without a declared cost model does not run.** Omitting the
`costs` block is a compile error, not a footnote. A zero-cost backtest is
fiction; you may write fiction, but you must declare it explicitly —
`fee 0bp` compiles, and the report header says so in plain text. Components:
`fee` (per-trade or per-share), `spread` (half-spread paid on crossing),
`slippage` (adverse drift) — all in `bp`/`pct`/currency units (§6).

**Fill assumptions are declared, never implied.** The default is
`fills next_bar_open`: a decision on bar *t*'s close fills at bar *t+1*'s
open — the conservative, causally-clean convention. Same-bar fills (deciding
on a close and pretending to fill at it) are execution-side look-ahead; they
exist only as `fills same_bar optimistic`, and the `optimistic` marker is
mandatory, greppable, and printed in the report header (§7).

## 5. Data hygiene

Data comes in through `schema` (sibling spec): this macro brings no data
layer of its own — it consumes the one that exists, as-of discipline included.

- **Point-in-time joins.** Any join against fundamentals, earnings, or
  announcements is an **as-of join**: the row visible at bar *t* is the row
  known at *t*, not the restated figure published later — schema's as-of
  discipline pointed at market data; latest-value joins against dated tables
  are rejected with an explainer.
- **Survivorship bias, named.** Universe declarations are **dated**:
  `universe sp500 as_of 2015-01-01` means membership *on that date*,
  delistings included thereafter. Running today's membership over the past
  is the classic setup; the macro cannot prove a data vendor honest, but
  it forces the declaration to say which universe is meant, and the report
  repeats it.
- **Walk-forward splits — leakage inexpressible.** `split walk_forward(train:
  2y, test: 6mo, step: 6mo)` makes the split a **type-level boundary**: an
  indicator warmed up or fitted on test-segment data does not type-check
  inside that segment — the causality index again, along the train/test axis
  instead of time. Parameter selection lands on train segments only, by
  construction.

## 6. Units

Money and rates are typed; the classic silent-scaling bugs are inexpressible:

- **Currencies never mix.** `10_000usd + 500eur` is a type error; conversion
  is an explicit function taking a rate — itself a dated, as-of value (§5).
  Money units are the `ledger` idea's machinery, reused (§10).
- **Percent and basis points are distinct types.** The off-by-100 confusion
  between `1bp` and `1pct` cannot compile; both convert explicitly.
- **Periods carry units.** `sma(10)` is 10 *bars* (the honest unit — bars are
  what the stream contains); calendar periods (`2y`, `6mo`) appear only where
  calendars are real (data ranges, splits). Mixing the two is an error, not
  a coercion.

## 7. Reproducibility

The engine is `sim`'s deterministic lockstep runtime (sibling spec §2.2):
bars are ticks, per-bar evaluation is a pure function of (state, bar, PRNG),
commits happen at the bar boundary. Same inputs, same numbers, exactly —
sim's purity dividend, again.

Every report header carries the **data hash** of the exact rows consumed,
the **cost model** verbatim, the **fill assumption** (any `optimistic`
marker included), the **seed**, and the toolchain version. Two people
running the same backtest get identical numbers **or a named difference**
(the headers diff and name it). A result that cannot state its inputs is
not a result; it is an anecdote.

## 8. Explainers

Per the parent's error-explainer architecture (§4), errors speak trader
vocabulary; raw kernel output reaching a user is a defect by definition.

```
error[E235]: this signal at bar t reads bar t+1's close
  --> macross.cure:7    let confirm = px.close |> shift(-1)
  That's look-ahead — trading on information the strategy did not have.
  Use the completed bar's close (px.close), or shift the signal backward
  (shift(1) = yesterday's close).

error[E236]: no cost model declared
  --> macross.cure:14
  A backtest with zero costs overstates returns — every trade pays fees,
  spread, and slippage in the real world. Declare a `costs` block, even an
  optimistic one:  costs / fee 1bp per_trade / spread 0.5bp / slippage 1bp

error[E237]: indicator `fast` is warmed up on test-segment data
  --> macross.cure:22
  The walk-forward split makes test data invisible to anything the strategy
  computes with. Warm indicators inside the train segment, or widen the
  train window.
```

## 9. `check` integration (parent §7.5 — the macro ships its templates)

- **Leverage invariant:** the strategy never exceeds its declared
  `leverage max`. Static where derivable — `size fraction(f)`, `f <= 1.0`,
  no pyramiding discharges by refinement, *proved by construction — 0 runs*;
  otherwise property-tested over generated bar sequences.
- **Cost-sensitivity template:** re-run at 2× the declared costs and report
  whether the strategy stays profitable. **Reported, not enforced** — dying
  at 2× costs is information, not an error.
- **Overfitting lint:** a warning when free-parameter count is large relative
  to data length (a crude degrees-of-freedom ratio), with the honest caveat
  printed alongside: *no lint detects overfitting reliably; walk-forward
  results (§5) are the evidence that matters.* Never laundered into a
  guarantee.
- **Determinism template:** same seed + same data hash ⇒ identical report —
  `sim`'s reproducibility template, re-shipped here.

## 10. Relations

- **`flow`** — the substrate: strategies *are* flow programs; the causality
  index is the whole §3 story. Nothing new at the type level.
- **`schema`/`table`** — all data in; as-of joins and dated universes (§5)
  are schema machinery consumed, not duplicated.
- **`sim`** — the deterministic lockstep engine (§7), seeded-run templates.
- **`units` / `ledger` idea** — currency, `pct`/`bp`, period units (§6);
  money types come from the ledger direction when it lands.
- **`view`** — equity curves, drawdown charts, and walk-forward panels are
  observation streams rendered by `view`; the report is a document.
- **`check`** — §9; static discharge of the leverage bound is this macro's
  "tests you don't have to run" moment.

## 11. Safety & honesty

This macro is not financial advice and does not produce it. A backtest is
a statement about the past under declared assumptions; **it is not evidence
of future returns**, and the report template says so verbatim. The compiler
removes specific self-deceptions (§§3–5); it cannot remove market risk,
regime change, or wishful parameter choice.

**Live-trading execution is a ledger item (§12.1) with a hard warning.**
Broker adapters change the risk class entirely — real money, partial fills,
outages, API semantics no type system here models. If adapters ever ship, a
paper-trading adapter ships first as the loud default, and a live adapter
would carry an unmissable acknowledgment step. Nothing here commits to either.

## 12. Open decisions (ledger)

1. **Live/paper trading adapters** — see §11; paper-first if ever, and the
   question is deliberately left open, defaulting to *no*.
2. **Granularity v1** — bars vs intraday/tick. **Recommendation: bars only.**
   Tick data multiplies volume, cost-model subtlety, and fill-model fiction;
   bars keep the honesty story checkable. Revisit with real users.
3. **Portfolio vs single instrument** — v1 leans single-instrument (the
   worked example's shape); multi-asset adds correlation, rebalancing, and
   cross-margin questions. Decide after v1 programs exist.
4. **Corporate actions** — splits/dividends as a data-layer contract:
   adjusted vs unadjusted declared on the `schema` table; the backtest
   refuses mixed-adjustment joins. Exact contract shape open.
5. **Options/derivatives** — probably a permanent non-goal (§13); ledgered
   so the "no" is a recorded decision, not an omission.
6. **Monte-Carlo robustness** — resampled-return robustness runs as a
   `check` template (seeded, so reproducible). Worth shipping; scope open.
7. **Benchmark comparison** — buy-and-hold baseline in every report by
   default? Likely yes — it is the honest denominator; confirm.

## 13. Non-goals

- **Not financial advice**, and no feature will be framed as such (§11).
- **No HFT** — microsecond execution modeling is permanently out of scope;
  the honesty story does not extend there.
- **No options pricing** — no greeks, no vol surfaces, no derivatives math.
- **Not a data vendor** — bring your own data through `schema`; the macro
  checks what you declare about it, and cannot check what you did not.

# cure_pool design notes (verified against the compiler)

These notes record what was **empirically verified** against the `cure` escript
(0.34.3, Elixir 1.20.4 / OTP 29) while building this example. Every claim here
was reproduced with a `cure run` invocation; nothing is assumed from the docs.

## Verified: the dependent pool count

Indexed family, `Nat` index, explicit index argument:

```cure
type Nat = Z | S(Nat)
type Pool indices (avail: Nat, in_use: Nat)
  mk_pool : (capacity: Int) -> Pool(avail, in_use)

fn make(n: Nat, capacity: Int) -> Pool(n, Z) = mk_pool(capacity)
fn checkout(n: Nat, m: Nat, k: Nat, worker: Int, p: Pool(S(n), m)) -> %[Lease(k), Pool(n, S(m))] = ...
```

* `checkout` on a non-empty pool: **accepted**.
* `checkout` on `Pool(Z, m)`: **rejected** with `E093 ANNOTATION DOES NOT MATCH`
  (`Expected: Pool(S(Z), Z)`, `Found: Pool(Z, Z)`). This is the over-checkout
  guarantee (G1).

## Verified: the linear lease

The kernel's `{0,1,ω}` usage checker enforces linearity on `@linear`
**parameters**:

* A `@linear` parameter consumed exactly once: **accepted**.
* A `@linear` parameter never consumed: **rejected** with
  `E117 LINEAR VALUE IS NOT USED` (the leak / forgot-to-check-in guarantee).
* A `@linear` parameter consumed twice on one path: **rejected** with
  `E117 LINEAR VALUE MAY BE USED MORE THAN ONCE` (the double-return /
  use-after-free guarantee).

The accepted idiom is the one the stdlib uses for `@linear from : Reply(r)`:

```cure
## match the lease directly and reproduce it in the same arm
fn run(k: Nat, @linear lease: Lease(k), task: Int) -> %[Int, Lease(k)] =
  match lease
    mk_lease(worker) ->
      let value: Int = worker + task
      %[value, mk_lease(value)]
```

**Aliasing a linear value with `let l = lease` and then using `l` twice is
rejected** (this is the `let_linear_soundness_test.exs` rule: usage is scaled
by the alias's usage). Matching directly and reconstructing in the arm is the
pattern that both consumes the token once and returns a fresh one.

## Verified toolchain limitations that shape the layout

1. **Every index parameter must be explicit.** A function that mentions an index
   as an implicit `{n: Nat}` parameter (e.g. `run({k: Nat}, @linear lease, ...)`)
   is silently mis-resolved and the *caller* fails with a confusing
   `E093 ... Found: {:data, :"Pool.Core#Lease", ...}`. Writing the index as an
   ordinary argument (`run(k: Nat, ...)`) fixes it. This is why `reserve`,
   `unreserve`, `run`, and `capacity` all take explicit index arguments.

2. **A cross-file annotation on a nested indexed type is rejected by a
   definitional-equality bug.** In project mode, `let p: Pool(S(S(Z())), Z()) =
   make(...)` in a *different file* from the `Pool` definition fails with
   `Expected: Pool(S (S Z), Z) / Found: Pool(S(S(Z)), Z)` -- the same type,
   printed two ways, rejected. The same code in the same file compiles. →
   The counts are written once, in `Pool.Core`; `main.cure` and the tests rely
   on inference. The types are still fully checked; they are just not repeated
   at every binding. (`cure run` on a single concatenated file is unaffected.)

3. **`cure check` does not reliably validate an `fsm` declaration**, and a
   macro-generated submodule cannot be called from project-mode Cure code.
   → The FSM is validated with `cure run <single-file>`; the *live* runtime
   lives in the Elixir-hosted half, driven by the raw BEAM atom (the
   `cure_moneta` / `cure_exchange` pattern).

4. **`Std.Otp.spawn` is rejected outside a managed `actor`/`fsm`/`sup`
   declaration.** → All live processes are `fsm`/`actor`/`sup`-declared or
   Elixir `GenServer`s.

5. **Inline `##` comments are not allowed inside a function body.** → Doc
   comments live on declarations, not between statements.

## The honest headline

The compiler proves three things about this pool, and each is demonstrated by a
fixture that **must fail to compile**:

| Guarantee | Diagnostic | Fixture |
|---|---|---|
| no over-checkout | `E093` | `negative/checkout_empty.cure` |
| no double-return | `E117` (used more than once) | `negative/double_return.cure` |
| no leak | `E117` (not used) | `negative/dropped_lease.cure` |

The live half (crash-reclaim under a supervisor) is proven at runtime in the
Elixir-hosted project, because that is the one path the toolchain reliably
supports for live OTP processes.

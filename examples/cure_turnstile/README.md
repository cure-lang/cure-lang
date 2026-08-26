# CureTurnstile

A small Cure process example using the transparent FSM macro.

The source in `cure_src/turnstile.cure` is intentionally small:

```cure
use Std.Fsm

fsm Turnstile with Tuple(Int, Int)
  Locked --coin--> Unlocked
    update %[data.1 + 1, data.2]
  Unlocked --push--> Locked
    update %[data.1, data.2 + 1]
  Unlocked --coin--> Unlocked
    update %[data.1 + 1, data.2]
  Locked --push--> Locked
```

`fsm` is an auto-preluded standard-library macro. It expands to an ordinary
lifted module and uses the checked `Std.Otp` process algebra for startup. There
is no FSM-specific compiler object or source-string callback parser.

The bare source name is owned by the implicit top-level `Main` module, so this
particular project emits `Cure.Main.Turnstile`. The `Cure.` prefix is BEAM
emitter policy, not source syntax.

## Usage

```bash
cd examples/cure_turnstile
mix deps.get
mix compile
mix test
```

The Elixir wrapper in `lib/` remains ordinary application code. It is useful
for demonstrating interop, but it does not implement the Cure FSM semantics.

# Trace Replay

The current transparent macro system does not attach an implicit journal to a
macro expansion. Recording and replay are therefore ordinary runtime APIs, not
compiler callbacks or a hidden FSM parser.

## Journal API

`Cure.Observe.Journal` stores generic five-tuples:

```elixir
{process_id, state_before, event, state_after, timestamp_us}
```

Use `record/4`, `entries/0`, `entries/1`, `clear/0`, `flush/1`, and `load/1`
from Elixir runtime code when an application deliberately chooses this trace
format. The journal does not claim that a declaration named `fsm` has special
compiler semantics.

## Inspection

```bash
cure replay .cure-trace/example.journal
```

Without a replay target this prints the stored entries. Live replay remains a
runtime integration concern for a module that implements the caller-selected
event protocol; it is not part of transparent macro expansion.

The generic `Cure.Observe.Trace` API is the preferred current instrumentation
surface for typed function calls. See `docs/OBSERVABILITY.md` for the broader
runtime tooling reference.

# cure_motif

A dependent-data example with transparent Cure process modules.

The project combines length-indexed values, ordinary ADTs, and the four
standard-library macro surfaces. Its process declarations are intentionally
small floors while the domain code remains pure Cure.

## Quick start

```bash
cd examples/cure_motif
mix deps.get
mix test
```

## Transparent process declarations

The source files use standard-library syntax directly:

```cure
use Std.Fsm

fsm Envelope with Int
  Silent --note_on--> Attack
  Attack --on_timer--> Sustain
  Sustain --note_off--> Release
  Release --on_timer--> Silent
  * --kill--> Silent
```

```cure
use Std.Actor

actor Voice
  state Tuple(Atom, Int, Int)
  initial %[:silent, 0, 0]
  messages Tuple(Atom, Int, Int)
  handle_cast
    let tag = message.1
    pickup
      tag == :play -> %[:noreply, %[:playing, message.2, message.3]]
      tag == :stop -> %[:noreply, %[:released, state.2, state.3]]
      else -> %[:noreply, state]
```

```cure
use Std.Supervisor

sup Motif.Orchestra
  children
    worker Main.Clock as clock
    worker Main.Sequencer as sequencer
    worker Main.Voice as voice
```

```cure
use Std.App

app CureMotif
  root Motif.Orchestra
```

Each form expands recursively to a checked `lift module`. `beam_ops` and the
typed `Std.Otp` aliases provide the process algebra; the compiler only sees
ordinary parsed Cure declarations and a generic lifted-module request.

## Domain focus

`motif.cure` contains the MIDI-domain aliases, ADTs, and pure rendering
functions over typed runtime lists. The Elixir piano-roll renderer and
application harness are conventional interop code around the generated modules.

Bare process names are qualified by their lexical owner. Dotted names such as
`Motif.Orchestra` are absolute within the Cure source namespace; neither form
authors the BEAM-only `Cure.` prefix.

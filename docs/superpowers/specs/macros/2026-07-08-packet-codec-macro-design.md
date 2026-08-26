# `packet` / `codec` — Wire Formats and Data Schemas, One Layout Declaration

**Date:** 2026-07-08
**Status:** design (operator-requested). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(§6.3 `packet` + §7.2 `codec`); substrate of
[`2026-07-08-protocol-macro-design.md`](2026-07-08-protocol-macro-design.md)
(every protocol message compiles to a packet frame, §4 there). Built as a
`macro` (§5) — zero compiler special-casing.

---

## 1. Purpose & positioning

A `packet` declares a **binary wire layout** — fields, widths, endianness,
length dependencies, checksums — once, as a table a human can read against
a datasheet. From it Cure generates a parser that **cannot overrun by
construction** and an encoder that is its exact inverse. A `codec` is the
same field grammar pointed at **self-describing formats** (JSON/CBOR/
MessagePack) instead of raw bytes.

One declaration, both ends of the wire (parent §7 preamble): the ESP32
firmware and the host/broker side compile the *same* `packet` — a single
source of truth. Covers UART protocols, I2C/SPI payloads, LoRa frames, MQTT
payloads, NMEA, and (via `codec`) every JSON API the device talks to.

The bug class killed: hand-rolled offset arithmetic — off-by-one reads,
buffers indexed past their end, checksums over the wrong byte range, guessed
endianness. The genre becomes inexpressible, per hiding principle 2.

## 2. Surface — `packet`

The canonical example (parent §6.3, verbatim semantics):

```cure
packet Frame
  magic:   const 0xA7
  version: Byte
  length:  Byte
  payload: bytes(length)                 # indexed by the field above
  crc:     crc8 over [version, length, payload]
```

Fields parse top-to-bottom; a field may refer to any **earlier** field, and
only earlier ones (a forward reference is a compile error, §6). The full
inventory:

```cure
packet SensorReport
  endian be                              # packet-wide default for multi-byte scalars

  magic:   const 0xC5 0x01               # multi-byte magic, checked on parse,
                                         # auto-emitted on encode — never stored
  kind:    enum Byte                     # enum-as-tagged-byte; values are explicit
             Reading = 0x01              # (wire stability: no implicit ordinals)
             Fault   = 0x02
  seq:     u16                           # big-endian per the packet default
  temp:    i16(le)                       # per-field endianness override
  header:  Frame                         # nested packet — parse/encode compose
  count:   Byte
  samples: bytes(count)                  # length-dependent, like Frame.payload
  crc:     crc16(ccitt) over [kind, seq, temp, count, samples]
```

### 2.1 Scalar notation (decision)

Scalars are `u8/u16/u32/i8/i16/i32` with endianness as an argument:
`u16(be)`, `u32(le)`. A packet-level `endian be | le` line sets the default;
a multi-byte scalar with **neither** a packet default nor a per-field
argument is a compile error — no silent host-endian fallback. `Byte` is the
blessed alias for `u8` (no endianness question at one byte). The `u16le`
mashed-token style and width-vague `word(be)` are **rejected**: the
parenthesized form reads as what it is and leaves room for future arguments
without new lexing.

### 2.2 Field kinds

| Kind | Parse behavior | Encode behavior |
|---|---|---|
| `const 0xA7 …` | bytes must match, else `ParseError` at that offset | emitted automatically; not a record field |
| scalar (`u16(be)`, …) | fixed-width read, endianness applied | fixed-width write |
| `enum Byte …` | byte→constructor table; unknown byte is an offset-precise error | constructor→byte |
| `bytes(n)` (literal) | exactly `n` bytes | length checked statically |
| `bytes(field)` | exactly the count the earlier field parsed | length **emitted from the payload** — the user never sets `length` by hand (§3) |
| nested packet | inner parse at the current offset; inner errors carry the **absolute** outer offset | inner encode spliced |
| `crc8` / `crc16(poly)` `over [fields…]` | computed over the named fields' byte spans, compared, else error | computed and appended — never user-supplied |

Checksum coverage is **declared by field name, never by hand offset** — the
elaborator derives the byte range from the layout, so inserting a field
cannot silently desynchronize the CRC span.

## 3. Generated API

```cure
Frame.parse  : Bytes -> Result(Frame, ParseError)
Frame.encode : Frame -> Bytes
```

with the frame value itself carrying the dependency:

```cure
f.payload : Bytes(f.length)              # length-indexed — reads can't overrun
```

A failed parse yields an offset-precise, field-named `ParseError` (§6).
Construction never asks for derived fields: `Frame{version: 1, payload: p}`
is complete — `length` is `p`'s length (carried by the index), `magic` and
`crc` are the encoder's job. A frame with a lying length field is
**unrepresentable**, which is half of why round-trip holds (§5).

## 4. Surface — `codec`

The same field grammar, targeting self-describing formats:

```cure
codec Reading
  tag:     const "reading"               # discriminator field, checked on decode
  device:  String as "deviceId"          # wire-name rename
  temp:    Float
  battery: {p: Int | 0 <= p and p <= 100}
  note:    Option(String)                # omitted when None; absent-or-null on decode
```

```cure
Reading.encode : Reading -> Format -> Bytes      # Format = :json | :cbor | :msgpack
Reading.parse  : Bytes -> Format -> Result(Reading, DecodeError)
```

Rules where the two containers diverge (self-describing formats already
carry structure the wire format had to spell out):

- **Naming**: field names go on the wire as written; `as "camelName"`
  renames, per-field and explicit — no global casing knob.
- **Omission**: `Option` fields are omitted when `None` on encode; decode
  accepts absent *or* explicit null. Everything else is required — a missing
  field is a `DecodeError` naming the field and its path (`$.device`), the
  JSON analogue of a byte offset.
- **Lengths and checksums**: `bytes(field)` needs no length field (the
  format self-describes lengths); `crc*` is **rejected in `codec`** with an
  explainer — integrity is the transport's job there (TLS etc.); a CRC
  field in JSON is a smell, not a feature.
- **Refinements validate on decode**: `battery: {p: Int | 0 <= p <= 100}`
  makes out-of-range input a `DecodeError`, not a latent bad value.

Relation to the existing `@derive(Json)`: deriving stays the quick path for
*internal* data (debug dumps, logs) where the shape is whatever the type is.
`codec` is for **contracts** — renames, `const` discriminators, refinement
gates, evolution rules (§9.7), the inherited round-trip. A `codec`
declaration backs the type's `Json` protocol instance, so the two never
disagree about one type.

## 5. Invisible machinery

- `payload : Bytes(length)` is the landed **length-indexed Vector** with
  Nat→Int erasure — the index costs zero bytes at runtime; parse cannot
  overrun *by construction*, because every read's extent is a type-level
  consequence of already-parsed fields.
- **BEAM lowering is binary pattern matching**: a packet parse compiles to
  one `<<magic, version, length, payload:length/binary, crc>>`-shaped match,
  so `f.payload` is a **zero-copy sub-binary** of the input — the safe parser
  is also the fast one, because the generated code is exactly what an expert
  Erlang hand would write.
- The **round-trip property `parse(encode(f)) == Ok(f)` is established
  once, centrally, at the library level** (proved/Antigen-checked against
  the field-kind combinators). Every user declaration composes those
  combinators, so every packet and codec inherits it for free (parent §3).
- Erasure: `const` and `crc` fields have no runtime slot; a parsed `Frame`
  is version + length + a sub-binary reference.

## 6. Errors

Two audiences. **Compile-time** errors are layout mistakes, explained via
the macro's `explain` block:

```
error[E155]: samples' length field comes after it
  --> report.cure:11
   |
11 |   samples: bytes(count)
   |                  ^^^^^
  bytes(count) needs count already parsed, but count is declared on line 12.
  A length field must come before the bytes it measures — move count above
  samples (this is also the only order a receiver can parse).
```

**Runtime** `ParseError` values are offset-precise and field-named, and
render on the same what-arrived → why → what-now template:

```
Frame.parse failed at byte 3 of 5: payload truncated
  length (byte 2) = 7, so payload spans bytes 3..9 — but the input ends at byte 5.
  Likely a partial read: buffer more bytes and re-parse (streaming, §9.3).
```

```
Frame.parse failed at byte 12: crc mismatch in Frame.crc
  computed 0x5A over [version, length, payload] (bytes 1..11); frame carries
  0x3F. Corrupted in transit — drop it and let the sender resend.
```

Nested packets report the **absolute** outer-frame offset plus the field
path (`SensorReport.header.version at byte 7`), never inner-relative math.

## 7. `check` integration

`packet`/`codec` ship the flagship macro property template (parent §7.5):

- **Round-trip**: `parse(encode(f)) == Ok(f)` re-run as a template on every
  user declaration — belt over the central proof, and it exercises the
  user's own field mix.
- **Generators produce *valid* frames**: a generated `Frame` has a
  consistent `length`, correct `magic`, and a freshly computed `crc` — by
  construction, because generation goes through `encode`. No run is wasted
  on frames the parser must reject; corruption is *deliberate*, via the
  fault-injection template (flip a byte → parse must return `Error`, never
  a wrong `Ok`, never a crash).
- **Total rejection**: `parse` over *arbitrary* bytes always returns `Ok` or
  `Error` — never throws, never hangs (totality is already checked).

## 8. Relations

- **`protocol`** — each protocol message compiles to a packet frame; at a
  *deterministic* session step both ends know which message is next, so
  protocol calls that message's parser directly and the wire carries **no
  discriminator** (protocol §4 tag elision). `packet` enables this by
  generating a standalone parser per declaration — self-tagging is opt-in
  (an `enum` kind field), never imposed.
- **`driver`** — multi-byte register bursts (`reg raw_temp … bytes(3)`,
  parent §6.2) are degenerate packets; `driver` reuses the scalar/endianness
  machinery so a big-endian 20-bit ADC read is declared, not shifted by hand.
- **`fleet`** — fleet's generated channel layouts are packet declarations
  emitted by its elaborator; telemetry frames inherit round-trip and
  truncation-safe parse without fleet doing any wire work itself.
- **`parse`** (parent §7.2) — text vs binary, no overlap: `parse` is PEG
  grammars over characters; `packet` is fixed layout over bytes. A textual
  protocol (NMEA sentences) uses `parse`; its checksummed byte envelope
  uses `packet`.
- **`check`** — §7; the generator/oracle machinery is Antigen's, reused.

## 9. Open decisions (ledger)

1. **Variable-length collections** — `repeat(count) Item` (count-prefixed)
   vs terminator-byte vs length-in-bytes-then-parse-to-exhaustion. All three
   exist in real protocols; pick the v1 subset (count-prefixed is the safe
   first, it's `bytes(field)` generalized) and the notation for the rest.
2. **Versioned frames / evolution rules** — can `version: Byte` gate later
   fields (`present when version >= 2`)? Interacts with the protocol
   declaration-hash handshake (protocol §10.5) — resolve compatibly.
3. **Streaming / incremental parse** — a frame arriving in chunks over
   UART: does `parse` grow a `More(needed: Int)` verdict (the §6 truncation
   error already knows the count) or does an accumulator own reassembly?
4. **Max-size bounds for MCU preallocation** — a refinement on the length
   field (`length: Byte where length <= 64`) lets the runtime preallocate
   and reject oversized frames at the header, before the payload arrives.
   Cheap, likely v1.
5. **Bitfield packing** — sub-byte fields (`flags: bits(3)`); `driver`
   already has `bits(7..5)` field windows — unify that notation here or keep
   packets byte-aligned in v1.
6. **Alignment / padding notation** — explicit `pad 2` vs auto-align
   directives; only matters for memory-mapped layouts, may be a `driver`
   concern only.
7. **`codec` schema evolution** — do codecs get looser rules than packets
   (added optional fields are compatible; JSON consumers expect this) while
   packets stay hash-strict? Probably yes; decide where the rule lives.
8. **Unknown-field policy for `codec`** — ignore (Postel, default?) vs
   error (strict contracts) vs preserve-and-re-emit (proxy use); knob per
   declaration or per parse call.

## 10. Non-goals

- **Not a protobuf/ASN.1/Kaitai compiler in v1** — no schema-language
  import, no descriptor files, no protobuf wire-compatibility. §2.2's
  inventory plus the ledgered collections cover the hobbyist wire world;
  interop compilers can be macros later, by somebody.
- **No compression** — a compressed body is `bytes(n)` handed to a library.
- **No encryption** — that's transport; the `secret`-field × transport check
  lives in `protocol` (§6 there, keyed-edge story in protocol §10.8).
  `packet` neither encrypts nor pretends a CRC is security.
- No general bit-level DSL in v1 (§9.5) and no expression-computed offsets —
  a field's position is always the sum of the fields before it.

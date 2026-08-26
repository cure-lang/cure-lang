# Length-Indexed Binary (Dependent Bit-Syntax) — Design Spec

**Status:** DEFERRED. Design recorded; the build is gated on a real consumer
(see §5). This spec exists so that when a consumer appears, the design decision
is already made and the ordering dependencies are explicit.

**Layer:** E (elaborator) + K (kernel). Additive over the `Binary` primitive
base type (`{:binary_type}`) — it does **not** modify that primitive, it indexes
it.

**Relationship to the four-item batch:** This is item **#4** of the
Effect/Binary/bit-ops batch. Items #1 (opaque `Effect` former), #2 (Int bitwise
delta-globals), and #3 (`Binary` as an `Int`-tier primitive base type) are built
now. #4 is deliberately held.

---

## 1. What it is

A dependently-indexed binary type

```
Binary(n)          -- a BEAM binary statically known to be exactly n bytes
```

together with **dependent bit-syntax** where a field read earlier in a pattern
flows into the *type* of a field read later:

```cure
match frame
  <<len: 8, payload: len/binary, crc: 8>> -> ...   -- payload : Binary(len)
```

Here `len` is an ordinary runtime `Int`, but the elaborator refines the type of
`payload` to `Binary(len)`, so any downstream function indexed by that length
(a checksum over exactly `len` bytes, a decoder whose result type mentions the
frame length) type-checks against the *same* `len`.

This is the binary analogue of `Vector(n)` over `List`: `Binary` is the
un-indexed primitive (#3, always available); `Binary(n)` is the indexed view
that carries a length proof.

## 2. What it is NOT (and why #3 already covers the common case)

**Fixed-literal field sizes need nothing here.** A match whose field widths are
compile-time literals —

```cure
<<x: 16, y: 16, z: 16>> = read(port, addr, 6)     -- I2C burst read
```

— is a **primitive-op signature** ("consume a `Binary`, produce `Int, Int,
Int`"), not a motive-carrying eliminator. The result types depend on no runtime
value. This is handled entirely by #3's bit-syntax op table with literal sizes
and is the shape the overwhelming majority of driver code takes. #4 is required
**only** when a field width is a *runtime value that must appear in a type*.

**Runtime-length frames do not, by themselves, need it either.** In
`<<len:8, payload:len/binary>>`, `len` came off the wire, so it is not a
compile-time index; the value you would obtain is morally `Σ(n:Nat). Binary(n)`,
an existentially-packed length. The BEAM binary match **already enforces** at
runtime that exactly `len` bytes are consumed (or the match fails). Lifting the
length into the type buys nothing *at the point of the match itself* — it pays
off only if a **downstream** computation is genuinely indexed by that length
(§5, case A).

## 3. Design sketch (for when it is built)

### 3.1 The indexed family

`Binary(n)` is indexed by a **byte** count `n : Nat` (not a bit count — byte
granularity matches every BEAM binary BIF and the `<<_/binary>>` segment unit;
bit-level indexing is a further, separate extension and is out of scope even
here). It is *not* a new inductive family; it is the `{:binary_type}` primitive
paired with an erased `Nat` index — the same way `Bounded(k)` is a primitive
value carrying an erased bound. Concretely:

- Introduce it as an indexed view: `Binary(n)` elaborates to the primitive
  `{:binary_type}` refined by a proposition `byte_size(b) ≡ n`, OR as a
  distinct `{:binary_type, n_core}` node. **Open decision — must be settled
  before build:** refinement-carrying primitive vs. indexed node. The refinement
  form reuses the identity-type machinery (`Eq`/`refl`) but needs the
  refinement/bound support that was removed (see smt-trust-boundary memory);
  the indexed-node form is self-contained but adds a second `binary_type` arity
  the ~13 primitive sites (see the #3 checklist) must each handle.

### 3.2 Dependent bit-syntax elaboration

Bit-syntax match reuses the existing dependent-match machinery — it is *not* new
kernel surface:

- A segment `field: sizeExpr/binary` where `sizeExpr` mentions an earlier bound
  variable elaborates to an index-refinement step: the elaborator threads
  `sizeExpr`'s value into the goal type of `field` via the same
  `unify_indices` / `elaborate_match` path used for GADT index refinement.
- The motive is built by `build_motive`, exactly as for `case` on an indexed
  family. No new eliminator is introduced; `Binary(n)` destructuring is a
  motive-carrying use of the #3 primitive match.

### 3.3 Erasure

The `n` index is **erased**. At runtime `Binary(n)` is a plain BEAM binary and
the dependent bit-syntax match lowers to an ordinary BEAM binary match
(`<<Len:8, Payload:Len/binary, Crc:8>>`) — identical bytes to the non-indexed
form. The length proof exists only during type-checking. This is the standard
`{0,ω}` erasure story (erasure-relevance-check-decision memory): the index is a
0-quantity witness.

## 4. Prerequisites (hard ordering)

1. **#3 must land first.** `Binary(n)` indexes `{:binary_type}`; without the
   primitive there is nothing to index.
2. **The §3.1 type-former decision must be made** (refinement-carrying vs.
   indexed node). This is a design call, not an implementation detail, and it
   determines whether the removed refinement machinery must be partially
   restored.
3. **For §5 case B only:** a `Nat` lower-bound / refinement facility
   (`n ≥ 6`) — currently removed. Cases A and C do not need it.

## 5. When to build it — the named consumer cases

Build #4 when, and only when, one of these has an actual in-tree consumer:

### Case A — a typed protocol / session library with length invariants
A library (not a byte-banging driver) where a frame's length must flow into the
types of later operations: e.g. a message codec whose *result type* carries the
payload length, or a checksum/HMAC function typed `crc : Binary(n) -> Int`
applied to exactly the payload that a `len` byte announced. Here the type system
is what guarantees the checksum covers the whole payload and nothing else. This
is the primary and most likely trigger — it is the layer *above* the I2C/UART
drivers, e.g. a typed CoAP/MQTT-SN/Modbus frame library, or a `Std.Parse`-style
combinator library specialized to binaries that tracks remaining length in the
type.

### Case B — totalizing a fixed-size destructure via a length lower-bound
Turning a *partial* match `<<x:16, y:16, z:16>> = buf` (which crashes at runtime
if `buf` is short) into a **total** match by giving `buf : Binary(n)` with a
statically-known `n ≥ 6`. This is a robustness win — "you cannot under-read" as
a compile-time guarantee. It is a nice-to-have, **not** something a driver needs
to function (AtomVM drivers live fine with runtime match failures today), and it
additionally requires the removed `Nat`-bound/refinement machinery. Build only
if a subsystem's correctness argument actually depends on read-totality.

### Case C — zero-copy length-indexed sub-binary views
A binary parser-combinator library that produces sub-binaries (offset+length
views, no copy) and wants the *remaining* length tracked in the type across
combinator composition, so a combinator's type states how many bytes it
consumes. This is Case A's machinery applied to zero-copy slicing; it becomes
relevant if a real streaming parser over large binaries is written.

### Explicitly NOT a trigger — the I2C/UART driver layer
Direct I2C/SPI/UART framing is **not** a consumer:
- Sensor register reads (I2C burst, SPI register maps) use compile-time-literal
  field sizes → handled by #3 with no indexing.
- Length-prefixed stream frames have runtime lengths that are not compile-time
  indices; the dynamic BEAM binary match already enforces the length, and the
  driver hands the payload straight to a parser or the application without
  needing the type system to carry the length.

Drivers argue *for* #3 (the primitive + literal-size bit-syntax) and are neutral
on #4. The line falls between the driver layer (fixed/dynamic, #3) and a typed
protocol layer that reasons about lengths (#4).

## 6. Non-goals

- **Bit-level (sub-byte) indexing.** `Binary(n)` counts bytes. Bit-granular
  dependent widths are a further extension, not in scope even when #4 is built.
- **Re-introducing general refinement types.** Case B wants a narrow `Nat`
  lower-bound, not the full SMT-backed refinement layer that was removed; if
  Case B is built, restore only the minimal bound facility.
- **Changing the `{:binary_type}` primitive.** #4 is strictly additive.

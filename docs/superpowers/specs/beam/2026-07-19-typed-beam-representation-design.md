# Typed BEAM Representation

**Status:** Implementing

**Applies to:** `Std.Beam`, `deriving BeamEncode`, foreign wrappers, and the
`actor`, `fsm`, `sup`, and `app` macro families.

## Decision

Cure values cross foreign boundaries through two ordinary typeclasses:

```cure
interface BeamEncode(t)
  fn to_beam(value: t) -> BeamTerm

interface BeamDecode(t)
  fn from_beam(term: BeamTerm) -> Result(t, BeamDecodeError)
```

`BeamTerm` is opaque. Encoding is total; decoding is fallible. No API may use a
polymorphic cast from `BeamTerm` as a successful decoder.

## Derivation and coherence

Boundary representation is an ABI commitment, so it is explicitly requested:

```cure
type Message = Ping | Data(Int) deriving BeamEncode
```

The derived encoder exposes the ADT's existing native BEAM representation as
opaque `BeamTerm`. A user-owned hand-written `implementation BeamEncode for T`
is the override mechanism. Importing `Std.Beam` alone does not commit every type
in a module to a wire representation.

`BeamDecode` is not derived until the generated decoder validates every
constructor tag, arity, primitive guard, and recursively decoded field.

## Macro staging rule

A macro expansion must not call a newly constrained helper while its generated
expression is being proof-checked outside the final lifted module. Typeclass
dictionaries are resolved in the final generated declaration environment.

Therefore a typed OTP macro emits a local adapter with a concrete captured type:

```cure
fn encode_child_id(id: ChildId) -> BeamTerm = to_beam(id)
```

and its callback/helper calls that adapter. The lifted module explicitly imports
the interface. This keeps recursive expansion transparent and avoids hidden
dictionary arguments at the isolated expansion-proof seam.

The general compiler gate is: a source-defined macro may generate a lifted
module containing a `where BeamEncode(t)` adapter and a call using an explicitly
derived instance. The result must compile and run through the ordinary pipeline.

## OTP surface

- Actor messages and requests are typed values; generated send/call wrappers
  encode at the boundary.
- FSM state names, events, and callback actions are typed values. Generated
  callbacks lower `Keep`, `Next`, and `Stop` to native `gen_statem` results.
- Supervisor strategies, restart policies, shutdown policies, child kinds, and
  child identities are typed. Raw child specifications remain explicit.
- Application phases are typed. Generated callbacks encode/decode only at the
  application boundary.

Existing raw OTP forms remain available under visibly raw names. They do not
define the preferred public vocabulary.

## Verification

Each migration requires:

1. elaboration rejection without the required instance;
2. derived representation and hand-written override tests;
3. recursively expanded macro coverage;
4. a live OTP runtime test;
5. generic-Unix AtomVM verification where the underlying facility exists.

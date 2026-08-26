# Compile-Time Reflective BEAM Macros

**Status:** authoritative design for the remaining macro work

**Date:** 2026-07-14

**Applies to:** the macro facility, source-defined BEAM algebra, `actor`,
`fsm`, `sup`, `app`, and the final AtomVM integration work

**Mandatory diagnostic dependency:**
`2026-07-20-structured-compiler-diagnostics-design.md`. The remaining macro
phases use its structured errors, source labels, and expansion provenance; they
must not introduce new bare verifier errors.

## 1. Purpose

Cure is moving from compiler-owned OTP object classes to source-defined,
transparent macros. The final system must let a user define an actor-like
abstraction using the same language facilities used by the standard library.
The compiler may provide generic parsing, expansion, elaboration, reflection,
and code emission, but it must not contain an OTP object model or an OTP-
specific lowering case.

Macro interpretation is a compile-time computation. Its result is ordinary
Cure source syntax and declarations, which are parsed, elaborated,
kernel-checked, erased, and compiled into direct BEAM code. This document is
the design authority for resolving the remaining gaps. The autopilot plan
remains the chronological execution ledger and must be updated as each phase
lands.

## 2. Non-negotiable invariants

### 2.1 Compile-time only

Macro reflection and syntax values exist only while compiling. They must not
introduce any of the following into generated runtime code:

- a `Syntax` value or syntax interpreter;
- a dynamic macro dispatcher;
- a runtime type or tag test used to emulate macro expansion;
- an `EffectM` or free-monad interpreter for BEAM operations;
- an opaque container helper such as `__otp_container`;
- a second runtime object layer around processes;
- a runtime indirection solely because a construct was produced by a macro.

The output of a macro must be observationally equivalent to the code a user
would write by hand. Any runtime value that remains must be demanded by the
user's program or by the explicit BEAM operation itself, never by the macro
implementation.

### 2.2 Normal compilation after expansion

Every expansion follows the same path as handwritten code:

1. recursively expand nested macros from the inside out;
2. parse the resulting syntax and declarations;
3. resolve names and imports;
4. elaborate to Core;
5. normalize and kernel-check where required;
6. erase compile-time-only indices and evidence;
7. emit direct runtime code.

No macro-specific runtime path may bypass these stages.

### 2.3 User-definable vocabulary

The compiler owns generic mechanisms only. BEAM vocabulary, callback names,
behavior declarations, message-code derivation, state transitions, child
specifications, and application startup structure belong in Cure source files.
The standard library may define these as ordinary functions, syntax macros,
computed macros, data types, and explicit FFI declarations. Moving an
OTP-specific helper from the compiler into an Elixir helper is not sufficient.

### 2.4 No avoidable workarounds

An implementation must extend the generic language mechanism when the current
mechanism is insufficient. It must not preserve a bespoke compiler case,
require users to write declarations that the macro can derive, or hide a
missing normalization rule behind aliases, opaque helper calls, or runtime
dispatch.

## 3. What is already useful and remains

The following work is foundation and must be preserved:

- local syntax macro parsing and use-site expansion;
- recursive inside-out computed expansion;
- active-stack cycle detection with an infinite production budget;
- expansion provenance and callback context plumbing;
- hygienic fresh names and metadata-aware substitution;
- typed repeated syntax fields represented as `List(Syntax)`;
- `Std.Syntax` as a real reflected Cure ADT;
- source-level syntax builders and `lift_module` construction;
- declaration-position computed expansion before `LiftModule.collect`;
- compile-time totality closure for ordinary helper functions;
- the expansion soundness firewall and generative macro checks;
- generic, qualified import resolution in ordinary elaboration;
- the checked BEAM process algebra and raw foreign boundary;
- the transparent source-level actor prototype and its end-to-end tests.

Some current standard-library macro bodies are exploratory implementations.
They may be replaced by more general source-level analyzers, but the parser,
reflection bridge, expansion engine, declaration ordering, and proof gates are
not throwaway work.

## 4. Research conclusions

### 4.1 Racket: bindings are not names

Racket syntax objects combine datum with lexical scopes, source information,
and properties. Expansion recursively processes syntax objects at phase levels;
binding identity is determined by scope sets and phase, not by comparing the
printed symbol. This is the relevant lesson from the local Racket checkout at
`/Users/ch/Develop/racket`, especially its syntax model and expander sources.

Cure does not need to reproduce Racket's complete scope-set implementation in
this phase. It does need the same separation of concerns:

- syntax inspection is structural and staged;
- name resolution produces binding identity before evaluation;
- generated identifiers carry hygiene information;
- macro expansion is recursive parsing, not string substitution followed by a
  special OTP compiler.

### 4.2 Dependent type reflection and normalization

The local research corpus contains the most relevant implementation-oriented
papers:

- de Moura et al., *Elaboration in Dependent Type Theory*
  (`1505.04324`): elaboration turns incomplete surface input into explicit
  terms and uses computational reduction while solving constraints.
- Vivekanandan, *Code Generation for Higher Inductive Types: A Study in Agda
  Metaprogramming* (`1808.08330`): Agda elaborator reflection exposes typed
  quote/unquote and declaration construction rather than asking a runtime
  interpreter to inspect code.
- Ullrich and de Moura, *Beyond Notations: Hygienic Macro Expansion for
  Theorem Proving Languages* (`2001.10490`): hygiene is applied at the
  elaborator boundary so later phases do not need to know how it was achieved.
- Jang et al., *Moebius: Metaprogramming using Contextual Types*
  (`2111.08099`): contextual types describe open code together with the
  context in which it is valid, and typed pattern matching can inspect code.
- Kovacs, *Staged Compilation with Two-Level Type Theory* (`2209.09729`):
  staging-by-evaluation gives code generation through a semantic domain and
  preserves conversion rather than manipulating arbitrary ASTs.
- Hu and Pientka, *DeLaM: A Dependent Layered Modal Type Theory for
  Meta-programming* (`2404.17065`): typed, layered code inspection and
  recursive code manipulation can coexist with decidable conversion.
- Christiansen and Brady, *Elaborator Reflection: Extending Idris in Idris*
  (ICFP 2016): a metaprogram inspects reflected clauses (`lookupFunDefnExact`
  returns a function's defining clauses) and emits top-level declarations
  (`declareDatatype`, `defineFunction`) through the same elaborator that
  checks handwritten code. The representation is typed core syntax (`Raw`
  elaborated to `TT`), not a semantic domain. This is the closest living
  precedent for `derive_actor`, and — since Cure targets Idris parity — the
  primary model to follow.
- Altenkirch and Kaposi, *Normalisation by Evaluation for Type Theory, in
  Type Theory* (`1612.02462`): normalisation-by-evaluation yields decidability
  of definitional equality for dependent type theory. This is the
  conversion-decidability foundation the reflection layer must respect, and an
  exemplar of the tradition beneath Kovacs's staging-by-evaluation. Its theory
  has no primitive-literal layer, so it does not by itself license reducing
  `atom == atom` — that is a separate primitive-reduction completeness fix
  (§5).

These papers do not agree; the corpus splits into two camps. The
*semantic/staging* route (Kovacs; Altenkirch-Kaposi underneath) buys decidable
conversion precisely by **forbidding** intensional inspection of object code.
The *typed-syntactic/modal* route (Christiansen-Brady's Idris reflection,
DeLaM, Moebius; and pragmatically Lean 4 macros) keeps decidable conversion
**while** inspecting code, by working over typed modal or contextual *syntax*
rather than a semantic domain.

Cure's design inspects code: `derive_actor` traverses a `Std.Syntax` ADT,
classifies handler arms, and emits declarations. It therefore belongs to the
typed-syntactic camp, not the semantic one. The correct consequence is that
the next reflection work is a typed, **compile-time syntactic** reflection
interface (Idris-elaborator-reflection-shaped), never a *runtime* `Syntax`
evaluator, and it must preserve decidable conversion in the Altenkirch-Kaposi /
Kovacs sense. The existing `Std.Syntax` ADT and `MacroSyntax` bridge are the
beginning of this interface.

## 5. Atom equality normalization

### 5.1 The gap

Reflected syntax tags are atoms. A generic source-level helper such as:

```cure
fn has_tag(syntax: Syntax, expected: Atom) -> Bool = tag(syntax) == expected
```

is valid Cure, but the compile-time evaluator currently does not normalize
equality between atom literals. This makes generic structural analyzers
artificially unable to branch on a reflected tag. Avoiding the comparison in
one macro is not a complete language solution.

### 5.2 Correct solution

Atom equality must be implemented as a normal compile-time computation in the
primitive-reduction layer, subject to the same termination and conversion rules
as existing primitive literal reductions. Concretely: `==`/`!=` on non-numeric
operands already elaborate to the polymorphic `struct_eq`/`struct_ne` global,
whose reduction fold currently fires only for numeric literals (`{:vint,_}` /
`{:vfloat,_}`). The fix is to extend that existing fold with an `{:vatom,_}`
clause, mirroring the numeric case — not to introduce a new atom-specific
reduction rule. (Atom *values* are already compared in the conversion layer;
this closes the parallel gap in `==`/`struct_eq` reduction.) The reduction
must:

- reduce equality of two known equal atom literals to `true`;
- reduce equality of two known distinct atom literals to `false`;
- leave equality involving a neutral or unknown atom unreduced;
- preserve symmetry and congruence;
- avoid equating atoms with any other primitive or syntax constructor;
- have no special knowledge of OTP, macros, or `Std.Syntax`.

This is a completeness fix to primitive reduction, not a runtime feature and
not a macro-specific escape hatch. It may touch the trusted reduction layer
only under the full TCB bar already recorded in the autopilot state:
red-green tests, termination coverage, no-new-equations coverage, the complete
Antigen gate, and the complete ExUnit gate. No runtime atom-discrimination
helper may be added as a substitute.

### 5.3 Required proof cases

The implementation must cover at least:

1. `:node == :node` normalizes to `true`;
2. `:node == :leaf` normalizes to `false`;
3. `tag(Node(...)) == :node` reduces through the reflected syntax builder;
4. an open atom variable remains neutral;
5. atom equality is not convertible with integer, boolean, or string equality;
6. nested equality computations terminate by structural descent;
7. generated macro code contains no runtime tag comparison introduced by this
   feature.

## 6. Qualified names in staged elaboration

Every global reference in a computed callback must resolve to the same stable
registry key used by ordinary module elaboration. For example, unqualified
`map` imported from `Std.List` must become `:"Std.List#map"` in callback Core
when that is the binding selected by the importing environment.

The fix must be in generic name resolution, not in `actor.cure` and not in a
fully qualified spelling forced on macro authors. Ordinary expressions,
callback bodies, generated helper functions, and nested macro callbacks must
share this resolution path. The totality checker must receive qualified Core
globals and reject only genuinely unknown or non-total definitions.

Required tests include an imported helper used unqualified in a callback, a
local definition shadowing an imported helper, a qualified callback call, a
nested callback using a transitive import, ambiguous imports, and a proof that
no bare dangling global remains before compile-time certification.

## 7. Typed staged reflection

### 7.1 Reflection object

`Std.Syntax` remains a compile-time data type. It is not emitted into runtime
modules. Its constructors and builders must be sufficient to inspect and
construct ordinary Cure syntax, declarations, blocks, and lifted modules.

Reflection must carry a typed expansion context when a delayed callback is
interpreted. The context is compile-time metadata and may include the enclosing
declaration kind, callback name and arity, parameter names and syntax,
parameter type syntax, declared return type syntax, state and message/event
type syntax when available, and source provenance for diagnostics. The parser
now records parameter and return type syntax in the generic callback context;
later source-defined builders may add domain-neutral declarations such as
inherited state or protocol fields without changing the compiler's object
model.

The context must be explicit in the reflected input, not recovered by an
OTP-specific compiler branch. If a callback needs more context, extend the
generic staged input record so the context is supplied as typed input.

Note on `contextual`: in the current implementation `contextual` is a
macro-*rule* flag, not a callback marker. Its only operational effect is to
exempt the rule from the standalone expansion-soundness proof — the MacroFuzz
generative firewall records such rules as `deferred` rather than proving them
in isolation — because the rule's template contains free type holes that are
only resolvable once a use site supplies the enclosing types. It does not defer
elaboration and does not leave a metavariable unsolved. The goal is to retire
the *need* for this proof exemption by deriving message/callback types (§9), so
that the transparent rules either disappear or become provable standalone — not
to "unmark" a callback. Retiring `contextual` therefore depends on the
derivation work and cannot precede it (see §12).

### 7.2 Structural analysis

Generic syntax operations may include structural traversal, constructor views,
attribute lookup, list traversal, literal inspection, and declaration
construction. They must not encode actor, FSM, supervisor, or application
semantics in `Std.Syntax`.

Actor-specific interpretation belongs in `actor.cure`; FSM-specific
interpretation belongs in `fsm.cure`; shared generic syntax mechanics belong in
`Std.Syntax`. This preserves user extensibility while allowing lexical reuse of
ordinary Cure functions.

### 7.3 Hygiene and scopes

Generated bindings must remain hygienic. Existing `<fresh Name>` support is a
valid foundation, but declaration-producing reflection must also ensure that
generated nominal type names do not collide with user declarations, generated
callback helpers cannot capture use-site variables, user syntax retains its
intended bindings, and generated declarations resolve in their insertion
environment.

The implementation may use Cure's deterministic gensym mechanism while richer
scope representation is developed. It must not use runtime names or string
post-processing as a substitute for compile-time binding tracking.

## 8. Declaration-producing expansion

A computed declaration can produce more than one compile-time artifact. The
required result model is a syntax block containing ordinary declarations and a
lifted module, or an equivalent typed declaration bundle. The generic pipeline
must:

1. expand nested computed uses inside the declaration;
2. splice every produced declaration into the surrounding declaration stream;
3. register generated nominal types before generated functions refer to them;
4. collect `lift module` requests only after expansion;
5. elaborate the lifted module in an environment containing generated
   declarations, imports, macros, and ordinary helpers;
6. preserve enclosing source provenance and hygiene.

The generated message type must be one nominal declaration shared by the
handler module and external callers. Reconstructing an equivalent anonymous
union at each use site is not acceptable.

## 9. Source-level derivation of process codes

### 9.1 Actor and FSM message types

`actor` and `fsm` should infer their message/event code from handler clauses
when the input is derivable. An explicit `messages <Type>` or `events <Type>`
annotation remains a supported override, but is no longer the required normal
path.

Derivation must inspect handler syntax at compile time and produce a nominal
message/event type declaration, any aliases needed by generated callbacks, the
callback declarations and behavior metadata, and the lifted module containing
direct BEAM code.

The derived type must be the same type used by `Pid(m)`, `send`, `call`, and
external constructors. Type indices and message codes are erased from runtime
values; they exist to check the program before emission.

### 9.2 Soundness policy

Derivation must reject, with a source diagnostic, handlers that cannot yield a
closed and correct code set. In particular, reject or require an explicit
override for catch-all or variable-only arms, guards whose accepted set cannot
be represented, duplicate or overlapping constructor heads with incompatible
payload views, non-exhaustive handlers when totality is required, reply types
that cannot be inferred from `handle_call`, and malformed callbacks.

The macro must never guess a narrower message type and thereby manufacture an
unsound `Pid(m)`.

### 9.3 Shared construction

Common syntax traversal and declaration construction may be ordinary reusable
Cure functions. They are not actor-specific compiler helpers. A local macro or
shared builder may return a syntax block, but it must remain transparent and
must not hide an opaque container call.

### 9.4 Reply channels

`handle_call` induces a request-reply exchange, and its reply type is part of
the derived contract. The reply is not a bare value type; it is a one-shot
typed channel. Following the typed-actor idiom (mailbox types,
`https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/`), the caller allocates a fresh single-use
process reference typed to accept exactly one reply message `Reply(T)`, and
passes the *output* capability to the actor as a payload of the call message;
the caller retains the *input* capability and waits on it. The derived message
type for a `handle_call` clause therefore carries a `Pid(Reply(T))`-typed
field, where `T` is the reply type inferred from the clause body. This typing
yields forgotten-reply and caller self-deadlock detection, and erases to an
ordinary BEAM reference at runtime.

### 9.5 Scope of the message discipline

`Pid(m)` for v1 is a nominal message type — the closed set of message
constructors an actor accepts — plus the one-shot reply channels of §9.4. This
is a legitimate "typed channels v1": it delivers **send-conformance** (a
`send`/`call` cannot carry a constructor the actor does not handle), which is
the primary safety property, and it is exactly what the derivation produces. A
constructor set is therefore not under-powered for v1.

The following richer mailbox-type disciplines are explicitly **out of scope for
v1** and belong on the roadmap, in priority order:

- *typestate / protocol state* — a message type that evolves as messages are
  consumed (e.g. "handle `Init` before any `Request`"), expressible as the
  residual of a commutative-regex mailbox pattern. This is the only discipline
  that structurally exceeds a constructor set, and the primary future target;
  it is also the most inference-hungry (Special Delivery names inference as the
  open usability problem). Note too that the BEAM mailbox is ordered by arrival
  with selective receive on *every* BEAM (not just AtomVM — this is the standard
  concurrent-Core-Erlang semantics, machine-checked in Bereczky et al.,
  `https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/`), whereas the mailbox-type theory above is
  stated for *unordered* interactions; the commutative-regex residual therefore
  does not transfer to BEAM without first reconciling that ordering gap.
- *multiplicity* — bounds on how many of each message may be pending (e.g. "at
  most one `Config`").
- *junk-freedom* — a static guarantee that no message is left unconsumed.

Adopting any of these must not weaken the v1 send-conformance guarantee or
introduce a runtime mailbox interpreter.

## 10. BEAM algebra and direct lowering

The checked BEAM algebra remains a standard-library layer over honest raw
foreign operations. It describes typed operations such as process creation,
message send, receive, call/reply, links, monitors, and supervision. Its types
and evidence are checked at compile time and erased where appropriate.

`beam_ops` is a source-defined macro over that algebra. It must expand into
ordinary operation composition and direct FFI-facing code. There is no runtime
operation interpreter. The generated module must contain the calls and control
flow required by the requested operation sequence, just as handwritten code
would.

The four standard macros are thin adapters:

- `actor.cure` derives message code and emits actor callbacks;
- `fsm.cure` derives event code and emits transition callbacks;
- `supervisor.cure` validates child declarations and emits supervisor code;
- `app.cure` emits application startup and supervision wiring.

The detailed FSM surface, verification contract, and normative lowering of an
FSM through the shared source-defined actor behavior substrate are specified in
`2026-07-19-typed-fsm-as-constrained-actor-design.md`.

The compiler must not recognize these four names specially. A user-defined
macro that emits the same generic declaration vocabulary must use the same
pipeline.

### 10.1 Reusable macro rule families

The public standard macros must be authorable without copying a large
declaration template into every grammar alternative. The current form repeats
the same `syntax actor`/`syntax fsm`/`syntax sup`/`syntax app` prefix and the
same lifted-module declarations for each optional lifecycle clause. That is a
poor source-language abstraction boundary: changing one common callback,
import, alias, behavior declaration, or startup operation requires editing
many independent rules, and a user-defined behavior cannot reuse the common
part without moving it into an opaque compiler or Elixir helper.

This is a language facility, not a request to hide the generated runtime behind
a helper. It has two required layers:

1. **Shared declaration builders.** Ordinary Cure functions over `Std.Syntax`
   construct reusable declaration bundles: imports, behavior metadata, state
   aliases, default callbacks, lifecycle functions, and caller-supplied
   overrides. The builder returns ordinary syntax that is reparsed,
   recursively expanded, elaborated, checked, and emitted through the common
   pipeline. It must not return an opaque container value or invoke a runtime
   dispatcher.
2. **Composable grammar rule families.** The public vocabulary should describe
   the syntax shape, not parser mechanics. A family uses ordinary words for
   cardinality and receives a generated typed syntax record:

```cure
syntax family GenServerDefinition
  state Type
  optional messages Type
  optional initial Expression
  optional init Code
  optional on_call Cases
  optional on_cast Cases
  optional on_info Cases
  optional terminate Code
  optional code_change Code
end

macro actor <name: ModuleName>
  accepts GenServerDefinition
  expands with derive_actor
```

`state Type` is exactly one section; `optional on_call Cases` is zero or one;
`repeated route Route` is zero or more; and `one_or_more field Field` requires
at least one. Indented sections end naturally at dedent. `Code` remains an
explicit escape hatch for genuinely free-form bodies, but macro authors do not
write `Code until dedent` in the normal case. The initial built-in categories
are `Name`, `ModuleName`, `Type`, `Pattern`, `Expression`, `Statement`, `Code`,
`Cases`, `Parameters`, `Fields`, `Declarations`, `ModuleBody`, `Token`, and
`Syntax`.

The generated record is conceptually:

```cure
type GenServerDefinitionSyntax = {
  state: Syntax,
  messages: Option(Syntax),
  initial: Option(Syntax),
  init: Option(Syntax),
  on_call: Option(Syntax),
  on_cast: Option(Syntax),
  on_info: Option(Syntax),
  terminate: Option(Syntax),
  code_change: Option(Syntax)
}
```

The category is validated by the family parser and preserved in field metadata;
the runtime representation remains ordinary reflected syntax. Source ranges,
section provenance, cardinality, and order must survive reflection so tooling
and diagnostics can identify both the duplicate and the original declaration.

The expander API should be beginner-readable:

```cure
fn derive_actor(
  name: ModuleNameSyntax,
  definition: GenServerDefinitionSyntax
) -> MacroResult = ...
```

`accepts` supplies the structured body and `expands with` names the compile-time
function. Internally the implementation may lower this to the existing
`computed by` machinery, but `computed by` and `contextual` are not required
surface syntax for ordinary macro authors.

Families may be reused with `includes OtherFamily`, exposing included fields
directly. Initial support must reject conflicting fields rather than offer
renaming/exclusion transformations. Defaults should normally be applied by the
expander, preserving the distinction between an absent section and a section
whose semantic value happens to be defaulted. Cross-field validation remains
ordinary Cure code returning structured diagnostics, not a new constraint DSL.

Families may also declare reusable token productions. A production captures
ordinary typed grammar categories, and a field whose shape names that family
may consume the production without adding an artificial section keyword:

```cure
syntax family Transition
  syntax <from: Name> --<event: Name>--> <to: Name>
  optional update Expression

syntax family Machine
  one_or_more transitions Transition
```

The production's holes and structured child sections form one generated typed
record. Thus `Locked --Coin--> Unlocked` is data for the source-defined macro,
not compiler-owned FSM syntax. An optional indented body belongs to that record,
so the same facility can represent nested grammars such as knitting sections
and rows. Production matching, indentation, cardinality, provenance, reflection,
printing, and diagnostics are generic compiler mechanisms; the meaning of the
captured names and punctuation remains ordinary Cure expander code.

The semantic contract is fixed: a user can define an actor-like macro by
reusing the generic family and changing only its expansion function. The
generated result remains direct Cure declarations and direct foreign
operations. Tests must prove a user-defined family, nested family composition,
duplicate and ambiguous sections, cardinality errors, source-range diagnostics,
and hygiene all use the same ordinary AST/Core path as a handwritten expansion.

### 10.2 Beginner-friendly feature priority

The following requests are intentionally split so the macro implementation has
a coherent safe beginner path rather than accumulating convenience syntax before
the representation and hygiene contracts are sound.

**Build now, as part of the family and safe-syntax foundation:**

- semantic capture types for simple literals (`Atom`, `Int`, `String`, etc.) and
  explicit syntax wrappers for unevaluated `Expression`, `Pattern`, `Type`, and
  `Code` captures;
- direct expander parameters (`derive_actor(name, definition)`) with generated
  input records retained as an advanced fallback;
- typed `syntax ...` templates with visibly distinct syntax splicing, literal
  lifting, declaration-list splicing, and intentional identifier construction;
- automatic lifting only for the closed set of primitive/tuple/list values, never
  arbitrary strings as identifiers;
- definition-site hygiene by default, explicit caller-name capture, and explicit
  fresh/private/exported name construction;
- typed `Std.Syntax` declaration builders with named arguments, including
  functions, modules, aliases, parameters, match arms, imports, and `use`;
- generated family fields as ordinary record access, repeated captures as
  ordinary `List(T)`, unordered sections by default, and declarative empty-block
  cardinality (`Cases` nonempty, `Code` optionally empty);
- `MacroResult`/structured diagnostics, `Result` convenience conversion, source
  provenance, and expansion-aware errors that point back to authored sections;
- a clear safe `Std.Syntax` versus advanced `Std.Syntax.Raw` boundary. Raw node,
  token, scope, and metadata operations remain available but are visibly unsafe.

Macro declarations and families follow Cure's ordinary layout convention. They
do not introduce a special `end` requirement or expose `Code until dedent` to
authors; the parser owns indentation boundaries.

**Maybe later, after the foundation is stable:**

- inline expansion clauses for tiny macros and implicit `block macro` body
  capture;
- generated `has_field`/`field_or` convenience methods and friendly field aliases;
- custom family examples, editor completion/hover, canonical formatting, macro
  check/expand/trace commands, and source-side expansion assertions;
- grouped/plural section spellings, canonical section ordering, normalization
  hooks, and advanced family inclusion transformations;
- user-defined syntax categories, constructor-style syntax alternatives, parser
  derivation from semantic ADTs, and pattern matching directly over syntax;
- dedicated `derive`/`typed macro` forms, explicit phase controls, public API
  export policies, and broader syntax-provenance controls.

These later features must build on the same typed family records, hygiene,
diagnostic, and direct-emission contracts. None may reintroduce string-based
rewriting, runtime macro interpretation, or compiler-owned OTP knowledge.

## 11. Complete standard OTP macro contract

This section is normative and exhaustive for the first complete implementation
of `actor`, `fsm`, `sup`, and `app`. A feature described here is not optional
merely because an older macro, public document, or test exercises a smaller
surface. The implementation ledger may divide the work into smaller commits,
but completion means every requirement and gate in this section is satisfied.

The four forms are ordinary standard-library macros. Their authored syntax is
parsed by generic syntax families, their expanders are total Cure functions,
and their output is ordinary declarations plus direct checked BEAM operations.
They share infrastructure; they do not share a runtime object system.

### 11.1 Shared architecture and representation boundary

All four macros MUST use the following compilation architecture:

```text
authored container syntax
  -> typed source-defined syntax-family records
  -> total source-defined validation and derivation
  -> recursively expanded ordinary Cure declarations
  -> ordinary elaboration and kernel checking
  -> erasure of types, indices, syntax, and proofs
  -> direct OTP callbacks and checked foreign operations
```

`Std.ActorBehavior` (or a later source-defined replacement) is the reusable
compile-time module-emission substrate. It may construct direct `gen_server`,
`gen_statem`, `supervisor`, and `application` callback modules, but it MUST NOT
exist as a runtime dispatcher or wrapper. `fsm` is a constrained actor and MUST
reuse this substrate for process lifecycle, delivery, calls, stop behavior, and
optional capabilities. `sup` and `app` reuse the same declaration builders and
checked startup algebra without pretending to be actors.

The raw BEAM boundary is explicit and narrow:

- `BeamTerm`/`RawTerm`, module atoms, callback tuples, and foreign result shapes
  may occur in `Std.Otp.Raw`, representation codecs, and visibly raw escape
  hatches;
- preferred APIs use nominal Cure types, `ExitReason`, typed handles, typed
  messages/requests/events, closed policy types, and `StartResult`;
- `BeamEncode`/`BeamDecode` (or their final consistently named equivalents)
  define how typed values cross the boundary; derivation is structural and may
  be overridden by an explicit implementation;
- inbound decoding MUST validate the runtime shape before attaching phantom
  indices or constructing a typed value; an unchecked polymorphic projection
  from `BeamTerm` is forbidden;
- outbound encoding MUST not silently widen arbitrary typed values to atoms or
  raw terms; use of the raw representation is syntactically visible;
- codec failures are typed results or declared process failures, never a forged
  typed value.

The compiler remains unaware of OTP behavior names, callbacks, actor state,
transition graphs, child policies, application phases, and all vocabulary in
the following subsections. Generic support for identifier transformation,
typed patterns, nested productions, declaration publication, or diagnostics
must be added to `Std.Syntax`/the generic macro pipeline when required. An
actor-specific Elixir helper is not an acceptable shortcut.

### 11.2 Actor: typed mailbox fold

An actor is an effectful mailbox fold whose accumulator is an immutable Cure
value retained as the argument of OTP's suspended receive loop:

```text
loop(state)
  receive message
  next <- handle(message, state)
  loop(next)
```

OTP owns scheduling, suspension, mailbox receipt, and tail recursion. Cure owns
the state type, message/request algebras, handler coverage, reply family, and
every state update. State MUST NOT live in a mandatory ETS registry, host-side
mutable actor object, process-dictionary state slot, or hidden
`%State{caller, meta, payload}` wrapper.

#### 11.2.1 Preferred actor surface

The preferred structured surface is domain vocabulary, not callback tuples:

```cure
rec CounterState
  count: Int

actor Counter
  state CounterState
  initial CounterState{count: 0}

  on_message
    Increment() -> CounterState{state | count: state.count + 1}
    Add(amount: Int) -> CounterState{state | count: state.count + amount}

  on_call Value() returns Int
    reply state.count
```

The final query production MAY use equivalent layout punctuation, but it MUST
capture the request constructor, typed payload binders, declared reply type,
reply expression, and optional state update as typed fields. It MUST NOT infer
reply types by sniffing integer, float, atom, boolean, tuple, or variable syntax.
The explicit `returns` information derives `ReplyOf`; it is not a redundant
annotation on a raw callback.

The complete preferred grammar provides:

- exactly one `state Type`;
- optional `initial Expression` or typed `on_start`, with a diagnostic for an
  invalid combination or uninitialised state;
- one nonempty `on_message` section containing nominal constructor patterns;
- zero or more typed `on_call Request(...) returns ReplyType` productions;
- optional typed `on_info`, limited to an explicitly declared external/system
  message code rather than `Any`;
- optional `on_start`, `on_stop`, and `on_failure` lifecycle sections;
- optional typed observer, timer, name, link, monitor, and introspection
  capabilities, each requested explicitly;
- an optional declaration body for helper types/functions used by the generated
  behavior, with deterministic declaration ordering and hygiene.

`on_message` bodies return the next `State`. Query clauses return a value of
their declared reply type and preserve state unless an explicit `update State`
section is present. Lifecycle hooks receive typed values: `on_stop` receives
`ExitReason`, failures receive a closed generated or declared error type, and
observers receive only their declared notice type. Preferred handlers never see
OTP `from` tuples, callback result tags, raw module atoms, or `BeamTerm`.

Raw `init`, `handle_cast`, `handle_call`, `handle_info`, `terminate`, and
`code_change` remain available only under a visibly raw escape-hatch surface.
They use checked raw boundary types and do not weaken or silently merge with the
preferred derived contract. Unreleased legacy aliases and duplicate backend
templates MUST be removed; compatibility is not a reason to retain them.

#### 11.2.2 Derived actor declarations

The actor macro derives, as applicable:

```cure
type Message = Increment | Add(Int)
type Request = Value

fn ReplyOf(request: Request) -> Type = match request
  Value() -> Int

typealias Handle = DepActorServer(Message, Request, ReplyOf)
```

An asynchronous-only actor derives a nominal empty `Request` type and uses
`ActorServer(Message, Request, Unit)`. A uniform-reply optimization MAY use
`ActorServer(Message, Request, Reply)` internally, but it must preserve the
same separation between asynchronous messages and synchronous requests.

Repeated constructor appearances MUST agree on payload arity, type, relevance,
and order. Binder names may differ when their positional types agree. Catch-all,
variable-only, guarded, overlapping, malformed, or open constructor sets MUST
be rejected unless an explicit typed protocol override makes the accepted set
closed and sound. Handler coverage is checked against the derived or declared
protocol. A message value can never be used as a request, and a request cannot
be sent asynchronously unless it also appears independently in `Message`.

Dependent replies are mandatory. Distinct request constructors may return
distinct types from one PID. The generated callback is checked against
`ReplyOf(request)` under constructor refinement, and the client adapter returns
`Effect(ReplyOf(request))`. Returning another request's reply type is a compile
error. Syntax-level uniform reply guessing is removed from the preferred path.

#### 11.2.3 Generated actor API

Every preferred actor generates direct typed adapters:

```cure
fn start(...) -> Effect(StartResult(Handle))
fn send(handle: Handle, message: Message) -> Effect(Unit)
fn stop(handle: Handle, reason: ExitReason) -> Effect(Unit)
```

The startup parameters are derived from the initialization mode. A stable
surface SHOULD expose `start()` for a declared initial value and
`start_with(initial: State)` when callers supply state; temporary compatibility
`start_link` helpers may remain only until all in-tree callers migrate.
`StartResult` models `Started(handle)`, startup failure with its typed/opaque
reason policy, `StartIgnored`, and malformed foreign results honestly. Only a
validated `{:ok, pid}` result may acquire the actor indices.

Each declared query generates a lower-case, hygienic named adapter, including
payload parameters, for example:

```cure
fn value(handle: Handle) -> Effect(Int)
fn lookup(handle: Handle, key: Key) -> Effect(Option(Value))
```

Identifier case conversion is a generic pure compile-time `Std.Syntax`
operation. It MUST NOT invoke a runtime string extern during expansion or add
an actor-specific host callback. A generic `request(handle, request)` MAY also
be emitted. There is no universal `get_state`; state is private unless an
authored query exposes it.

Observer delivery is opt-in:

```cure
actor Worker notifying WorkerNotice
```

Startup then requires a typed observer capability, and `notify` accepts only
`WorkerNotice`. With no observer declaration, no observer field, process-
dictionary registration, notification branch, or runtime call is emitted.
Names, history, health, registry membership, timers, links, and monitors follow
the same capability rule.

#### 11.2.4 Actor completion gates

Actor is complete only when tests prove:

- sequential messages observe immutable state evolution;
- payload-bearing messages update multiple record fields;
- wrong messages and message/request crossing fail before emission;
- multiple request constructors return distinct dependent reply types;
- wrong-branch replies and missing/duplicate handlers fail;
- generated named query adapters have correct payload and result types;
- startup success, error, ignore, and malformed results are decoded safely;
- lifecycle ordering and typed stop reasons;
- observer delivery when enabled and zero observer machinery when absent;
- no undeclared state inspection API exists;
- a user-defined actor-like macro targets the same substrate without compiler
  changes;
- emitted BEAM contains direct callbacks/operations and no syntax interpreter,
  registry requirement, actor wrapper, or type witness call.

### 11.3 FSM: verified constrained actor

The normative FSM design is additionally detailed in
`2026-07-19-typed-fsm-as-constrained-actor-design.md`. If wording conflicts,
the stricter requirement applies. The complete public surface begins with the
compact graph:

```cure
fsm TrafficLight with TrafficData
  initial Red
  terminal Failed

  Red --Timer--> Green
  Green --Timer--> Yellow
  Yellow --Timer--> Red
  * --Emergency(reason: EmergencyReason)--> Failed
    update TrafficData{data | failure: Some(reason)}
```

There is no space between `--` and the event constructor. States and events are
PascalCase nominal constructors, never preferred Atom labels. The macro derives
closed `State` and `Event` types by cataloguing the graph. Typed event payload
binders are scoped over that edge's `when`, `update`, and `perform` sections;
every occurrence of an event agrees on positional payload structure.

The graph grammar and implementation MUST support:

- explicit `initial` plus first-non-wildcard-source defaulting;
- repeatable terminal states;
- wildcard source rows with explicit-row precedence;
- typed payload-bearing events;
- pure `when Bool` guards and pure `update Data` expressions;
- every valid record-update layout supported by Cure, including multiple-field
  updates and a `|` beside either the source record or first field;
- visibly effectful `perform` sections through the checked BEAM algebra;
- typed notices and optional transition telemetry;
- `on_start`, `on_stop`, `on_enter`, `on_exit`, `on_failure`, and `on_timer`;
- timer declarations, hard events (`Event!`), and soft events (`Event?`);
- optional history, registry, and health layers with zero generated residue when
  disabled.

`update` defaults to preserving data. Effects are sequenced separately and do
not mutate the pure reducer's value behind the type checker. Hard events fire
automatically after entry and are valid only as the sole unconditional outgoing
event. Soft failure preserves the current state/data and bypasses normal failure
routing as declared. Timers deliver a typed event or typed hook; they do not
inject an untyped mailbox term into the public event algebra.

#### 11.3.1 FSM derivation and lowering

Each FSM derives at least:

```cure
type State = ...
type Event = ...

rec MachineState
  state: State
  data: Data
```

It then derives a total pure transition reducer containing direct nested matches
over these constructors. The reducer returns a typed keep/next/failure result;
it is not a runtime transition table. The generated actor behavior owns the
suspended `MachineState`, receives typed events, evaluates the reducer, performs
declared effects, commits the returned state/data, and serves explicitly
specified administrative queries.

The preferred implementation MUST NOT retain `on_transition`, callback-mode
maps, lowercase event atoms, `%[:ok, ...]` result tuples,
`%Cure.FSM.State{caller, meta, payload}`, a host-side FSM runtime shell, or a
runtime graph/verifier for compatibility. A direct `gen_statem` callback module
is acceptable when produced by the shared source-defined behavior substrate;
an interpreter over reflected transitions is not.

The generated typed API includes:

```cure
fn start(data: Data) -> Effect(StartResult(Handle))
fn send(handle: Handle, event: Event) -> Effect(Unit)
fn state(handle: Handle) -> Effect(State)
fn data(handle: Handle) -> Effect(Data)
fn snapshot(handle: Handle) -> Effect(Snapshot(State, Data))
fn stop(handle: Handle, reason: ExitReason) -> Effect(Unit)
```

Payload delivery uses the event constructor itself, not
`send_with(pid, :event, arbitrary_payload)`. The generated module name is the
authored name; no hidden `Cure.FSM.` prefix is added.

#### 11.3.2 FSM compile-time verifier

Verification is a total source-defined Cure computation over reflected graph
records and emits structured diagnostics with both original source locations.
It MUST check:

1. closed and well-formed state/event catalogues;
2. event payload consistency;
3. initial and terminal state validity;
4. reachability from the selected initial state;
5. deadlock freedom for reachable non-terminal states;
6. duplicate unguarded transitions;
7. guarded-edge ambiguity, rejecting when disjointness is not established;
8. wildcard precedence and complete shadowing;
9. hard-event exclusivity and soft-event policy;
10. update result type and payload/data binder scope;
11. hook, notice, timer, and failure typing;
12. total reducer coverage for every accepted state/event pair.

The compiler MUST contain no FSM verifier knowledge. Unsound ambiguity is an
error, not a warning resolved by source order.

#### 11.3.3 FSM completion gates

FSM is complete only when positive and negative tests cover every feature and
verifier item above, shared-actor-substrate architecture, absence of forbidden
legacy/runtime machinery, live Unix behavior, and live AtomVM behavior for the
documented supported subset. The nested production mechanism must also be
generic enough to implement the knitting algebra without an FSM parser case.

### 11.4 Supervisor: typed static supervision tree

`sup` declares a statically checked supervision tree and emits a direct OTP
`supervisor` behavior module. Its preferred surface is structured data:

```cure
sup App.Root
  strategy OneForOne
  intensity 3
  period 5

  children
    actor Counter as CounterChild
      start Counter.start_with(0)
      restart Permanent
      shutdown After(5000)

    supervisor App.Workers as WorkersChild
      restart Permanent
```

Equivalent concise defaults are allowed, but the reflected family MUST retain
the distinction between absent and explicitly supplied fields. Module names are
`ModuleName` syntax known at compile time, not user-authored module atoms.
Child identities are derived nominal constructors (or values of an explicitly
declared `ChildId` type), not an untyped Atom requirement. At the final OTP
boundary they are encoded through `BeamEncode`. Startup arguments retain their
typed values until that explicit encoding boundary; heterogeneous raw MFA lists
require a visibly raw form.

The closed policy vocabulary is:

- strategy: `OneForOne`, `OneForAll`, or `RestForOne`;
- restart: `Permanent`, `Transient`, or `Temporary`;
- shutdown: `BrutalKill`, `Infinity`, or `After(PositiveDuration)`;
- child kind: actor/worker or supervisor;
- restart intensity: `Nat` (zero allowed);
- restart period: a strictly positive duration.

Arbitrary atoms and negative/unrestricted integers are rejected by ordinary
elaboration. Policy conversion to OTP atoms/integers occurs in one private
source-defined boundary. If AtomVM supports a smaller policy subset, the
unsupported choice receives a compile/package diagnostic rather than silently
changing semantics.

The supervisor verifier MUST check before emission:

1. child IDs are unique;
2. each child start expression has the generated/declared typed startup result;
3. actor and supervisor child kinds match their handle/start contract;
4. restart, shutdown, strategy, intensity, and period are closed valid values;
5. a supervisor is not its own direct or transitive descendant;
6. referenced generated modules exist in the project graph;
7. dependency cycles and duplicate nested ownership are diagnosed with paths;
8. child ordering is preserved where `RestForOne` gives it semantics;
9. raw argument/foreign forms are explicit and cannot contaminate typed sibling
   specs.

Cross-module existence and cycle checks integrate with the generic project
dependency graph and exported macro/module metadata. They do not justify a
compiler-owned supervisor object model.

The macro derives an ordinary nominal child catalogue and checked child specs,
then emits direct `init/1` and startup callbacks. The public API includes a
typed supervisor handle, honest `StartResult`, stop with `ExitReason`, and typed
child inspection when requested. A mandatory ETS registry keyed by module atom
is forbidden; naming and discovery are optional layers.

Supervisor is complete only when tests prove default and every policy,
typed/encoded identities and startup arguments, nested supervisors, real child
restart behavior, duplicate/cycle/unknown-child failures, `RestForOne` order,
optional inspection, no registry when absent, direct Unix execution, and the
supported AtomVM subset. Emitted code contains no child-spec interpreter or
opaque supervisor container.

### 11.5 Application: typed OTP ownership and release entry point

`app` declares the OTP application callback module that owns one root
supervision tree. Project/package metadata remains in `Cure.toml`; callback
behavior remains in Cure source:

```cure
app CureForge
  root Forge.Root

  phase WarmCache
    perform Cache.warm()

  phase Ready
    after WarmCache
    perform Metrics.ready()

  on_stop reason
    perform Telemetry.stopped(reason)
```

The complete application family supports:

- exactly one root supervisor module and its typed startup input;
- optional typed application state when more than the root handle is required;
- zero or more nominal start phases with typed phase arguments/results;
- explicit phase dependencies and deterministic order;
- effectful phase bodies through the checked algebra;
- typed `on_start`, `on_stop ExitReason`, and declared startup-failure policy;
- optional included OTP applications and environment requirements validated
  against project metadata;
- direct release/application-resource generation for Unix and AtomVM.

Phase names are derived nominal constructors in Cure. Conversion to OTP's phase
atom and inbound phase-argument decoding occur at the representation boundary.
The preferred source does not use a flat alternating Atom list. Duplicate
phases, unknown dependencies, dependency cycles, phase declarations absent from
the manifest, and manifest phases absent from source are compile errors. Phase
bodies are ordinary effects and execute once in dependency order under OTP's
application lifecycle.

The generated application callbacks:

- validate/decode OTP's startup kind and arguments where the program uses them;
- start the declared root through its typed generated API or the checked
  supervisor algebra;
- return the honest OTP application start result without asserting success;
- retain exactly the typed application state required for `stop` and phases;
- route phase dispatch through direct constructor matches, not a runtime phase
  table or macro dispatcher;
- stop/clean up through typed lifecycle code and `ExitReason`.

Project compilation MUST enforce one application owner per application
artifact, source/manifest name agreement, root inclusion in the emitted module
set, included-application availability, phase agreement, and deterministic
`.app`/release metadata. Release construction uses already checked emitted
modules; it does not reparse Cure source or resurrect a container compiler.

The public control API (`ensure_started`, `ensure_all_started`, stop, and typed
environment access) belongs to `Std.App` over checked/raw boundaries. Environment
decoding uses `BeamDecode`; a missing or malformed value is represented by
`Option`/`Result`, not an unchecked cast.

Application is complete only when tests prove root startup and failure,
stateful stop, multiple ordered effectful phases, phase dependency diagnostics,
manifest/source agreement, environment decoding, `.app` generation, bootable
Unix release behavior, supported AtomVM packaging/boot, and absence of a runtime
phase interpreter or opaque application container.

### 11.6 Cross-container composition requirements

The four completed macros MUST compose in one real program:

1. an application starts a generated root supervisor;
2. the supervisor starts generated actors and an FSM with typed initial values;
3. actors exchange only their declared message/request values;
4. the FSM receives payload-bearing events and emits a typed notice to an
   explicitly supplied actor observer;
5. dependent queries return distinct types from the same actor;
6. a supervised failure exercises the declared restart/shutdown policy;
7. application phases perform checked operations before readiness;
8. shutdown delivers typed reasons and runs lifecycle hooks in observable order.

This integration program MUST compile and run on Unix BEAM. A documented subset
MUST package and run on the supported generic-unix AtomVM; target exclusions
must be explicit diagnostics and tests, not silent skips. The test inspects the
emitted BEAM/imports to prove there is no syntax value, macro dispatcher,
transition/child/phase interpreter, mandatory registry, legacy container class,
or runtime type witness introduced by expansion.

### 11.7 Mandatory removal and documentation work

Completion also requires deletion, not merely disuse, of:

- bespoke compiler cases or host helpers recognizing `actor`, `fsm`, `sup`, or
  `app` semantics;
- duplicate legacy macro backends and unreleased compatibility grammars;
- preferred APIs based on untyped Atom messages/events/IDs/phases;
- mandatory actor/FSM registries, hidden callers, metadata/payload wrappers,
  history, and health state;
- runtime syntax, operation, transition, child-spec, or phase interpreters;
- opaque `__otp_container`-style expansion targets;
- obsolete docs/tests that advertise deleted syntax or runtime architecture.

Raw foreign escape hatches remain, but their names, types, documentation, and
tests MUST make unsafety visible. Examples are migrated to the preferred
surfaces only when examples are restored; an intentionally empty examples
directory is not repopulated merely to satisfy this gate.

Public documentation MUST show the final authored syntax, derived types,
generated APIs, capability model, runtime state location, FFI encoding/decoding,
diagnostics, and target support for all four macros. The roadmap and autopilot
ledger must contain no stale claim that an intermediate floor is complete
parity.

## 12. Required implementation order

Implement in this order; do not use a later layer to paper over an earlier gap:

1. **Core primitive reduction:** add and prove compile-time Atom equality.
2. **Staged name resolution:** ensure callback globals are fully qualified.
3. **Typed callback context:** supply the enclosing declaration/callback
   context as explicit typed staged input, so no callback relies on context
   recovered by a bespoke compiler branch. (Retiring the `contextual`
   proof-exemption is *not* this step — it depends on derivation and lands in
    step 10; see §7.1.)
4. **Declaration bundles:** support generated nominal declarations plus lifted
   modules in one expansion.
5. **Generic syntax analysis:** add the structural traversal and declaration
   builders needed for derivation.
5a. **Reusable macro rule families:** factor repeated standard-library grammar
   and lifted-declaration templates into source-defined `Std.Syntax` builders,
   then add generic grammar-family composition usable by user macros. Preserve
   ordinary parsing, diagnostics, lexical scope, hygiene, recursive expansion,
   and direct checked emission.
6. **Representation boundary and checked BEAM algebra:** complete structural
   and overridable `BeamEncode`/`BeamDecode`, inbound validation, nominal
   handles, `ExitReason`, `StartResult`, and the raw escape-hatch namespace;
   make `beam_ops` use derived operation codes and direct expansion.
7. **Actor derivation and behavior:** implement §11.2 completely: derive the
   message, request, dependent reply, notice, and failure algebras; generate
   the typed lifecycle and API; prove state is threaded by the direct receive
   loop; add named query adapters through generic identifier transformation;
   and implement each optional capability without a mandatory wrapper.
8. **FSM derivation and verification:** implement §11.3 completely on the actor
   substrate: payload-bearing events, graph expansion, total reducer,
   wildcard/guard/update/effect ordering, lifecycle, timers, hard/soft events,
   typed API, all static verifier passes, and the generic hooks required by a
   later knitting-algebra macro.
9. **Supervisor derivation and verification:** implement §11.4 completely:
   typed child identifiers and policies, typed child starts, structural and
   transitive verification, direct supervisor callbacks, and typed lifecycle
   and inspection APIs without a mandatory registry.
10. **Application derivation and release integration:** implement §11.5
    completely: typed phases and dependencies, root-supervisor startup,
    lifecycle, environment decoding, manifest generation, project discovery,
    release integration, and direct application callbacks.
11. **Cross-container composition:** pass the §11.6 application → supervisor →
    actor/FSM proof, including messages, dependent queries, notices, restart,
    phases, shutdown, and inspection of emitted BEAM for forbidden machinery.
12. **Compiler and legacy cleanup:** perform every deletion in §11.7, remove
    every bespoke OTP object path and forbidden
    opaque helper, and retire the `contextual` proof-exemption once the derived
    rules (steps 7–8) have replaced the transparent templates that required it —
    every remaining rule must then pass the standalone expansion-soundness
    proof rather than being recorded `deferred`.
13. **Branch integration:** merge `kernel-parity-batch` into `idris-parity`,
    then merge `idris-parity` into `core-let-binder`, resolving in favor of
    source-defined macros and the generic pipeline.
14. **Runtime gates:** run Unix and generic-unix AtomVM proofs, then focused,
    full-suite, Antigen, formatting, and warnings-as-errors gates.

Every item is a phase with a descriptive commit. Run `mix format` after each
phase commit and commit formatter changes separately when they occur.

## 13. Verification requirements

Each phase must include positive, negative, diagnostic, expansion-shape, and
runtime tests appropriate to that phase and preserve the full existing suite.
The final verification matrix MUST include:

| Area | Required proof |
|---|---|
| Generic macro facility | Recursive inside-out expansion terminates; hygiene, provenance, nested production families, declaration publication, typed callback context, and generic identifier transformation work without OTP-specific compiler knowledge. |
| Representation boundary | Derived and overridden encoders round-trip supported values; decoders reject malformed terms before constructing typed values; raw escape hatches are visibly raw; no unchecked polymorphic decode exists. |
| Actor | All derived message/request/reply types are nominally shared; dependent query replies type-check at callers; malformed sends and replies fail statically; lifecycle and opt-in capabilities work; state survives between messages only through the receive-loop accumulator. |
| FSM | State/event cataloguing, payloads, wildcards, initial/terminal rules, guards, updates, effects, timers, hard/soft events, lifecycle, static graph diagnostics, and typed state/data APIs work; invalid graphs fail at compile time. |
| Supervisor | Typed child IDs and policies, typed startup, nested trees, ordering, cycle/duplicate/self-reference checks, restart behavior, shutdown, and opt-in inspection work without a mandatory registry. |
| Application | Typed phases and dependencies, root startup, environment decoding, lifecycle, manifest/project/release integration, and phase diagnostics work without atom-list protocols or runtime phase interpretation. |
| Composition | One real application boots a supervisor containing actors and FSMs, exchanges typed messages and dependent queries, restarts a failed child, executes phases, emits typed notices, and shuts down cleanly. |
| Architecture | Emitted Core/BEAM and imports contain no runtime `Syntax`, macro dispatcher, operation/transition/child/phase interpreter, opaque OTP container, mandatory registry, legacy container class, or runtime type witness introduced by expansion. |
| Targets and quality | The same required surface passes Unix and generic-unix AtomVM gates, the full test suite, Antigen, formatter checks, warnings-as-errors, and the trusted-core/termination gates required by any primitive-reduction change. |

Direct BEAM operation calls must match equivalent handwritten behavior. The
compiler source scan must find no OTP-specific object cases, behavior names,
callback vocabularies, or opaque container helper. Documentation tests must use
the final authored syntax and generated API, so stale examples cannot preserve
an obsolete architecture accidentally.

Useful negative tests must assert that generated runtime code does **not** call
any syntax interpreter, macro dispatcher, or opaque OTP container helper.

## 14. Design references

Repository references:

- `docs/superpowers/specs/beam/2026-07-09-typed-beam-process-algebra-design.md`
- `docs/superpowers/specs/tooling/2026-07-12-tier3-computed-by-execution-design.md`
- `docs/superpowers/specs/macros/2026-07-13-transparent-beam-algebra-otp-macros-design.md`
- `docs/superpowers/specs/beam/2026-07-19-typed-beam-representation-design.md`
- `docs/superpowers/specs/beam/2026-07-19-typed-actor-behavior-design.md`
- `docs/superpowers/specs/beam/2026-07-19-typed-fsm-as-constrained-actor-design.md`
- `docs/superpowers/specs/macros/2026-07-19-constrained-macro-expansions-design.md`
- `docs/superpowers/plans/2026-07-12-macro-facility-autopilot-state.md`
- `docs/SUPERVISION.md` and `docs/APP.md` (migration inputs; update them to
  describe the final architecture rather than preserving legacy behavior)
- `docs/research/metaprogramming/`
- `https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/`

External research:

- https://arxiv.org/abs/1505.04324
- https://arxiv.org/abs/1808.08330
- https://arxiv.org/abs/2001.10490
- https://arxiv.org/abs/2111.08099
- https://arxiv.org/abs/2209.09729
- https://arxiv.org/abs/2404.17065
- https://arxiv.org/abs/1612.02462
- Christiansen and Brady, *Elaborator Reflection: Extending Idris in Idris*,
  ICFP 2016
- https://arxiv.org/abs/1801.04167 (Mailbox Types for Unordered Interactions)
- https://arxiv.org/abs/2306.12935 (Special Delivery: Programming with Mailbox
  Types)
- https://arxiv.org/abs/2311.10482 (Bereczky, Horpácsi & Thompson, *A
  Formalisation of Core Erlang, a Concurrent Actor Language*) — reference
  operational semantics for the sealed raw process base; see
  `https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/raw-algebra-conformance-checklist.md`

# Constrained Macro Expansions

**Status:** Approved design; implementation pending

**Applies to:** structured syntax families, typed captures, generated-expansion
proofs, lifted modules, `BeamEncode`, and the standard `actor`, `fsm`, `sup`,
and `app` macros.

**Parent specifications:**

- `2026-07-14-compile-time-reflective-beam-macros-design.md`
- `2026-07-19-typed-beam-representation-design.md`

## 1. Problem

The macro system can capture syntax by grammatical shape, but it cannot yet
state that the value denoted by a captured expression must satisfy a typeclass.
This blocks direct typed boundary syntax such as:

```cure
sup My.Root
  children
    child My.Worker id CounterWorker()
```

The child identity is an ordinary Cure expression. Its type is known only after
elaboration, and its BEAM representation is supplied by `BeamEncode`. Expanding
it through an ordinary helper carrying `where BeamEncode(i)` currently exposes
the helper's hidden dictionary argument during isolated expansion checking and
can fail as `:too_few_arguments`.

Two adjacent defects make workarounds worse:

1. `Expression` is an authoritative macro category but the generated proof
   machinery can reject it as `{:unsupported_hole_type, "Expression"}`.
2. A syntax family containing only optional sections may accept an empty prefix,
   leave meaningful tokens unconsumed, and allow a less-specific fallback rule
   to consume the declaration.

The solution must be generic. The compiler must not learn supervisor, actor,
FSM, application, OTP callback, or `BeamEncode` vocabulary.

## 2. Required surface

### 2.1 Expression captures

`Expression` captures one complete Cure expression using the ordinary expression
parser and precedence table:

```cure
syntax child <module: ModuleName> id <identity: Expression>
```

It is narrower than `Code`: it cannot consume declarations, multiple statements,
or a dedent-delimited block. It retains source provenance and hygiene exactly as
other reflected syntax.

### 2.2 Capture obligations

A rule or family field may attach typeclass obligations to the semantic value of
an expression capture:

```cure
syntax child <module: ModuleName> id <identity: Expression>
  where BeamEncode(identity)
```

For reusable families the same spelling applies to a field:

```cure
syntax family ChildDefinition
  module ModuleName
  id Expression where BeamEncode(id)
```

The name inside the obligation must name a capture in the same rule or family.
An obligation may mention its inferred type but may not treat the captured value
as a type. The conceptual elaborated constraint is:

```cure
where BeamEncode(type_of(identity))
```

The surface uses `BeamEncode(identity)` because `type_of` is an elaborator
operation, not a runtime or source-level function.

Multiple obligations are permitted and are resolved in written order. Ordinary
interface coherence rules apply; named-instance selection is not inferred.

### 2.3 Complete family matching

A structured family match succeeds only if:

1. every required/`one_or_more` field is present;
2. every consumed section is valid;
3. the match consumes the complete indented family definition; and
4. at least one token after the macro prefix is consumed unless the family has
   an explicitly declared empty form.

An optional-only family does not implicitly declare an empty form. Authors who
want one write:

```cure
accepts Definition or empty
```

If a family recognizes a section word but its contents are invalid, that is a
diagnostic for that family, not permission to fall through to a broader raw
rule. Fallback occurs only when the next token cannot begin any family section.

This makes the following invalid rather than silently selecting another rule:

```cure
macro sup <name: ModuleName>
  syntax family Definition
    optional children Code
    optional typed_children Code

sup Root
  typed_children ... # must be consumed or diagnosed by Definition
```

## 3. Elaboration and staging

### 3.1 Two-stage obligation handling

Constraint-bearing expansion has two checks:

1. **Use-site check.** Elaborate the captured expression, infer its type, and
   resolve every declared interface obligation in the caller's environment.
2. **Generated-unit check.** Reify the resolved obligation as an ordinary hidden
   dictionary parameter or a concrete local adapter in the generated syntax,
   then elaborate the complete generated unit through the ordinary pipeline.

The macro expander must not evaluate `BeamEncode`, call an Elixir helper, or
manufacture a BEAM term. It transports checked syntax and the same dictionary
evidence ordinary Cure calls use.

### 3.2 Lifted-module adapter

When a constrained capture is used inside a lifted module, expansion emits an
ordinary Cure adapter with the concrete captured type:

```cure
fn __encode_child_id(id: ChildIdentity) -> BeamTerm
  where BeamEncode(ChildIdentity) =
  to_beam(id)
```

The name is hygienically generated. The adapter and its dictionary are ordinary
declarations: they are reparsed, recursively expanded, elaborated, checked,
erased, and emitted normally.

If the captured expression is closed, expansion may instead emit the expression
directly at the adapter call site. It may not precompute or serialize it in the
macro evaluator.

### 3.3 Imported and derived instances

The final lifted module inherits owner declarations according to the existing
lifted-module scope rules. A type declared with:

```cure
type ChildIdentity = Counter | Backup deriving BeamEncode
```

is re-elaborated in the lifted owner environment and its derived implementation
is registered by the ordinary deriving/coherence pass. No separate macro
instance registry exists.

A hand-written implementation remains authoritative through normal coherence.

### 3.4 Failure modes

Failures are reported at the captured expression, not as generated helper arity
errors:

- missing instance: `no BeamEncode implementation for ChildIdentity`;
- overlapping instance: the normal coherence diagnostic;
- expression has the wrong contextual type: the normal conversion diagnostic;
- malformed generated adapter: generated-expansion diagnostic with expansion
  provenance.

`:too_few_arguments` must never be the user-visible result of an unresolved
macro capture obligation.

## 4. Expansion proof system

### 4.1 Expression witnesses

The macro proof generator must support `Expression`. Its base witness inventory
contains checked expressions for primitive types and locally generated ADTs:

- `0 : Int`
- `false : Bool`
- `:witness : Atom`
- a generated nullary constructor for an owned witness ADT
- a generated unary constructor containing an `Int`

Witnesses are syntax inputs only. They do not become runtime interpreters or
compiler-owned OTP containers.

### 4.2 Constraint-aware witnesses

For `Expression where Interface(capture)`, the proof generator creates a fresh
owned witness type and an ordinary implementation of the required interface.
For `BeamEncode` the generated proof fixture is conceptually:

```cure
type Witness = WitnessA | WitnessB deriving BeamEncode
```

The rule is then expanded using `WitnessA()`. This proves that:

- the capture parses as an expression;
- derivation/implementation registration happens before use;
- dictionary resolution survives expansion;
- the generated unit elaborates; and
- the dictionary is erased or emitted exactly as for handwritten Cure.

The proof generator must not special-case `BeamEncode`: it uses the interface
descriptor and either a requested deriving facility or a generated handwritten
implementation body supplied by the proof fixture protocol. If no witness can
be constructed, macro definition fails with a specific unsupported-proof
obligation rather than accepting the macro unchecked.

### 4.3 Negative proof

Every constrained rule receives a negative proof run with the implementation
removed. Expansion must fail with `no_instance` at the capture. This prevents a
rule from declaring an obligation it never actually threads into generated code.

## 5. Standard macro expansions

These are library definitions built on the generic facility, not compiler cases.

### 5.1 Actor

Preferred source:

```cure
type Command = Increment | Reset deriving BeamEncode

actor Counter
  state Int
  messages Command
  initial 0
  on_cast
    Increment -> state + 1
    Reset -> 0
```

The macro emits an ordinary `gen_server` module. Generated client wrappers call
`to_beam` only where an opaque/raw foreign primitive requires `BeamTerm`;
callback-local typed dispatch continues to use `Command`. Derived actor message
types request `deriving BeamEncode` explicitly in generated syntax.

Raw callback-result forms remain under raw syntax and do not define the normal
actor surface.

### 5.2 FSM

Preferred source:

```cure
type DoorState = Locked | Unlocked deriving BeamEncode
type DoorEvent = Coin | Push deriving BeamEncode

fsm Turnstile
  state Int
  states DoorState
  initial Locked
  event_type DoorEvent
  events
    Coin -> Next(Unlocked(), data + 1)
    Push -> Keep(data)
```

`Keep`, `Next`, and `Stop` are checked `FsmAction(state, data)` constructors.
The generated callback calls the standard-library action encoder and returns the
native `gen_statem` tuple. User code never writes `:keep_state_and_data` or
`:next_state` in the preferred form.

### 5.3 Supervisor

Preferred source:

```cure
type ChildIdentity = CounterWorker | BackupWorker deriving BeamEncode

sup Root
  children
    child Counter id CounterWorker()
    child Backup id BackupWorker()
```

Each `id` is an `Expression where BeamEncode(id)`. Expansion produces the native
child-spec tuple with an opaque `BeamTerm` ID slot. Module names are reflected
from `ModuleName`; users do not write module atoms or placeholder IDs.

Policies remain closed Cure values:

```cure
restart Permanent()
shutdown ShutdownAfter(Seconds(5))
kind Worker()
```

An explicitly raw child declaration accepts an opaque raw child specification
for third-party OTP integration.

### 5.4 Application

Preferred source:

```cure
type BootPhase = WarmCache | Ready deriving BeamEncode

app Main
  root Root
  phases BootPhase
    WarmCache -> warm_cache()
    Ready -> ready()
```

Phase patterns and values are typed. The generated application callback performs
the boundary translation required by OTP's phase atom/term vocabulary. The root
remains a `ModuleName` capture and lowers directly to supervisor startup.

Raw lifecycle callbacks remain available explicitly for release-tool and
third-party integration.

## 6. Soundness and runtime constraints

- Generated runtime code contains direct functions, matches, constructors, and
  foreign calls only. There is no syntax interpreter or runtime macro dispatcher.
- `BeamTerm` remains opaque.
- Encoding is total. Decoding foreign input remains fallible.
- A constraint is resolved by the ordinary coherence table.
- Erased proofs and dictionaries do not become wire fields.
- Macro evaluation never executes FFI operations.
- No change to `lib/cure/core/*` is required.

## 7. Ordered implementation

1. Reject incomplete/zero-progress structured-family matches.
2. Implement `Expression` capture in parsing, reflection, printing, validation,
   fuzz witnesses, and provenance.
3. Parse and represent capture obligations.
4. Resolve obligations at actual macro use sites.
5. Thread evidence into lifted generated modules through ordinary adapters.
6. Add positive and negative generic macro proof fixtures.
7. Replace supervisor placeholder-ID workarounds with constrained child syntax.
8. Migrate actor send wrappers and derived messages.
9. Complete typed FSM event/state boundary coverage.
10. Add typed application phases.
11. Run focused, compiler/stdlib, full, Antigen, Unix OTP, and AtomVM gates.

Each phase is committed independently and updates the autopilot ledger.

## 8. Acceptance gates

- An optional-only family cannot silently accept an empty prefix before known
  section tokens.
- `Expression` is accepted anywhere the authoritative macro category list allows.
- A user-defined macro—not only `sup`—can require `BeamEncode` for a captured
  expression and use it in a lifted module.
- Derived and hand-written encoders both work; missing encoders fail at the
  capture.
- Supervisor child IDs require no atom or placeholder in preferred syntax.
- FSM users require no raw OTP result atoms in preferred syntax.
- Application phases can be user ADTs.
- Actor/FSM/supervisor/application live-container tests pass on Unix OTP.
- The generic-Unix AtomVM container proof passes when AtomVM is available.
- No generated module contains a runtime macro interpreter, `Cure.*.Builtins`
  bridge, or opaque OTP container introduced by expansion.

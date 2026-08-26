# Cure Multiple-IR Architecture

**Status:** Design specification  
**Date:** 2026-07-21  
**Scope:** Dependent typing, algebraic effects, monadic composition, explicit
flow/state-machine execution, actors, and BEAM/Cure restricted-runtime backends.

## 1. Decision summary

Cure will not lower its source AST directly to Erlang abstract forms. It will
use a sequence of typed intermediate representations, each with a narrower
purpose and an explicit preservation contract:

```text
Surface AST
  → Elaborated Core
  → Typed Value/Computation IR
  → Handler/Continuation IR
  → Defunctionalized Flow IR
  → Concurrency/Capability IR
       ├→ Core Erlang          (BEAM/OTP)
       └→ C/ESP32 machine IR   (restricted backend)
```

The arrows are not all mandatory for every function. Pure straight-line code
may stop at Typed Value/Computation IR and lower directly to a target. Code
that can suspend, cross a handler boundary, enter a scheduler, or cross an
actor/process boundary must pass through Flow IR. Concurrency/Capability IR is
required for process topology and deployment checking, but may be erased after
those checks when its facts are represented in explicit target operations.

The central invariant is:

> Every IR preserves the semantics and static obligations of the preceding IR;
> an IR may erase information only when the preceding phase has discharged the
> proofs or checks that depended on it.

Core Erlang and C are targets, not Cure's semantic IR. Neither target can
represent all of Cure's dependent proofs, effect rows, latent effects,
continuation ownership, or deployment constraints.

## 2. Evidence and design consequences

### 2.1 Dependent effects: separate values from computations

The dependent-effects paper uses fine-grain call-by-value with distinct value
and computation terms. Its dependent value and computation types have the shape

```text
A, B := base | dependent pair | dependent function | sum
C, D := T_E A
```

and restrict dependencies in types and refinements to value terms, not
computations. Its `let` rule composes effects but initially does not permit the
continuation effect to depend directly on the result of the preceding
computation; refinements can recover useful cases by rewriting the result.
See [A Category-Theoretic Framework for Dependent Effect
Systems](https://arxiv.org/abs/2601.14846).

Cure adopts this as the boundary between the trusted value Core and
Computation IR:

- dependent types, proofs, conversion, and normalization operate on values;
- computations have result types plus qualitative effect rows and optional
  indexed/refinement summaries;
- effectful computation nodes never become ordinary kernel values merely
  because they are stored in a runtime closure or frame;
- dependent facts needed by a frame are reified as checked value fields or
  proof-carrying metadata before lowering.

### 2.2 CPS and defunctionalization: the origin of Flow IR

CPS serializes evaluation order; defunctionalization replaces the resulting
higher-order continuations with first-order data constructors. The resulting
abstract machine is the relevant precedent for Cure Flow IR, especially when a
recursive interpreter or direct-style program must execute without an implicit
call stack. See [Continuation-Passing Style, Defunctionalization,
Accumulations, and Associativity](https://arxiv.org/abs/2111.10413).

The paper also gives an important limitation: defunctionalization is a data
refinement justified by the set of continuation shapes actually produced. Cure
must therefore derive Flow frame constructors from typed continuation sites,
not use one untyped universal continuation record.

### 2.3 Handlers: typed continuation obligations

The effect-handler verification paper translates handler continuations through
defunctionalization so that verification can reason about them as first-order
objects. It also specifies client/server protocols using preconditions,
postconditions, and modified state. See [A Framework for the Automated
Verification of Algebraic Effects and Handlers](https://arxiv.org/abs/2302.01265).

Cure's Handler/Continuation IR therefore has to retain more than an operation
label:

- operation parameter and result types;
- continuation input and answer types;
- pre/postconditions or refinement summaries where available;
- state/resource locations the handler may modify;
- whether the continuation is one-shot, affine, or unrestricted;
- whether the handler is deep, shallow, scoped, or sealed.

### 2.4 Low-level continuation targets: single-shot is a real design point

WasmFX provides typed continuation creation, suspension, and resumption as a
low-level target mechanism. Its `resume` consumes a continuation and therefore
supports single-shot continuations; it explicitly associates handler behavior
with resumption and permits scheduler queues of suspended continuations. See
[Continuing WebAssembly with Effect Handlers](https://arxiv.org/abs/2308.08347).

Cure will not require BEAM or C to expose native continuation primitives. The
paper nevertheless supports three Cure decisions:

1. continuation types must be explicit at an intermediate boundary;
2. one-shot continuation ownership is a practical first implementation;
3. scheduler queues may store suspended computations, but only as typed
   computation-layer objects.

### 2.5 Core Erlang: frame semantics and actor semantics are references

The sequential Core Erlang formalization defines evaluation frames and frame
stacks as an executable small-step semantics. The concurrent formalization
builds process-local frame execution into actor/node semantics containing
mailboxes, links, signals, and scheduling actions, and uses bisimulation for
observable equivalence. See [A Frame Stack Semantics for Sequential Core
Erlang](https://arxiv.org/abs/2308.12403) and [A Formalisation of Core Erlang, a
Concurrent Actor Language](https://arxiv.org/abs/2311.10482).

These are semantic and verification precedents, not a complete Cure compiler
IR. Cure should borrow their separation between local evaluation frames and
concurrent process state, while retaining Cure-specific effect and type
metadata before the Core Erlang boundary.

### 2.6 Direct-style elaboration: keep source syntax independent of lowering

Frank elaborates direct-style effect programs into a smaller Core language of
functions, cases, and unary handlers, with a sound small-step semantics. See
[Do Be Do Be Do](https://arxiv.org/abs/1611.09259).

This supports Cure having ordinary direct-style source syntax and a separate
computation representation. It does not require Cure to copy Frank's ambient
ability syntax or its treatment of suspended computations as source-level
values; the latter would be unsafe inside Cure's dependent kernel.

## 3. IR responsibilities

### 3.1 Surface AST

The Surface AST preserves source spans, user syntax, macro forms, patterns,
dependent terms, effect declarations, handlers, process declarations, and
deployment declarations.

It is not type-safe enough to serve as a backend input. Macros must be expanded
before semantic IR construction, and compile-time macro machinery must not
survive into runtime IR.

### 3.2 Elaborated Core

Elaborated Core resolves names, implicit arguments, overloaded syntax, pattern
desugaring, dependent applications, and macro expansion. It has explicit
binders and source locations but may still contain dependent type terms and
high-level effect/handler syntax.

Required properties:

- all identifiers are resolved;
- generated terms have source-origin metadata;
- macros are absent as runtime constructs;
- dependent terms are explicit enough for kernel checking;
- every effectful form is classified as primitive, abstract, higher-order,
  suspension, actor/process, or rejected.

Elaborated Core is the last representation that is allowed to contain the full
dependent language and source-level handler syntax.

### 3.3 Typed Value IR

Typed Value IR is the pure, normalized-by-construction value language used by
the dependent kernel and by the front end of code generation.

Representative grammar:

```text
v ::= variable
    | constructor(v*)
    | literal
    | pure primitive(v*)
    | closure(params, computation)
    | dependent pair(value, value)
    | proof term
```

Typed Value IR may contain closures whose bodies are computations, but a
closure is still a value only when its capture and body types have been
checked. It must not evaluate effectful bodies during kernel conversion.

Preserved information:

- value types and dependent indices;
- proof terms and definitional equality evidence;
- constructor and pattern information needed by later case compilation;
- closure capture types;
- source spans.

Erased later:

- proof terms not needed at runtime;
- definitional equality witnesses;
- source-only dependent annotations after compilation checks.

### 3.4 Typed Computation IR

Typed Computation IR is a fine-grain call-by-value representation. It separates
evaluation order from pure values and makes effect composition explicit.

Representative grammar:

```text
c ::= return(v)
    | let x = c1 in c2
    | apply(v, v*)
    | pure_op(op, v*)
    | perform(operation, v*)
    | case(v, branches)
    | raise(exception, v*)
    | handle(c, handler)
    | suspend(operation, v*, continuation)
    | spawn(actor_body, v*)
    | send(pid, v)
    | receive(patterns)
```

Each computation has a checked type:

```text
Γ ⊢c c : A ! ρ [ι]
```

where `A` is a value result type, `ρ` is a qualitative effect row, and `ι` is
optional indexed/refinement information such as protocol state, cost, resource
ownership, or a deployment fact. `ι` is never used as a substitute for the
qualitative effect row.

Required effect categories:

```text
Primitive   sealed runtime operation
Abstract    user-declared operation handled by Cure
HigherOrder operation receiving or storing a computation
Suspend     sealed control transfer to a scheduler/outer loop
Actor       spawn/send/receive/link/supervisor operation
Foreign     explicitly declared FFI operation
```

The categories may share the row namespace, but sealed effects cannot be
silently removed by an ordinary user handler. Handling an abstract effect
removes it only when the handler typing rule proves that all clauses and the
return path account for it.

The initial dependent sequencing rule follows the conservative rule from the
dependent-effects paper: the continuation's effect/index summary may not
depend directly on the result of an effectful computation. Refinement
substitution can discharge that dependency where sound.

### 3.5 Handler/Continuation IR

Handler/Continuation IR makes the control relationship around a potentially
suspending operation explicit while preserving typed handler information.

Representative entities:

```text
Handler h = {
  handled operations,
  return clause,
  operation clauses,
  deep/shallow/scoped mode,
  answer-type transition,
  state/resource protocol,
  continuation-use policy
}

Continuation k = {
  result type A,
  answer type before/after,
  captured value environment,
  remaining computation,
  effect row,
  ownership = one_shot | affine | unrestricted
}
```

This IR is the last place where a continuation may remain represented as a
higher-order function. It is also the place where answer-type modification,
handler nesting, handler completeness, and protocol obligations are checked.

The first implementation supports only `one_shot` continuations. A continuation
must be consumed, aborted, or transferred to an explicitly owning scheduler;
dropping it without a checked cleanup path is an error for resource-bearing
effects.

`handle` may lower to direct handler code when no suspension escapes the local
scope. Otherwise it produces a Flow IR boundary.

### 3.6 Flow IR

Flow IR is the typed, first-order, defunctionalized control representation. It
is the shared control boundary for BEAM, AtomVM, C, and ESP32 scheduler loops.

Representative grammar:

```text
program ::= flow_function*

flow_function ::= {
  name,
  parameters,
  entry_state,
  states,
  result/failure signatures
}

state ::= {
  id,
  parameters/captured fields,
  step,
  transitions
}

step ::= return(value)
       | call(function, values, success_state, failure_state)
       | perform(operation, values, success_state, failure_state, control_mode)
       | branch(scrutinee, cases)
       | concurrency_action(action, next_state)
       | abort(reason)

frame ::= {
  state_id,
  captured_fields,
  result_slot/type,
  handler_environment,
  ownership_token
}
```

Flow IR does not contain arbitrary closures as continuations. Every continuation
site has a state identifier and a statically known capture layout. Recursive
control is represented by transitions between states, not by an unbounded
compiler-generated call chain.

Flow IR invariants:

1. **Typed transitions:** every transition supplies exactly the fields required
   by its target state and produces the target's expected value/effect type.
2. **Explicit suspension:** a `suspend` step identifies the operation, captured
   values, owner, and resume state.
3. **Single ownership:** a one-shot frame has exactly one legal consume,
   abort, or transfer transition.
4. **No hidden effects:** every operation that can suspend, allocate, send,
   receive, spawn, fail, or call foreign code is present in the row and in the
   transition.
5. **Bounded frame shape:** each state has a statically known field layout;
   dynamic collections are explicit heap/scheduler values, not hidden stack
   captures.
6. **Pure fast path:** computations that cannot suspend or cross a required
   boundary may lower without allocating a frame.
7. **Handler scope:** a handler environment is captured only when the target
   transition can observe it; sealed runtime handlers cannot be forged as
   ordinary user data.
8. **Debug identity:** states and transitions retain source-origin IDs for
   diagnostics and backend equivalence tests.

Flow IR is not necessarily a single global state machine. It is a collection of
per-function flow machines connected by typed calls, concurrency actions, and
scheduler transitions.

### 3.7 Concurrency/Capability IR

Concurrency/Capability IR separates local continuation execution from generic
process topology, lifecycle, and capability requirements. It does not contain
compiler-owned `actor`, `fsm`, `sup`, or `app` constructs; those are expanded by
Cure macros before this boundary.

Representative entities:

```text
process_definition ::= {
  process_id,
  state_schema,
  entry_flow,
  mailbox_schema,
  handlers,
  links/monitors,
  supervision policy
}

deployment ::= {
  processes,
  process instances,
  scheduler/loop ownership,
  foreign capabilities,
  required effect closure,
  platform restrictions
}

concurrency_action ::= spawn | send | receive | link | monitor | exit | yield
```

An ordinary process body is a Flow machine plus an explicit mailbox/process boundary. A
callback or child body carries its latent computation row; spawning does not
erase that row. The deployment checker closes effects over all reachable actor
bodies, callbacks, supervisors, and foreign primitives.

The Core Erlang formalisation's process-local frame stack and process/node
semantics motivate this split. Cure's Concurrency/Capability IR may lower to Core
Erlang process primitives on BEAM or to a scheduler/runtime ABI on ESP32, but
the source-level actor abstraction remains defined in Cure rather than in an
OTP-specific compiler helper.

### 3.8 Target IRs

#### Core Erlang target

The BEAM backend emits a versioned, tested Core Erlang subset through an
isolated OTP adapter. The target includes only constructs needed by Cure:

```text
modules, functions, calls, let/letrec, case, receive,
literals, tuples, maps/binaries as required,
process primitives, and explicit flow dispatch.
```

Rows, proof terms, handler completeness evidence, one-shot ownership, and
dependent indices are erased only after their checks. Runtime-relevant facts
become ordinary Core Erlang data or direct operations. The generated program
must not contain a syntax interpreter, runtime macro dispatcher, opaque OTP
container, or generic `Effect(A)` wrapper introduced to hide an unlowered
computation.

#### C/ESP32 target

The restricted backend lowers Flow IR to C functions and explicit scheduler
records. A flow step returns a tagged transition such as:

```text
Done(value)
Next(state_id, frame_fields)
Perform(operation, payload, owner)
Fail(error)
```

The concrete ABI is a later design, but it must not rely on recursive stack
growth for suspended computations. The outer loop owns scheduling and performs
device effects only when the transition reaches the runtime boundary.

#### AtomVM target

AtomVM initially consumes the same BEAM-compatible output path where possible.
Any AtomVM-specific restriction is represented as a target capability check in
Concurrency/Capability IR or the backend, not by weakening the source effect
types.

## 4. Information-flow and erasure policy

| Information | Elaborated Core | Value/Computation IR | Handler/Continuation IR | Flow IR | Target |
|---|---:|---:|---:|---:|---:|
| Source spans | retain | retain | retain | retain IDs | debug metadata |
| Dependent types/proofs | retain | check/retain | use summaries | erase after checks | erase unless runtime witness |
| Qualitative effect rows | classify | infer/check | refine | attach to transitions | erase after closure check |
| Indexed/refinement facts | retain | check | answer/protocol checks | retain required witnesses | erase or compile witness |
| Higher-order latent effects | explicit | explicit | explicit | fields/transitions | runtime ABI/data |
| Continuation functions | may exist | may exist locally | allowed before conversion | forbidden | target calls/data |
| Frame ownership | absent/latent | latent | check | explicit token/state | runtime ownership/linear ABI |
| Actor topology | source declarations | typed operations | latent actor effects | process actions | process primitives |
| Macro syntax/interpreter | compile time only | absent | absent | absent | absent |

No phase may infer “pure” from the absence of a runtime call in its emitted
code. Purity is a typed property established before lowering, and sealed
runtime effects remain accounted for even when the target instruction is
implemented as a primitive.

## 5. Lowering contracts

### 5.1 Elaborated Core → Typed Value/Computation IR

Must preserve typing, source spans, effect declarations, and dependent
substitution. It must reject unresolved handlers, unclassified foreign calls,
and effectful terms used where kernel values are required.

### 5.2 Computation IR → Handler/Continuation IR

Must make handler scope, answer-type changes, operation clauses, continuation
captures, and continuation-use policy explicit. A handler may remove only the
effects it is typed to handle. Deep/shallow behavior must not be inferred from
backend convenience.

### 5.3 Handler/Continuation IR → Flow IR

Must be a semantics-preserving CPS/defunctionalization pass. For every
continuation shape, generate a state constructor and capture layout. The pass
must produce a proof/test artifact showing that invoking the generated state
with its frame is equivalent to invoking the source continuation.

The pass may apply the pure fast path only when no continuation escapes and no
operation can suspend across the local boundary.

### 5.4 Flow IR → Concurrency/Capability IR

Must preserve latent effects of callbacks, spawned children, supervisors, and
mailbox handlers. Every cross-process transition gets an explicit protocol and
serialization/ownership decision. The deployment effect closure is computed
before target selection.

### 5.5 Concurrency/Capability IR → Core Erlang or C

Must preserve observable concurrency actions, failure behavior, mailbox ordering
assumptions, and flow-state transitions. The Core Erlang backend is validated
through the installed OTP compiler; the C backend is validated against the
same Flow semantics and platform capability model.

## 6. Worked lowering shape

For a direct-style computation that performs an operation and then uses its
result:

```text
let y = perform Read() in
return (y + 1)
```

Typed Computation IR records `Read` and the result type. Handler/Continuation IR
records a continuation equivalent to `λy. return (y + 1)`. Flow IR may produce:

```text
state entry() =
  suspend Read(_, frame = ReadK)

state ReadK(y) =
  return (y + 1)
```

On BEAM, this may lower to a direct call when `Read` is handled locally and
cannot escape. Otherwise it lowers to an explicit state dispatch. On ESP32,
the runtime loop receives `Perform(Read, owner)` and later invokes `ReadK` with
the result. In both cases the source effect row and one-shot ownership were
checked before target lowering.

For a process callback, the callback's latent row is attached to its Flow entry
and retained in Concurrency/Capability IR. Sending the callback or spawning its owner
does not turn the callback into an untracked opaque value.

## 7. Verification strategy

The implementation should establish the following gates incrementally:

1. **Value preservation:** elaborated pure terms type-check and normalize under
   the trusted kernel without evaluating computations.
2. **Computation preservation:** Computation IR typing preserves result types
   and effect rows.
3. **Handler preservation:** handler clauses preserve answer types and protocol
   obligations; handled effects are removed only when justified.
4. **Defunctionalization preservation:** every Handler/Continuation IR step has
   an equivalent Flow transition.
5. **Frame ownership:** one-shot continuations cannot be consumed twice or
   silently dropped when cleanup is required.
6. **Concurrency preservation:** local Flow transitions and process actions preserve
   observable message/failure behavior under the chosen scheduling model.
7. **Core Erlang preservation:** generated Core Erlang is accepted by OTP and
   agrees with the Flow semantics on the supported subset.
8. **ESP32 preservation:** C/scheduler execution agrees with Flow semantics and
   satisfies stack, allocation, and capability bounds.
9. **Deployment closure:** no reachable callback, process, supervisor, or foreign
   primitive has an unaccounted effect.

The Core Erlang formalisation can serve as a future semantic reference for
sequential and concurrent target fragments. The first Cure implementation may
use executable differential tests and checked invariants; it must not claim a
full compiler-correctness proof until the target relation and all supported
constructs are formalized.

## 8. Implementation ledger

1. Freeze the source effect/handler and suspension semantics.
2. Add value/computation judgments and effect-row representations.
3. Define typed Computation IR and its printer/debugger.
4. Implement pure/effectful lowering without Flow IR for non-suspending code.
5. Define Handler/Continuation IR, answer-type checks, and one-shot policy.
6. Implement CPS/defunctionalization into typed Flow IR.
7. Add frame ownership, explicit abort/cleanup, and scheduler transitions.
8. Add Concurrency/Capability IR and latent-effect closure checking.
9. Lower one example to Core Erlang and one to a C-style scheduler loop.
10. Add Core Erlang acceptance/differential tests and AtomVM capability gates.
11. Add abstract effects and handlers after primitive flow execution is stable.
12. Defer multi-shot continuations, unrestricted effectful dependent indices,
    and direct BEAM bytecode emission until separately specified and verified.

## 9. Non-goals

This specification does not yet fix surface keywords, the concrete syntax of
effect rows, the exact Core Erlang constructor API, the C scheduler ABI, or the
full dependent treatment of answer-type modification. Those are downstream
designs constrained by these IR boundaries.

The ownership-aware restricted target profile is specified in
[`2026-07-21-lowcure-restricted-ir-design.md`](2026-07-21-lowcure-restricted-ir-design.md).

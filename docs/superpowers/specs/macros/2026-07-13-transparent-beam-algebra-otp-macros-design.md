# Transparent BEAM Algebra and OTP Macros

**Date:** 2026-07-13  
**Status:** design specification  
**Scope:** BEAM process algebra, transparent macro expansion, `beam_ops`, and
the `actor`/`fsm`/`sup`/`app` standard-library macros

This specification is the implementation contract for replacing the bespoke
compiler implementations of the four OTP object forms with ordinary Cure
macros. It consumes the existing macro facility, effect type former, typed
BEAM process algebra, and `lift module` designs:

- [`macros/2026-07-08-macro-facility-design.md`](macros/2026-07-08-macro-facility-design.md)
- [`2026-07-09-effect-type-former-design.md`](2026-07-09-effect-type-former-design.md)
- [`2026-07-09-typed-beam-process-algebra-design.md`](2026-07-09-typed-beam-process-algebra-design.md)
- [`2026-07-10-checked-beam-concurrency-design.md`](2026-07-10-checked-beam-concurrency-design.md)
- [`2026-07-09-classic-pipeline-deletion-design.md`](2026-07-09-classic-pipeline-deletion-design.md)

The central implementation order is:

1. establish the checked BEAM algebra over the honest raw BEAM boundary;
2. make macro interpretation transparent and recursively compositional;
3. implement the `beam_ops` macro using that algebra;
4. define `actor`, `fsm`, `sup`, and `app` in their own standard-library
   files using `beam_ops`, `behaviour`, `callback`, and `lift module`;
5. delete the bespoke compiler paths and prove that the ordinary compiler
   pipeline handles every resulting module.

The four OTP forms are not allowed to retain a compiler-only marker such as
`__otp_container`. A macro expansion must produce syntax that the normal Cure
parser, expander, elaborator, validator, and emitter can understand.

## 1. Decisions

### 1.1 The BEAM algebra is a checked standard-library layer

The user-visible BEAM algebra is ordinary, kernel-checked Cure. It describes
process identities, message sets, replies, supervision, links, monitors,
timers, and application lifecycle operations. It is typed in terms of the
inert `Effect(T)` type former and lowers to the sealed raw foreign boundary.

The algebra is not a collection of unchecked compiler intrinsics. The only
asserted foreign signatures are the honest, maximally permissive operations in
`Std.Otp.Raw`. All useful precision is supplied by checked definitions in the
typed layer.

The first implementation may expose fewer operations than the final algebra,
but it must establish the layering and extension points below. It must not
make the four OTP macros depend on a new opaque Elixir or Elixir-generated
runtime object.

### 1.2 `Effect(T)` remains inert

The selected effect design is retained:

- `Effect(T)` is a type former;
- effectful operations return values of type `Effect(T)`;
- effect sequencing is represented by the existing effectful let/bind path;
- there is no new `EffectM` free-monad runtime representation;
- the compiler may lower a checked effect chain to direct BEAM statements;
- an effect value that escapes a direct statement position is represented by
  the existing thunk/fallback strategy.

The BEAM algebra is therefore about typed operation signatures and checked
composition, not about giving the runtime a new monad implementation.

### 1.3 Macro output is syntax, not a compiler command

Macro interpretation returns a parsed Cure AST or a closed compile-time value
whose contents are parsed Cure AST. It never returns an Elixir source string,
raw Erlang abstract forms, a loaded module, or an opaque instruction to a
specialized compiler.

`lift module` is the one explicit compile-time value for producing an
additional compilation unit. It is collected by elaboration and emitted by the
ordinary module writer in the same commit step as the enclosing module.

### 1.4 Expansion is recursively inside out

Macro expansion is a recursive normalization to a fixed point. Nested macro
invocations are expanded before the enclosing macro interprets their result.
Every macro-generated AST is parsed and recursively expanded again before it
is elaborated or emitted.

This is a hard semantic requirement, not an optimization or a best-effort
feature. A macro must be able to use another macro in any syntax position
where ordinary Cure syntax is accepted, including:

- function bodies;
- callback bodies;
- `lift module` declarations;
- BEAM operation arguments;
- patterns and guards where the category permits macros;
- blocks captured by an outer macro and inserted into a generated module.

The implementation must also support the case where an outer macro introduces
the context required to interpret an inner macro. That case is specified in
§5.5; it must not be solved by returning an opaque marker to a special
compiler.

### 1.5 The four public macros live in their own standard-library files

The definitions remain in:

- `lib/std/actor.cure`;
- `lib/std/fsm.cure`;
- `lib/std/supervisor.cure`;
- `lib/std/app.cure`.

They are auto-preluded as standard library syntax. A separate Elixir
`builtin_macros` implementation is not the target architecture. Elixir code
may implement the generic parser/expander runtime, but it must not own the
semantics of these four OTP forms.

### 1.6 The replacement is generic, not a renamed bespoke compiler

After this work, adding a new behavior-shaped object must require:

- a standard-library macro definition;
- ordinary BEAM algebra definitions or operations;
- tests and, where appropriate, a closed callback vocabulary extension.

It must not require a new `Cure.Compiler.*Macro` module, a new compiler
dispatch branch, a source-string compiler, raw form construction, or direct
code-server mutation.

## 2. Terminology and layers

### 2.1 Layers

The implementation has five explicit layers:

~~~text
user source and standard-library macros
        |
        v
recursive parsed-AST macro expansion
        |
        v
checked BEAM algebra and transparent lift-module values
        |
        v
ordinary Cure elaboration and BEAM form emission
        |
        v
honest raw BEAM externs and OTP runtime modules
~~~

The layers have one-way ownership:

- standard-library code may use the typed algebra;
- macros may produce ordinary syntax and closed compile-time declarations;
- the elaborator validates generated syntax like handwritten syntax;
- the emitter consumes validated Core and quoted-module values;
- only the raw boundary names foreign BEAM operations.

### 2.2 BEAM algebra

In this document, **BEAM algebra** means the typed family of values and
operations that describe process interaction. It includes the following
conceptual categories:

- `Pid(messages)`, an erased process handle indexed by accepted messages;
- `GenServer(requests, replies)` and behavior-specific handles;
- message and reply codes derived from declared ADTs and callbacks;
- effect-typed operations such as `self`, `send`, `call`, `cast`,
  `spawn`, `start_link`, `stop`, timers, links, and monitors;
- supervision and application descriptors used by generated modules;
- callback result types and process-state transitions.

The algebra is not required to expose all of these as one universal sum type.
Prefer typed functions and closed ADTs where the operation family is known.
Use a closed operation description only where `beam_ops` needs to interpret a
sequence or declaration of operations.

### 2.3 Raw boundary

`Std.Otp.Raw` remains the only foreign boundary. Its operations are typed at
the most permissive honest signatures, for example:

~~~cure
raw_self() -> Effect(RawPid)
raw_send(RawPid, Any) -> Effect(Unit)
raw_call(RawPid, Any) -> Effect(Any)
raw_cast(RawPid, Any) -> Effect(Unit)
raw_monitor(RawPid) -> Effect(MonitorRef)
~~~

The exact extern spelling is an implementation detail of the existing raw
stdlib. The important properties are that the signatures are honest, the
module is sealed from ordinary user imports, and typed wrappers perform the
checked conversion before calling it.

## 3. BEAM algebra design

### 3.1 Message codes

The message index of a process handle is a code, not an unchecked type
assertion. Conceptually:

~~~text
MessageShape = { tag: Atom, fields: List(TypeCode) }
MessageCode  = Set(MessageShape)
~~~

`El(code)` is the checked Cure type of messages described by the code. Codes
are derived from declared ADTs and callback patterns. Users should not need
to hand-maintain a parallel message schema.

The first floor may use a simpler closed representation, but the representation
must leave room for:

- tag lookup;
- payload arity and field-type lookup;
- `subset` and `union` computation;
- reply lookup for request/response calls;
- erasure of code indices at runtime.

The following operations are total computations over codes:

~~~text
handles : MessageCode -> Atom -> Bool
subset  : MessageCode -> MessageCode -> Bool
union   : MessageCode -> MessageCode -> MessageCode
~~~

There is no subtyping judgment. A widening or narrowing operation is an
explicit checked function whose obligation is discharged by normalization.

### 3.2 Typed handles

The typed surface should retain the existing direction:

~~~cure
type Pid(messages)
type GenServer(requests, replies)
~~~

The code indices are erased. Runtime values remain ordinary BEAM pids or
references. The type checker sees the indices; the device sees the runtime
identity only.

Representative signatures are:

~~~cure
self() -> Effect(Pid(SelfMessages))
send(Pid(messages), El(messages)) -> Effect(Unit)
call(GenServer(requests, replies), El(requests)) -> Effect(El(replies))
cast(GenServer(requests, Unit), El(requests)) -> Effect(Unit)
stop(Pid(messages), Reason) -> Effect(Unit)
~~~

The precise `SelfMessages`, request, and reply indices depend on the ambient
behavior context. If the first floor cannot infer an index, it must expose an
explicit typed constructor or require the macro-generated declaration to
provide it. It must not silently fall back to `Any` in the public typed API.

### 3.3 Process lifecycle operations

The algebra must eventually cover the operations needed by all four macros:

| Family | Operations | Required typing property |
| --- | --- | --- |
| identity | `self`, named lookup, registration | handle index is preserved |
| messages | `send`, `cast`, event send | payload is accepted by the handle |
| requests | `call`, reply extraction | request and reply codes agree |
| process creation | `spawn`, `spawn_link`, `start_link` | callback module and init argument agree |
| lifecycle | `stop`, exit reason | target handle and reason are explicit |
| supervision | child specs, strategy, intensity, period | child descriptors are behavior-shaped |
| application | start, stop, phases | lifecycle callbacks have fixed signatures |
| observation | monitor, demonitor, process status | monitor reference is not confused with a pid |
| scheduling | send-after, cancel timer | timer reference is tracked distinctly |
| topology | link, unlink, trap-exit | link operations are effectful and explicit |

Do not add a generic `beam_op(Any)` escape to make an incomplete family appear
complete. Missing operations are implementation gaps and should be recorded as
such until they have checked signatures and honest lowering.

### 3.4 Direct lowering

The normal emitter lowers a checked effect chain directly when it is in a
statement position. For example, the conceptual program:

~~~cure
let pid = self()
let _ = send(pid, message)
pure(Unit)
~~~

must remain a checked sequence whose generated BEAM forms perform `self/0`
and `erlang:send/2` in order. The BEAM algebra must not force every
operation through a runtime interpreter.

When an effectful computation is stored or returned, the existing effect
fallback applies. This preserves the distinction between checked algebraic
composition and runtime representation.

### 3.5 Process context

Generated callback bodies need a context containing at least:

- current behavior;
- current process message code;
- request and reply codes where applicable;
- state type;
- allowed callback result shape;
- whether the body is in initialization, message handling, termination,
  supervision, or application lifecycle position.

This context is a checked elaboration context, not a dynamic global and not an
opaque compiler flag. It is introduced by `callback` and `lift module`, then
passed explicitly to recursive expansion and elaboration of their bodies.

## 4. Transparent macro contract

### 4.1 Source-level definitions

The standard-library macro files are the semantic source of the public forms.
For example, the eventual `actor.cure` definition should express an actor in
terms of:

~~~cure
macro actor ...
becomes
  lift module Named(...)
    behaviour GenServer
    callback init(...) -> ...
    callback handle_info(...) -> ...
    callback terminate(...) -> ...
    fn start_link(...) -> ...
~~~

The example is schematic. The required property is that all emitted members
are ordinary syntax or closed declarations understood by the generic pipeline.

### 4.2 Forbidden expansion products

The following are forbidden in the output of the four macros and `beam_ops`:

- `__otp_container` or an equivalent marker consumed only by a compiler
  branch;
- Elixir source strings passed to `Code.compile_string`;
- raw Erlang abstract forms assembled by a macro implementation;
- `:code.load_binary`, `:code.purge`, or equivalent code-server mutation;
- a compiler-owned behavior class that has no Cure syntax or value;
- a callback body that bypasses normal parsing, expansion, or elaboration;
- a dynamic operation name or callback name accepted through `Any`.

The compiler may use internal representations after elaboration, including
Erlang abstract forms, but those are emitter products, never macro products.

### 4.3 Re-elaboration is mandatory

Every macro result is re-entered into the normal pipeline:

1. parse or validate the returned AST;
2. recursively expand nested macros to a fixed point;
3. elaborate and type-check the expanded result;
4. validate closed behavior/callback/lift-module declarations;
5. emit only after all generated code has passed the same checks as source.

An expansion that merely records a marker for a later special-case compiler is
not transparent and does not satisfy this specification.

### 4.4 Provenance and errors

Each generated node carries:

- the original source span of the macro invocation;
- the macro name and definition span;
- the expansion path from outer invocation to inner invocation;
- the generated-node span or template label where available.

An error in a nested `beam_ops` operation inside an actor callback must point
to the user callback and show the expansion path through `actor` and
`beam_ops`. It must not report a generic failure in `ContainerMacro`
because that implementation must no longer exist.

## 5. Recursive inside-out expansion

### 5.1 Required semantic model

Define a normalizer:

~~~text
expand_fixed_point(node, context, provenance) -> Expanded(node) | Error
~~~

The normalizer recursively visits syntax children and repeatedly expands
macro invocations until the result contains no expandable invocation in any
active syntax category. It returns an AST, not source text.

The phrase **inside out** means:

~~~text
parse inner source
  -> expand its children
  -> interpret the innermost macro
  -> parse/validate its result
  -> expand macros introduced by that result
  -> hand the normalized result to the enclosing macro
~~~

For nested invocations `outer(inner(value))`, `inner` is interpreted before
`outer` receives the value unless `outer` explicitly captures the child as
a quoted syntax object. This makes macro composition deterministic and
prevents an outer macro from observing an implementation-specific
half-expanded AST.

### 5.2 Recursive traversal algorithm

The implementation should follow this shape, regardless of the concrete
Elixir module names:

~~~text
normalize(node, context, origin):
  if node is a quoted syntax object:
    return node

  if node is a macro invocation:
    args = normalize_macro_arguments(node.args, context, origin)
    raw_result = interpret_macro(node.name, args, context, origin)
    parsed_result = parse_macro_result(raw_result, origin.child(node.name))
    return normalize_generated(parsed_result, context, origin.child(node.name))

  children = map_syntax_children(node, fn child ->
    normalize(child, child_context(node, context), origin)
  end)
  return rebuild(node, children)
~~~

`normalize_macro_arguments` must distinguish syntax categories:

- ordinary expression, pattern, declaration, and block arguments recurse;
- `quote`/syntax-literal arguments remain quoted and do not recurse;
- an argument explicitly declared as delayed by the macro signature remains
  delayed until the macro introduces its declared context;
- values used only as macro parameters are normalized according to their
  category, not according to a string representation.

The parser is called on macro-produced syntax before the result is traversed.
String concatenation followed by a special compiler parser is not an allowed
implementation of this algorithm.

### 5.3 Fixed-point condition

Expansion completes only when the expanded AST has no active macro invocation
in any non-quoted syntax position. A macro invocation introduced by another
macro is therefore not left for the elaborator to discover accidentally and
not left for a behavior-specific compiler branch.

The fixed-point check must inspect all nested declarations and compilation
units, including the bodies of `lift module`, `callback`, and `beam_ops`
output.

### 5.4 Termination and cycle detection

Recursive expansion needs explicit safeguards:

- every invocation receives a stable expansion identity;
- the expander tracks `(macro_name, invocation_shape, definition_version)` on
  the current path;
- direct and indirect cycles produce a diagnostic naming the cycle;
- a configurable expansion budget prevents unbounded generated trees;
- the budget counts both invocations and generated AST size;
- a successful fixed point resets no hidden global state and is deterministic.

The budget is a diagnostic guard, not a substitute for cycle detection. Its
production default is **infinite**: valid deeply nested or linked-list-shaped
expansion is bounded by structural cycle detection, not by an arbitrary depth
constant. Hosts and tests may supply a finite invocation/AST-size budget for
resource governance, but no user program may disable cycle detection. The
active identity set is stack-scoped rather than global, so two sibling uses of
the same macro remain legal and independent.

### 5.5 Context-introducing outer macros

Strict source nesting is insufficient for OTP callbacks. An actor macro can
introduce a `GenServer` callback context that a nested `beam_ops` invocation
needs in order to type `self`, `send`, or `call`.

The expander handles this with explicit delayed syntax slots rather than an
opaque marker:

1. the outer macro signature declares which captured slots are delayed blocks;
2. the outer expansion produces a `lift module` value with a declared
   behavior and callback context;
3. the generic `lift module` expander enters that context;
4. each delayed callback block is recursively normalized inside that context;
5. the resulting callback syntax is attached to the `callback` declaration;
6. the complete lifted module is then elaborated and validated.

This remains inside-out in dependency order: the nested `beam_ops` body is
expanded before its callback is elaborated or emitted, while the behavior
context is established by the transparent `lift module` boundary. The
implementation must never expand the body as an untyped string and must never
use the old container marker to smuggle the context around the checker.

The context is lexical and scoped. It cannot leak from one lifted module into
another or from a callback body into the enclosing user module.

### 5.6 Macro-generated macros

If a macro generates a macro declaration, the declaration is registered only
after its generated syntax has been parsed and validated. Its body is not
executed during registration. A later invocation enters the same recursive
normalizer and carries the full provenance chain.

This rule avoids order-dependent behavior where a partially interpreted outer
macro mutates the global macro environment while its own children are still
being expanded.

### 5.7 Hygiene and names

Inside-out expansion must preserve lexical hygiene:

- generated temporary names use the existing fresh-name mechanism;
- user names captured by a macro are distinct from generated names;
- a `Named` lifted module name is deterministic and collision-checked;
- `Fresh` names are stable for one compilation and do not depend on traversal
  order outside the specified recursive order;
- imports and prelude bindings are resolved in the generated module's stated
  scope, not in whichever macro happened to run last.

### 5.8 Required expansion tests

The expansion engine must have focused tests for:

1. `outer(inner(value))` expanding inner first;
2. a macro-generated invocation being expanded to a fixed point;
3. nested invocations in a function body and a callback body;
4. quoted syntax remaining unexpanded;
5. delayed callback syntax expanding after `lift module` establishes context;
6. direct and indirect recursive macro cycles;
7. generated-node and source-node provenance in a nested failure;
8. hygiene under two nested macros that each bind the same temporary name;
9. duplicate lifted module names from different expansion branches;
10. expansion-budget diagnostics with the complete invocation chain.

## 6. `behaviour`, `callback`, and `lift module`

### 6.1 Closed behavior vocabulary

The behavior kind is a closed Cure value:

~~~cure
type OTPBehaviour = GenStatem | GenServer | Supervisor | Application
~~~

The implementation must validate callback names and arities against the
selected behavior. Unknown callbacks are errors. An accepted callback name
must not become an arbitrary export merely because a macro supplied it.

The initial callback vocabulary is:

~~~text
GenStatem:  callback_mode/0, init/1, handle_event/4
GenServer:  init/1, handle_call/3, handle_cast/2, handle_info/2,
            terminate/2, code_change/3
Supervisor: init/1
Application: start/2, stop/1, start_phase/3
~~~

Optional callbacks remain explicit optional declarations in the closed
vocabulary. Their absence and presence must both be validated.

### 6.2 Callback declarations

A callback declaration contains a name, parameter patterns, body syntax, and
the behavior context established by the containing lifted module. Its body is
ordinary Cure code after recursive expansion.

Conceptually:

~~~cure
callback handle_info(message, state) -> body
~~~

The callback declaration is not an immediate Erlang function form. It is a
closed compile-time declaration that the normal elaborator turns into a Core
function with the correct behavior callback type.

### 6.3 Quoted modules

`lift module` produces a compile-time `QuotedModule` value with at least:

~~~text
QuotedModule {
  module_name,
  behaviour,
  callbacks,
  ordinary_declarations,
  imports,
  source_provenance
}
~~~

The value is collected during compilation. It is not a runtime term and is
not allowed to escape into a compiled program as a way of executing compiler
operations.

The module validator must check:

- module name syntax and collision policy;
- one behavior declaration;
- required callback presence;
- callback name and arity;
- callback result shape;
- ordinary declaration names and exports;
- imports and generated-module dependencies;
- no remaining macro invocation in any body.

### 6.4 Multi-module emission

The compiler must collect the enclosing module plus every `QuotedModule` in a
single compilation result. It must then:

1. validate all module names and dependencies;
2. elaborate each module through the common path;
3. compile all validated forms without loading them;
4. write/load them through the existing shared writer once;
5. report all generated modules and their source provenance.

The exact topological ordering depends on the BEAM writer and dependency
model, but order must be deterministic and duplicate names must be rejected
before code loading begins.

## 7. The `beam_ops` macro

### 7.1 Role

`beam_ops` is a standard-library macro layered over the checked BEAM algebra.
It exists to make common process operations concise inside generated callbacks
and process declarations. It is not a second compiler for OTP objects.

Its expansion must produce ordinary calls to `Std.Otp` and ordinary effect
sequencing. It may produce closed algebra declarations where an operation
needs a compile-time message or reply code, but it must not directly emit raw
BEAM forms.

### 7.2 Operation vocabulary

The initial closed vocabulary should cover the minimum needed by the four
macros:

~~~text
self
send / tell
call
cast
spawn / spawn_link
start_link
stop
send_after / cancel_timer
monitor / demonitor
link / unlink
~~~

The syntax should use typed categories rather than a free-form operation name
and argument list. A schematic shape is:

~~~cure
beam_ops
  let pid = self()
  send pid message
  pure Unit
~~~

The final surface spelling is subject to the existing parser conventions, but
each operation must map to one closed algebra constructor or one ordinary
typed wrapper. Unknown operations are parse or validation errors.

### 7.3 Expansion requirements

`beam_ops` must:

- expand recursively inside its own operation arguments;
- preserve source order and effect order;
- infer or validate the current process context;
- reject a message not accepted by the target handle;
- reject a reply consumed at the wrong type;
- preserve the `Effect(T)` result;
- produce ordinary Cure AST before elaboration;
- work in user functions and generated callbacks identically;
- emit no behavior-specific marker.

### 7.4 Callback-specific operations

Some operations are valid only in a callback context. For example, a
`GenServer` callback may return a callback result containing a new state and
actions, while an application `start/2` callback returns a supervision-tree
result.

The operation macro must express these distinctions through the context and
result types. It must not accept every operation in every callback and defer
failure to the BEAM runtime.

### 7.5 Raw operations remain a boundary

If a future operation cannot be expressed by the checked algebra, the correct
sequence is:

1. specify its honest raw signature;
2. add a checked typed wrapper or closed algebra constructor;
3. add lowering and negative tests;
4. expose it through `beam_ops` only after those checks exist.

Adding a raw operation directly to `beam_ops` is explicitly out of scope.

## 8. The four macros

### 8.1 `actor`

`actor.cure` defines `actor` as a macro that:

- derives the actor message code from its message handlers;
- creates a `QuotedModule` named by the existing actor naming convention;
- declares `GenServer` behavior;
- emits `init/1`, message handling, and termination callbacks;
- emits ordinary `start_link` and typed send/call helpers;
- uses `beam_ops` for process operations in bodies;
- recursively expands nested operation macros before callback elaboration.

The actor body must not be interpreted by an Elixir callback compiler or
passed through a source-string template.

### 8.2 `fsm`

`fsm.cure` defines `fsm` as a macro over the algebra and closed behavior
declarations. It must support both existing modes:

- transition-table mode, using `GenStatem` callbacks and generated dispatch;
- callback mode, using the checked `GenServer` callback surface where that is
  the established compatibility behavior.

The mode choice must be a transparent macro decision represented in generated
syntax. Transition tables, allowed-event queries, state accessors, and
convenience functions are ordinary declarations in the lifted module.

The transition table and callback bodies must share the same derived message
and state information. They may not each assert an independent raw type.

### 8.3 `sup`

`supervisor.cure` defines `sup` as a declarative macro that:

- validates child declarations and restart metadata;
- creates a `Supervisor` lifted module;
- emits `init/1` with a checked child-spec structure;
- emits `start_link` as an ordinary typed function;
- uses the typed lifecycle algebra for child startup.

The child-spec vocabulary is closed. Strategy, intensity, period, restart,
shutdown, and child type must not be arbitrary terms accepted by a compiler
template.

### 8.4 `app`

`app.cure` defines `app` as a macro that:

- creates an `Application` lifted module;
- emits `start/2`, `stop/1`, and optional `start_phase/3` callbacks;
- represents startup and shutdown bodies as ordinary expanded Cure code;
- uses the supervision/application algebra for returned child trees and
  lifecycle results;
- validates application metadata and callback presence before emission.

### 8.5 Shared behavior

Anything shared by these macros must be transparent and live in one of:

- checked standard-library definitions;
- the generic macro expansion/lift-module implementation;
- the closed behavior/callback data definitions;
- the typed BEAM algebra.

It must not be hidden in a new four-way compiler helper that recreates the
old class hierarchy under a different name.

## 9. Compiler pipeline changes

### 9.1 Required pipeline

The final pipeline is:

~~~text
source
  -> parse
  -> recursive inside-out macro expansion to fixed point
  -> collect ordinary declarations and QuotedModules
  -> elaborate/type-check all generated syntax
  -> validate behavior, callback, and module contracts
  -> lower Core to BEAM forms
  -> compile/write/load through the common writer
~~~

No phase after recursive expansion may need to know that a declaration came
from `actor`, `fsm`, `sup`, or `app`, except for provenance and
diagnostics.

### 9.2 Existing compiler paths to remove

Once the replacement is proven, remove:

- the `__otp_container` syntax marker and parser fallback;
- the compiler dispatch branch dedicated to container markers;
- `ContainerMacro` as the implementation of OTP semantics;
- direct source-string compilation for actor, callback-mode fsm, sup, and app;
- direct code-server loading in those implementations;
- behavior-specific form constructors that bypass ordinary elaboration;
- any compiler-owned class/type required solely by the old four forms.

The shared BEAM form writer remains. The generic quoted-module collector and
emitter are infrastructure, not a bespoke implementation of any one OTP
object.

### 9.3 Parser and lexer policy

The parser must parse macro-produced declarations using the same syntax path
as source declarations. `sup` and `app` currently have contextual/soft
keyword behavior; `actor` and `fsm` may require lexer treatment if their
literal spellings remain hard keywords.

Keyword demotion is a separate compatibility change and needs its own focused
tests. It must not be hidden in the macro implementation or worked around by
generating source strings.

## 10. Current implementation gaps

The implementation plan must explicitly close these gaps rather than treating
the existing scaffolding as complete:

1. **`lift module` is parser scaffolding only.** The parsed AST is not yet a
   complete elaborator input or a multi-module compiler result.
2. **`behaviour` and `callback` lack a complete checked pipeline.** The
   closed vocabulary and pure Elixir validation helpers do not yet establish
   an ambient callback context in ordinary Cure elaboration.
3. **`QuotedModule` has no complete common emitter.** Generated modules need
   validation, dependency collection, deterministic naming, form generation,
   and one shared write/load step.
4. **`OtpMacro` is not the standard-library implementation.** Its pure
   Elixir scaffolding may support bootstrapping and tests, but it must not be
   the long-term semantic home of the four public macros.
5. **The opaque `__otp_container` path remains.** It must be deleted after the
   transparent path reaches parity.
6. **The BEAM algebra is incomplete.** Existing raw and typed modules cover
   only part of the operation family; lifecycle, supervision, application,
   timer, link, and process-creation paths need checked signatures and
   lowering.
7. **`effect_op` is not a shortcut.** The current effect operation table is
   intentionally empty. The first algebra implementation should use the
   existing effect-typed raw externs and typed wrappers unless a separate
   operation-table design is approved.
8. **Nested callback bodies need context-aware expansion.** A body containing
   `beam_ops` cannot be expanded as a raw parser fallback or only after code
   generation.
9. **Tier 3 compile-time execution is incomplete.** If macro interpretation
   needs computed declarations, it must use the specified typed execution
   path and preserve provenance; arbitrary compile-time evaluation is not an
   escape hatch.
10. **Module imports and names need integration.** Generated modules must
    resolve stdlib imports, avoid collisions, and preserve deterministic
    names across repeated compilation.
11. **The lexer has a hard-keyword obstacle.** Literal `actor` and `fsm`
    replacement may require demotion or an explicitly justified fresh syntax
    while compatibility tests are added.
12. **Runtime parity is not proven by unit expansion tests.** Generic Unix and
    AtomVM execution must exercise generated modules and cross-module calls.
13. **Direct effectful case motives are incomplete.** The current kernel
    accepts `Effect(T)` everywhere else required by the effect design, but its
    case-motive result classifier does not recognize a direct `Effect(T)` value
    as a type. Consequently a `match` whose branches perform effects fails with
    `:bad_motive`; a transparent source-level `typealias` to `Effect(T)` makes
    the same checked term pass, but that is only a compatibility bridge and
    does not close the kernel completeness gap. The macro work must not replace
    this with an opaque runner or compiler special case. This remains open
    under the standing zero-TCB-delta rule until an approved language-level
    solution exists.

Each gap is a tracked implementation item. No gap may be silently converted
into a compiler special case.

## 11. Implementation phases and commits

Each phase is independently testable and must be committed with a descriptive
message before the next phase starts.

### Phase 1: establish the BEAM algebra

Deliver:

- raw boundary inventory and honest signatures;
- typed handle/message-code foundation;
- effect-typed wrappers for the minimum operation family;
- code-index erasure checks;
- negative type tests for wrong messages and replies;
- direct lowering tests for effect order.

Suggested commit message:

`feat(std): establish the checked BEAM process algebra over raw OTP externs`

### Phase 2: implement transparent recursive expansion

Deliver:

- AST-returning macro interpretation;
- recursive inside-out fixed-point expansion;
- delayed callback-slot context handling;
- cycle detection, expansion budget, hygiene, and provenance;
- parsed and validated `behaviour`, `callback`, and `lift module` forms;
- quoted-module collection without code-server effects.

Suggested commit message:

`feat(compiler): add transparent inside-out macro expansion and lifted modules`

### Phase 3: implement `beam_ops`

Deliver:

- standard-library `beam_ops` definition;
- closed operation vocabulary;
- expansion to ordinary typed algebra calls;
- callback-context validation;
- tests proving nested operation macros expand before callback elaboration.

Suggested commit message:

`feat(std): define beam_ops over the checked process algebra`

### Phase 4: replace the four OTP forms

Deliver:

- `actor.cure`, `fsm.cure`, `supervisor.cure`, and `app.cure` definitions;
- compatibility behavior for existing syntax and generated helper exports;
- nested `beam_ops` in all callback/body positions;
- transparent `QuotedModule` output for all four forms;
- parity tests against existing behavior.

Suggested commit message:

`feat(std): replace actor fsm supervisor and application compilers with macros`

### Phase 5: delete the old implementation and prove end to end

Deliver:

- removal of marker and bespoke compiler dispatch;
- removal of source-string and direct-load paths;
- no remaining compiler-owned OTP object classes;
- Unix runtime tests;
- AtomVM generic-unix and target-relevant tests;
- full test suite and formatted Elixir sources.

Suggested commit message:

`refactor(compiler): remove bespoke OTP object compilation after macro parity`

If a phase needs a corrective follow-up, the follow-up is a separate commit
with the failure and correction named explicitly. Do not combine unrelated
phases into one commit.

## 12. Verification gates

### 12.1 Expansion and transparency

Add tests that assert:

- no public OTP macro expansion contains `__otp_container`;
- no public OTP macro expansion returns raw Erlang forms;
- no public OTP macro expansion calls `Code.compile_string` or code loading;
- nested macros reach a fixed point before elaboration;
- the same expansion result is obtained on repeated compilation;
- source spans and expansion chains survive nested errors.

### 12.2 Algebra typing

Add positive and negative tests for:

- sending every legal constructor;
- rejecting an illegal tag;
- rejecting an accepted tag with an illegal payload;
- matching request and reply codes for `call`;
- rejecting operations in the wrong callback context;
- preserving the effect result through nested binds;
- erasing message-code indices from emitted runtime values.

### 12.3 Lifted module validation

Add tests for:

- required and optional callbacks for each behavior;
- wrong callback name and arity;
- missing behavior declaration;
- duplicate behavior declaration;
- duplicate generated module name;
- generated module import resolution;
- deterministic `Named` and `Fresh` names;
- multiple lifted modules emitted in one compilation;
- cross-module calls and startup order.

### 12.4 Recursive composition

The minimum golden expansion matrix is:

~~~text
beam_ops inside actor callback
beam_ops inside fsm transition callback
beam_ops inside supervisor child declaration/body
beam_ops inside application start/stop/phase callback
actor/fsm/sup/app nested in another transparent macro
macro-generated lift module containing macro-generated callbacks
~~~

Every case must show the normalized AST or an equivalent stable structural
assertion. Tests must not only assert that compilation succeeds; they must
prove that the inner macro was expanded before the outer declaration was
validated.

### 12.5 Runtime and compatibility

Run:

- focused compiler and stdlib tests after each phase;
- the existing OTP/container compatibility tests;
- generic Unix runtime tests for all four generated object types;
- AtomVM generic-unix proof tests and any available target tests;
- the full `mix test` gate;
- Antigen shape coverage;
- `mix format --check-formatted` after Elixir changes.

The final phase must also use repository searches to prove removal:

~~~text
rg "__otp_container|ContainerMacro|Code.compile_string|load_binary" lib test
~~~

Any remaining match must be justified as generic infrastructure or a raw
foreign-boundary test. A match in an OTP macro implementation fails the gate.

## 13. Non-goals and rejected shortcuts

This work does not:

- add a general arbitrary BEAM form emission API;
- add a runtime `EffectM` interpreter;
- make `Any` a public top type or subtyping escape;
- allow macros to mutate the code server;
- preserve bespoke compiler classes for compatibility;
- expand quoted syntax accidentally;
- defer nested macro expansion until after type checking;
- accept a behavior callback because a generated Elixir module happens to
  compile;
- claim full session-typed state-transition guarantees before the deferred
  effect/session work is implemented.

The first algebra floor may be conservative. It is better to reject an
operation whose checked type is not available than to make the transparent
macro path opaque or unsound.

## 14. Completion criteria

This specification is complete in implementation terms only when all of the
following are true:

1. the typed BEAM algebra is defined in standard-library code over a sealed,
   honest raw boundary;
2. `Effect(T)` sequencing and direct lowering remain correct;
3. macro interpretation recursively expands from the inside out to a fixed
   point, including generated syntax and delayed callback bodies;
4. nested expansion has cycle detection, budget enforcement, hygiene, and
   provenance;
5. `behaviour`, `callback`, and `lift module` are checked and emitted by
   the common pipeline;
6. `beam_ops` is a standard-library macro over the algebra;
7. `actor`, `fsm`, `sup`, and `app` are defined in their respective Cure
   files and use `beam_ops` rather than an opaque container call;
8. all four preserve their supported existing behavior and tests;
9. new tests cover legal/illegal algebra use, nested expansion, callback
   context, module collection, and runtime execution;
10. the old marker and bespoke OTP compiler paths are removed;
11. Unix and AtomVM end-to-end tests pass;
12. the full repository test and formatting gates pass;
13. no task or implementation gap listed in §10 remains open.

Until every criterion is met, the macro replacement is work in progress and
must not be described as complete.

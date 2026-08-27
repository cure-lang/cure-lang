# Cure Ownership and Unique Types

**Status:** design specification; deferred until after the direct-style algebraic-effects work.

**Dependency:** [Cure Direct-Style Computation System](../effects/README.md).

## 1. Purpose

Cure needs a static way to describe resources for which there must be one live
owner, even when the resource's operations are effectful. Examples include
files, sockets, device buffers, DMA regions, raw inboxes, transaction handles,
and process capabilities.

This is an ownership/aliasing property. It is not the same property as linear
or affine use-counting:

```text
usage:     unrestricted | affine | linear
ownership: shared | unique
```

The ownership axis is deliberately deferred until after algebraic effects and
effect rows are implemented. Ownership transfer, borrowing, and resource
finalization depend on computation typing and effect sequencing.

## 2. Terminology

An **owner** is the statically-authorized reference through which a resource's
exclusive operations may be performed.

A **unique value** has at most one live owner. The owner may use it repeatedly
when the operation preserves ownership.

A **shared value** may have any number of aliases. Subjects and ordinary Pids
are shared by design.

A **borrow** is a temporary view derived from a unique owner. A borrow cannot
outlive the owner operation and cannot be stored or sent unless its type says
that this is safe.

A **transfer** moves ownership from one binding or process to another. After a
successful transfer, the sender's ownership is unusable.

## 3. User-facing syntax

The primary binder syntax is:

```cure
fn write(@unique file: File(Open), bytes: Bytes)
  -> File(Open) ! FileWrite =
  File.write(file, bytes)
```

`@unique` is an ownership qualifier, not a new source-level type constructor.
The type remains `File(Open)`.

The existing usage qualifiers remain independent:

```cure
fn close(@linear file: File(Open)) -> File(Closed) ! FileWrite
fn cancel(@affine monitor: Monitor(Message)) -> Unit ! Otp.Monitor
fn inspect(@unique file: File(Open)) -> FileInfo ! FileRead
```

`@linear` means the binding is consumed exactly once. `@unique` means no alias
to the owned resource may exist. A unique binding may be used repeatedly by an
operation that preserves ownership:

```cure
fn write_header(@unique file: File(Open)) -> File(Open) ! FileWrite =
  let file = File.write(file, header)
  File.write(file, metadata)
```

The language must not silently interpret `@unique` as `@linear`.

## 4. Transfer

Ownership-transfer operations consume the source owner and return or send the
new owner:

```cure
fn hand_off(@unique socket: Socket(Open)) -> Unit ! Otp.Send =
  Worker.send(socket)
```

After `Worker.send(socket)`, using `socket` again is an elaboration error.

An explicit return can transfer ownership back:

```cure
fn reopen(@unique file: File(Closed)) -> File(Open) ! FileRead =
  File.open(file)
```

The compiler must know, from the callee signature, whether an argument is:

- borrowed temporarily;
- consumed and not returned;
- consumed and returned under a new state;
- copied as a shared value.

There is no implicit ownership duplication.

## 5. Borrowing

Borrowing is a later extension of the ownership design, but the core model
must reserve the distinction:

```cure
fn read_metadata(@borrow file: File(Open)) -> Metadata ! FileRead
```

A borrow:

- cannot outlive the owner scope;
- cannot be stored in unrestricted data;
- cannot be sent to another process by default;
- cannot be used to create a second unique owner;
- may be used repeatedly while the borrow is live if the borrow is read-only.

Mutable or effectful borrows require an explicit rule. The first implementation
may support transfer without general borrowing, but it must not design the
type representation in a way that precludes borrows.

## 6. Shared values

Not every capability is unique. These remain shared:

```cure
Subject(Message)
Pid(Message)
Name(Message)
```

Subjects may be copied, stored, embedded in messages, and sent to other
processes. Their operations are governed by effect rows and protocol types,
not by uniqueness.

The following are likely unique or linear resources, subject to individual API
decisions:

- raw `Inbox(Message)` ownership;
- open files and sockets;
- DMA/device buffers;
- transaction/session handles;
- reply capabilities;
- process-start capabilities;
- mutable foreign resources.

`Reply(A)` remains primarily linear: exactly one reply is required. It need not
also be unique unless an API specifically permits persistent reply ownership.

## 7. Interaction with effects

Ownership does not replace effect rows.

```cure
fn send(@unique reply: Reply(A), value: A) -> Unit ! Otp.Send
```

The effect row says the function may send. The usage qualifier says the reply
capability must be consumed. Ownership says whether aliases to a resource may
exist.

Effectful operations must be checked before ownership is discharged. A failed
operation must have a specified ownership result:

```text
success: transfer completed; source owner is consumed
failure: source owner is preserved, or ownership moves to an explicit recovery
         state; it must never disappear silently
```

This is one reason ownership implementation follows the algebraic-effects
system.

## 8. Processes and message passing

Sending a unique value through an unrestricted message channel is rejected by
default:

```cure
type Message =
  GiveSocket(@unique Socket(Open))
```

An explicitly ownership-carrying message may transfer the resource to the
receiver. The sender cannot use it after constructing/sending the message.

The compiler must distinguish:

- copying a shared subject into a message;
- transferring a unique capability into a message;
- attempting to send a borrowed value;
- sending a linear reply capability under an allowed ownership contract.

Spawn and supervisor specifications must preserve ownership contracts for
child capabilities in addition to their latent effect rows.

## 9. Foreign functions

Foreign resources require explicit ownership metadata. A foreign declaration
must specify creation, transfer, consumption, finalization, and failure
behavior:

```cure
@extern(:driver, :open, 1)
@creates_unique File(Open)
fn raw_open(path: Path) -> File(Open) ! Foreign(driver)
```

Unknown externs may not return a unique resource without an ownership
annotation or an explicit unsafe assumption.

An extern must not fabricate a proof that a unique resource was consumed.

## 10. Core representation

Ownership belongs in the elaboration/type-checking layer and in the final Core
binder metadata. It must not be represented as an ordinary runtime wrapper.

The final binder representation should retain separate fields for:

```text
usage:     0 | affine | linear | unrestricted
ownership: shared | unique | borrowed
```

The exact names may change, but the axes must remain distinct. Conversion and
kernel checking must compare ownership annotations wherever binder identity or
resource safety depends on them.

Unique values may erase to ordinary BEAM terms; uniqueness is a static
property, not a runtime tag. Runtime wrappers are permitted only when an FFI or
debugging boundary explicitly requires them.

## 11. Diagnostics

The implementation should provide dedicated errors:

```text
UNIQUE_DUPLICATED
  cannot copy unique value `file`

UNIQUE_ALIAS
  a second live owner of `socket` would be created here

UNIQUE_USE_AFTER_TRANSFER
  `socket` was transferred and cannot be used again

UNIQUE_BORROW_ESCAPES
  borrowed value `file_view` escapes its owner scope

UNIQUE_SEND
  unique value cannot cross this message boundary without an ownership transfer

UNIQUE_FOREIGN_CONTRACT
  foreign function does not declare how ownership of `resource` changes
```

Diagnostics should explain whether the violation concerns usage count,
aliasing, borrowing, or transfer. These must not all collapse into a generic
linear-use error.

## 12. Implementation order

Ownership is deferred until the direct-style effect system is complete.

The later implementation order is:

1. Define the ownership vocabulary and binder metadata.
2. Add unique/borrowed/transfer checking for local bindings.
3. Add state-transition APIs for resources (`Open -> Closed`, etc.).
4. Add ownership-aware message transfer and process boundaries.
5. Add foreign ownership contracts.
6. Integrate ownership with linear/affine checking.
7. Add erasure and BEAM/AtomVM preservation gates.
8. Add soundness, negative, and concurrency tests.

General borrow checking, shared mutable borrows, and multi-shot ownership
transfer are not part of the first slice.

## 13. Non-goals

This specification does not introduce:

- a global `World` token;
- runtime uniqueness checks for ordinary values;
- uniqueness for `Subject` or ordinary `Pid` values;
- a replacement for effect rows;
- automatic inference that every FFI resource is unique;
- unrestricted multi-shot borrowing;
- a claim that uniqueness proves operation ordering or exactly-once behavior;
- a requirement that all unique values be linear.

## 14. Acceptance criteria

The ownership system is complete when:

1. Unique and shared resources are statically distinguishable.
2. Ownership transfer consumes the source owner.
3. Unique aliases cannot be created or stored without an explicit contract.
4. Borrowed values cannot escape their borrow scope.
5. Message passing distinguishes copying from ownership transfer.
6. Linear and affine usage remain separate from uniqueness.
7. Effect rows remain separate from ownership and usage.
8. Foreign resources declare ownership transitions.
9. Actor, supervisor, and spawn APIs preserve ownership contracts.
10. Erasure removes ownership metadata without changing runtime resource identity.
11. The kernel never accepts an ownership-invalid proof-relevant term.

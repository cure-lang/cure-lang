# Ownership & Unique Types — Master Spec

**Date:** 2026-07-21

Scope: the condensed authority for Cure's ownership axis — unique vs shared values, usage qualifiers, borrowing, ownership transfer (including across process boundaries), foreign-resource ownership contracts, and Core-layer representation. Status: **design specification, deferred** until after the direct-style algebraic-effects work (dependency: `../2026-07-20-algebraic-effects.md`), because transfer, borrowing, and finalization depend on computation typing and effect sequencing.

## Purpose

A static way to say a resource has exactly one live owner even when its operations are effectful: files, sockets, device/DMA buffers, raw inboxes, transaction/session handles, reply and process-start capabilities, mutable foreign resources.

## Core distinction (locked): ownership ≠ usage

Two independent axes; they must never collapse:

```text
usage:     unrestricted | affine | linear   (how many times a binding is used)
ownership: shared | unique                  (whether aliases may exist)
```

- `@linear` = consumed exactly once. `@unique` = no alias to the owned resource may exist; a unique binding **may be used repeatedly** by ownership-preserving operations.
- **Non-negotiable:** the language must not silently interpret `@unique` as `@linear`, and not all unique values are linear.
- Ownership also does not replace **effect rows** — three separate concerns (effect row: may send; usage: reply must be consumed; ownership: no aliases).

## Terminology

- **Owner** — the statically-authorized reference through which a resource's exclusive operations may be performed.
- **Unique value** — at most one live owner; owner may use it repeatedly under ownership-preserving ops.
- **Shared value** — any number of aliases; Subjects and ordinary Pids are shared by design.
- **Borrow** — temporary view derived from a unique owner; cannot outlive the owner operation, cannot be stored or sent unless its type says so.
- **Transfer** — moves ownership between bindings/processes; the sender's ownership becomes unusable afterward.

## Surface syntax

`@unique` is an **ownership qualifier on a binder**, not a new type constructor — the type stays e.g. `File(Open)`. Usage qualifiers (`@linear`, `@affine`) remain independent.

```cure
fn write(@unique file: File(Open), bytes: Bytes) -> File(Open) ! FileWrite =
  File.write(file, bytes)
```

## Transfer rules

- Transfer operations consume the source owner and return or send the new owner; using the source afterward is an **elaboration error**.
- The compiler must know from the **callee signature** whether an argument is: borrowed temporarily / consumed and not returned / consumed and returned under a new state / copied as shared. **No implicit ownership duplication.**
- Failure semantics (locked, and the reason ownership follows effects): effectful ops are checked before ownership is discharged. On success the source owner is consumed; on failure the source owner is preserved or moves to an explicit recovery state — ownership **never disappears silently**.

## Borrowing

Later extension (`@borrow`), but the type representation must not preclude it. A borrow: cannot outlive the owner scope; cannot be stored in unrestricted data; cannot be sent to another process by default; cannot create a second unique owner; may be used repeatedly while live if read-only. Mutable/effectful borrows require an explicit rule. First slice may ship transfer without general borrowing.

## Shared vs unique inventory

- **Shared by design:** `Subject(Message)`, `Pid(Message)`, `Name(Message)` — copyable, storable, sendable; governed by effect rows and protocol types, not uniqueness.
- **Likely unique/linear (per-API decision):** raw `Inbox(Message)`, open files/sockets, DMA/device buffers, transaction/session handles, reply capabilities, process-start capabilities, mutable foreign resources.
- `Reply(A)` remains primarily **linear** (exactly one reply required); it need not also be unique unless an API permits persistent reply ownership.

## Processes and message passing

Sending a unique value through an unrestricted message channel is **rejected by default**. An explicitly ownership-carrying message (e.g. `GiveSocket(@unique Socket(Open))`) transfers to the receiver; the sender loses use at construction/send. The compiler must distinguish: copying a shared subject into a message / transferring a unique capability / attempting to send a borrow / sending a linear reply capability under an allowed contract. Spawn and supervisor specs must preserve ownership contracts for child capabilities in addition to latent effect rows.

## Foreign functions

Foreign resources require explicit ownership metadata (creation, transfer, consumption, finalization, failure behavior), e.g. `@creates_unique File(Open)` on an `@extern`. Unknown externs may **not** return a unique resource without an ownership annotation or an explicit unsafe assumption. An extern must not fabricate a proof that a unique resource was consumed.

## Core representation (locked)

- Ownership lives in the elaboration/type-checking layer and in final Core **binder metadata** — never as an ordinary runtime wrapper.
- Binders retain **separate fields**: `usage: 0 | affine | linear | unrestricted` and `ownership: shared | unique | borrowed`. Names may change; the axes must stay distinct.
- Conversion and kernel checking compare ownership annotations wherever binder identity or resource safety depends on them.
- Unique values **erase to ordinary BEAM terms** — uniqueness is static, not a runtime tag. Runtime wrappers only at an FFI/debug boundary that explicitly requires them.

## Diagnostics

Dedicated errors — must **not** collapse into a generic linear-use error; each explains whether the violation is usage count, aliasing, borrowing, or transfer: `UNIQUE_DUPLICATED`, `UNIQUE_ALIAS`, `UNIQUE_USE_AFTER_TRANSFER`, `UNIQUE_BORROW_ESCAPES`, `UNIQUE_SEND`, `UNIQUE_FOREIGN_CONTRACT`.

## Implementation order (post-effects)

1. Ownership vocabulary + binder metadata. 2. Unique/borrowed/transfer checking for local bindings. 3. Resource state-transition APIs (`Open -> Closed`). 4. Ownership-aware message transfer and process boundaries. 5. Foreign ownership contracts. 6. Integration with linear/affine checking. 7. Erasure + BEAM/AtomVM preservation gates. 8. Soundness/negative/concurrency tests.

First slice excludes: general borrow checking, shared mutable borrows, multi-shot ownership transfer.

## Non-goals

No global `World` token; no runtime uniqueness checks for ordinary values; no uniqueness for `Subject`/ordinary `Pid`; not a replacement for effect rows; no automatic "every FFI resource is unique" inference; no unrestricted multi-shot borrowing; no claim that uniqueness proves ordering or exactly-once behavior; no requirement that all unique values be linear.

## Acceptance criteria

1. Unique vs shared statically distinguishable. 2. Transfer consumes the source owner. 3. No unique aliases created/stored without explicit contract. 4. Borrows cannot escape their scope. 5. Message passing distinguishes copy vs transfer. 6. Linear/affine usage stays separate from uniqueness. 7. Effect rows stay separate from both. 8. Foreign resources declare ownership transitions. 9. Actor/supervisor/spawn APIs preserve ownership contracts. 10. Erasure removes ownership metadata without changing runtime resource identity. 11. The kernel never accepts an ownership-invalid proof-relevant term.

## Source specs

- `2026-07-20-ownership-and-unique-types-design.md` — full design for the ownership/uniqueness axis: qualifiers, transfer, borrowing, process boundaries, FFI contracts, Core representation, diagnostics, phased plan.

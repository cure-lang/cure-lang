# Macro Composition — Stacked Languages, Composed Proofs

**Date:** 2026-07-08
**Status:** design (operator insight, same day). Child of
[`2026-07-08-macro-facility-design.md`](2026-07-08-macro-facility-design.md),
extending its §7 (scoping & composition) into a full mechanism. Consumes the
`check` ladder ([`2026-07-08-check-macro-design.md`](2026-07-08-check-macro-design.md))
and the explainer architecture
([`2026-07-08-error-explainer-design.md`](2026-07-08-error-explainer-design.md)).

**The operator's insight (verbatim intent):** if users can stack DSLs inside
DSLs, the dependent types can stay abstracted away — with the proofs still
proved. This spec names why that works, what it already does accidentally,
and the two mechanisms that make it general: **theorem signatures** and
**parameterized categories**.

---

## 1. The closure property — why stacking hides types without losing proofs

The scary syntax of dependent types is the syntax of *human-stated
generality*: binders, quantifiers, explicit indices. Every macro trades
that generality for concreteness — indices flow from declarations, so they
are literals, so obligations discharge by computation (parent thesis §1).

The observation that makes stacking a *mechanism* rather than a trick:

> **Seam obligations are machine-authored on both sides.** When macro B is
> nested inside macro A, the proof obligations arising at the seam are
> between two elaborator-manufactured types. Machine-manufactured types keep
> their indices concrete. Therefore seam obligations live in exactly the
> fragment that discharges by computation — and the user-facing proof burden
> of dependent types, which only ever arises where a *human* wrote a type,
> never arises at all, because in a macro stack no human writes a type at
> any layer.

This is a closure property, not a coincidence: it holds for every pair of
conforming macros, at every nesting depth.

**Generality is recovered structurally.** A quantifier is just an outer
macro. "Stitch counts balance *for all sizes*" is a ∀ written as
`sizes S, M, L` and proved by enumeration over the declared index set.
"No single fault defeats the quorum" is a ∀ over fault domains written as
node/mount/bus declarations. The outer macro quantifies **by
declaration**; the user writes a universally quantified theorem and
experiences it as filling in a form.

## 2. Accidental composition — what the corpus already does

Three existing seams, hand-designed before this mechanism existed, share the
shape this spec generalizes:

- **`protocol` × `packet` → tag elision.** "At a deterministic step the wire
  needs no discriminator" is a theorem that exists *only at the seam* —
  neither macro can state it alone (protocol has the step-determinism,
  packet has the parse discipline). §8 reworks this as the canonical
  example.
- **`reef` × `fleet` → fail-safe under partition.** Quorum arithmetic (reef)
  plus vote-lives-at-the-actuator (fleet ownership rule 4) compose into a
  guarantee neither owns.
- **`units` × everything.** The degenerate case: a macro that exists
  almost entirely as *proof plumbing* — its exported carrier laws are what
  make other macros' arithmetic obligations well-formed.

What they share: an outer macro needed a **fact** the inner macro could
supply, and today that supply is implicit (rediscovered by computation) or
hand-wired (designed-in pairing). The generalization is to make the facts
explicit, typed, and resolvable.

## 3. Theorem signatures — `provides` / `requires`

A macro exports not just types but **named, kernel-checked facts**. Two
new member kinds in the `macro` container:

```cure
macro Packet
  ...
  provides roundtrip(p: $P) = parse(encode(p)) == Ok(p)
    proved by Packet.Proofs.roundtrip          # library Core term
  provides parse_total($P)
    proved by construction                      # totality certificate, per instantiation

macro Protocol
  ...
  requires Packet.roundtrip, Packet.parse_total
    for $msg:Packet.FieldDecl                   # facts demanded of embedded packets
```

- **Statement form:** a `provides` fact is stated as a `check`-style prop —
  Bool-valued, quantified only over the macro's declared parameters (`$P`
  ranges over the macro's own instantiations). Theorem signatures and
  check templates are **the same artifact**: a template *is* a fact, and its
  ladder rung decides what it may be used for (§3.1).
- **Witness forms:** `proved by construction` (static discharge at each
  instantiation — the elaborator re-derives it by computation for the
  user's concrete declaration); `proved by <name>` (a Core proof term
  shipped with the macro's library — the route for *inductive* facts like
  round-trip, proved once centrally per the check spec's honest boundary);
  `certificate` (elevated at instantiation via the check spec's SMT
  reconstruction pipeline; cached like any certificate).
- **Instantiation:** facts are families. `Packet.roundtrip` is instantiated
  per user `packet` declaration, exactly as check templates attach — same
  mechanism, promoted.
- **Resolution:** when an outer macro's `elab` hits an obligation matching
  a `requires`, the elaborator wires the embedded declaration's instantiated
  fact in — instance-style resolution where the instances are entire
  languages. The wiring is untrusted; the composed term is kernel-checked.
  **TCB delta: zero**, same argument as everything else.

### 3.1 The trust rule (load-bearing)

> **Only *proved-by-construction* and *proved (certificate)* rung facts may
> participate in typing. *Tested*-rung facts are advisory only — they may
> inform lints and reports, never discharge an obligation.**

This is the check ladder reused as a proof-trust policy, and it is what
keeps theorem signatures from becoming typeclass laws (promises the compiler
trusts because someone wrote them down). A fact that is merely tested
cannot make a program type-check. The honest boundary from the check spec
becomes a *feature*: inductive facts get proved once, centrally, by a
macro author or library — and the export is the proof.

## 4. Parameterized categories — indices flowing inward

The facility's typed non-terminals are today fixed categories
(`$payload:Packet.FieldDecl`). The general form parameterizes a category by
**outer-macro values**:

```cure
syntax ... $payload:Packet.FieldDecl(max_size: $transport.mtu) ...
```

The inner macro's grammar/elaboration now receives an index from the outer
macro's declarations — a fleet transport's MTU constrains the packet
grammar embedded in its edges; a protocol step's identity flows into the
frame layout; a board's bus width flows into a regmap. This is literally a
dependent type **between languages** — the inner category's type depends on
the outer macro's value — and only *macro authors* ever see it. Users
see: "your frame won't fit ESP-NOW."

Semantics: category parameters are ordinary values of the outer macro's
quoted-AST/derived types, threaded into the inner macro's `elab` as extra
arguments and available to its refinements. The facility's two-pass
resolution (§6 there) already sequences this: parameters are resolvable at
the signature pass because they come from declarations, not elaboration
results. Parameters that would require the *inner* elaboration's output to
compute (true circularity) are rejected with a facility-level error.

## 5. Seam obligations — the discharge protocol

At every seam, in order:

1. **Computation** — whnf/delta over the concrete indices (the closure
   property, §1; the common case).
2. **Fact resolution** — a `requires`-matched, trust-eligible `provides`
   fact (§3).
3. **Failure** — a **composition error**, charged to the macro authors,
   never surfaced as a goal. Extended hiding principle 3:

> A seam obligation that neither computes away nor resolves against an
> exported fact is a defect in the *composition*, not the user's program.
> The error names both macros, states the missing fact in both
> vocabularies, and tells the user to report it — the never-raw guarantee's
> seam case.

## 6. Seam explainers — bilingual by construction

Provenance already records expansion chains (explainer spec §2); a seam
failure carries both macros' provenance. Requirements:

- Seam explainers speak **both vocabularies in one message**:

  ```
  error[E27x]: this packet cannot ride this fleet edge
    Frame `SensorReport` is 312 bytes (packet: header 4 + payload 300 + crc 8);
    the sump→rim edge uses ESP-NOW (fleet: transport espnow), which caps
    frames at 250 bytes. Shrink the payload, split the report, or move the
    edge to udp(:lan).
  ```

- Resolution order stays innermost-wins, but a `requires`-declaring macro
  may register **seam explainers** keyed on (its macro, embedded macro,
  failure shape) — a third registration kind alongside own-failures and
  wraps.
- Error-code allocation: composition errors get their own registry block
  (ledger §11.6).

## 7. Composition templates — testing the seam

Macro pairs that intend to compose ship **composition templates** — check
templates keyed to the pair, exercising the seam on the user's actual
declarations:

```cure
templates for composition $p:Packet in Protocol
  prop framed_roundtrip(msg) = ...   # the elided-tag frame still round-trips
```

These run in `cure test` like any template, report on the ladder, and — per
§3.1 — the ones that reach the proved rungs *are* the facts future
compositions resolve against. The seam's tests and the seam's theorems are
one artifact at three confidence levels.

## 8. Worked seam — `protocol` × `packet` tag elision

The canonical example, reworked through the mechanism:

- **What protocol knows:** at a deterministic step, the local session type
  fixes the unique next message shape (its own static fact:
  `step_unique(s)` — proved by construction from the session grammar).
- **What packet provides:** `roundtrip(p)` (library proof) and
  `parse_total` (per-instantiation totality certificate).
- **The seam theorem:** *a frame at a deterministic step may omit its
  discriminator, and fidelity is preserved* — because `step_unique` selects
  the parser, `parse_total` guarantees it consumes the frame or fails
  cleanly, and `roundtrip` guarantees the sender's encoding is the thing
  parsed. The elaborator assembles this from the three facts; the kernel
  checks the assembly.
- **What the user sees:** nothing. Smaller frames on the wire, and one line
  in `cure protocol report`: `tag elision: 7 of 9 steps (saves 7 bytes/frame,
  proved)`. The proof's only public appearance is a bandwidth number — which
  is the whole thesis of this spec in one line.

## 9. The gradual-reveal ladder (pedagogy, free)

A stacked program is one artifact with a descent path: **blocks view →
macro text → the surface Cure it expands to → Core**. Every rung shows the
same program (facility round-trip guarantee), so curiosity has a staircase
instead of a cliff. The LSP hover gets the positive twin of explainers:
"what did this line prove?" answers in domain vocabulary — the discharged
obligations and consumed facts, e.g. hovering a `sink` shows "proved: no
feedback loop; relay never faster than 1Hz (hold_for)". Users descend
exactly as far as they care to; the types were never hidden, only
translated.

## 10. Risks & containment

- **Seam explosion (N macros → N² seams?)** — no: seams are demand-driven
  (only nestings that occur in programs), fact interfaces are added when a
  composition wants one, and the standing layering argument caps the damage
  of an untested composition at *rejected program or ugly error, never
  unsoundness* — the kernel re-checks every composed term.
- **Non-discharging seams** — handled by the §5 protocol; the defect class
  is bounded and reportable, like the explainer never-raw case.
- **Semantic mismatch that isn't type mismatch** — two macros with
  different models of the same quantity (pattern's cycle clock vs. flow's
  sample clock). These need **explicit adapter forms at the seam** — the
  precedent is synth's `a2k(window:)`/`k2a(slew:)` converters, whose
  mandatory parameters force the semantic decision into the open. Rule:
  when a seam needs an adapter, the adapter's parameters must make the
  lossy choice explicit; silent coercion between models is banned.
- **Elaboration cost of deep stacks** — staged, per-declaration, cacheable;
  facts instantiate once per declaration; certificates cache (check spec).
  No new mechanism needed; noted for the toolchain's incremental story.

## 11. Open decisions (ledger)

1. **Fact-statement language** — §3 uses check-prop syntax; confirm the
   exact fragment (quantification only over macro parameters; Bool-valued
   bodies; no nested facts in v1).
2. **Resolution mechanics** — matching `requires` to obligations: syntactic
   fact-name keying (recommended v1) vs. shape-directed search (later, if
   ever; search is where instance systems go to die).
3. **Fact versioning** — a macro upgrade that strengthens/weakens a
   provided fact vs. downstream macros compiled against the old statement;
   likely rides the facility's source-package answer (recompile), but state
   the compatibility rule.
4. **Parameterized-category typing** — the precise rule for which outer
   values are admissible parameters (declaration-derived only, per §4) and
   how they appear in the inner macro's quoted-AST types.
5. **Adapter-form convention** (§10) — a facility-level marker so seam
   adapters are recognizable/greppable, or purely per-macro idiom.
6. **Composition error-code block** — allocate (e.g. E270–E279) in the
   explainer registry's next pass.
7. **Recursive facts** — may a `provides` witness consume another macro's
   fact? (Almost certainly yes — the protocol×packet example already wants
   it — but confirm the acyclicity story with two-pass resolution.)
8. **LSP "what did this prove?"** — surface and scope of the hover (§9);
   belongs jointly to the toolchain and explainer specs.

## 12. Non-goals

- **No user-visible proof language.** This spec adds proof *plumbing*
  between macros; if it ever surfaces a goal to an end user, it has
  failed (§5).
- **No trusted laws.** Tested-rung facts never type (§3.1) — there is no
  "the author promises" tier, and there never will be.
- **No global inference across seams.** Facts resolve against explicit
  `requires` only; no whole-program search for whatever lemma might fit.
- **No cross-macro semantic unification.** Adapters make model differences
  explicit; the facility will not invent a universal clock, unit, or state
  model to paper over them.

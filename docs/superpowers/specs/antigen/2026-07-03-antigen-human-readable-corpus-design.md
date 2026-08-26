# Antigen human-readable corpus — design

**Status:** approved (design gate). Autopilot run on `autopilot/antigen-tier-b` (stays on this worktree per operator preference).

## 1. Motivation

Banked Antigen corpus records (`test/antigen/seeds.sexp`, runtime antibody files) are
today opaque: each term is `id::Base64(Serialize.encode(term))`, the `note` is
Base64, and a mutant's `fault` provenance map is buried inside the Base64
`scaffold`. The operator wants to **open the file and read/debug the terms by
hand**. This spec makes the load-bearing, human-facing parts of a record
readable on disk while preserving exact round-trip replay.

Scope (locked at the design gate): **terms (all Term pieces) + note + mutant
fault provenance** become readable. General (non-fault) scaffold content and the
dedup `key` stay Base64. Variables stay **positional de Bruijn** — no name
recovery.

## 2. On-disk format

A record is unchanged in shape: one line, tab-separated `field=value` pairs, led
by the `antigen-record` marker. Three fields change form:

### 2.1 `pieces` — tagged s-expressions

Today: `id::Base64(Serialize.encode(t))`, pieces joined by `;;`.
New: `id::(sexpr)` where `(sexpr)` is the tagged s-expression of the Term
(§3). Example (a conversion reject carrier, one line):

```
pieces=term::(ctor vcons (app (app (global plus) (ctor S (ctor Z))) (ctor Z)) (ctor Z) (ctor vnil))
```

The `;;` piece separator and `::` id/term separator are retained; neither
appears inside an s-expression (names are atoms; structure is parens/spaces).

### 2.2 `note` — plaintext

Today: `Base64(note)` or `-` for nil. New: the note verbatim, with a minimal
escaping so it cannot break the tab-separated / newline-terminated record:
percent-encode `%`→`%25`, tab→`%09`, newline→`%0A`, **applied in that order
(`%` first)** — encoding tab/newline before `%` would double-escape the `%`
those substitutions introduce (`%09`/`%0A` contain a literal `%`), corrupting
the round-trip. A single-pass scan (matching one of `%`/tab/newline per step,
never rescanning already-substituted output) is equally correct and avoids the
ordering question entirely; a naive sequence of independent whole-string
`String.replace/3` calls MUST run `%` first. `nil` still encodes as the bare
sentinel `-`; a genuine note equal to `"-"` is escaped to `%2D` so it never
collides with the sentinel (§6.1).

### 2.3 `fault` — readable provenance field (mutants only)

Today: the fault map rides inside the Base64 `scaffold`. New: a dedicated
`fault=` field holding a readable assoc-list s-expression, and the fault is
**removed from the Base64 scaffold**. The fault map is flat, but its values are
**not** uniformly atom/integer/nil/list-of-atom — verified against every
fault-producing call site (`Generators.Mutation.build/2`,
`Generators.Conversion.conv_reject/0`), the value universe is: atom / integer /
`nil` / list-of-atom / **integer-pair** / **nested Core-term**. The common case
(5 of 7 mutation operators, plus both conversion carriers) is atom/integer/nil,
e.g.:

```
fault=((depth 3) (expected_head Nat) (injected_head Vec) (kind head_swap) (scope nil) (witness head) (wrap_path (app_arg case_branch)))
```

(keys shown alphabetically — `depth, expected_head, injected_head, kind, scope, witness, wrap_path` — matching §3.4's "fixed key order (sorted by key atom)" rule, not the generator's map-literal insertion order.)

but two operators need the wider value grammar (§3.4 gives the exact printed
form for each):

- `:out_of_scope_var`'s `scope` is a 2-tuple of integers `{lo, hi}`
  (`Generators.Mutation.build(ctx, :out_of_scope_var)`), not `nil` or an atom.
- `:universe`'s `expected_head`/`injected_head` are Core-term tuples
  (`{:type, 0}` / `{:type, 1}`, `Generators.Mutation.build(ctx, :universe)`),
  not atom head-names — even though those same two keys hold atom head-names
  (`Nat`, `Vec`, `Z`, `S`, `Sigma`) for every other operator.

Non-mutant records have **no** `fault=` field.

### 2.4 Unchanged fields

`kind`, `assay`, `label`, `seed` (already plaintext), `key` (stays Base64 — it
is a dedup identity, not human-facing), and the **non-fault** `scaffold`
(stays Base64 `term_to_binary`, per scope).

## 3.0 Planning-stage revision — reuse `Cure.Core.Serialize` (SUPERSEDES the new-module design below)

**Discovery (Stage 2, grounded against source):** `Cure.Core.Serialize`
(`lib/cure/core/serialize.ex`) is *already* exactly this tagged s-expression
codec — byte-identical to §3.1's grammar. Live proof:

```
Serialize.encode({:ctor,:vcons,[{:app,{:app,{:global,:plus},{:ctor,:S,[{:ctor,:Z,[]}]}},{:ctor,:Z,[]}},{:ctor,:Z,[]},{:ctor,:vnil,[]}]})
#=> "(ctor vcons (app (app (global plus) (ctor S (ctor Z))) (ctor Z)) (ctor Z) (ctor vnil))"
Serialize.encode({:case, …, [{:T,0,…},{:F,1,{:var,0}}]})
#=> "(case … (branch T 0 …) (branch F 1 (var 0)))"
Serialize.encode({:type, 0}) #=> "(type 0)"
```

It is the design spec's **C2 re-validation format** and already has its own
round-trip test suite. Therefore:

- **No new `Antigen.SExpr` module.** Readable pieces are `Serialize.encode(t)`
  with the `Base64` wrapper removed; decode is `Serialize.decode/1`
  (`:: {:ok, term} | {:error, _}`). The prose grammar in §3.1–§3.3 below is
  retained only as documentation of the format Serialize implements.
- **Atom-safety (§3.3) is MOOT — not a regression.** `Serialize.decode` uses
  `String.to_atom` (verified: `serialize.ex:145/176/180/185/217`), i.e. it
  mints. But the corpus term path **already** goes through `Serialize.decode`
  today (`Corpus.decode_pieces` does `Serialize.decode(Base.decode64!(b64))`),
  so reusing it un-Base64'd preserves the *exact* current posture. The
  `:boom` / `@known_atoms` gap the Stage-1 review flagged only bites a *new*
  `to_existing_atom` decoder; reusing Serialize means it never arises. **No
  generator audit, no `@known_atoms` change, no `:boom` fix is needed.**
  - *Known limitation (documented, accepted):* a hand-edited corpus typo like
    `(global pluss)` mints `:pluss` rather than erroring — identical to today's
    behavior. A safe (`to_existing_atom`) decode is a trivial future follow-up
    if hand-edit typo-catching is ever wanted; out of scope here (YAGNI).
- **§7 test 1 (former round-trip)** is already covered by Serialize's own tests;
  this feature does not re-test it. The load-bearing new tests are the
  **corpus-record** round-trips (§7 test 3), the **fault codec** (§3.4), the
  **dual-read** (§7 test 4), and **migration** (§7 test 5). §7 test 2
  (atom-safety) is **removed** (moot).
- **§8 Files:** `lib/antigen/sexpr.ex` / `test/antigen/sexpr_test.exs` are **not
  created**. The only genuinely new codec is the small **fault** encoder/decoder
  (§3.4), which lives in `lib/antigen/corpus.ex` (private helpers) and reuses
  `Serialize.encode/decode` for any Core-term–valued fault entry.

Everything below (§3.1–§3.3) stands as the format's documentation; §3.4 (fault
codec) and §4–§9 are unaffected in intent, with "SExpr" read as "Serialize".

## 3. `Antigen.SExpr` — the term codec (SUPERSEDED by §3.0 — reuse `Serialize`)

New module `lib/antigen/sexpr.ex`. Pure, dependency-free (no backend, no
generator). Two public functions:

- `encode(Cure.Core.Term.t()) :: String.t()`
- `decode(String.t()) :: {:ok, Cure.Core.Term.t()} | {:error, term()}`

**Round-trip contract:** for every well-formed Core term `t`,
`decode(encode(t)) == {:ok, t}`. This is the load-bearing invariant (§7 test 1).

### 3.1 Grammar (tagged, one former per parenthesized node)

Leaves inside a node are either **integers** (de Bruijn index / universe level /
int literal) or **atom names** (constructor / global / data / primitive-op /
branch-constructor names). Every former keeps an explicit head tag so decode is
**menu-independent** and unambiguous:

| Former (Core tuple) | s-expression |
|---|---|
| `{:var, k}` | `(var k)` |
| `{:type, l}` | `(type l)` |
| `{:global, n}` | `(global n)` |
| `{:ctor, n, args}` | `(ctor n arg…)` |
| `{:data, n, params, indices}` | `(data n (param…) (index…))` |
| `{:app, f, a}` | `(app f a)` |
| `{:lam, dom, body}` | `(lam dom body)` |
| `{:pi, dom, cod}` | `(pi dom cod)` |
| `{:sigma, a, b}` | `(sigma a b)` |
| `{:pair, a, b}` | `(pair a b)` |
| `{:fst, p}` / `{:snd, p}` | `(fst p)` / `(snd p)` |
| `{:case, s, m, brs}` | `(case s m ((cname arity body)…))` |
| `{:eq, ty, a, b}` | `(eq ty a b)` |
| `{:refl, a}` | `(refl a)` |
| `{:rewrite, p, m, b}` | `(rewrite p m b)` |
| `{:prim, op, args}` | `(prim op (arg…))` |
| primitive literals | `(int_type)`, `(int_lit n)`, `(bool_type)`, `(bool_lit true\|false)`, `(float_type)`, `(float_lit f)` |

> The exact former set is **defined by `Cure.Core.Term`**, not by this table —
> Stage 2 (plan) must enumerate the live formers from the source of truth
> (`lib/cure/core/term.ex` and/or `Term.term?/1`'s accepted shapes) and cover
> **every** one, so an unlisted former is a plan bug, not a silent
> passthrough. `encode/1` MUST raise on an unrecognized shape (never emit a
> lossy or ambiguous form); `decode/1` MUST return `{:error, _}` on an
> unrecognized head (never mint a wrong term). Round-trip coverage (§7 test 1)
> enumerates the full former set from that source.

### 3.2 Printer

Recursive descent over the tuple. Names printed with `Atom.to_string/1`.
Integers printed decimally. Nested nodes separated by single spaces. No
pretty-print line-wrapping — a piece is one line (the record is one line).

### 3.3 Parser

Tokenizer → recursive-descent reader.

- **Tokens:** `(`, `)`, and atoms (maximal runs of non-paren, non-whitespace
  chars). Whitespace between tokens is insignificant.
- **Atom classification at a leaf:** an all-digits (optionally leading `-`)
  token is an integer; `true`/`false` inside a `bool_lit` are booleans;
  a float token (contains `.`) inside `float_lit` is a float; otherwise it is a
  **name**, interned with `String.to_existing_atom/1`.
- **Atom safety:** names use `String.to_existing_atom/1` — a name not already
  interned yields `{:error, {:unknown_atom, s}}` (rescued from the raised
  `ArgumentError`), never minting. This is safe **only if** every name a v1
  corpus can contain is already interned via `Challenge.@known_atoms` (the
  corpus decode path already force-interns them — see `Corpus.decode_record`).
  Decode MUST force `Challenge.__known_atoms__()` before parsing, exactly as
  `decode_record` does today.

  > **Verified gap, must be closed before Stage 4:** this safety property does
  > **not** currently hold. `Generators.Stub` (`lib/antigen/generators/stub.ex`)
  > produces a challenge whose term piece is `{:global, :boom}`, and
  > `test/antigen/runner_test.exs:44-49` round-trips exactly this challenge
  > through `Corpus.append`/`Runner.replay` (i.e. through `decode_record`).
  > `:boom` is absent from `@known_atoms`. Today this is harmless because
  > `Cure.Core.Serialize.decode/1` mints atoms via `String.to_atom/1` (no
  > existing-only constraint); switching pieces to `SExpr.decode`'s
  > `String.to_existing_atom/1` turns this into a live regression — that
  > `runner_test.exs` test would start failing to decode `(global boom)` in a
  > process that hasn't otherwise loaded `Generators.Stub`. Stage 2 must add
  > `:boom` to `@known_atoms` and re-audit **every** generator module (not just
  > the ones already reflected in the comment's "vertical" list) for atom
  > literals reachable inside a `Term` piece, since this class of gap was
  > silent under the old minting decoder and only becomes fatal under the new
  > safe decoder.
- **Errors:** unbalanced parens, unexpected EOF, a head tag not in §3.1, or an
  arity mismatch (e.g. `(app f)` with one child) → `{:error, reason}`. Never
  raise out of `decode/1`; wrap in `{:error, _}`.

### 3.4 Fault codec

The fault assoc-list (§2.3) reuses the same tokenizer. `encode_fault(map) ::
String.t()` emits `((key val)…)` with a **fixed key order** (sorted by key atom,
so output is deterministic). Values: atom → name, integer → digits, `nil` →
`nil`, list-of-atom → `(a b c)`. `decode_fault(str) :: {:ok, map} | {:error, _}`
inverts it; keys and atom values via `String.to_existing_atom/1`; `nil`→`nil`;
a parenthesized group → list. Fault keys (`kind`, `witness`, `expected_head`,
`injected_head`, `scope`, `depth`, `wrap_path`, plus the deep/conv fields
`wrap_path`/`carrier`/`reduction`/…) are all in `@known_atoms` already.

**Two value shapes beyond the above (verified against
`Generators.Mutation.build/2` — not hypothetical, these are live):**

- **`scope` for `:out_of_scope_var`** is a 2-tuple of integers, not `nil`/atom.
  Print as a nested paren-pair of bare integers: `(scope (5 5))`. This is the
  one **key-specific** decode rule the fault codec needs: `decode_fault` must
  know that a parenthesized group of exactly two integer tokens under the key
  `scope` decodes to a 2-tuple `{5, 5}`, not the 2-element list `[5, 5]` that
  the generic list-of-atom rule would otherwise produce for a bare paren group
  (no other fault key currently emits a bare list of integers, so this
  key→shape binding is unambiguous today but is a schema fact, not something
  `decode_fault` can infer from the printed form alone).
- **`expected_head`/`injected_head` for `:universe`** hold a Core-term tuple
  (`{:type, 0}` / `{:type, 1}`), not an atom head-name. Print by recursing into
  the **term** grammar (§3.1) instead of the atom-name rule:
  `(expected_head (type 0))`, `(injected_head (type 1))`. Because these same
  two keys hold plain atom head-names (`Nat`, `Vec`, `Z`, `S`, `Sigma`) for
  every other mutation operator, `encode_fault`/`decode_fault` must dispatch
  **per value**, not per key: an atom value prints/parses as a bare name: a
  tuple value prints/parses as a nested term node. This mirrors how the outer
  `SExpr` codec already distinguishes leaves from nodes — no new ambiguity is
  introduced, since a bare name token and a parenthesized term node are always
  syntactically distinct.

§7 test 3 must exercise both shapes explicitly (not just "a mutant_term"):
at minimum one banked `:out_of_scope_var` mutant and one banked `:universe`
mutant, asserting their `fault=` field round-trips the tuple/term values
exactly.

> **Value-type ambiguity note:** `nil` as an atom value vs. a name literally
> spelled `nil` — the fault schema never uses a name `nil` except as the
> genuine `nil` sentinel (`scope: nil`), so decoding the bare token `nil` to
> Elixir `nil` is correct for this schema. Documented as a fault-schema
> assumption, not a general s-expression rule.

## 4. `Antigen.Corpus` changes

All format changes live here (plus the new module); **`Challenge` is
untouched** — see §5.

### 4.1 Encode (`encode_record/2`)

- **pieces:** `"#{id}::#{SExpr.encode(t)}"` instead of the Base64 form.
- **note:** `enc_note(c.note)` — `nil`→`"-"`, else percent-escaped plaintext.
- **fault:** pop `"fault"` out of the scaffold map before Base64; if present,
  emit a `fault=#{SExpr.encode_fault(fault)}` field and Base64 only the
  remaining scaffold. Field order: `…scaffold=…\tfault=…\tkey=…\tpieces=…`
  (fault present only when the popped value is non-nil).
- **key:** unchanged (Base64).

### 4.2 Decode (`decode_record/1`) — dual-read

- **pieces (per piece):** if the body after `::` starts with `(` →
  `SExpr.decode`; else legacy `Serialize.decode(Base.decode64!(body))`.
  (Unambiguous: Base64's alphabet `A–Za–z0–9+/=` never starts with `(`.)
- **note:** if the value looks percent-escaped/plaintext, `dec_note`; a legacy
  Base64 note decodes to itself as text — acceptable (note is cosmetic, and the
  migrated file has no legacy notes). Concretely: new reader always treats
  `note=` as escaped-plaintext (`dec_note`); a legacy record read before
  migration shows its note as the raw Base64 string (harmless, non-load-bearing).
- **fault:** if a `fault=` field is present, `SExpr.decode_fault` → merge into
  the reconstructed scaffold map as `scaffold["fault"]`; else the fault is read
  from the (legacy) Base64 scaffold as today. Either way `from_pieces` sees
  `scaffold["fault"]` and is unchanged.
- Force `Challenge.__known_atoms__()` first (already done today).

### 4.3 `dedup_key/2` unchanged

`dedup_key(_, :antibody)` uses `Serialize.encode(t)` (binary) — **independent of
display format**. So dedup identity, `seen?`, and the `key=` field are all
stable across the format change: a migrated seed has the **same** dedup key as
before. This is what makes migration lossless (§7 test 5).

## 5. `Antigen.Challenge` — no change

Because the fault is relocated at the Corpus layer (pop-on-encode /
merge-into-scaffold-on-decode), `Challenge.to_pieces/1` and
`Challenge.from_pieces/7` need **no modification** — `to_pieces(:mutant_term)`
still emits `scaffold["fault"]`, and `Corpus.encode_record` pops it out for the
readable field; `from_pieces(:mutant_term)` still reads `scaffold["fault"]`,
which `decode_record` has merged back. Keeping `Challenge` untouched minimizes
blast radius and keeps the per-kind reconstruction logic in one place.

## 6. Migration

A one-time migration rewrites **every** committed banked-record file from the
old Base64 form to the new readable form: `test/antigen/seeds.sexp`,
`test/antigen/corpus.sexp`, and `test/antigen/reach.sexp` (verified via
`git ls-files | grep '\.sexp$'` — these are the only three; all three are in
the identical `antigen-record` format and are exercised by static replay tests
— `corpus_replay_test.exs`, `indexed_seed_test.exs`, `positivity_seed_test.exs`,
`totality_seed_test.exs`, `universes_seed_test.exs`, `reach_pin_test.exs`).
Dual-read (§4.2) would keep `corpus.sexp`/`reach.sexp` decodable if left
un-migrated, but the spec's own motivation — the operator reading/debugging
terms by hand — is unmet for whichever files stay in Base64 form, so all three
migrate together in Stage 4.

- **Mechanism:** stream the existing file through `Corpus.decode_record`
  (reads legacy Base64), then re-serialize each challenge through the new
  `Corpus.encode_record` (writes readable), preserving the **exact** stored
  dedup key (decode the legacy `key=` field and pass it verbatim to
  `encode_record/2`, so `key=` is byte-identical). Write to a temp file, then
  atomically replace.
- **Delivered as:** a small `Mix.Tasks.Antigen.Migrate` task (or a checked-in
  one-shot script under `test/support/`), run once during Stage 4, and the
  migrated `seeds.sexp` is committed. The task is idempotent (re-running on an
  already-migrated file is a no-op-equivalent: decode reads s-expr, re-encode
  writes the same s-expr).
- **Safety:** because §4.3 guarantees dedup-key stability, the migrated file has
  the same record identities in the same order; the static replay meta-tests
  (`mutation_meta`, `conversion`, `corpus_replay`) must stay green unchanged.

### 6.1 Edge case — note `"-"`

A genuine note equal to `"-"` would otherwise be indistinguishable from the nil
sentinel. Rule: the bare token `-` is reserved for nil; `enc_note` escapes a
real note of exactly `"-"` to `%2D`. Decode: `-` → nil; anything else →
percent-unescape. Costs one extra escape rule. (The v1 corpus notes are all
human sentences, so this path is defensive, not currently exercised by real
data — but it keeps the codec total.)

## 7. Testing (TDD, per Stage 4)

1. **SExpr round-trip (load-bearing):** enumerate **every** Core former from the
   source of truth; assert `decode(encode(t)) == {:ok, t}` for each, plus a
   deep nested composite (a `case` with binder branches, a `pi`, a `data` with
   indices, a `plus`-headed `Vec` index). RED first (module absent).
2. **SExpr atom-safety:** `decode("(global no_such_name_xyz)")` →
   `{:error, {:unknown_atom, _}}`, and the atom is **not** minted
   (`assert_raise ArgumentError, fn -> String.to_existing_atom("no_such_name_xyz") end`
   still raises afterwards). Malformed input (`"(app f"`, `"()"`, `"(bogus 1)"`)
   → `{:error, _}`, never raises.
3. **Corpus record round-trip (new format):** `encode_record |> decode_record ==
   {:ok, challenge}` for a `typed_term`; a `mutant_term` for **each** of the 7
   `Generators.Mutation` operators, not just one — in particular
   `:out_of_scope_var` (asserts `fault["scope"]` round-trips as the 2-tuple
   `{lo, hi}`, §3.4) and `:universe` (asserts `fault["expected_head"]`/
   `["injected_head"]` round-trip as `{:type, _}` term tuples, §3.4) — plus the
   5 atom/integer-only operators; and a non-term kind (e.g. `:family`, as
   produced by the `positivity` assay — pieces round-trip, no `fault=`).
4. **Dual-read legacy:** a **hand-written legacy record** (Base64 pieces +
   fault-in-scaffold, Base64 note) still `decode_record`s to the correct
   challenge, incl. the fault. Guards backward compatibility.
5. **Migration lossless:** run the migration on a fixture built from N banked
   challenges; assert (a) every migrated record decodes, (b) the multiset of
   dedup keys is identical pre/post, (c) the decoded challenges equal the
   originals, (d) re-running migration is idempotent (byte-identical output).
6. **Readability smoke:** encode a `mutant_term`; assert the line contains a
   plaintext `note=` (not Base64), a `pieces=…(ctor …)` s-expr, and a readable
   `fault=((kind …)…)`, and that **none** of the `note`/`pieces`/`fault` field
   values match a "looks-like-Base64" pattern.
7. **Full suite once** (Stage 5): all green, including the existing
   `architecture_test` quarantine (SExpr is outside `generators/`/`assays/`, so
   no `StreamData` literal concern) and the static replay meta-tests against all
   three migrated files (`seeds.sexp`, `corpus.sexp`, `reach.sexp`, §6).

## 8. Files

- **Create:** `lib/antigen/sexpr.ex`, `test/antigen/sexpr_test.exs`.
- **Modify:** `lib/antigen/corpus.ex` (pieces/note/fault encode+decode, dual-read),
  `test/antigen/corpus_test.exs` (or the existing corpus test file — Stage 2
  locates it) for record-level tests.
- **Migrate + commit:** `test/antigen/seeds.sexp`, `test/antigen/corpus.sexp`,
  `test/antigen/reach.sexp` (§6 — all three committed `.sexp` files).
- **Migration harness:** `lib/mix/tasks/antigen.migrate.ex` **or**
  `test/support/seeds_migrate.exs` (Stage 2 picks; a Mix task is preferred so
  it is rerunnable and discoverable).
- **Untouched:** `lib/antigen/challenge.ex`, `lib/cure/core/serialize.ex`
  (Serialize still backs dedup keys), all generators/assays.

## 9. Non-goals (YAGNI)

- Recovering variable **names** — positional de Bruijn stays; documented in the
  `SExpr` moduledoc.
- Making the non-fault **scaffold** or the dedup **key** readable.
- A **surface-syntax** parser (this is a Core-term codec, not Cure source).
- Changing the `Serialize` **binary** format — it still backs dedup keys and the
  legacy read path.
- A pretty-printer / multi-line layout — one piece, one line.
- ChoiceSeq / shrinking (separate, already shipped/shelved).

## 10. Risks

- **Missed former:** if a Core former is absent from the printer, `encode`
  raises at generation/bank time. Mitigation: §7 test 1 enumerates the former
  set from the source of truth; a missed former fails the round-trip test in
  RED, not in production.
- **Missed fault-value shape:** the fault map is not uniformly
  atom/integer/nil/list-of-atom — `:out_of_scope_var` (2-tuple `scope`) and
  `:universe` (Core-term `expected_head`/`injected_head`) need the extended
  value grammar in §3.4. Mitigated by naming both operators explicitly in §3.4
  and §7 test 3, rather than trusting one generic "a mutant_term" fixture to
  incidentally cover them (equal-weight operator selection means either could
  be absent from a small fixture by chance).
- **Atom minting via the parser:** mitigated by `String.to_existing_atom` +
  the forced `__known_atoms__()` intern (§3.3), tested in §7 test 2.
- **Migration divergence:** mitigated by dedup-key stability (§4.3) + §7 test 5
  asserting key-multiset equality and idempotency.
- **Delimiter collision:** an s-expr containing `;;`/`::`/tab would corrupt a
  record. It cannot: names are atoms (no such chars), structure is parens and
  single spaces. Asserted implicitly by round-trip through `decode_record`
  (which splits on those delimiters) in §7 test 3.

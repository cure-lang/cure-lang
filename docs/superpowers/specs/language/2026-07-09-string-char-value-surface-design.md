# String & Char as Dependent Value-Surface Types (charlist representation) — Design

**Status:** approved design (operator: "we'll do A"), spec written under autopilot.
**Program:** value-surface parity (#23) — bring String/Char into the dependent
pipeline (`lib/cure/elab/*` + `lib/cure/core/*` + `emit.ex`) so the classic
pipeline (`lib/cure/compiler/*` + `lib/cure/types/*`) can be deleted (#18).
**Layer:** K (one aligned kernel primitive) + E (elaboration) + C (emit/erase).
**Verification:** cure-porting differential oracle + Antigen (for the TCB slice).

---

## 1. Goal

`String` and `Char` become ordinary dependent-pipeline values:

- **`Char`** — a primitive base type, an inhabitant is a Unicode **code point**
  (`0 ≤ c ≤ 0x10FFFF`). Erases to a bare BEAM integer.
- **`String = List(Char)`** — a type-level *definition*, not a new primitive.
  A `String` value is a native cons list of code-point integers — i.e. an
  Erlang **charlist** `[97, 98, 99]`. String literals and interpolations
  elaborate to that list.
- **`Atom`** — explicitly **out of scope** for this wave (see §7). It is a
  separate minimal opaque base type; deferred.

The payoff: `String` stops being a would-be kernel base type. It is *dissolved*
into the already-working `List` machinery, so the "add a String primitive to the
TCB" ask disappears. The only kernel addition is `Char`, which is
Agda/Idris-faithful (both have a primitive `Char`) and mechanically parallel to
the existing `Int`/`Float` primitives.

## 2. Why this shape (alternatives considered & rejected)

### 2.1 `Char = Bounded(0x110000)` — REJECTED for this wave (measured; see the option-(a) note)
`Std.Bounded` (`lib/std/bounded.cure`) is a **unary Peano** Fin:
`First : Bounded(S(m))`, `Next : Bounded(m) -> Bounded(S(m))`. Representing code
point 97 would require 97 nested `Next` constructors. This was re-examined
empirically rather than dismissed on principle:

- **The value tower is *not* the blocker (fixed).** A char *value* `Next^k(First)`
  is a deep constructor spine; the only expensive operation on it was
  `Kernel.infer`, which was O(n²) (a single emoji, depth 128512, typechecked in
  **4m 23s**). That quadratic was fixed — commit `341b1f1` ("perf(kernel): linear
  infer on deep constructor spines") makes it linear; re-measured **153 ms** at
  emoji depth (`nf`/`conv` were already linear, ~30 ms — BEAM grows process
  stacks on the heap, so deep recursion never crashes). So the value tower alone
  would now be feasible.
- **The *bound* is the decisive blocker (measured, not fixed).** `Bounded(n)`'s
  index `n` is a unary `Nat`, so the *type* `Bounded(0x110000)` must materialize
  `n = 1,114,112` as a 1.1-million-deep `S`-tower. Measured (`bound_bench`): build
  82 ms, `nf` 398 ms, `infer` 593 ms, and **~370 MB resident** (VM total
  108 MB → 479 MB) — for the type index alone, present in every `Char`
  signature. `341b1f1` does not touch this (it addressed the value spine, not the
  index), and there is an unmeasured additional risk that index conversion
  re-normalizes the bound *per char literal* (~400 ms × every `Char` literal).
  This is what rules `Bounded` out for the working design.

**Option (a) — the path that *would* make `Char = Bounded(0x110000)` viable —
is a separate, parallel workstream (owned by another agent), not this wave.**
Compact `Nat` literals in the kernel (native literal + `Nat.rec` peeling — Lean's
kernel `Nat`, Agda's `{-# BUILTIN NATURAL #-}`) would give `Bounded(0x110000)` a
*compact* index (no 1.1M tower) and a compact char *value* (an `int_lit` at
`Bounded`, no value tower either). When that lands, `Char` may migrate to
`Bounded(0x110000)` with a compact index. Until then, this wave ships the
bespoke `Char` primitive (§2.3, option (b)) — compact, nominally distinct, and
sidestepping *both* towers because its `0 ≤ cp ≤ 0x10FFFF` bound is a plain
integer check in the elaborator's literal handler (§4.2), not a `Nat` index.

### 2.2 `Char` erases to `Int`, nominal only in the elaborator (kernel `Char = Int`) — REJECTED
Zero-TCB, but `Char` and `Int` become kernel-indistinguishable: `f(c: Char)`
would silently accept an `Int`, and `String = List(Char) = List(Int)` conflates
strings with integer lists. Loses the type distinction the whole exercise is for.

### 2.3 `Char` as a primitive base type — CHOSEN (option (b), the working design for this wave)
Agda: `{-# BUILTIN CHAR Char #-}` (primitive, distinct from `Nat`, with
`primCharToNat`/`primNatToChar`). Idris: primitive `Char`. Lean: a validated
`UInt32` structure. Two of three real languages make `Char` a *primitive*, so a
`{:char_type}`/`{:char_lit}` kernel pair is **alignment-faithful** and covered by
the TCB blanket approval — while still requiring the full Antigen + suite gate
(it is a TCB change; treat it as HARD-STOP-reviewed, but the *direction* is
pre-approved because it matches Agda/Idris). It mirrors the existing
`{:int_type}`/`{:int_lit}` clauses one-for-one, so the diff is mechanical.

### 2.4 `String` primitive with `toList`/`fromList` (the Agda/Idris shape) — NOT CHOSEN (operator override)
Agda/Idris make `String` a **primitive** (a packed representation) with
`primStringToList : String → List Char` and `primStringFromList` — String is
*not* literally `List Char`. That is the binary-backed "Option B" from the design
conversation. The operator explicitly chose **Option A**: `String` *is*
`List(Char)`, represented as a charlist. This is a **deliberate, recorded
divergence** from Agda/Idris, taken because (a) it makes the
`String = List(Char)` equation literally true rather than a conversion, (b) it
needs the least machinery — no String primitive, no packed-string ops surface —
and (c) the `to_binary`/`from_binary` `@extern` bridge at the binary boundary
(§4.6) preserves a later migration to a packed representation *behind the
unchanged `List(Char)` type*, if embedded perf ever demands it. (Note: `@builtin`
is a distinct, narrower mechanism — see §4.6 — not part of this bridge; corrected
here to avoid conflating the two.) The alignment default is overridden by an
explicit operator decision; recorded here so review does not "correct" it back
to a primitive.

### 2.5 Grapheme clusters (`Character` à la Swift) — DEFERRED
AtomVM ships **no** grapheme segmentation (`string.erl` is codepoint/charlist
based: `to_upper`/`to_lower`/`split`/`trim`/`find`/`length`/`jaro`, no
`next_grapheme`). A Swift-style `GraphemeCluster` would be a pure-Cure derived
library over `List(Char)` doing its own Unicode boundary tables — real work with
zero native help. Correctly a *later, derived* type; not this wave.

## 3. Runtime & AtomVM substrate (verified in the tree)

Confirmed native in `/Users/ch/Develop/esp32-beam/AtomVM`:
- **UTF-8 bitstring codegen is native** (`bitstring.c`: `bs_utf8_size`,
  `bitstring_utf8_encode`, `bitstring_match_utf8`). `<<C/utf8>>` build **and**
  `<<C/utf8, Rest/binary>>` match run on-device. This is what lets the
  charlist↔binary bridge be plain Erlang, no custom NIF.
- **`unicode:characters_to_binary/1,2,3`** and **`characters_to_list/1,2`** are
  real native NIFs (`nifs.c:6850,6911`) — charlist↔UTF-8-binary both directions.
- Atoms are UTF-8 (`unicode_utf8_decode`, `unicode_is_valid_codepoint` in the
  atom path). (Relevant to the deferred Atom work, not this wave.)
- `binary` module: `at/2, part/3, split, match, replace, copy, encode/decode_hex`.
- `string` module: codepoint-based, Latin-1 `to_upper/to_lower`, `split, trim,
  find, length, jaro`.

Consequence: a `String` value = an Erlang charlist works everywhere charlists
work (`~ts` formatting, `unicode:characters_to_binary`), and a binary is produced
on demand by one native NIF call at the interop boundary.

## 4. Components

### 4.1 Kernel: the `Char` primitive (TCB — HARD-STOP-reviewed, Agda/Idris-aligned)
Mirror the existing `Int` base-type machinery in `lib/cure/core/term.ex`:
- **Terms:** add `{:char_type}` (the type) and `{:char_lit, cp}` (a literal
  code point, `cp` a non-negative integer `≤ 0x10FFFF`), parallel to
  `{:int_type}`/`{:int_lit, n}`.
- Clauses to add, each mirroring the `int_*` neighbour verbatim (line numbers
  verified against this worktree; each of the five functions below has its
  `int_type`/`int_lit` case as a **2-line pair** — one clause per constructor —
  immediately followed by the analogous `float_type`/`float_lit` 2-line pair,
  so a `char_type`/`char_lit` 2-line pair should be inserted between them, not
  a single line):
  - `term?/1` — int pair at lines 61-62; float pair follows at 63-64
  - `shift/*` — int pair at lines 86-87; float pair follows at 88-89
  - `subst/*` — int pair at lines 149-150; float pair follows at 151-152
  - `to_external/1` — int pair at lines 215-216; float pair follows at 217-218
  - `from_external/1` — int pair at lines 249-250; float pair follows at 251-252
- **Evaluation (`eval.ex`) — required, and missing from an earlier draft of
  this list.** `{:char_lit, cp}`/`{:char_type}` are Core *terms*; they only
  become checkable *values* through `eval.ex`, mirroring the exact int pattern:
  `eval.ex:43` (`def eval({:int_type}, _env), do: {:vint_type}`) and
  `eval.ex:44` (`def eval({:int_lit, n}, _env), do: {:vint, n}`) — add
  `eval({:char_type}, _env), do: {:vchar_type}` and `eval({:char_lit, cp},
  _env), do: {:vchar, cp}` alongside them. **Without this, `conv.ex`'s clause
  below is never reached** (there is no `{:vchar,_}` value for it to pattern-match
  on) — this is not optional bookkeeping, it's the load-bearing step that makes
  everything downstream work.
- **Value predicate (`value.ex`) — also required, also missing from an earlier
  draft.** Mirror `value.ex:45-46` (`value?({:vint_type}), do: true`;
  `value?({:vint, n}), do: is_integer(n)`): add `value?({:vchar_type}), do:
  true` and `value?({:vchar, n}), do: is_integer(n)`.
- **Conversion (`conv.ex`)**: `{:char_lit, a}` conv `{:char_lit, b}` ⇔ `a == b`;
  `{:char_type}` conv `{:char_type}`. **Two distinct clauses, verified — an
  earlier draft of this spec pointed at the wrong one for the literal-equality
  property:**
  - The **literal-value** "equate iff equal" property — the actual subject of
    the Antigen obligation below — lives at `conv.ex:75`
    (`conv_struct?({:vint, a}, {:vint, b}, _depth, _sig), do: a == b`) and its
    no-δ twin `conv.ex:165` (`same_value_no_delta?({:vint, a}, {:vint, b},
    ...), do: a == b`). Add `conv_struct?({:vchar, a}, {:vchar, b}, ...), do: a
    == b` and the `same_value_no_delta?` twin here — these pattern-match on the
    `:vint`/`:vchar` tuple **head**, so a `:vchar` clause cannot accidentally
    collide with `:vint` values; no extra guard needed.
  - The **type-identity** clause (both sides are the type itself, trivially
    `true`) is the *adjacent but separate* `conv.ex:74`
    (`conv_struct?({:vint_type}, {:vint_type}, ...), do: true`) and its twin
    `conv.ex:164`. Add the `{:vchar_type}` equivalent here too — both this and
    the literal clause above are needed, they are not alternatives.
- **Reification (`quote.ex`)**: mirror the existing `{:vint_type}` reify-to-term
  case (quote.ex:64, `{:vint_type}` → `{:int_type}`) with a `{:vchar_type}` →
  `{:char_type}` case (and `{:vchar, n}` → `{:char_lit, n}`), so normal forms
  read back into valid surface Core terms.
- **Kernel inference (`kernel.ex`)**: mirror the existing Int handling (`Int`
  infers/type-checks via the `{:vint_type}`/`{:vint,_}` cases referenced at
  `kernel.ex:59` and `kernel.ex:635`) with the `Char` equivalents, so
  `Kernel.infer/2` on a `{:char_lit, cp}` term returns `{:ok, {:vchar_type}}`
  the same way it does for `{:int_lit, n}` → `{:ok, {:vint_type}}`.
- **Normalisation (`normalise.ex`)**: **no new clause needed.** Verified: this
  file has no per-constructor `int_lit`/`int_type` case to mirror — "already
  normal" is handled generically by the catch-all `whnf_value(value, _sig,
  _opts), do: value` (line 69), which already covers any non-`:vneutral` value
  including the new `{:vchar_type}`/`{:vchar_lit}` forms by fallthrough. Do not
  add a normalise.ex clause; there is nothing there to mirror.
- **No new eliminator, no arithmetic in the kernel.** `Char` is inert: it is
  introduced by literals and consumed only by equality (via `==`, §4.4) and by
  the `to_binary`/`from_binary` `@extern` bridge (§4.6). Codepoint↔Int
  conversion lives in the elaborator/std as `@extern` (mirrors Agda's
  `primCharToNat`), NOT as kernel reduction — keeps the TCB minimal.
- **Erasure (`erase.ex`): also no new clause needed.** Verified: `erase.ex` does
  not enumerate base types at all — `{:int_lit,_}`/`{:int_type}` (and
  `float_*`) already fall through its generic catch-all `def erase(_env,
  term), do: term` (line 112). `{:char_lit,_}`/`{:char_type}` will erase
  correctly the same way, with zero new code. (This resolves the hedge that
  used to live in §4.5 — see there.)

**Antigen obligation (mandatory for the TCB slice):** a new antibody proving the
new `Char` clauses across `term.ex`/`eval.ex`/`value.ex`/`conv.ex`/`quote.ex`/
`kernel.ex` (a) terminate and (b) equate no distinct normal forms
(`{:char_lit, a} ≡ {:char_lit, b}` iff `a == b`, the property enforced at
`conv.ex:75`/`165` above) — the same soundness *property* the `Int` literal
clauses have. Caveat verified against this worktree: there is
**no existing Antigen antibody file** that states this "iff" property for
`int_lit` specifically today — the closest existing artifact is a plain kernel
unit test, `test/cure/core/int_prim_test.exs:55-58` (checks
`Conv.conv?/5` on `int_lit`/`int_add` directly, not framed as an antibody). The
structurally closest *antibody* (same "iff convertible" shape, different
subject) is `test/antigen/eq_inductive_antibody_test.exs`, which pins "a `refl`
proof inhabits `Equivalent(ty,x,y)` iff `x` and `y` are convertible" against the
independent oracle `Cure.Core.Conv.conv_within?`. The new `char_lit` antibody
should follow that template's shape (independent-oracle-checked iff-property),
not a copy-paste of a nonexistent `int_lit` antibody. Plus the full Antigen
suite (`test/antigen/`, which runs as part of plain `mix test` — no separate
invocation) and full `mix test`, run once, alone (never concurrent with another
`mix` invocation).

### 4.2 Elaboration: char literals
`lib/cure/elab/elaborator.ex` has **two** literal-handler locations, verified to
have *different return shapes* — both need a `:char` clause, but not the same
one:
- `elaborate_expr_typed/4` (`:literal` clause spans 446-461, `:integer` arm at
  452-453: `{:ok, {:int_lit, value}, {:vint_type}}`). Add:
  `:char when is_integer(value) -> {:ok, {:char_lit, value}, {:vchar_type}}`
  (mirror the `:integer` arm at 452-453), where `{:vchar_type}` is the value
  form of `{:char_type}` (add the value-form constructor alongside `{:vint_type}`,
  following that constructor's existing footprint in `value.ex`, `eval.ex`,
  `quote.ex`, `kernel.ex`, `conv.ex`).
- `elaborate_expr/3` (the second, infer-mode copy, at line 4907, `:integer` arm
  at line 4910: `{:ok, {:int_lit, value}}`). This clause returns **only the
  term, no type** — add `:char when is_integer(value) -> {:ok, {:char_lit,
  value}}` here, a **2-tuple**, not the 3-tuple used at 452-453. Copying the
  452-453 shape verbatim into this location is a return-arity mismatch; call
  this out explicitly so the implementer does not paste one clause into both
  sites.

Both AST-producing sides are confirmed already in place: the lexer emits a
`:char` token whose value is the decoded code-point integer
(`lib/cure/compiler/lexer.ex:886-909`, first emission at line 909), and the
parser already produces a `:char` literal node
(`lib/cure/compiler/parser.ex:236-237`) — note the real path is
`lib/cure/compiler/{lexer,parser}.ex`; there is no separate
`lib/cure/elab/parser.ex` — the dependent pipeline (`elaborator.ex`,
`declarations.ex`) consumes the AST these classic-pipeline-housed lexer/parser
modules produce.

**Additional required locus — char literal PATTERNS, missing from the above
(expression-only) coverage.** Verified: elaborating `'a'` as an *expression*
(above) does **not** give you `case c of 'a' -> … | _ -> …` as a *pattern* —
these are two separate, independently-dispatched code paths in
`elaborator.ex`, exactly as `Int`/`Float`/`Bool` already are. The top-level
literal-pattern dispatcher is `try_literal_match/8`
(`elaborator.ex:2679-2798`), which classifies the scrutinee's type via
`primitive_scrut_kind/2` (2723-2730, currently recognizing only
`{:vint_type}`/`{:vfloat_type}`/Bool's `:vdata`) and then dispatches per-arm via
`literal_of?/2` (2752-2755) and `lit_core/2` (2760-2762) to build the match, and
`literal_chain/6` (2784-2798) to pick the equality global (`:int_eq`/
`:float_eq`/`eq` for bool). None of these currently recognize `Char` — a
char-scrutinee match falls through `primitive_scrut_kind/2`'s catch-all,
`try_literal_match` returns `:not_applicable`, and the pattern falls into the
`:vdata` constructor-pattern path, which has no case for a bare literal against
a non-inductive scrutinee. **This wave must add a `:char`/`{:vchar_type}` case
to all four of `primitive_scrut_kind/2`, `literal_of?/2`, `lit_core/2` (→
`{:char_lit, v}`), and `literal_chain/6` (→ a `char_eq` equality global,
mirroring `int_eq`) — mirroring the existing `Int`/`Float`/`Bool` cases exactly
— or `Char` is not actually "an ordinary dependent-pipeline value" per §1's own
goal statement (you could construct and compare Chars, but not pattern-match a
literal one, which is the idiomatic way most real code branches on a
character).** This is in addition to, not a substitute for, the expression-side
work above.

**Explicitly out of scope, flagged so it is not accidentally exercised —
string literal PATTERNS (`case s of "ab" -> … | _ -> …`).** This spec's own
test surface (§8) only promises *structural, variable-bound* String patterns
(`[]`/`c :: cs`, i.e. `Nil`/`Cons(h,t)` with pattern variables) — never a
literal-valued multi-element pattern like `"ab"` or `[97, 98]`. That is
deliberate, not an oversight: probing this found `List`-literal-*pattern*
desugaring already exists for expression-side reuse
(`desugar_list_patterns/1`, elaborator.ex:3831-3845, reusing the same
`desugar_list/1` used for expressions) and works correctly for **variable**-
or **nullary-constructor**-element patterns (`test/cure/elab/list_test.exs:158-172`),
but has a **pre-existing, silent-miscompile bug** for **literal-valued**
elements inside a multi-element constructor/list pattern: `split_ctor_arms/4`
(elaborator.ex:3201-3216) and `compile_matrix_split/4`'s ctor-collection
(elaborator.ex:3177-3184) have no clause for a `{:literal, m, v}` pattern node,
so a literal-element row (e.g. `[1, 2] -> true`) is silently dropped from
*both* the constructor arms and the default/wildcard arms whenever a catch-all
arm is present — `Program.elaborate/1` returns `{:ok, _}` with no error, but at
runtime the literal arm is unreachable and every input falls through to the
catch-all. This is a **pre-existing bug in the general pattern-matrix
compiler, unrelated to `Char` specifically** (it already affects e.g.
`[1, 2]: List(Int)` patterns today) — **do not attempt to fix it as part of
this wave**; it is out of scope. But it is the reason a naive "string literal
pattern via `desugar_list` reuse" implementation would *silently miscompile*
rather than cleanly reject, so: do not add string-literal-pattern support in
this wave, and do not write an oracle/unit test that exercises a literal-valued
multi-element `String`/`List` pattern — stick to the `[]`/`c :: cs` structural
form already specified in §8. File the matrix-compiler bug as an independent,
separately-tracked defect.

### 4.3 Elaboration: `Char` and `String` as named types
- `Char` resolves to `{:char_type}`. Add to the primitive-type resolver
  (`lib/cure/elab/declarations.ex:1126-1128`, where
  `primitive_type("Int") -> {:int_type}` lives at line 1126 and `Float` at
  1127, followed by a catch-all `nil` at 1128 — corrected from an earlier
  1113-1115 estimate): a `primitive_type("Char") -> {:char_type}` clause,
  inserted before the catch-all. `Char` needs **no** std `type` declaration (it
  is a primitive, like `Int`; note `Bool` is deliberately *not* in this
  resolver — it's a real inductive family, not a primitive — so `Char` joining
  `Int`/`Float` here is consistent with existing practice).
- `String` is a **type alias** for `List(Char)`. It is *not* a primitive and not
  a new inductive. **Resolved: Cure already has working surface type aliases —
  use the surface form, no elaborator-level resolver expansion needed.**
  Verified end-to-end: the parser's `parse_type_def_adt/4`
  (`lib/cure/compiler/parser.ex`, from line 3011) supports `type Name =
  ExistingType` producing a `{:type_annotation, meta, [rhs]}` node (its own
  code comment gives `type Celsius = Int` as the worked example, line 3085,
  distinguished from a single-ctor ADT via `variant_ctor?/1`), and the
  dependent pipeline already elaborates it:
  `lib/cure/elab/declarations.ex:235-242`,
  `elaborate({:type_annotation, meta, [rhs]}, env)`, elaborates the RHS via
  `idx_to_core` and installs it as a δ-unfoldable, non-recursive alias via
  `Env.add_def(env, name, {:type, 0}, rhs_core, [])` (doc comment at
  232-234 states this is exactly a δ-unfoldable alias). Concretely: add
  `type String = List(Char)` to `lib/std/string.cure` (or wherever the module
  boundary lands, §4.7) using this existing mechanism — do not add a resolver
  expansion, one is not needed.

### 4.4 Elaboration: string literals & interpolation → charlist
- A bare string literal reaches the dependent pipeline as the lexer/parser
  string form. Elaborate `"abc"` to the **`List(Char)` cons spine**
  `Cons('a', Cons('b', Cons('c', Nil)))` at the Core level — i.e. reuse the
  existing `:list` elaboration (already routed through `elaborate_expr_checked`,
  Wave 4) with `{:char_lit, cp}` elements. **Concrete reuse point, verified —
  not hand-waved:** `:list` AST nodes are folded into `Cons`/`Nil` `ctor_call`s
  by `desugar_list/1` (`lib/cure/elab/elaborator.ex:3806-3818`), which recurses
  on element ASTs generically (`desugar_list(h)`/`desugar_list(e)`) with **no
  branching on element type** — it does not special-case `Int` elements in a
  way that would need changing. Concretely: desugar the string literal node
  into a `:list` AST node whose elements are the `:char` literal nodes for each
  code point, and route it through this same, already-generic path — this
  produces the identical Core shape the list literal `['a','b','c']` would
  produce, so there is **one** list-elaboration path, not a bespoke string
  path.
- **Interpolation** (`{:string_interpolation, _, parts}`,
  `lib/cure/compiler/parser.ex:494`):
  desugar to `List` concatenation (`++`) of the parts, where a literal part is a
  charlist and an interpolated expression part is rendered to a `String`
  (`List(Char)`) via the `Show`/`to_string` path. For this wave, restrict
  interpolated parts to expressions already of type `String`; general
  `Show`-based rendering is a follow-up (typeclasses, #21). A string with no
  interpolation is the pure-literal case above.
- Equality: `s1 == s2` on `String` is `List(Char)` equality — already provided by
  the list machinery / the `==` dispatch, no new codepoint-eq primitive beyond
  `char_lit` conversion (§4.1).

### 4.5 Emit & erase (`lib/cure/elab/emit.ex`, `erase.ex`)
- `{:char_lit, cp}` → the BEAM integer literal `{:integer, @line, cp}` (mirror the
  `int_lit` lowering at `emit.ex:210` — a single-line clause, `defp lower(_env,
  {:int_lit, n}, _ctx), do: {:integer, @line, n}`; the char mirror is likewise
  one line). A `Char` is a bare integer at runtime.
- `String` needs **no** dedicated emit: it is `List(Char)`, and `List` already
  lowers to native cons cells (builtin-inductive-foundation). So `"abc"` lowers
  to `[97,98,99]` — a genuine Erlang charlist.
- Erasure: `Char` erases like `Int` (a bare integer; relevant, present) — **no
  new erase.ex clause is needed** (see §4.1's erasure note: erase.ex has no
  per-base-type clauses at all, only a generic catch-all at line 112, which
  already covers `char_lit`/`char_type` the same way it covers `int_lit`/
  `int_type` today).

### 4.6 The `String ↔ Binary` boundary bridge (`@extern`, plus one new opaque type)
Two std functions, the *only* place a binary appears:
- `to_binary(s: String) -> Binary` — `@extern(:unicode, :characters_to_binary, 1)`
  (native NIF; charlist → UTF-8 binary).
- `from_binary(b: Binary) -> String` —
  `@extern(:unicode, :characters_to_list, 1)` (native NIF; UTF-8 binary →
  charlist).

**Prerequisite gap, verified and now closed here — `Binary` does not exist in
the dependent pipeline today.** The original draft of this section assumed
`Binary` was "the existing binary type," carried over from the classic
pipeline's `resolve_name("Binary") -> :string` alias
(`lib/cure/types/type.ex:375`). That does **not** hold for the dependent
pipeline the rest of this spec targets: there is no `{:binary_type}` (or any
name) in `core/term.ex`/`conv.ex`/`normalise.ex`/`eval.ex`/`value.ex`, no
`@builtin(:binary)` family (the seeded families are exactly `:bool`, `:nat`,
`:eq`, `:sigma`, `:list` — `lib/cure/core/builtins.ex:107-111`), and although the
parser *does* tokenize `<<...>>` binary-literal syntax
(`lib/cure/compiler/parser.ex:963-978`, producing `{:literal, [subtype: :bytes,
...], segments}`), the elaborator explicitly rejects it: both `:literal`
dispatch points (`elaborator.ex:446-461` and `elaborator.ex:4907-4914`) only
handle `:boolean`/`:integer`/`:float` subtypes and fall through to
`{:error, {:unsupported_expression, expr}}` for `:bytes`. So `to_binary`/
`from_binary` as written could not even elaborate their own signatures — `Binary`
would fail to resolve as a type name.

**Fix, scoped to stay off the kernel/TCB:** introduce `Binary` as a plain,
**non-`@builtin`, zero-constructor** inductive — `type Binary = |` — in std
(alongside or near `Std.String`). This is **not** a kernel/TCB addition: it
requires **zero changes** to `lib/cure/core/*.ex`. It is precedented and already
shipped for exactly this "opaque, foreign-produced, never Cure-constructed"
purpose: `lib/std/decision.cure:28` declares `type Empty = |` (an explicit,
documented "constructor-less (uninhabited) type"; parser support at
`lib/cure/compiler/parser.ex:3062-3068`, `no_more_variants?/1` at 3251-3256;
test coverage `test/cure/compiler/empty_type_parse_test.exs`). The ordinary
(non-`@builtin`) `:container`/enum elaboration path handles an empty variant
list with no special-casing (`lib/cure/elab/declarations.ex:1119-1130` →
`build_ctors([])` → `{:ok, []}` → `declare_at_min_level/4`; `Kernel.check_family/2`,
`check_all_ctors/3`, and `Inductive.positive?/2` are all no-ops over an empty
ctor list), and the resulting `{:data, :Binary, [], []}` resolves through the
same generic `Inductive.family?/2` path any populated ADT name uses — usable
immediately as an `@extern` param/return type. At runtime, `@extern` defs
(`emit.ex:127-140`, `extern_form/2`) are type-blind — they emit `mod:fun(V0,
...)` verbatim, never inspecting the declared type — so a `Binary`-typed value
(really a raw Erlang binary under the hood) passes through untouched; since it
has no constructors, Cure code can never construct or pattern-match one
directly, which is exactly the "opaque, boundary-only" property this bridge
needs. **No new erase.ex/emit.ex work beyond what §4.1/§4.5 already established
(generic catch-alls) is required for `Binary` either.**

**Routing caveat:** a module elaborates via the dependent pipeline only if
`Cure.Elab.Program.dependent?/1` (`program.ex:274-307`) sees a dependent
trigger (an implicit/auto-generalized param, an indexed type, etc.) — a module
containing *only* `type Binary = |` plus non-generic `@extern` signatures would
itself evaluate `dependent?` to `false` and silently fall through to the
classic (soon-deleted) pipeline instead of `elab/declarations.ex`, defeating
the point. In practice this is a non-issue *if* `Binary` is declared inside
`lib/std/string.cure` itself (or another module that already has a dependent
trigger) rather than a brand-new, otherwise-plain module — `Std.String`
already has auto-generalized helpers (e.g. a `List(t) -> List(t)` shaped
function), which is enough to route the whole module through
`elab/declarations.ex`. Do not put `type Binary = |` in an isolated,
non-generic module by itself.

This keeps the wave's TCB footprint exactly as claimed elsewhere in this
document (§1, §9): `Char` remains the *only* kernel/Core addition. `Binary` is
an elaborator/std-level addition, mirroring `Std.Decision.Empty`'s precedent,
not `Char`'s. (One deliberate framing correction elsewhere in this spec: §2.4's
mention of `@builtin`/`@extern` "at the binary boundary" was imprecise —
`@builtin` is a real but unrelated decorator, used exactly 5 times, only on
type declarations in the prelude module, to register one of the kernel-seeded
canonical families (`bool`/`nat`/`sigma`/`list`/`eq` — `lib/cure/core/builtins.ex`,
registration path `lib/cure/elab/program.ex:739-758`). `Binary` must **not** be
`@builtin`-registered — it is a plain std type, not a kernel-seeded family.)

**Sequencing note:** land `type Binary = |` before implementing `to_binary`/
`from_binary` (this section) and before the §4.7 Unicode-heavy-ops migration,
which depends on both. See §9.

These let `Std.String` keep delegating heavy Unicode ops to native `:string`/
`:binary` NIFs by converting at the boundary, without a `String` primitive.

### 4.7 `Std.String` migration (`lib/std/string.cure`)
Current file is binary-backed (`@extern :erlang.byte_size` for `length`, etc.).
Because disposition is **binary per module**, `Std.String` flips to KEEP only
when *every* decl elaborates. Migration policy:
- **Structural ops → native `List` ops.** `length` = `List.length` (now a
  **code-point count**, strictly more correct than the current byte-count wart
  the file's own doc apologises for). `is_empty` = `List.is_empty`/`== ""`.
  `concat`/`++` = `List.append`. Reverse, etc. — `List` functions.
- **Unicode/heavy ops → bridge to native NIFs.** `upcase`/`downcase`/`trim`/
  `split` etc.: convert `String`→`Binary` via §4.6, call the native
  `:string`/`:binary` NIF (which want binaries), convert result back. Keep these
  as thin wrappers; do **not** reimplement Unicode tables in Cure.
- **Numeric parsers** (`to_int`/`from_int`/`to_float`…): these bridge to binary
  and call the existing BIFs; from_int etc. produce a charlist via `from_binary`.
- **Scope guard:** if the full-file migration is too large to land in one wave,
  the wave's ratchet may instead be demonstrated by a **new small module**
  (`lib/std/string_demo.cure` or a test module) that `use`s the foundation and
  KEEPs, with the legacy `Std.String` full migration split into an explicit
  follow-up. The ratchet (value-surface KEEP count) must move by ≥1 either way.
- **Note on the KEEP count mechanism (verified, not this spec's gap alone):**
  "re-run the stdlib disposition script" is how the roadmap and every wave plan
  before this one describe re-checking the N/39 count, but no such script or
  mix task is actually checked into the repo — `docs/superpowers/specs/roadmap/2026-07-09-value-surface-roadmap-design.md`
  §0 describes the metric in prose only ("modules that
  `Cure.Elab.Program.elaborate/1` accepts"), and every downstream wave plan
  just re-cites that same prose. (`mix cure.check.stdlib` is a *different*,
  already-real mix task — it compiles std via the classic pipeline
  (`Cure.Compiler.compile_file/2`) and is not the dependent-elaborator
  KEEP/FAILS tally.) This wave inherits that same gap rather than introducing
  it: the before/after count in §8 must be obtained by manually invoking
  `Cure.Elab.Program.elaborate/1` over each of the 39 std modules (e.g. from an
  `iex -S mix` session or a throwaway script), not by running a named command
  that doesn't exist yet. Do not block this wave on writing that script, but do
  not assume one is there to run.

## 5. Data flow

```
"abc"  --lex-->  :string token
       --parse-> :string_interpolation / string-literal node
       --elab--> Core Cons({:char_lit,97}, Cons(98, Cons(99, Nil)))   : List(Char)  (= String)
       --emit--> [97,98,99]   (Erlang charlist)
'a'    --lex-->  :char token (value 97)
       --parse-> {:char, _, 97}
       --elab--> {:char_lit, 97} : Char
       --emit--> 97
String --resolve--> List(Char)     (alias, §4.3)
String --to_binary--> unicode:characters_to_binary --> <<"abc"/utf8>>   (boundary only)
```

## 6. Error handling
- **Invalid code point in a `char_lit`** (surrogate `0xD800..0xDFFF`, or
  `> 0x10FFFF`): the *type* `Char` over-approximates (it admits the full
  `0..0x10FFFF` integer range including surrogates — there is no refinement type,
  those were dropped). Validity is a **boundary invariant**: the native
  `bitstring_utf8_encode`/`characters_to_binary` reject invalid code points at
  the `to_binary` boundary (returns error / raises), so an invalid `Char` cannot
  silently become a valid UTF-8 binary. Record this as a known, deliberate gap:
  a surrogate-excluding `Char` needs a refinement or a bespoke validated type,
  deferred. The lexer already rejects malformed char literals
  (`:unterminated_char`).
- **Interpolating a non-`String` expression** (this wave): a type error at
  elaboration (expected `String`), until `Show`-based rendering lands (#21).
- **`from_binary` on invalid UTF-8**: propagates the native NIF's error tuple /
  exception unchanged (matching the current BIF-raise convention documented in
  `string.cure`).

## 7. Scope / non-goals
- **`Atom`** — deferred. A minimal opaque base type (UTF-8 sentinel), not
  `List(Char)`. Separate follow-up wave; do not build here.
- **`Show`/`to_string` general rendering** in interpolation — deferred to
  typeclasses (#21). This wave restricts interpolation to `String` parts.
- **Grapheme clusters / `Character`** — deferred derived library (§2.5).
- **Surrogate-excluding refined `Char`** — deferred (no refinement types).
- **Migrating a packed/binary `String` representation** — explicitly not now;
  the `to_binary`/`from_binary` `@extern` bridge (§4.6) keeps it available later
  behind the unchanged `List(Char)` type. (Not `@builtin` — see §4.6's framing
  correction; `@builtin` is the unrelated kernel-family-registration decorator.)
- **No kernel arithmetic/eliminator for `Char`** — inert primitive only.

## 8. Testing

Strict red-green throughout; cure-porting differential oracle is the arbiter.

- **Kernel (TCB) — Antigen first.** New antibody: `char_lit` conversion soundness
  (equates iff equal code points, `conv.ex:75`/`165`) + termination of the new
  `term.ex`/`eval.ex`/`value.ex`/`conv.ex`/`quote.ex`/`kernel.ex` clauses (per
  §4.1's finding, `normalise.ex` and `erase.ex` get **no** new clauses — the new
  `Char` forms fall through existing generic catch-alls in both, so there is
  nothing new to prove termination of there). Full Antigen suite + full `mix
  test`, once, alone.
- **Oracle probes** (paired `.cure`/`.idr`, `mix cure.oracle` — real mix task,
  `lib/mix/tasks/cure.oracle.ex`, backed by `lib/cure/oracle.ex`; fixtures live
  under `test/oracle/<cluster>/<name>.{cure,idr}` + `verdicts.json`, e.g. the
  Int-literal template `test/oracle/cond/cond02_int_literal.{cure,idr}`).
  Verified: no `char`/`string` cluster directory exists yet among the current
  clusters (`alias, cond, cycle, dep, deprec, dotpat, dpair, erasedidx,
  erasure, frp, func, guard, guardscrut, impossible, infmatch, letbind, letin,
  lexterm, match, nidot, poly, record, refl, retflow, retpos, rewrite, sg,
  shadow, whnf, with, withctor, withmulti`) — this wave creates a **new**
  cluster following the existing short-mnemonic naming convention, e.g.
  `test/oracle/char/` (probes below use `charNN_*`/`strNN_*` fixture names by
  the same convention as `cond02_int_literal`):
  - a `Char` literal and a `Char`-typed function signature — `same` as Idris
    (Idris has primitive `Char`).
  - a `String` literal bound and pattern-matched as a list
    (`case unpack s of [] => … | c :: cs => …`) — note the *expected* divergence
    where Idris's `String` is primitive (needs `unpack`); mark the fixture
    relation honestly (`cure_stricter`/`idris_only` with the written reason that
    Cure's `String` *is* `List Char` by the operator's Option-A choice, §2.4).
    Do **not** silently label the divergence a bug.
- **Elaboration unit tests** (dependent pipeline only — ignore `compiler/*`,
  `types/*`):
  - `'a'` elaborates to `{:char_lit, 97}` of type `Char`.
  - `case c of 'a' -> … | _ -> …` (a `Char`-scrutinee literal **pattern**, not
    just an expression) elaborates and dispatches correctly on both the
    matching and non-matching branch — proves the `try_literal_match`
    additions in §4.2 (`primitive_scrut_kind`/`literal_of?`/`lit_core`/
    `literal_chain`), which are a separate code path from plain char-literal
    *expression* elaboration and easy to skip if only the expression path is
    implemented.
  - `"abc"` elaborates to the `List(Char)` cons spine and **emits** `[97,98,99]`
    (assert the emitted Erlang abstract form / a run through the dependent
    pipeline, not the classic codegen).
  - `String` in a signature resolves to `List(Char)`.
  - `to_binary("abc")` runs and yields `<<"abc">>`; `from_binary(<<"abc">>)`
    yields `"abc"` — round-trip on generic-unix AtomVM (per the esp32-beam
    superproject's `CLAUDE.md`, "validate on host before any claim"; note that
    file lives one level up, at the esp32-beam repo root, not in this cure-lang
    worktree). **Concrete locus** (not named elsewhere in this spec): a small
    demo `.cure` module calling `to_binary`/`from_binary`, built via `cure`
    (`mix escript.build`) and run through `phase35/run-on-unix.sh` against the
    generic-unix AtomVM build — the same harness `phase35/*.cure` feature
    probes already use. This is a cross-repo verification step (cure-lang →
    esp32-beam integration), separate from the in-repo `mix test`/Antigen/oracle
    gates above; do not conflate the two when reporting this wave's status.
- **Ratchet:** value-surface KEEP count moves by ≥1 (either legacy `Std.String`
  flips, or a new demo module KEEPs — §4.7 scope guard). Record the before/after
  count. No prior-KEEP regression; oracle replay green before commit.

## 9. Sequencing & risk
- The `Char` kernel slice is the only TCB touch: mechanical (mirror `Int`),
  Agda/Idris-aligned, blanket-approved in *direction* but gated by the full
  Antigen + suite run. Land it first, green, before the elaboration/emit slices.
- Everything else is E/C layer, low risk, reusing the `:list` path (Wave 4) and
  the native-cons `List` emit already in place — **with one specific exception
  to call out as a risk, not just low-risk boilerplate:** the char literal
  *pattern* work (§4.2's `try_literal_match`/`primitive_scrut_kind`/
  `literal_of?`/`lit_core`/`literal_chain` additions, `elaborator.ex:2679-2798`)
  is a separate code path from char literal *expression* elaboration and is
  easy to implement-and-forget if work stops once `'a'` elaborates as an
  expression — verify `case c of 'a' -> … | _ -> …` explicitly (§8) before
  declaring the elaboration slice done.
- **`type Binary = |` (§4.6) lands next, after `Char` but before `to_binary`/
  `from_binary` and before §4.7's Unicode-heavy-ops migration** — both of the
  latter reference `Binary` as a param/return type and cannot elaborate without
  it existing first. This is a std-level addition (zero-constructor inductive,
  precedented by `Std.Decision.Empty`), **not** a second TCB/kernel touch — the
  "`Char` is the only kernel addition" claim above is about `lib/cure/core/*.ex`
  specifically and still holds with `Binary` added at the std/elaborator level.
- Ghost-writer commits (`--author="Made In Heaven <madeinheaven@madeinheaven.com>"`,
  no co-sign), explicit-pathspec staging only, one build at a time. Stay on the
  existing `autopilot/kernel-parity-batch` worktree (operator preference — no new
  worktree per sub-feature).

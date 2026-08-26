# Precedence Groups + Operator Overloading — Design

*2026-07-18. feature/idris-parity.*

## Goal

Replace Cure's hardcoded operator system with a **declaration-driven** one, in the
shape Swift uses: named **precedence groups** with relative ordering and
associativity, and **fixity declarations** that attach an operator — symbolic
*or* a word — to a group. Every overloadable operator then desugars to a call to
an ordinary (overloaded) function of the same name, resolved by the
type-directed overload machinery already in the tree. `a and b` becomes a call
to `and` (→ `Std.Bool.and`); `a + b` becomes a call to `+` (→ the `Additive`
method); a user can declare their own `infix <?>` and give it meaning with an
ordinary function.

The end state: the compiler owns *no* fixed list of operators. `Precedence.ex`'s
static binding-power table is gone; the built-in operators are declared in the
standard library exactly as a user's would be, with the old table's numbers as
the seed precedences.

## Why now

This is the spec the overload work explicitly deferred to. `Std.Semigroup`,
`Std.Ord`, and `Std.Bool` operator routing already live *ad hoc* in the
elaborator; type-directed overload resolution (merged) is the engine that makes
"operator = overloaded function" real. The remaining blocker is that several
built-in operators have no function to resolve *to* — most of arithmetic — and
that operator-named functions can't be written because the lexer steals the
tokens. Both are addressed here.

## Non-goals / YAGNI

- **No new coherence policy.** Global uniqueness + named-instance escape hatch
  stays exactly as-is. We are not adopting Lean's overlapping-instance search.
- **No reducibility knob.** Every type synonym stays transparent to instance
  resolution (today's behavior). A Lean-style `abbrev`/`def` distinction for a
  `newtype`-style opaque synonym is a *future* lever, not part of this.
- **No custom precedence arithmetic exposed to users beyond `higher_than` /
  `lower_than` / `associativity`.** No numeric priorities in the surface syntax
  (Swift dropped these for the same reason — relations compose, numbers don't).
- **Built-in syntactic operators stay syntactic** (see §4.1). `.`, `|>`, `<-|`
  (Melquiades), `=`/`+=`, `..` participate in the precedence table but keep
  fixed compiler meaning; they are **not** overloadable typeclass methods.
- **TCB is untouched.** Operators erase to function calls before Core;
  precedence is a parse-time concern; interfaces/coherence are E-layer. The
  kernel never sees an operator or a precedence group.

## Enabling property (why this is tractable in Cure)

Cure has **no juxtaposition application** — calls are always parenthesized
(`f(x)`), never `f x`. So in operator position (immediately after a complete
left operand) an identifier can *only* be an infix operator; there is no
`f x`-vs-`x and y` ambiguity that makes word-operators hard in ML/Haskell.
`a and b` is unambiguous: after `a`, the identifier `and` is looked up in the
fixity table and, being declared infix, parses as one. This is what makes
words-as-operators a clean addition rather than a grammar overhaul.

---

## Step 1 — Kernel-routed instance elaboration

*A self-contained cleanup that stands on its own and de-risks everything after
it. No new user-facing feature; existing typeclass tests are the oracle.*

### Problem

`Cure.Elab.Implementation` runs in the **register pass**, before any body (or
the instance head itself) is elaborated to Core. Because it has only the
*surface* head name and *surface* method-signature ASTs at that point, it
hand-rolls two operations the kernel already owns:

- **`normalize_head/2`** — chases type synonyms on the surface to produce a
  single coherence-key atom, so `for Int` and `for MyInt` (where
  `MyInt = Int`) file under one key. This duplicates the kernel's δ-reduction.
- **`check_method_signature` / `alpha_equal?`** — a second, weaker
  structural-equality-modulo-renaming over surface type ASTs, verifying an
  instance's method signature matches the interface's (head-substituted). This
  duplicates the kernel's conversion.

Neither reimplementation is forced by the type system; both are forced by the
head type not being elaborated yet at registration time.

### How Idris/Lean/Agda avoid this

None of them key an instance on a *spelling*. The head is obtained by reducing
an already-elaborated type with the kernel's own reduction, and instance
matching is the same conversion that governs every other type equality:

- **Lean 4** indexes instances in a discrimination tree whose keys are head
  symbols computed via `whnf` at `reducible` transparency; a `def`-synonym stays
  opaque, an `abbrev` unfolds.
- **Agda** reduces the goal to WHNF, reads the head symbol, filters candidates,
  checks by unification, demands uniqueness.
- **Idris 2** resolves via auto-implicit search, unifying candidate types up to
  definitional equality.

### Change

Elaborate the instance head **eagerly** to a Core type, then:

1. **Coherence key = whnf head symbol.** Compute the key by `Normalise.whnf`-ing
   the Core head and reading its head constructor (`{:vint_type}` → `:Int`,
   `{:vdata, name, …}` → `name`). This is Lean's key-computation, using
   `Normalise.whnf/3`, which already exists and is what `Conv` uses. Because
   Cure's whnf δ-unfolds certified globals, a `typealias MyInt = Int` (a nullary
   def) unfolds exactly as `normalize_head` did today — **semantics unchanged,
   mechanism moved onto the kernel.** `normalize_head/2` and its `head_atom/4`
   helpers are **deleted**. What remains is a trivial total readback of a whnf'd
   type's head — not a synonym-chasing recursion.

2. **Signature conformance = kernel conversion.** Verify the instance method's
   elaborated Pi type is convertible to the interface method's Pi type with the
   head variable substituted by the instance head, via the kernel's conversion.
   `check_method_signature`, `alpha_equal?`, `alpha`, `alpha_name`, `type_var?`
   are **deleted**. Diagnostics must still point at the *implementation* (the
   reason the surface check existed): on conversion failure emit
   `{:method_signature_mismatch, iface, method}` sited at the instance, not a
   bare downstream `conversion_failure`.

*What is explicitly NOT taken from Lean:* the discrimination tree and best-first
search. Under global-uniqueness coherence, an exact single-atom key with direct
lookup is correct and simpler; Cure already keys on the outermost constructor
only (it drops params/indices — one `Semigroup for List(t)` regardless of `t`),
so the key is one atom, not a spine.

### Scope note

Global uniqueness, the coherence registry shape, mangled naming
(`__impl_<Iface>_<Head>_<method>`), dictionary threading, and named-instance
binding are **unchanged**. Only *how the head becomes a key* and *how a
signature is checked* move onto the kernel.

### Testing

- Existing typeclass / coherence / anonymous-instance suites stay green
  (differential oracle: same instances resolve, same overlaps reject).
- New: `implementation Eqs for MyInt` where `MyInt = Int` collides with
  `implementation Eqs for Int` under the whnf key (was already true; now via
  kernel) — regression pin.
- New: an instance whose method signature disagrees with the interface
  (`fn eq(x, y) -> Int` for `Equatable`) rejects with
  `{:method_signature_mismatch, …}` sited at the implementation.

---

## Step 2 — Expanded typeclasses (no syntax change)

*Give every built-in operator a real function to resolve to, on a minimal
conformance basis, and re-route the elaborator's existing operator handling
through it. `a + b` still **parses** exactly as today; it now **elaborates** to
an interface method instead of a builtin-op spine. Differential oracle: every
operator expression evaluates to the same value as before.*

### 2.0 Backtick-escaped identifiers (prerequisite slice)

Introduce `` `name` `` as an identifier escape at both definition and call
sites, so a function can *be named* by an operator lexeme
(`fn `+`(a, b) -> …`, `` `and`(x, y) ``) even while that lexeme is still a
keyword/operator token. Lexer: a backtick opens an escaped-identifier token
whose body is taken verbatim to the closing backtick. Parser: an escaped
identifier is an ordinary name everywhere a name is legal. This is the enabler
the whole flip rests on — it lets `Std.Bool.and` stop being a keyword-blocked
special case and become an ordinary, overloadable definition.

### 2.1 Superinterface constraints (new machinery)

`interface Comparable(t) requires Equatable(t)` — a superinterface clause.
Effects:

- **Conformance obligation.** Registering `implementation Comparable for T`
  requires an `Equatable` instance for `T` (the whnf key of `T`) to exist;
  otherwise `{:missing_superinterface, Comparable, Equatable, T}`.
- **Default-body scope.** A `Comparable` default method may call `Equatable`'s
  methods — the superinterface dictionary is in scope. This is load-bearing, not
  decorative: it is what lets `compare`'s default body (below) typecheck.

Defaults already exist (`Cure.Elab.Implementation` fills an omitted method from
the interface default with the head substituted); superinterface constraints are
the only genuinely new interface feature.

### 2.2 Equatable / Comparable on the `==`,`<` basis

The primitives are `==` (Equatable) and `<` (Comparable); the three-way
`Ordering` and every other comparison operator are **derived**. This is Swift's
basis, and it is deliberately chosen over the current `compare`-as-sole-method
design:

- **Hot operators dispatch directly.** `a < b` → the `<` method, `a == b` → the
  `==` method — no constructing a `LessThan` value and pattern-matching an
  `Ordering` on the two most common operators. On AtomVM/ESP32 that round-trip
  is an allocation-and-match per comparison in any hot loop; the tripartite ADT
  should be opt-in for three-way work, not a tax on `<`.
- **`==` stays primitively correct.** Deriving `==` from `compare` makes
  `NaN == NaN` true (`compare` returns `EqualTo`); with `==` primitive it is the
  IEEE equality, correctly false. No Float override needed to be correct.
- **The superinterface earns its keep.** `compare`'s derived default is
  `if a == b then EqualTo else if a < b then LessThan else GreaterThan` — it
  references `==` (from `Equatable`) *and* `<` (from `Comparable`), so
  `Comparable requires Equatable` is exactly what makes it typecheck.
- **Nothing lost vs the former.** `compare` is a derived *default*, still present
  for sorting, and a type where three-way is hot can *override* it with a direct
  implementation.

Shape (method names are the operator lexemes, backtick-escaped where needed;
default bodies use `pickup`/explicit form, never infix operators, to avoid
operator-in-its-own-definition regress — as `ne` already does):

```
interface Equatable(t)
  fn `==`(a: t, b: t) -> Bool          # sole obligation
  # `!=` derived: not (a == b)

interface Comparable(t) requires Equatable(t)
  fn `<`(a: t, b: t) -> Bool           # sole obligation
  # `<=`, `>`, `>=` derived from `<` (and inherited `==`)
  # `compare`/Ordering derived; overridable
```

- A fully-ordered type conforms **both** `Equatable` and `Comparable` (two
  `implementation` blocks), exactly as Swift's `: Comparable` also satisfies
  `Equatable`. In stdlib this is trivial — Int/Float/String/Char each supply
  both leaves as primitives.
- **Leaf primitives, not operators.** `Equatable for Int`'s `==` body is the
  primitive `int_eq`, **not** `a == b` — otherwise the post-flip desugaring
  `==` → `==` loops. Every interface leaf bottoms out in a builtin-op primitive.
- Float overrides nothing for correctness (`==` primitive is right); it may
  override `compare` if it wants BEAM term-order semantics for NaN.
- Fill the coverage hole: add `Equatable for Char`.

### 2.3 Arithmetic interfaces

No arithmetic interface exists today; `+ - * / %` are builtin-op spines with
nothing to resolve to. Introduce a **split** family rather than one `Num`,
motivated by `Std.Units` (a `Duration` has `+`/`-` but no
`Duration * Duration -> Duration`):

```
interface Additive(t)
  fn `+`(a: t, b: t) -> t
  fn `-`(a: t, b: t) -> t
  fn negate(a: t) -> t                 # unary minus wires here in Step 3

interface Multiplicative(t)
  fn `*`(a: t, b: t) -> t

interface Divisible(t)
  fn `/`(a: t, b: t) -> t
```

- Int and Float conform `Additive`, `Multiplicative`, `Divisible`; leaf bodies
  are the primitives (`int_add`, `float_mul`, …).
- **`%` (remainder)** is integer-specific (BEAM `rem`; no clean total Float
  modulo on AtomVM). It is **not** in `Divisible`. The plan pins its home; the
  recommended default is an `Integral(t)`-style interface (or an Int-only
  method) carrying `` `%` ``. Design doc leaves the exact interface name to the
  plan; the *decision* is: `%` does not force Float to implement a broken
  modulo.
- `<>` and non-numeric `+` continue through `Std.Semigroup.combine`, unchanged;
  numeric `+` now goes through `Additive`.

### 2.4 Bool connectives

`and`/`or`/`not` become ordinary backtick-named functions in `Std.Bool`
(`` `and` ``, `` `or` ``, `` `not` ``), monomorphic on `Bool` (no interface —
YAGNI; there is one conformer). Bodies are the existing `case`/`pickup`
eliminations. The elaborator's `and`/`or`/`not` special-casing is retired in
favor of resolving these names.

### 2.5 Re-route existing operator elaboration

`elaborate_expr_typed({:binary_op, …})` and the prefix/`not` paths stop building
builtin-op spines directly and instead **desugar to a call to the operator's
name**, resolved by overload resolution:

- `a + b` → call `+`(a, b) → `Additive`'s method → (for Int) `int_add`.
- `a < b` → call `<`(a, b) → `Comparable`'s method.
- `a == b` → call `==`(a, b) → `Equatable`'s method.
- Primitive operands still bottom out in the same builtin-op primitives, now one
  dispatch away (the interface leaf). The overload resolver's present-param
  type-direction picks the Int vs Float leaf, exactly as it picks any overload.

**Sole-route invariant.** After this step, the typeclass method is the *only*
way to reach `==`/`!=`/`<`/`<=`/`>`/`>=` in the language. `build_binop`'s
per-operand-type hardcoding for these operators is **removed**, not kept as a
parallel path: the primitive equality/ordering primitives (`int_eq`, `float_eq`,
`struct_eq`, `int_lt`, `float_lt`, `Std.Bool.` `` `eq` ``) live *only* inside the
leaf instance bodies (`Equatable for Int`, …). Because instance selection is
resolved statically when the operand type is concrete, `1 == 2` lowers to
exactly the same emitted Core spine as today — the fast path is preserved as an
*optimisation of the single route*, never as a second definition that could drift
or that a user cannot override.

**Universal structural equality becomes an auto-derived instance, not a
fallback.** Today `struct_eq` gives `==` on *any* ADT with zero instances. To keep
that ergonomics while making the typeclass the sole route, the elaborator
**auto-derives a structural `Equatable` instance** for every data type that lacks
a hand-written one (reusing the approved `deriving` machinery). The derived
instance *is* the field-wise `struct_eq` equality reached through coherence — so
`==`-on-anything is retained, but now:
  - it is **overridable** for user-owned types (a hand-written `Equatable for T`
    supersedes the derived one), whereas today's builtin `struct_eq` cannot be
    overridden;
  - the built-in **primitives stay canonical and locked** — global coherence
    forbids a second `Equatable for Int`, so `==` on the primitives means the
    same thing in every module, exactly as today.
  - Derivation is **per-type** (synthesised only when no explicit instance
    exists), *not* a blanket `Equatable for any-data` instance — a blanket
    instance plus specific user instances is the overlapping-instance case global
    coherence forbids.
  - `Comparable`/`<` is **not** auto-derived: there is no universal structural
    ordering today, so `Comparable` stays opt-in. `<` on a type with no
    `Comparable` instance is a compile error (see below).

**Ambient availability + bootstrap order.** Because `==`/`<` now *require* the
interfaces to be resolvable at every use site, `Std.Equatable` and
`Std.Comparable` (and their core-type instances) are marked `@prelude`-ambient so
`1 == 2` keeps working with no import, as today. Step 2.6 must **audit the stdlib
module DAG**: no module compiled *below* `Std.Equatable` may use `==` (the
primitive leaf definitions such as `Std.Bool.` `` `eq` `` are plain functions, not
`==`, so they are safe). When `==`/`<` is used on a type for which no instance
exists and (for `==`) structural derivation cannot apply, the elaborator rejects
with a clear `{:no_instance, Equatable | Comparable, T}` error rather than
silently falling back.

**No parse change in Step 2.** `{:binary_op}` nodes are still produced by the
current parser; only their elaboration target moves. This is what makes the
differential oracle exact.

### Testing

- Differential: a corpus of operator expressions (arithmetic, comparison,
  equality on primitives / ADTs / lists, boolean connectives) evaluates
  identically before and after re-routing.
- New: minimal-basis conformance — a user `struct` conforming only
  `Comparable`'s `<` (and `Equatable`'s `==`) gets `<= > >= != compare` for
  free; omitting the required `Equatable` instance rejects with
  `{:missing_superinterface, …}`.
- New: Float `NaN == NaN` is `false`; derived `NaN <= NaN` consistent with the
  primitive basis.
- New (auto-derive): a user ADT with **no** hand-written `Equatable` gets
  structural `==` for free (field-wise), evaluating identically to today's
  `struct_eq`; a user ADT **with** a hand-written `Equatable for T` uses that
  instance instead (override), proving the derived instance is superseded, not
  duplicated (no overlap error).
- New (sole route): `==` on the primitives is not user-overridable — a second
  `Equatable for Int` is rejected by coherence, confirming primitives stay
  canonical.
- New (no-instance): `<` on a type with no `Comparable` instance rejects with
  `{:no_instance, Comparable, T}` (no silent structural fallback for ordering).

---

## Step 3 — Precedence groups + fixity declarations + the flip

*The syntactic layer. The static `Precedence.ex` table is replaced by a table
assembled from declarations; the lexer stops owning a fixed operator set; every
operator expression now parses via the declared table and (for overloadable
operators) desugars to the named calls Step 2 made resolvable.*

### 3.1 Two kinds of operator

The precedence system governs parsing for **both**, but only the first routes
through interfaces:

- **Overloadable operators** — `+ - * / % == != < > <= >= <> and or not` and any
  user-declared operator. Desugar to an overloaded-name call; meaning comes from
  functions/interfaces (Step 2).
- **Built-in syntactic operators** — `.` (field access), `|>` (pipe), `<-|`/`✉`
  (Melquiades send), `=`/`+=`/`-=`/`*=`/`/=` (assignment), `..`/`..=` (range).
  They have precedence-group membership so they slot into the table, but their
  meaning is fixed compiler machinery and they are **not** overloadable. Their
  precedence declarations are marked `builtin` so a user cannot rebind them to a
  function.

### 3.2 Surface syntax

Precedence group:

```
precedencegroup Additive
  associativity: left
  higher_than: Comparison
  lower_than: Multiplicative      # relations may be given from either side
```

- `associativity:` ∈ `left | right | none` (`none` = the existing non-assoc
  rejection: `a == b == c` is a parse error).
- `higher_than:` / `lower_than:` name other groups; the parser derives a partial
  order and computes binding powers from it (topological, not literal numbers).
- Two groups with no ordering relation between them are **incomparable**: using
  their operators adjacently without parentheses is an
  `{:ambiguous_precedence, g1, g2}` error (Swift's behavior). This is *stricter
  and safer* than today's total numeric order and is the reason relations beat
  numbers.

Fixity declaration (the operator → group binding; meaning is separate):

```
infix `<?>` : Additive
infix and : LogicalConjunction
prefix not : Negation
postfix `!` : Postfix
```

- The operator token is a symbolic lexeme (backtick-escaped) or a word
  (bare identifier). `infix`/`prefix`/`postfix` set fixity.
- The declaration binds fixity + group only. Meaning is whatever
  function(s)/interface method(s) carry that name — resolved by Step 2's
  machinery. A fixity declaration with no corresponding function is a *parse*
  success but an *elaboration* error at any use site (`{:no_operator_meaning,
  name}`), pointing the user at "declare a function named `<?>`".

### 3.3 Where the built-in operators are declared

The core operators move to a preloaded stdlib module (`Std.Operators`, `@group(:core)`,
consumed by `Cure.Stdlib.Preload`), declared with the **same associativity and
relative order as today's `Precedence.ex` table** (the old numbers seed the
group ordering). This is the "compiler owns no operator list" end state: the
built-ins are declared exactly as a user's would be.

**Bootstrapping.** `Std.Operators` and the interface/connective modules that *define*
operator meanings must parse before their own operators are available. They
already avoid infix operators in the relevant bodies (interface leaves are
primitives; defaults use `pickup`; connectives use `case`) — so the bootstrap
module set is parseable with an empty/minimal fixity table. The plan pins the
preload order: fixity declarations load, then user modules parse against the
assembled table.

### 3.4 Parser mechanics (replacing `Precedence.ex`)

- **Lexer**: stop emitting dedicated tokens for the flippable operators. Symbolic
  operator characters lex into a generic operator-lexeme token; words lex as
  ordinary identifiers. The dedicated tokens that remain are only the built-in
  *syntactic* ones (`.`, `|>`, `<-|`, `=`/`+=`…, `..`) whose grammar is special.
- **Fixity table**: a compile-session map `lexeme → {fixity, group, assoc}`
  assembled from all in-scope fixity declarations, replacing the static
  `infix_bp/1`. Binding powers are computed once from the group partial order.
  Keep it an O(1) map (heed the parser-quadratic-token-lookup finding: no
  per-token linear scans).
- **Pratt loop**: in operator position, consult the fixity table by lexeme —
  symbolic *or* word. Unlisted identifier in operator position ⇒ not an operator,
  stop (the no-juxtaposition property makes this unambiguous). Non-assoc and
  incomparable-group rejection happen here.
- **Node**: overloadable operators still build `{:binary_op, [operator: name],
  …}` (or a prefix/postfix analogue) so Step 2's elaboration is reused verbatim;
  the `operator:` is now the resolved lexeme/name. Built-in syntactic operators
  build their existing dedicated nodes (`:send`, `:pipe`, `:attribute_access`,
  `:assignment`, `:range`).

### 3.5 Unary minus / `negate`

Prefix `-` is declared `prefix - : <group>` and desugars to a call to `negate`
(the `Additive` method), or equivalently to the `-`/1 overload member — the
overload resolver already discriminates by arity, so binary `-`/2 and unary
`-`/1 can share the name. The plan pins which spelling; recommended: prefix `-`
→ `negate` for an explicit method name.

### Testing

- Every existing operator expression in the test corpus parses and evaluates
  identically (the Step 2 differential corpus, re-run through the new parser).
- Word operators: `a and b`, `not x` resolve to `Std.Bool` functions and match
  the old keyword-operator results.
- Custom operator: declare `precedencegroup` + `infix <?>` + a function named
  `<?>`, use it, check associativity and precedence against a hand-computed
  expectation.
- Errors: incomparable groups without parens ⇒ `{:ambiguous_precedence, …}`;
  non-assoc chaining ⇒ parse error; fixity decl with no function ⇒
  `{:no_operator_meaning, …}` at use.
- Built-in syntactic operators (`|>`, `.`, `<-|`, `=`, `..`) unchanged; a user
  attempt to rebind one ⇒ rejected (`builtin`).

---

## Risks

- **Bootstrapping order** (Step 3) is the sharpest risk: the modules that define
  operators must parse before those operators exist. Mitigated by the
  no-infix-in-definitions discipline the stdlib already follows and an explicit
  pinned preload order; a bootstrap test parses `Std.Operators` + interface modules
  against an empty fixity table.
- **Diagnostic regressions.** Moving the signature check onto kernel conversion
  (Step 1) risks worse errors; mitigated by the sited
  `{:method_signature_mismatch, …}`. Incomparable-precedence errors are new
  surface area; they must name both groups and suggest parentheses.
- **Parser performance.** The fixity table must stay O(1) per lookup and be
  assembled once per session (not per expression); heed the existing
  parser-quadratic-token-lookup finding.
- **`%` / division partiality.** Left as a pinned plan decision rather than
  forced into a shared interface; the design commitment is only that Float is not
  made to implement a broken `%`.

## What stays out of the TCB

Everything. Step 1 moves instance elaboration *onto* existing kernel entry
points (`Normalise.whnf`, `Conv`) but adds nothing to `lib/cure/core/**`.
Steps 2–3 are surface + elaborator + parser. Operators and precedence groups
have no Core representation; they are gone before the kernel sees a term.

## Step boundaries (independently shippable)

1. **Kernel-routed instance elaboration** — green when existing typeclass suites
   pass through the whnf key + kernel signature check and the two surface
   reimplementations are deleted.
2. **Expanded typeclasses** — green when the operator differential corpus is
   byte-identical with operators re-routed through Additive/Multiplicative/
   Divisible/Equatable/Comparable/Bool, on the minimal `==`,`<` basis, with
   superinterface constraints enforced.
3. **Precedence groups + flip** — green when `Precedence.ex`'s static table is
   gone, built-in operators are declared in `Std.Operators`, word + custom operators
   work, and the differential corpus re-runs identically through the
   declaration-driven parser.

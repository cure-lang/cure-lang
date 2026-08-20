# Macros

`macro` is Cure's **one** frontend extension point. The compiler does not
contain a per-DSL parser: `fsm`, `actor`, `sup`, `app`, unit literals and regex
literals are all ordinary macros defined in `lib/std/*.cure` using exactly the
surface described here. Anything the standard library does to the grammar, your
library can do too.

Every `cure` fence in this document compiles against the tree as-is, and
`mix cure.check.docs` keeps it that way. Grammar fragments — rule shapes quoted
out of their container, excerpts of the `Std.Syntax` types, a template shown
because it *does not* parse — are `text` fences: they are not Cure source, and
there is no tag that would let them sit in a `cure` fence unchecked.

## 1. Quick start

```cure
mod Doubling
  macro Twice
    syntax twice <n: Code> becomes n + n
      example twice 21 expands 21 + 21

  fn start() -> Int = twice 21
end
```

Three things are happening:

- `macro Twice` opens a container, like `fsm`/`actor`/`sup`.
- `syntax twice <n: Code> becomes n + n` is a **rule**. Read it as a usage
  string: the user types `twice`, then any expression; the expansion is that
  expression added to itself.
- `example twice 21 expands 21 + 21` is a **worked example**, checked at compile
  time. Pin the wrong expansion and the build fails (§9).

A rule looks like what the user will type. That is the design constraint the
whole surface is built around: you define a macro by copying one example, not by
learning a grammar formalism.

## 2. The `macro` container

A macro is a module member. Its body is an indented block of these entries —
this list is exhaustive, and anything else is a parse error naming the
alternatives:

| Entry | Purpose | Section |
|---|---|---|
| `syntax <rule> becomes <template>` | hygienic template rule | §3, §5 |
| `syntax <rule> computed by <fn>` | rule expanded by a compile-time function | §6 |
| `syntax family <Name>` | a structured, indented body shape | §7 |
| `accepts <Family>` | the family this macro's body parses as | §7 |
| `expands with <fn>` | the function that turns that family into syntax | §7 |
| `literal <rule>` | a suffixed-literal rule (`5 tick`) | §4 |
| `explain` | per-failure-point error messages | §9 |
| `fail Name(p: T, …)` | an author-declared semantic failure point | §9 |
| `open <Category>` | mark a category other macros may extend | §3.3 |

The macro's own name may carry holes, which is how `fsm`/`sup`/`app` take the
name of the thing they generate:

```cure
macro TupleLenses                        # a plain name
macro app <name: ModuleName>             # one leading hole
macro fsm <name: ModuleName> with <data: Type>   # several
```

Doc comments (`##`) and blank lines inside the block are trivia and may appear
between entries.

## 3. Syntax rules

```
syntax <keyword> <segments…> [is <Category>] [where <Interface>(<capture>)]… [contextual] becomes <template>
syntax <keyword> <segments…> [is <Category>] [where …]… [contextual] computed by <function>
```

The first token after `syntax` is the rule's **dispatch keyword** — the word a
user types to reach this macro. Everything after it, up to the closing verb, is
the matched form.

`becomes`, `computed`, `by`, `is`, `contextual` and `where` are reserved across
the whole rule grammar; a rule cannot match a literal token spelled with one of
those words. Separately, `assert_type`, `rewrite`, `with`, `macro` and `have`
are reserved keywords a macro can never claim as its dispatch keyword.

### 3.1 Holes

A hole is `<name: Kind>`. The same `<name>` is the capture in the rule *and* the
splice in the template — one notation, symmetric:

```cure
mod Pairing
  macro Pair
    syntax pair <a: Code> to <b: Code> becomes %[a, b]
      example pair 1 to 2 expands %[1, 2]

  fn start() -> Tuple(Int, Int) = pair 1 to 2
end
```

Only these kinds change how a hole is *matched*; everything else falls through
to one shared behaviour:

| Kind | How it is matched |
|---|---|
| `Name` | exactly one identifier token, bound as a variable node |
| `ModuleName` | a dotted identifier path, bound as an atom literal |
| `Type` | the ordinary type-expression parser |
| `Parameters` | the ordinary typed-parameter parser — **the rule owns the surrounding parens**, so you get typed, graded, and implicit binders for free |
| `Int`, `Float`, `Atom`, `Bool` | an expression, then checked to be a literal of that subtype (otherwise `expected_literal_capture`) |
| `Code` | newlines are skipped first, then an expression — so a `Code` hole may open an indented block |
| *anything else* | an ordinary expression (`parse_expr`) |

That last row is the one to internalise. `<n: Number>`, `<e: Expression>`,
`<s: Statement>`, `<p: Pattern>` and `<t: Token>` are **not** distinct matchers —
each parses an expression, exactly as `<n: Foo>` would. Such a name is
documentation for your reader and a label in diagnostics; it is not a
constraint the parser enforces. If you need a real constraint, use one of the
rows above, a `where` obligation (§3.4), or check it in a `computed by`
expander (§6).

The richer vocabulary — `Pattern`, `Statement`, `Cases`, `Fields`,
`Declarations`, `ModuleBody`, `Token`, `Expression` — *is* meaningful in one
place: as a **`syntax family` field shape**, where it selects the derived field
type (§7.2). Do not carry that vocabulary back into `syntax` rules and expect
it to bite.

Four long-form holes exist for the raw/reader tier — capturing tokens the
ordinary expression parser should not interpret. Each is delimiter-bounded, and
the delimiter is what stops an indented block from swallowing the next literal
segment of your rule:

```text
<body: raw until dedent>           # verbatim tokens up to a delimiter
<body: delayed raw until dedent>   # …captured now, parsed later
<rhs: Code until dedent>           # an expression bounded by a delimiter
<decls: Declarations until dedent> # a declaration block in a positional slot
```

### 3.2 Repetition and optional groups

```text
syntax f(<args: Code>, ...)        # `...` — zero or more of the preceding segment
syntax listen (on <port: Number>)?  # ( … )? — an optional group
```

`...` always means *zero or more*. "At least one" is deliberately not a grammar
distinction: enforce it in the expander and emit a real explanation
("`reducer Door` declares no transitions") rather than a parse error saying
`expected Edge`.

### 3.3 Categories — `is`

`is <Category>` names the category a rule belongs to and creates it; no forward
declaration. Alternatives within a category are separate `syntax` lines, like
function clauses. `is` is a *suffix on a normal rule* — it does not replace the
closing verb, so every `is` rule still needs `becomes` or `computed by`:

```text
syntax emit <| <model: Code> <| <emission: Code>  is Action becomes …
syntax update <| <model: Code>                    is Action becomes …
```

Writing `syntax step <n: Code> is Leg` with no template is the error
`MACRO RULE NEEDS BECOMES [E094]`.

`open <Category>` marks a category that *other* macros may extend with their own
rules; extending a category that was never opened is rejected
(`closed_category_extension`), as is an extension that duplicates an existing
keyword (`ambiguous_macro_extension`).

### 3.4 Capture obligations — `where`

`where <Interface>(<capture>)` constrains a named capture to satisfy an
interface. The capture must be one this rule actually binds; naming a
non-existent one is a diagnostic listing the available captures. Obligations
also attach to `syntax family` fields (§7).

### 3.5 `contextual`

`contextual` before the closing verb marks a rule that only fires in a context
where its expansion makes sense, rather than claiming its keyword globally. The
whole `Std.Otp` `BeamOps` vocabulary (`beam_ops tell …`, `beam_ops call …`) is
declared this way.

## 4. Tier 1 — `literal` rules

The one narrow lexer extension: a numeric (or other literal) token juxtaposed
with a registered suffix.

```cure
mod Ticks
  macro Ticks
    literal <n: Number> tick becomes n * 1000

  fn start() -> Int = 5 tick
end
```

`literal` rules have no dispatch keyword — the use site is the literal itself.
They may close with `becomes` or `computed by` (also `computed directly by`).
Unlike `syntax` rules they are never required to carry worked examples.

Literal rules declared in the standard library are active in **every** file, the
same way `:syntax` prelude macros are.

## 5. Tier 2 — `becomes` templates

`becomes` takes a **single expression**, on the same line as the rule. It cannot
be an indented block:

```text
# does NOT parse
syntax dbl <n: Code> becomes
  let tmp = n
  tmp + tmp
```

Templates are hygienic: names introduced by the template cannot capture, or be
captured by, identifiers at the use site.

- `<fresh Name>` mints a readable unique name, identical at every mention within
  one rule — this is how `fsm <fresh Tick>` gets a stable-ish generated module
  atom. It is valid in binding positions too, including lambda parameters:
  `fn(<fresh tmp>) -> <fresh tmp>` binds both occurrences to one gensym.
- `<capture it>` is the marked, greppable escape for deliberate anaphora. It is
  never silent.

Templates may be recursive — a `becomes` may expand into its own or another
macro's syntax — provided the decreasing-input check passes.

## 6. Tier 3 — `computed by`

When the expansion depends on *analysing* the captured syntax rather than
re-arranging it, close the rule with `computed by <function>`. The function is
ordinary Cure, run on the host at compile time, over `Std.Syntax` values:

```text
macro RegexLiterals
  literal regex <pattern: String> <flags: String> computed by expand_literal

fn expand_literal(input: Syntax) -> MacroResult = match children(input)
  [pattern_syntax, flags_syntax] -> match leaf_value(pattern_syntax)
    SStr(pattern) -> …
    _ -> reject(Failure(:InvalidRegexPatternInput, []))
  _ -> reject(Failure(:InvalidRegexLiteralInput, []))
```

(from `lib/std_deps/regex/regex_syntax.cure`)

An expander returns `MacroResult`:

```text
type MacroResult =
  | Expanded(Syntax)
  | Rejected(List(Diagnostic))
```

built with `expand(syntax)`, `reject(diagnostic)`, or
`reject_all(diagnostics)`. A `Diagnostic` is just a `Syntax` — conventionally
`Failure(:some_reason, [])`.

Compile-time functions are **pure**: they see only the quoted input and the
reflection API. No ambient effects, because build determinism is
non-negotiable.

## 7. Structured macros — `syntax family`

Template and computed rules match a *line*. A `syntax family` describes an
indented **body shape**, which is what `fsm`, `sup` and `app` need. Three
entries work together:

- `syntax family <Name>` — declare the shape
- `accepts <Family>` — the macro's body parses as this family
- `expands with <fn>` — the function that turns the parsed family into syntax

```cure W000
mod Tables
  use Std.Syntax

  macro table <name: ModuleName>
    syntax family TableDefinition
      key Name
      optional label Expression
    accepts TableDefinition
    expands with derive_table

  fn derive_table(name: ModuleNameSyntax, definition: TableDefinitionSyntax) -> Syntax =
    let name_syntax: Syntax = name
    let module_name: SynLit = match name_syntax
      Leaf(_, _, SAtom(value)) -> SAtom(value)
      _ -> SStr("Cure.Generated.Table")
    lift_module(module_name, :none, [
      function("key_name", [], variable("Atom"), atom_literal(:isbn))
    ])

  table Books
    key isbn
end
```

That example compiles, but it also emits `COMPILER WARNING [W000] behaviour
none undefined`, because `lift_module` always attaches a `-behaviour`
attribute — see §13. That is why the fence is tagged `cure W000`: the
documentation checker requires the warning to still be there, so the day
`lift_module` stops emitting it this example fails and gets rewritten. Real
generated modules name a real behaviour (`:gen_server`, `:gen_statem`,
`:supervisor`, `:application`), which is what every stdlib container does.

### 7.1 Family members

A family body holds three kinds of line:

```text
syntax family TransitionTableDefinition
  optional initial Name                       # a field
  repeated terminal Name                      # a field, zero or more
  one_or_more transitions TransitionDefinition # a field, at least one
  includes SomeOtherFamily                     # splice another family's fields
  syntax <from: Name> --<event: Name>--> <to: Name>  # a production alternative
```

- **Fields** are `[cardinality] <field-name> <Shape>`. Cardinality is one of
  `optional`, `repeated`, `one_or_more`, or omitted for required. `Shape` is a
  hole kind (§3.1) or another family's name. Fields may carry `where`
  obligations.
- **`includes <Family>`** splices another family's fields in.
- **`syntax <production>`** declares an alternative form for the family itself —
  this is how `fsm`'s four arrow shapes are expressed.

### 7.2 The generated record type

Each family auto-derives a record the expander receives. The type name is the
family name with `Syntax` appended (`TableDefinition` → `TableDefinitionSyntax`),
and each field is reachable by name (`definition.key`, `definition.transitions`).

Field types follow the shape:

| Field shape | Derived type |
|---|---|
| `Name`, `ModuleName`, `Type`, `Pattern`, `Expression`, `Statement`, `Code`, `Cases`, `Fields`, `Declarations`, `ModuleBody`, `Token` | `<Shape>Syntax` — e.g. `Cases` → `CasesSyntax` |
| `Parameters` | `List(Syntax)` |
| `Int`, `Float`, `Atom`, `Bool` | the scalar type itself |
| `Syntax`, or any name not listed above | `Syntax` |

Every `…Syntax` alias *is* `Syntax` (see `lib/std/syntax.cure`) — they are
readability in the expander's signature, not separate representations.

Cardinality then wraps that type: `repeated`/`one_or_more` give
`List(<base>)`, and `optional` gives `Std.Option.Option(<base>)`. So
`optional label Expression` arrives as
`Std.Option.Option(ExpressionSyntax)`, and `one_or_more children ChildDefinition`
as `List(ChildDefinitionSyntax)`.

`one_or_more` and `repeated` derive the same type; they differ at parse time.
An absent `repeated` field arrives as `[]`, an absent `optional` field as a
not-present option, and an absent `one_or_more` field is the error
`missing_syntax_family_field`, reported at the end of the body where the
missing section should have gone.

This is the one place cardinality is enforced for you. The `...` repetition in a
*rule segment* (§3.2) is always zero-or-more, with no `one_or_more` counterpart.

The expander's parameters are the macro head's holes followed by the family
value: `macro table <name: ModuleName>` + `accepts TableDefinition` gives
`fn derive_table(name: ModuleNameSyntax, definition: TableDefinitionSyntax) -> Syntax`.

### 7.3 Family validation

`accepts`/`expands with`/`syntax family` are checked as a set before anything
else runs. The rejections, all reported as `invalid macro family`:

`accepts_without_syntax_family`, `accepts_without_expander`,
`expander_without_accepts`, `multiple_accepts_declarations`,
`multiple_expands_declarations`, `unknown_syntax_family`,
`duplicate_syntax_family`, `duplicate_syntax_family_field`,
`syntax_family_cycle`.

## 8. The quoted-AST API — `Std.Syntax`

`lib/std/syntax.cure` is the whole compile-time surface. The core type reflects
the parser's `{tag, meta, third}` node:

```text
type Syntax =
  | Node(Atom, List(Attr), List(Syntax))   # a tagged node with children
  | Leaf(Atom, List(Attr), SynLit)         # a tagged scalar
  | Raw(SynLit)                            # reflected opaquely
  | Quoted(Syntax)
  | Failure(Atom, List(Syntax))            # a diagnostic

type Attr = KV(Atom, SynLit)

type SynLit =
  | SInt(Int) | SChar(Char) | SFloat(Float) | SStr(String)
  | SBool(Bool) | SAtom(Atom) | SList(List(SynLit))
  | SSyntax(Syntax) | SMap(List(SynPair)) | SOpaque
```

Source positions are deliberately absent: the expansion is re-elaborated, so
generated syntax carries no authored coordinates (the K3 firewall).

**Inspection.** `tag/1`, `has_tag/2`, `attrs/1`, `children/1`, `leaf_value/1`,
`attr/2`, `attr_atom_is/3`, `is_variable_named/2`, `constructor_name/1`,
`expansion_context/1`, `context_attr/2`.

**Construction.** `node/3`, `leaf/3`, `variable/1`, `caller_identifier/1`,
`fresh/1`, `atom_literal/1`, `integer/1`, `call/2`, `parameter/2`,
`parameter_linear/2`, `function/4`, `match_arm/2`, `guarded_match_arm/3`,
`alias_node/2`, `enum_type/2`, `enum_variant/1`, `block/1`, `use_module/1`.
Record-shaped variants (`ParameterSpec`, `FunctionSpec`, `ModuleSpec`,
`AliasSpec`, with `parameter_from`/`function_from`/`module_from`/`alias_from`)
keep builder calls readable.

**Quoting.** `quote <expr>` builds a `Syntax` value from literal Cure source
instead of assembling builder calls by hand. Inside a quotation there are two
splice forms, and the difference matters:

| Form | Expects | Effect |
|---|---|---|
| `$(e)` | `e : Syntax` | fills **one** child position |
| `$(e ...)` | `e : List(Syntax)` | **flattens** the list into the enclosing node's child sequence |

`$(e ...)` is the Scheme `,@` analogue — reach for it whenever you are splicing
a repeated capture or a `repeated`/`one_or_more` family field, where the count
is not known at authoring time.

**Emitting a module.** `lift_module(name, behaviour, declarations)` mints a
compiled unit; `lift_module_isolated/3` does the same but does not inherit the
defining module's imports. This is how every OTP container is built —
`Std.ActorBehavior` wraps it as `actor_module` (`:gen_server`),
`state_machine_module` (`:gen_statem`), `supervisor_module` (`:supervisor`),
`application_module` (`:application`). Two hard constraints, both worth knowing
before you debug them (§13): the module name **must** match
`Cure.<Pascal>(.<Pascal>)*`, and a `-behaviour` attribute is always attached.

## 9. Self-proving macros

This is the part that makes macros safe to hand to strangers, and it is opt-in
by a single keyword.

### 9.1 Worked examples

```text
syntax twice <n: Code> becomes n + n
  example twice 21 expands 21 + 21     # pin the expansion
  example twice 21 expands : Int       # or pin only its type
```

The example block is indented beneath the rule. The use site is captured as raw
tokens and pushed back through the rule; the result is compared with the pin.
A mismatch is a build failure that quotes both the rule and the pin:

```
-- MACRO EXAMPLE HAS THE WRONG EXPANSION [E092] --

Macro example(s) do not match their actual expansions: twice.

3 |     syntax twice <n: Code> becomes n + n
  |     ------------------------------------ this rule owns the failing example
4 |       example twice 21 expands 21 * 2
  |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ this pin does not match the actual expansion

Hint: Update the pinned expansion or fix the macro rule
```

Examples you *do* write are always checked, whether or not you write `explain`.

### 9.2 `explain` and `fail`

`explain` gives a message per structural failure point. Clauses use `=>`, and a
point is a failure **category**, or `keyword "word"` for a literal token:

```cure
mod Guarding
  macro Guarded
    syntax only <n: Number> becomes n + n
      example only 3 expands 3 + 3
    explain
      Number => "only needs a literal number, as in `only 3`"
      keyword "only" => "write `only <number>`"

  fn start() -> Int = only 3
end
```

The template is `n + n` rather than `n * 2` on purpose. To prove the rule can
never generate ill-typed code the compiler samples the hole's category, and
`Number` samples floats as well as integers — so a template that combines the
hole with an `Int` literal is rejected with E092 even though every example you
wrote passes. Keep templates polymorphic in the hole, or pick a narrower
category.

`fail Name(reason: Atom)` declares an author-defined semantic failure point,
with typed parameters, so a Tier-3 expander can reject with a named diagnosis
rather than an anonymous atom. Declared `fail` points are themselves failure
points that `explain` must cover.

### 9.3 The contract `explain` turns on

Writing an `explain` block is a promise, and the compiler holds you to it:

1. **Exhaustiveness.** Every derived failure point must have a clause. Points are
   derived from each `syntax`/`literal`/`fail` rule: the rule's own dispatch
   keyword, every typed hole, every literal segment, and every declared `fail`
   name. Omit one and you get
   `MACRO EXPLANATIONS ARE INCOMPLETE [E092]`, naming what is unexplained.
2. **Every rule is pinned.** Every `syntax` and `computed by` rule must carry at
   least one worked example, or `MACRO RULE NEEDS A WORKED EXAMPLE [E092]`.
   (`literal` rules and family productions are exempt.)

Without `explain` you get the lightweight surface: examples are optional. This
is why the older standard-library vocabularies compile without pins.

Independent of `explain`, **every** macro goes through the expansion soundness
gate, plus reserved-field checks and computed-example execution.

## 10. Scope, staging, and the two-pass parse

- **Scoped by import.** Macro syntax reaches a module through `use`. There is no
  global grammar — except that standard-library macros are preluded, which is
  why `fsm`/`actor`/`sup`/`app` and the unit literals work everywhere. Local
  rules win over prelude rules on a collision.
- **Two-pass parsing.** Each file is parsed twice: a harvest pass with **no**
  active macros, which keeps only `{:macro_def, …}` nodes (use sites may
  mis-parse and are discarded), then an authoritative pass with the harvested
  grammars seeded so use sites expand. This is what lets a macro be used in the
  same file that defines it, above or below the definition.
- **Two-pass name resolution.** Within a module, a signature pass is intended to
  publish the names each macro instance will define before bodies elaborate, so
  user code may reference macro-*derived* names textually earlier than the macro
  that derives them, with cycles between two instances' derived types reported as
  an error naming both. This one is from the design
  (`2026-07-08-macro-facility-design.md`) and is the only claim in this document
  not re-verified against the compiler — check before depending on it.
- **Categories are namespaced by macro.** Cross-macro reuse is explicit
  (`<f: Packet.FieldDecl>`); extension needs `open` (§3.3).

## 11. Termination and purity

Expander functions are ordinary Cure, so they carry the same totality
obligation as the rest of your code — the design intent is that compile-time
evaluation cannot diverge, and that a recursive `becomes` template must consume
its input.

Two mechanisms actually enforce something today, and it is worth knowing which:

- **Normalisation fuel** *is* on by default. Reducing a `computed by`
  application is fuel-bounded, scaled by the term's node count
  (`10_000 + 100 × nodes`, capped at `1_000_000`). Exhausting it is the error
  `normalization_fuel_exhausted`, not a hang.
- **Expansion count and node count are `:infinity` by default**
  (`macro_expand.ex:23`). `max_expansions`/`max_nodes` exist as limits a caller
  can set, but no ceiling is applied unless one is. Do not treat a runaway-macro
  backstop as something you get for free.

Combined with purity (§6) — an expander sees only its quoted input and the
reflection API, never ambient effects — this is what keeps builds
deterministic: the same source always expands to the same tree.

## 12. Diagnostics

| Code | Catalog name | Rendered as, for macros | Typical cause |
|---|---|---|---|
| `E092` | Macro Expansion Failed | `MACRO EXPANSION FAILED`, `MACRO EXAMPLE HAS THE WRONG EXPANSION`, `MACRO EXPLANATIONS ARE INCOMPLETE`, `MACRO RULE NEEDS A WORKED EXAMPLE` | the self-proving obligations of §9 |
| `E093` | Type Mismatch | — | the expansion is well-formed but ill-typed at the use site |
| `E094` | Syntax Error | `MACRO SYNTAX DOES NOT MATCH`, `MACRO RULE NEEDS BECOMES`, `MACRO EXPLANATION POINT IS INVALID` | the rule grammar of §3 |
| `E101` | Internal Compiler Error | `CODE GENERATION FAILED` | a compiler defect downstream of expansion — see §13 |

One code, several rendered titles: the header names the specific obligation you
broke, so `E092` alone is not the diagnosis. `cure explain E092` prints the
catalog entry. Macro diagnostics carry the owning rule as a secondary label, so
the error points at both the use site and the rule that was supposed to match
it — as in §9.1's `this rule owns the failing example` / `this pin does not
match` pair.

By the catalog's own rule, `E101` "must never be used for ordinary source
errors" — so an `E101` from a macro is always a bug worth reporting with its
fingerprint, even when your input provoked it (§13).

## 13. Known limits and sharp edges

Each of these was reproduced against the current tree.

- **A `Code` hole is greedy, so an operator-shaped separator is swallowed.**
  `syntax pair <a: Code> and <b: Code>` never matches `pair 1 and 2`, because
  `1 and 2` parses as one expression and the literal `and` is consumed. Choose a
  separator that is not also an operator (`to`, `into`, `as`).
- **`becomes` takes one expression, not a block.** An indented template body is
  `E094`. Wrap the work in a function or move to `computed by`.
- **A `ModuleName` capture is qualified for you.** `table Books` and
  `table Demo.Books` both work: the parser qualifies a `ModuleName` hole the same
  way it qualifies a `mod` name, so the emitter's prefix never has to appear in
  source. A name that is already qualified is left alone, and an `Elixir.`-prefixed
  or lowercase name is treated as a foreign module and kept verbatim. Building a
  name yourself inside `derive_*` bypasses this — hand `lift_module` a
  fully-qualified `Cure.` string. Invalid generated names are rejected during
  lifted-request validation by both `cure check` and `cure compile`, before
  code generation.
- **A bare `ModuleName` is scoped to the enclosing `mod`, but its members are
  still out of reach.** `table Books` inside `mod Demo` generates `Demo.Books`,
  so two modules can each declare a `Books`. What it does *not* give you is
  access: `Books.key_name()` and `Books.Key` do not resolve from the defining
  module, because the generated unit is elaborated separately. Anything the
  enclosing module needs to name must be declared there and passed in — that is
  what `fsm`'s `event_type` is for.
- **Types a `derive_*` synthesises belong inside the generated module.** Declare
  them in the `lift_module` declaration list, as `fsm` does with `Event`/`State`,
  not beside it in the caller's scope. A type emitted into the caller binds a
  name nobody wrote, and two sibling modules invoking the same family collide on
  it with `sibling_module_collision`.
- **`lift_module` always attaches a `-behaviour` attribute.** There is no "plain
  module" behaviour, so a generated data module emits
  `COMPILER WARNING [W000] behaviour none undefined` unless it names a real OTP
  behaviour.

## 14. Where to look in the tree

**Worked macros, smallest first:**

| File | Shows |
|---|---|
| `lib/std/optic.cure:439` | the minimal shape — two bare-name rules with pins |
| `lib/std_deps/regex/regex_syntax.cure` | a `literal … computed by` expander end to end |
| `lib/std/otp.cure` | a large `contextual` keyword vocabulary |
| `lib/std/app.cure` | the smallest `syntax family` + `expands with` |
| `lib/std/supervisor.cure` | a family with nested families and validation |
| `lib/std/fsm.cure` | the full surface: parameterised head, production alternatives, cardinalities, graph validation |

**Implementation:**

| File | Owns |
|---|---|
| `lib/cure/compiler/parser.ex:11117` | `parse_macro_def` — the container |
| `lib/cure/compiler/parser.ex:11512` | the member dispatch table of §2 |
| `lib/cure/compiler/parser.ex:11609` | `syntax family` |
| `lib/cure/compiler/parser.ex:12560` | rule segments, holes, `...`, `( … )?` |
| `lib/cure/compiler/macro_family.ex` | family validation and derived record types |
| `lib/cure/compiler/macro_validate.ex` | the self-proving obligations of §9 |
| `lib/cure/compiler/macro_syntax.ex` | reflection: parser AST ⟷ `Std.Syntax` |
| `lib/cure/compiler/lift_module.ex` | minting compiled units |
| `lib/cure/elab/macro_expand.ex` | expansion during elaboration |
| `lib/cure/diagnostic/adapter/macro.ex` | every macro diagnostic's prose |

**Design specs** live in `docs/superpowers/specs/macros/`. The architecture is
`2026-07-08-macro-facility-design.md`; `2026-07-08-macro-composition-design.md`
covers stacking macros; `2026-07-11-self-proving-macros-design.md` is §9's
rationale. The remaining forty-odd files are library designs built on this
facility. Where a spec and this document disagree, this document was checked
against the compiler and the spec was not.

## See also

- [FSM Guide](FSM_GUIDE.md) — the `fsm` macro from a user's point of view
- [Supervision](SUPERVISION.md), [App](APP.md) — the other OTP container macros
- [Language Spec](LANGUAGE_SPEC.md) — the non-macro surface
- [Match](MATCH.md) — §17 covers what macro-generated `match` nodes must satisfy

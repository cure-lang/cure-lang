defmodule Cure.Diagnostic.Registry.Entry do
  @moduledoc false

  @enforce_keys [
    :code,
    :key,
    :severity,
    :title,
    :status,
    :subsystem,
    :payload_schema,
    :schema_version,
    :producers,
    :producer_fixtures,
    :producer_converters,
    :converter,
    :converter_function,
    :catalog_case,
    :fixture_id,
    :retirement_reason,
    :brief,
    :explanation
  ]
  defstruct @enforce_keys

  @type t :: %__MODULE__{
          code: String.t(),
          key: atom(),
          severity: Cure.Diagnostic.severity(),
          title: String.t(),
          status: :reachable | :retired,
          subsystem: atom(),
          payload_schema: pos_integer(),
          schema_version: pos_integer(),
          producers: [atom(), ...],
          producer_fixtures: %{optional(atom()) => atom()},
          producer_converters: %{optional(atom()) => {module(), atom()}},
          converter: module(),
          converter_function: atom(),
          catalog_case: atom() | nil,
          fixture_id: atom() | nil,
          retirement_reason: String.t() | nil,
          brief: String.t(),
          explanation: String.t()
        }
end

defmodule Cure.Diagnostic.Registry do
  @moduledoc "Typed ownership and reachability metadata for every stable diagnostic code."

  alias Cure.Diagnostic.Registry.Entry

  @retired ~w[E001 E002 E004 E005 E006 E007 E009 E010 E012 E015 E016 E017 E018 E019 E020 E023 E024 E025 E027 E028 E029 E031 E032 E033 E034 E036 E037 E063 E071 E072 E073 E074 E075 E079 E080 E085 E086 H083 H084 W081 W082 W088]
  @operational ~w[E008 E030 E038 E039 E040 E041 E042 E065 E066 E067 E068 E069 E070 E095 E096 E097 E098 E099 E100 E101 W000 W001 W002 W003]
  @retirement_reasons %{
    "E001" => "No first-party producer remains; contextual E093 is the active type-mismatch path.",
    "E002" => "No first-party producer remains; unresolved value names are reported as contextual E091 diagnostics.",
    "E004" => "No first-party producer remains; match coverage is not emitted as this catalog code.",
    "E005" => "No first-party producer remains; guard constraints are reported through contextual checking.",
    "E006" => "No first-party producer remains; effect failures use contextual checking diagnostics.",
    "E007" => "No first-party producer remains; unused-variable analysis is not emitted by the compiler.",
    "E009" => "No first-party producer remains; unreachable-clause analysis is not emitted by the compiler.",
    "E010" => "No first-party producer remains; effect annotations are checked contextually.",
    "E012" => "No first-party producer remains; sigma failures use dependent type diagnostics.",
    "E015" => "The former error path was consolidated into the contextual declaration diagnostics.",
    "E016" => "No first-party producer remains; dependent mismatches use contextual E093 diagnostics.",
    "E017" => "No first-party producer remains; equality failures use contextual E093 diagnostics.",
    "E018" => "The former error path was consolidated into the contextual declaration diagnostics.",
    "E019" => "No first-party producer remains; implicit failures use E011.",
    "E020" => "No first-party producer remains; doctest reporting is not emitted by the compiler.",
    "E023" => "No first-party producer remains; map-pattern keys are rejected by generic syntax handling.",
    "E024" => "No first-party producer remains; pin failures are not emitted as this catalog code.",
    "E025" => "No first-party producer remains; nested coverage is not emitted as this catalog code.",
    "E027" => "No first-party producer remains; assert_type failures use contextual E093 diagnostics.",
    "E028" => "No first-party producer remains; record defaults use contextual type checking.",
    "E029" => "No first-party producer remains; mutual-recursion structural checks are not emitted as this code.",
    "E031" => "No first-party producer remains; binary coverage is not emitted as this catalog code.",
    "E032" => "No first-party producer remains; unreachable match clauses are not emitted as this code.",
    "E033" => "No first-party producer remains; branch joins use contextual E093 diagnostics.",
    "E034" => "No first-party producer remains; let-pattern coverage is not emitted as this code.",
    "E036" => "No first-party producer remains; binary comprehension failures use generic syntax handling.",
    "E037" => "No first-party producer remains; binary segment failures use generic type checking.",
    "E063" =>
      "No first-party producer remains; parser recovery retains and reports the original contextual E094 error.",
    "E071" => "No first-party producer remains; function payload failures use name/type diagnostics.",
    "E072" => "No first-party producer remains; multiline type layout failures use syntax diagnostics.",
    "E073" => "No first-party producer remains; empty pickup blocks use E076.",
    "E074" => "No first-party producer remains; nullary pattern failures use pattern diagnostics.",
    "E075" => "No first-party producer remains; constructor arity failures use contextual checking.",
    "E079" => "No first-party producer remains; pickup guards use contextual E093 diagnostics.",
    "E080" => "No first-party producer remains; pickup branch joins use contextual E093 diagnostics.",
    "E085" => "The legacy if migration is emitted as a migration event, not a compiler diagnostic.",
    "E086" =>
      "The legacy parenthesised tuple-type migration is emitted as a deprecation event, not a compile-stopping diagnostic.",
    "H083" => "Formatter normalization is not emitted as a diagnostic code.",
    "H084" => "Formatter normalization is not emitted as a diagnostic code.",
    "W081" => "No first-party producer remains; pickup reachability warnings are not emitted.",
    "W082" => "No first-party producer remains; pickup reachability warnings are not emitted.",
    "W088" =>
      "No first-party producer remains; the dependent-only pipeline rejects unresolved imported names as E091 before any fallback resolution can occur."
  }
  @structured ~w[E002 E003 E011 E013 E014 E021 E022 E026 E035 E056 E057 E063 E076 E077 E078 E087 E089 E090 E091 E092 E093 E094 E102 E103 E104 E105 E106 E107 E108 E109 E110 E111 E112 E113 E114 E115 E116 E117 E118 E119 E120 W086 W088]
  @known_producers ~w[
    beam_writer dependency_graph elaboration kernel lexer macro_expansion
    name_resolution operational parser pattern_checker proof_checker
    totality_checker
  ]a
  @producer_modules %{
    beam_writer: Cure.Compiler.BeamWriter,
    dependency_graph: Cure.Compiler.DepGraph,
    elaboration: Cure.Elab.Program,
    kernel: Cure.Core.Kernel,
    lexer: Cure.Compiler.Lexer,
    macro_expansion: Cure.Elab.MacroExpand,
    name_resolution: Cure.Elab.Resolution,
    operational: Cure.Diagnostic.Adapter.Operational,
    parser: Cure.Compiler.Parser,
    pattern_checker: Cure.Elab.Elaborator,
    proof_checker: Cure.Elab.ProofSearch,
    totality_checker: Cure.Elab.TotalityClosure
  }
  @catalog_cases %{
    "E002" => :unbound_variable,
    "E008" => :undocumented_public_function,
    "E003" => :arity_mismatch,
    "E011" => :missing_implicit,
    "E013" => :totality_failure,
    "E014" => :unfilled_hole,
    "E021" => :unknown_record,
    "E022" => :record_field_mismatch,
    "E026" => :proof_shape_mismatch,
    "E030" => :package_version_conflict,
    "E035" => :unterminated_lambda,
    "E041" => :registry_signature_invalid,
    "E042" => :transparency_log_unreachable,
    "E038" => :registry_fetch_failed,
    "E039" => :registry_hash_mismatch,
    "E040" => :registry_package_not_found,
    "E056" => :extern_untyped_head,
    "E057" => :extern_has_body,
    "E076" => :pickup_missing_else,
    "E077" => :pickup_else_not_last,
    "E078" => :pickup_multiple_else,
    "E063" => :parse_recovered,
    "E065" => :proof_file_missing,
    "E066" => :proof_verification_failed,
    "E067" => :proof_schema_incompatible,
    "E069" => :snap_schema_incompatible,
    "E087" => :duplicate_module,
    "E089" => :ambiguous_name,
    "E068" => :export_unmappable,
    "E070" => :snap_missing,
    "E091" => :unknown_name,
    "E090" => :unrecognized_pattern,
    "E092" => :macro_expansion,
    "E093" => :type_mismatch,
    "E094" => :syntax_error,
    "E095" => :file_read,
    "E096" => :file_write,
    "E097" => :dependency,
    "E098" => :command,
    "E099" => :usage,
    "E100" => :artifact,
    "E101" => :internal_compiler_error,
    "E102" => :erasure_violation,
    "E103" => :non_strictly_positive_type,
    "E104" => :erased_value_used_relevantly,
    "E105" => :declaration_conflict,
    "E106" => :operator_declaration_conflict,
    "E107" => :unsupported_async,
    "E108" => :splice_outside_quote,
    "E109" => :proof_chain_syntax,
    "E110" => :proof_chain_mismatch,
    "E111" => :rewrite_failed,
    "E112" => :simplification_failed,
    "E113" => :induction_failed,
    "E114" => :defining_equation_unavailable,
    "E115" => :named_argument_mismatch,
    "E116" => :implementation_scope,
    "E117" => :resource_usage_violation,
    "E118" => :pattern_coverage,
    "E119" => :pattern_structure,
    "E120" => :primitive_declaration,
    "W000" => :compiler_warning,
    "W001" => :migration_warning,
    "W002" => :configuration_warning,
    "W003" => :destructive_format_warning,
    "W086" => :import_cycle,
    "W088" => :unresolved_import
  }

  @catalog %{
    "E001" => """
    E001: Type Mismatch

    A function's body type does not match its declared return type,
    or an argument type does not match the parameter type.

    Example:
      fn add(a: Int, b: Int) -> String = a + b
      # Error: declared return type String but body has type Int

    Fix: change the return type annotation or the function body.
    """,
    "E002" => """
    E002: Unbound Variable

    A variable is referenced that has not been defined in the current scope.

    Example:
      fn foo() -> Int = x + 1
      # Error: undefined variable 'x'

    Fix: define the variable with let, or check for typos.
    """,
    "E003" => """
    E003: Arity Mismatch

    A function is called with the wrong number of arguments.

    Example:
      fn add(a: Int, b: Int) -> Int = a + b
      fn main() -> Int = add(1)  # Error: expects 2 arguments, got 1

    Fix: provide the correct number of arguments.
    """,
    "E004" => """
    E004: Non-Exhaustive Match

    A match expression does not cover all possible values of the scrutinee type.

    Example:
      match x
        true -> "yes"
      # Warning: missing pattern for 'false'

    Fix: add the missing patterns or a wildcard (_ -> ...).
    """,
    "E005" => """
    E005: Constraint Violation

    A function with a guard constraint is called with arguments that
    may violate the constraint.

    Example:
      fn safe_div(a: Int, b: Int) -> Int when b != 0 = a / b
      fn main() -> Int = safe_div(10, 0)  # Warning: b != 0 may be violated

    Fix: ensure the arguments satisfy the guard condition.
    """,
    "E006" => """
    E006: Effect Violation

    A function performs an effect that is not declared in its effect
    annotation. Either add the missing effect to the `!` annotation or
    remove the effectful operation.

    Example:
      fn pure_add(a: Int, b: Int) -> Int = println("adding"); a + b
      # Error: undeclared effect Io

    Fix: annotate as `fn pure_add(a: Int, b: Int) -> Int ! Io` or
    remove the println call.
    """,
    "E007" => """
    E007: Unused Variable

    A variable is defined but never referenced. Prefix unused variables
    with `_` to suppress this warning.

    Example:
      fn foo() -> Int =
        let x = 42
        0
      # Warning: unused variable 'x'

    Fix: use the variable or rename it to `_x`.
    """,
    "E008" => """
    E008: Undocumented Public Function

    A public function has no `##` doc comment. This warning is only
    emitted when `cure doc --strict` is used.

    Fix: add a `##` doc comment above the function definition.
    """,
    "E009" => """
    E009: Unreachable Clause

    A pattern matching clause is shadowed by a prior clause and can
    never be reached.

    Example:
      fn classify(x: Int) -> String
        | _ -> "other"
        | 0 -> "zero"   # Unreachable: wildcard above catches everything

    Fix: reorder the clauses so more specific patterns come first.
    """,
    "E010" => """
    E010: Missing Effect Annotation

    A public function performs side effects but has no `!` annotation.
    This warning is only emitted when `--strict-effects` is enabled.

    Fix: add an effect annotation, e.g. `fn greet() -> Atom ! Io`.
    """,
    "E011" => """
    E011: Missing Implicit Argument

    Implicit unification could not solve every implicit parameter at a
    call site. The unification trace shows which constraint failed.

    Fix: pass the implicit explicitly with `{T = ConcreteType}`, or
    constrain the explicit arguments so the implicit can be inferred.
    """,
    "E012" => """
    E012: Sigma Destructuring Failure

    A pattern attempted to destructure a sigma value into shapes that
    don't agree with its declared first or second component.

    Fix: ensure the pattern matches the sigma's structure, or relax
    the type to a plain tuple where dependency is not required.
    """,
    "E013" => """
    E013: Totality Failure

    A function annotated `@total true` is not provably total. Either
    coverage is incomplete or a recursive call doesn't shrink any
    structural argument.

    Fix: add the missing patterns, restructure the recursion to use
    a smaller sub-term, or remove `@total true` if partiality is OK.
    """,
    "E014" => """
    E014: Unfilled Hole

    The compiler reached a `?name`, `?_`, or generated `???` placeholder that
    must not cross the emission boundary. If the surrounding expression has no
    expected type, Cure cannot report a useful goal until one is declared.

    Fix: add a type annotation when needed, then replace the hole with a real
    expression of the reported goal type.
    """,
    "E015" => """
    E015: Refinement Counterexample (retired)

    Reserved. This code covered refinement-type counterexamples, a
    feature removed pending SMTCoq-style proof reconstruction; it no
    longer fires.

    Fix: no action required -- refinement types are not currently part
    of the language.
    """,
    "E016" => """
    E016: Dependent Type Mismatch

    A function's dependent return type, after substituting the
    call-site arguments and normalising, does not match the expected
    type at the use site.

    Fix: check that the actual arguments produce the expected
    relationship (e.g. `m + n` versus the literal length).
    """,
    "E017" => """
    E017: Equality Proof Mismatch

    `refl(x)` was used to inhabit `Eq(T, a, b)` where `a` and `b` are
    not definitionally equal to `x`.

    Fix: if the equality is true but not definitional, prove it using
    `Std.Equivalent.trans/2`, `Std.Equivalent.cong/2`, or a `rewrite` step.
    """,
    "E018" => """
    E018: Path-sensitive Refinement Conflict (retired)

    Reserved. This code covered path-sensitive refinement conflicts, a
    feature removed pending SMTCoq-style proof reconstruction; it no
    longer fires.

    Fix: no action required -- refinement types are not currently part
    of the language.
    """,
    "E019" => """
    E019: Implicit Argument Solved Inconsistently

    The same implicit argument was solved to two different types from
    different parts of the call site.

    Fix: pass the implicit explicitly, or ensure the call-site
    arguments agree on the inferred type.
    """,
    "E020" => """
    E020: Doctest Mismatch

    A `cure>` doctest produced a different value from its `=>`
    expected line.

    Fix: update either the doctest expectation or the function it
    documents.
    """,
    "E021" => """
    E021: Unknown Record Field in Pattern

    A record pattern references a field that is not declared in the
    record's schema.

    Example:
      rec Point
        x: Int
        y: Int

      fn f(p: Point) -> Int =
        match p
          Point{z: v} -> v   # Error: Point has no field 'z'

    Fix: use one of the declared fields, or remove the clause.
    """,
    "E022" => """
    E022: Record Pattern Field Type Mismatch

    A sub-pattern inside a record pattern is incompatible with the
    declared type of that field.

    Example:
      rec Person
        age: Int

      match p
        Person{age: "forty"} -> ...   # Error: age is Int, not String

    Fix: change the sub-pattern or the field type so they agree.
    """,
    "E023" => """
    E023: Non-Literal Map Pattern Key

    Map keys in pattern position must be literal values (atoms,
    integers, strings, etc.). Bound variables may be used as keys
    only when they are already in scope; in that case they are
    looked up, not bound.

    Example:
      match m
        %{key(): v} -> v   # Error: function calls not allowed as keys

    Fix: use a literal key, or pre-compute the key with `let`.
    """,
    "E024" => """
    E024: Unbound Pin Variable

    The pin operator `^x` was used on a name that is not in scope at
    the pattern's position. The pin operator only compares against
    previously bound values.

    Example:
      match tag
        ^status -> :hit   # Error: 'status' is not bound

    Fix: bind the variable with `let` before the match, or drop the
    `^` if you intended to introduce a fresh binding.
    """,
    "E025" => """
    E025: Non-Exhaustive Nested Match

    A `match` expression with nested patterns does not cover every
    inhabitant of the scrutinee type. The compiler prints a concrete
    witness for the missing case.

    Example:
      match %[r]
        %[Ok(_)] -> :ok
      # Warning: missing pattern `%[Error(_)]`

    Fix: add the missing clause or a wildcard.
    """,
    "E026" => """
    E026: Proof Shape Mismatch

    A binding inside a `proof` container does not elaborate to an
    `Eq(T, a, b)` proof. Proof containers are intended exclusively for
    propositional laws.

    Example:
      proof Arithmetic
        fn meaning() -> Int = 42   # Error: not a proof shape

    Fix: move ordinary code into a `mod` container; keep `proof`
    containers for functions returning `Eq(...)`.
    """,
    "E027" => """
    E027: assert_type Assertion Failed

    The `assert_type expr : T` builtin was used but the type
    inferred for `expr` is not compatible with `T`.

    Example:
      fn f() -> Int = assert_type 42 : String
      # Error: assert_type expected String, got Int

    Fix: either change the asserted type or the expression. The
    wrapper disappears at runtime, so nothing breaks at runtime when
    it succeeds.
    """,
    "E028" => """
    E028: Record Default Type Mismatch

    A record field declared with a default value has a default whose
    inferred type does not match the declared field type.

    Example:
      rec Person
        name: String = 0       # Error: name is String, default is Int

    Fix: change the default or the declared field type.
    """,
    "E029" => """
    E029: Mutual Recursion Not Structural

    Two or more functions annotated with `@total true` call each other
    in a cycle in which no argument shrinks structurally on every
    path through the cycle. The compiler cannot prove termination.

    Example:
      @total true
      fn a(x: Nat) -> Nat = b(x)

      @total true
      fn b(x: Nat) -> Nat = a(x)
      # Error: neither clause decreases

    Fix: restructure the cycle so some structural argument shrinks
    on every path, or drop `@total true` if partiality is acceptable.
    """,
    "E030" => """
    E030: Package Version Conflict

    The dependency resolver could not find a set of versions that
    satisfies every constraint in `Cure.toml` and the transitive
    dependency graph.

    Example:
      # Cure.toml declares http ~> 1.0
      # but dep Foo requires http ~> 2.0
      # Error: no version of http satisfies both ~> 1.0 and ~> 2.0

    Fix: relax one of the constraints, or pin to a compatible
    version.
    """,
    "E031" => """
    E031: Binary Pattern Not Exhaustive

    A sequence of binary patterns (in a `match`, function head, `let`,
    or comprehension generator) does not cover every byte-length
    inhabitant of the scrutinee's Bitstring type.

    Example:
      fn first_byte(buf: Bitstring) -> Int =
        match buf
          <<b, _rest::binary>> -> b
      # Warning: missing pattern `<<>>`

    Fix: add the missing shape (typically `<<>>` or a size-0 case) or
    provide a catch-all arm.
    """,
    "E032" => """
    E032: Match Clause Unreachable (W-MATCH-UNREACHABLE)

    A `match` arm is provably shadowed by an earlier arm, so its
    pattern can never match (its guard, if any, is therefore never
    evaluated). The compiler emits this as a warning under MATCH §6.4
    so unreachable clauses surface during compilation rather than at
    review time.

    Example:
      match x
        _ -> :a       # wildcard absorbs everything
        0 -> :b       # warning E032: unreachable

    Fix: reorder the arms so more specific patterns come first, drop
    the redundant arm, or tighten the earlier pattern (or its guard)
    so the later arm is reachable. Numeric code reserved by
    `docs/MATCH.md` §20 -- the descriptive alias is `W-MATCH-UNREACHABLE`.
    """,
    "E033" => """
    E033: Match Branches Have No Common Type (E-MATCH-BRANCH-MISMATCH)

    The right-hand sides of two or more `match` arms produce values
    whose types do not admit a least upper bound under the
    language's existing subtyping rules. The result type of the
    whole `match` is therefore undefined.

    Example:
      match x
        "yes" -> 1     # Int
        42    -> "two" # String
      # error E033: branches have no common upper bound

    Fix: change the bodies so all arms produce the same type, or
    explicitly widen via `assert_type` or a sum-type wrapper. Numeric
    code reserved by `docs/MATCH.md` §20 -- the descriptive alias is
    `E-MATCH-BRANCH-MISMATCH`.
    """,
    "E071" => """
    E071: Function Type Payload Invalid

    An ADT constructor payload carries a value whose type cannot be
    resolved. The most common trigger is a bare identifier that does
    not refer to a declared type. Function-type payloads
    (e.g. `On(Int -> Int)` and `On((Int, Int) -> Int)`) are allowed
    and compile to first-class functions at runtime.

    Example:
      type Callback = On(DoesNotExist) | Off   # Error: unknown type

    Fix: use a concrete type, a declared type alias, or a function
    arrow for callable payloads.

    History: this diagnostic was previously code `E032`. The number
    was reassigned to `W-MATCH-UNREACHABLE` per `docs/MATCH.md` §20.
    """,
    "E072" => """
    E072: Multi-line Type Layout Invalid

    A `type` ADT declaration spans multiple lines but the layout
    cannot be absorbed by `parse_type_def/1`. This usually means the
    continuation lines are not indented beyond the `type` keyword or
    a leading `|` is followed by a closing `:dedent` instead of a
    variant name.

    Example:
      type Shape =
      | Circle(Int)   # error: continuation lines must be indented

    Fix: indent every continuation line at the same column inside
    the parent block, for example:
      type Shape =
        | Circle(Int)
        | Square(Int)

    History: this diagnostic was previously code `E033`. The number
    was reassigned to `E-MATCH-BRANCH-MISMATCH` per `docs/MATCH.md`
    §20.
    """,
    "E073" => """
    E073: Empty Match Block (E-MATCH-EMPTY)

    A `match` expression has no clauses. Empty `match` blocks are
    rejected at the macro-invocation site per `docs/MATCH.md` §17,
    so a macro that constructs a `match` AST without any clauses is
    flagged here rather than at runtime.

    Fix: ensure every macro-generated `match` has at least one clause,
    or guard the macro so the empty case never reaches expansion.
    """,
    "E074" => """
    E074: Bare Nullary Constructor in Pattern (E-MATCH-NULLARY-NEEDS-PARENS)

    A pattern position carries a bare PascalCase identifier such as
    `None`. `docs/MATCH.md` §5.12 requires nullary constructors to be
    written with explicit empty parentheses so the parser can tell
    them apart from a regular variable binding (which is lowercase).

    Example:
      match opt
        Some(x) -> x
        None    -> default     # error: write `None()`

    Fix: rewrite the pattern as `None()`. The compiler ships a code
    action that performs the rewrite automatically.
    """,
    "E075" => """
    E075: Constructor Arity Mismatch in Pattern (E-MATCH-CONSTRUCTOR-ARITY)

    A constructor pattern is applied to a different number of
    arguments than the constructor was declared with. `docs/MATCH.md`
    §5.12 requires the pattern arity to match the declaration.

    Example:
      type Pair = P(Int, Int)

      match p
        P(x) -> x         # error: P/2 received 1 argument

    Fix: change the pattern to match the declared arity, or change
    the type so the constructor accepts the new shape.
    """,
    "E076" => """
    E076: pickup Without else (E-PICKUP-NO-ELSE)

    A `pickup` block does not end in a mandatory terminating clause.
    `docs/PICKUP.md` §5.2 requires every `pickup` to end in either
    `else -> ...` (canonical) or a trailing `true -> ...` (alternative
    form normalised by the formatter).

    Example:
      pickup
        x > 0 -> :positive
        x < 0 -> :negative
      # error E076: missing terminator

    Fix: add a final `else -> ...` arm. The language server provides
    an "Add missing else" code action.
    """,
    "E077" => """
    E077: pickup else Not Last (E-PICKUP-ELSE-NOT-LAST)

    A `pickup` block has a clause after the `else ->` terminator.
    `docs/PICKUP.md` §4.1 forbids any clause after the terminator,
    because subsequent clauses would be unreachable by construction.

    Fix: move the `else ->` arm to the end of the block, or delete
    the trailing clauses.
    """,
    "E078" => """
    E078: pickup Has Multiple else (E-PICKUP-MULTIPLE-ELSE)

    A `pickup` block contains more than one `else ->` arm. Per
    `docs/PICKUP.md` §4.1 the terminator is unique.

    Fix: keep one terminator and inline or relocate the other arms.
    """,
    "E079" => """
    E079: pickup Guard Not Bool (E-PICKUP-GUARD-TYPE)

    A `pickup` guard expression has a type other than `Bool`. `pickup`
    is strict about guard typing per `docs/PICKUP.md` §5.1; there is
    no truthy/falsy coercion.

    Example:
      pickup
        "yes" -> :positive    # error: guard is String
        else  -> :other

    Fix: rewrite the guard as a Boolean expression, e.g.
    `name == "yes"` or `is_positive?(n)`.
    """,
    "E080" => """
    E080: pickup Branch Type Mismatch (E-PICKUP-BRANCH-MISMATCH)

    The right-hand sides of two or more `pickup` clauses produce
    values whose types do not admit a least upper bound. `pickup`'s
    branch-join rule is identical to `match`'s; see `docs/PICKUP.md`
    §5.6.

    Fix: align the branch types, wrap one branch in a sum type, or
    use `assert_type` to widen explicitly.
    """,
    "W081" => """
    W081: pickup Guard Unreachable (W-PICKUP-UNREACHABLE)

    A `pickup` guard is provably shadowed by a constant-true earlier
    guard, so it (and any subsequent guards) can never be evaluated.
    `docs/PICKUP.md` §5.3 mandates a sound, possibly incomplete
    reachability check; the implementation reports the obvious
    constant-`true` short-circuit case here.

    Fix: reorder the clauses, drop the dead arm, or replace the
    constant-true guard with a real condition.
    """,
    "W082" => """
    W082: pickup Terminator Unreachable (W-PICKUP-DEAD-ELSE)

    A `pickup` terminator can be shown unreachable because some
    earlier guard is statically `true`. The terminator is preserved
    syntactically so the totality property of `pickup` still holds,
    but the dead branch is reported as a warning per
    `docs/PICKUP.md` §5.3.

    Fix: drop the unreachable terminator or, if it is the intended
    branch, demote the redundant constant-true guard above it.
    """,
    "H083" => """
    H083: pickup `true ->` Normalised to `else ->` (H-PICKUP-PREFER-ELSE)

    The formatter rewrote a trailing `true -> ...` arm into the
    canonical `else -> ...` form. Both forms compile identically, but
    `else ->` reads as the default arm and is the surface form
    `docs/PICKUP.md` §8.3 prescribes.
    """,
    "H084" => """
    H084: Degenerate `pickup` Reduced (H-PICKUP-DEGENERATE)

    A `pickup` block whose only clause is the terminator was reduced
    to its right-hand side by the formatter. Per `docs/PICKUP.md`
    §8.6 the wrapping `pickup` carries no behaviour beyond evaluating
    its single body, so removing it produces equivalent code.
    """,
    "E085" => """
    E085: `if` Removed -- Use `pickup` (E-IF-REMOVED)

    `docs/PICKUP.md` §17 retires the `if`/`elif`/`then` keywords in
    favour of `pickup`. The current release keeps the parser
    permissive so legacy sources still compile, but `cure check`
    surfaces this hint so authors can migrate. The `mix cure.rewrite`
    task produces the canonical replacement automatically.

    Fix: replace the `if` chain with a `pickup` block, or run
    `mix cure.rewrite if-to-pickup <path>` to convert the file in
    place.
    """,
    "E086" => """
    E086: Parenthesised Tuple Type Deprecated (E-TYPE-TUPLE-PAREN)

    A type expression uses the legacy parenthesised tuple form `(A, B)`.
    Tuple values use `%[a, b]`, and the canonical type spelling now mirrors
    them as `%[A, B]`. The legacy spelling remains accepted and elaborates to
    exactly the same dependent tuple type, but parser tooling emits a
    deprecation event so editors and migration tools can suggest the clearer
    form.

    Example:
      fn divmod(a: Int, b: Int) -> (Int, Int)     # deprecated
      fn divmod(a: Int, b: Int) -> %[Int, Int]    # preferred

    Grouping `(A)` and a function domain `(A, B) -> C` are unaffected.

    Fix: replace `(A, B)` with `%[A, B]`. The rewrite is mechanical and does
    not change the elaborated type or emitted BEAM representation.
    """,
    "E034" => """
    E034: Let Pattern Not Exhaustive

    A `let` binding destructures its RHS with a pattern that does
    not cover every inhabitant of the RHS type. The binding still
    compiles -- Erlang's `=` raises at runtime on a failed match --
    but the compiler surfaces the gap as a warning so you can decide
    whether to widen the pattern or mark the let partial.

    Example:
      fn first_ok(r: Result(Int, String)) -> Int =
        let Ok(x) = r       # warning: missing `Error(_)`
        x

    Fix: rewrite as a `match` with every branch covered, add a
    wildcard by widening to `let _ = r`, or annotate the let's
    AST metadata with `partial: true` (reserved for tooling that
    knows the pattern is acceptable by construction).
    """,
    "E035" => """
    E035: Lambda Block Unterminated

    A multi-statement lambda body (v0.22.0) opened a brace block or
    began an `end`-terminated block but never closed it. The parser
    reached the end of the enclosing expression without seeing `}`
    or `end`.

    Example:
      map(xs, fn (x) -> { x + 1; x * 2 ) # Error: missing '}'
      map(xs, fn (x) -> x + 1; x * 2)    # Error: missing 'end'

    Fix: close the block with a matching `}` for brace-delimited
    bodies or with `end` for end-terminated ones. If the body is a
    single expression, use the v0.19.0 single-expression or indented
    form without `{` and without `;`.
    """,
    "E036" => """
    E036: Binary Comprehension Source Not Bitstring

    A binary comprehension generator `for <<pattern <- source>>`
    requires `source` to be a `Bitstring` (or a subtype of it).
    An Int, List, or other shape cannot drive byte-level iteration.

    Example:
      [b for <<b <- 123>>]   # Error: 123 is Int, not Bitstring

    Fix: pass a `Bitstring` value, for example a string literal
    (`"abc"`) or a `<<...>>` construction.
    """,
    "E038" => """
    E038: Registry Fetch Failed

    A call to the Cure package registry returned a non-2xx status or
    hit a transport error. The failure is surfaced through
    `Cure.Pipeline.Events` on the `:registry` stage; rerun with
    `--verbose` for the HTTP status or transport reason.

    Fix: verify the registry URL (env `CURE_REGISTRY_URL`), check
    network connectivity, or retry after the upstream incident is
    resolved.
    """,
    "E039" => """
    E039: Registry Hash Mismatch

    A tarball downloaded from the registry does not match the sha256
    the index declared for that version. This is treated as an
    unconditional error: the bytes are discarded and the install
    aborts.

    Fix: run `cure deps update` to force a re-resolution against the
    current index. If the mismatch persists, the registry entry is
    corrupt and should be reported upstream.
    """,
    "E040" => """
    E040: Registry Package Not Found

    The registry index has no entry for the requested package name.

    Fix: check the spelling in `Cure.toml`, confirm the package is
    published, or search the index with `cure search <query>`.
    """,
    "E041" => """
    E041: Registry Signature Invalid

    A tarball's Ed25519 signature failed verification against the
    trusted public key for its publisher. The install is aborted.

    Fix: either trust the publisher's key explicitly
    (`cure keys generate / cure keys list`) or reject the package
    until the publisher rotates a compromised key.
    """,
    "E042" => """
    E042: Transparency Log Unreachable

    The registry's transparency log did not respond to the pre-install
    verification request. By default the install continues with an
    :unverified annotation; set `config :cure,
    strict_transparency: true` to make this a hard failure.

    Fix: check connectivity to the registry's `/log` endpoint, or
    accept the unverified install if you trust the transport.
    """,
    "E037" => """
    E037: Binary Segment Size Non-Linear

    The compiler tried to compute the exact byte length of a trailing
    `rest::binary` segment as `byte_size(scrutinee) -
    sum_of_preceding_sizes`, but one of the preceding segments carries
    a size expression that cannot be linearised (for example an
    arbitrary runtime expression, or a non-byte-aligned specifier).
    The segment is typed as plain `Bitstring` and the pipeline emits
    this warning so you can choose whether to tighten the pattern or
    accept the looser type.

    Example:
      fn f(buf: Bitstring, n: Int) -> Int =
        match buf
          <<head::size(n)-unit(3), rest::binary>> -> ...
                    # warning: non-byte-aligned head size (E037)

      Fix: use byte-aligned sizes (multiples of 8 bits) or explicit
      literal sizes so the arithmetic can be emitted; otherwise accept
      that `rest` binds to plain `Bitstring` and let runtime pattern
      matching enforce the remaining invariants.
    """,
    "E056" => """
    E056: @extern Declaration Missing a Typed Head

    A function annotated with `@extern(:mod, :fun, arity)` is a type-only
    foreign-function signature: the compiler does not see its implementation,
    so it must trust the declared types and lower the call to a direct Erlang
    remote call. That trust only holds if the head is fully typed -- every
    parameter annotated and a return type declared. An untyped head would
    silently default to `Any`, defeating the type checker at every call site.

    Rejected:
      @extern(:erlang, :abs, 1)
      fn abs(x)                  # parameter `x` has no type, no return type

    Fix: annotate the whole head.
      @extern(:erlang, :abs, 1)
      fn abs(x: Int) -> Int

    A zero-parameter extern still needs its return type:
      @extern(:math, :pi, 0)
      fn pi() -> Float
    """,
    "E057" => """
    E057: @extern Declaration Has a Body

    A function annotated with `@extern` is a signature only. Codegen lowers it
    to a direct remote call to the external function, so any body you write is
    dead code -- it is never compiled or run. To stop that silent discard from
    misleading readers, a body on an `@extern` function is an error. This covers
    both a `= ...` body and a multi-clause `|` definition.

    Rejected:
      @extern(:erlang, :abs, 1)
      fn abs(x: Int) -> Int = x  # the `= x` body is ignored by codegen

    Also rejected (the clauses are ignored just the same):
      @extern(:erlang, :abs, 1)
      fn abs(x: Int) -> Int
        | 0 -> 0
        | n -> n

    Fix: drop the body; keep only the typed head.
      @extern(:erlang, :abs, 1)
      fn abs(x: Int) -> Int

    If you actually need local logic, write a normal function and call the
    extern from inside it:
      @extern(:erlang, :abs, 1)
      fn raw_abs(x: Int) -> Int

      fn abs_or_zero(x: Int) -> Int =
        pickup
          x < -1000 -> 0
          else      -> raw_abs(x)
    """,
    "E063" => """
    E063: Parse Error (recovered)

    A statement contained a syntax error from which the parser
    recovered by skipping tokens until the next statement boundary
    (newline, dedent, or definition-opening keyword such as `fn`,
    `mod`, `rec`, etc.). Subsequent definitions in the same file are
    still reported.

    A file that contains this error will also contain one or more
    primary parse errors (e.g. `:unexpected_token`) that identify
    the root cause. Fix those first; E063 errors will disappear once
    the primary error is resolved.

    Example:
      mod M
        fn foo() -> ???bad     # primary parse error here
        fn bar() -> Int = 0    # still parsed; E063 recovery consumed
                               # the tokens between the two fns

    Fix: address the root syntax error. E063 diagnostics are
    informational and do not indicate a new, independent bug.
    """,
    "E065" => """
    E065: Proof File Missing

    `cure verify` found no `.cureproof` artifact in the package
    tarball or extracted directory, and `strict_proofs: true` is set
    in `config.exs`.

    The `.cureproof` file is generated during `cure publish` when
    `[publish] include_proofs = true` is set in the project's
    `Cure.toml` (the default). A missing artifact means the publisher
    either disabled proof inclusion explicitly or published with an
    older version of Cure that predates v0.32.0.

    Fix: if you control the upstream package, re-publish with proof
    collection enabled. Otherwise, remove `strict_proofs: true` from
    your `config.exs` to allow packages without proof artifacts.
    """,
    "E066" => """
    E066: Proof Verification Failed

    `cure verify` successfully loaded a `.cureproof` artifact but one
    or more certificates could not be replayed. The diagnostic
    includes the module name and the failing proposition.

    This may indicate:
      - The package tarball was modified after signing (integrity
        violation). Cross-check the tarball hash against the
        transparency log (`cure info <pkg>:<ver>`).
      - The proof depends on a Z3 lemma whose off-line replay requires
        a solver version newer than the one installed locally.
      - The proof was produced in a development build with weakened
        checker settings.

    Fix: if you suspect tampering, discard the package and fetch a
    fresh copy. Otherwise, check the solver version with
    `cure doctor` and update it if necessary.
    """,
    "E067" => """
    E067: Proof Schema Incompatible

    The `.cureproof` file's embedded version byte does not match the
    schema the running Cure release understands. This happens when a
    proof artifact generated by a future release of Cure is verified
    by an older toolchain, or vice versa.

    Fix: update Cure to at least the version that generated the proof
    artifact, or ask the publisher to re-publish with the current
    Cure release.
    """,
    "E068" => """
    E068: Export Type Unmappable

    `cure export-types` encountered a Cure type that has no direct
    equivalent in the target language. The offending field is replaced
    by a comment in the generated output so the remaining types are
    still exported.

    Types that commonly trigger E068:
      - Dependent types (`Nat`, `Vec n T`) have no standard proto3
        representation.
      - Higher-kinded types and type-level functions.
      - `proof` container types (they are erased at runtime).

    Fix: annotate the field in the source with a `@export_as`
    attribute to give `cure export-types` a concrete target type, or
    wrap the value in an outer `rec` and export only the record.
    """,
    "E069" => """
    E069: Snap Schema Incompatible

    The `.cure-snap` file was produced by a different version of the
    Cure REPL serializer. The `snap_vsn` field inside the file does
    not match the version this Cure release understands.

    Fix: discard the old snap file and create a new one with the
    current Cure version via `:snap save <path>`.
    """,
    "E070" => """
    E070: Snap Module Missing

    A `.cure-snap` file recorded one or more files that were loaded
    via `:load` during the original session, but one or more of those
    files no longer exist at the saved path. The rest of the session
    has been restored normally; only the bindings from the missing
    file are absent.

    Fix: locate the missing `.cure` file and run `:load <path>` to
    restore its bindings manually, or delete the entry from the snap
    file's `loaded_paths` list.
    """,
    "W086" => """
    W086: Import Cycle

    Two or more modules in one compile set reference each other through
    `use` declarations, forming a cycle. This is NOT an error: the cycle's
    members compile together as a single group in deterministic
    (alphabetical) order -- Cure's compile-set model matches Rust's
    crate-internal modules, where module cycles are legal -- and the cycle
    is reported as a closed walk (`A (a.cure:3) -> B (b.cure:2) -> A`).

    A cycle is harmless when the modules only depend on each other's
    types or qualified calls, which lower syntactically and impose no
    order. It becomes actionable when the modules CALL each other's
    imported functions UNQUALIFIED: resolution inside the group is
    order-dependent, so an unqualified call may fall back to a local
    reference and surface as W088.

    Fix: qualify the cross-module calls (`Other.fn(...)`), merge the
    mutually-recursive modules into one, or drop a redundant `use`.
    """,
    "E087" => """
    E087: Duplicate Module

    Two or more files in the same compile set declare a module with the
    same name. The build driver scans every `.cure` source before
    ordering and aborts here, because a duplicate name makes the
    dependency graph -- and the emitted beam -- ambiguous.

    Example:
      one.cure:  mod Dup
      two.cure:  mod Dup      # Error: 'Dup' declared twice

    Fix: rename one of the modules, or remove the redundant file if it
    was an accidental copy.
    """,
    "E089" => """
    E089: Ambiguous Name

    An unqualified reference names a global that two or more imported
    modules provide, and the local module does not redeclare it to claim
    the name. Approach B re-keys every colliding import to its qualified
    key (`Mod#name`), so the bare name has no single owner -- resolving it
    silently would pick whichever import merged last. This fires at BOTH
    reference sites: a call (`name(...)`) and a bare value (`f(name)`).

    Example:
      mod P
        use Std.CollA        # exports helper/1
        use Std.CollB        # also exports helper/1
        fn f() -> Nat = helper(Z())   # Error: 'helper' is ambiguous
      end

    Fix: qualify the reference (`Std.CollA.helper(...)`), or define a
    local `helper` to shadow both imports.
    """,
    "E090" => """
    E090: Unrecognized Pattern Shape (E-MATCH-UNRECOGNIZED-PATTERN)

    A pattern's head is not one the pattern compiler recognizes. Match
    arms are parsed with the general expression parser, so shapes that
    are legal expressions but not legal patterns reach pattern position
    and must be rejected here.

    Pattern compilation specializes over a closed set of head shapes; a
    shape outside that set used to compile to a wildcard, which matches
    every value and shadows every arm below it.

    Examples:
      match x
        1..10 -> 1        # error: range patterns are not supported
        some(v) -> v      # error: lowercase head is not a constructor
        -f(x) -> 0        # error: unary `-` is not a pattern

    Fix: use a `when` guard for a range test (`n when n >= 1 and n <= 10`),
    capitalize a constructor name, or bind a variable and test in the body.
    """,
    "E091" => """
    E091: Unknown Name

    A value, type, constructor, module, or module member is not available in
    the namespace where it was referenced. The diagnostic payload records the
    namespace, original spelling, visible candidates, owner when applicable,
    and the declaration currently being checked.

    Fix: correct the spelling, import or qualify the definition, or use a name
    from the required namespace. Suggestions are filtered by namespace and
    visibility before they are shown.
    """,
    "E092" => """
    E092: Macro Expansion Failed

    A public macro generated a declaration that the compiler rejected. The
    default diagnostic names the macro and its authored declaration rather
    than exposing generated implementation source. Its structured cause and
    complete expansion provenance remain available to compiler tooling.

    Fix the authored macro declaration or captured argument identified by the
    diagnostic. If generated syntax alone is invalid, report the macro or
    compiler defect; users must never be asked to edit generated code.
    """,
    "E093" => """
    E093: Type Mismatch

    An expression's inferred type is not definitionally equal to the type
    required at that position. Dependent indices and normalized type forms are
    retained in the structured payload, while the ordinary message uses Cure
    surface spelling instead of raw Core tuples.

    Fix the expression, its annotation, or the relevant dependent index so the
    actual type agrees with the expected type.
    """,
    "E094" => """
    E094: Syntax Error

    The parser encountered a token or construct that cannot appear at this
    point. The diagnostic records the expected and actual syntax categories and
    labels the offending authored source.

    Fix the indicated delimiter, keyword, expression, or declaration shape.
    """,
    "E095" => """
    E095: Could Not Read File

    Cure could not read a required source, manifest, journal, or artifact.
    The payload retains the path and host file-system reason.
    """,
    "E096" => """
    E096: Could Not Write File

    Cure could not write a generated source, artifact, journal, or report.
    The payload retains the path and host file-system reason.
    """,
    "E097" => """
    E097: Dependency Resolution Failed

    The project dependency graph could not be resolved consistently.
    """,
    "E098" => """
    E098: Command Failed

    An external or project operation returned a deliberate failure.
    """,
    "E099" => """
    E099: Invalid Command Usage

    A Cure command was invoked with missing or incompatible arguments.
    """,
    "E100" => """
    E100: Invalid Build Artifact

    A required build, proof, snapshot, or release artifact is absent,
    corrupt, incompatible, or has the wrong format.
    """,
    "E101" => """
    E101: Internal Compiler Error

    Cure caught an exception or received an impossible return shape inside the
    compiler. The diagnostic includes a stable fingerprint; stacktraces are
    retained only in debug payloads.

    Ordinary source errors must never use E101. Please report the fingerprint
    with a minimal reproducer.
    """,
    "E102" => """
    E102: Erasure Violation

    An opaque type declares an invalid runtime erasure, or an erasure
    declaration is applied to a type whose runtime shape is determined by
    constructors.

    Fix: use one of the supported erasure classes on a constructor-less
    opaque type, or remove the declaration from a constructed type.
    """,
    "E103" => """
    E103: Non-Strictly-Positive Type

    An inductive type refers to itself in a negative or otherwise
    non-strictly-positive position. Such a definition would make the
    normalising kernel unsound.

    Fix: move the recursive occurrence to a strictly positive constructor
    argument or introduce an appropriate external boundary.
    """,
    "E104" => """
    E104: Erased Value Used Relevantly

    A value marked erased is used in a runtime-relevant position. Erased
    values are unavailable after compilation and cannot influence returned
    values, present arguments, or other runtime computation.

    Fix: remove the runtime use or make the binding relevant.
    """,
    "E105" => """
    E105: Declaration Conflict

    A declaration conflicts with another declaration, constructor, field,
    parameter, or reserved name in the same visible namespace.

    Fix: rename the declaration or change its signature so each visible
    declaration has a unique identity.
    """,
    "E106" => """
    E106: Operator Declaration Conflict

    An operator declaration is invalid because its precedence declarations
    form a cycle or it attempts to overload a built-in operator that cannot
    be redefined.

    Fix: remove the cycle and use a user-defined operator with a supported
    fixity.
    """,
    "E107" => """
    E107: Unsupported Asynchronous Primitive

    An asynchronous primitive such as `spawn` cannot be lowered by the
    dependent runtime while preserving Cure's checked process and message
    types. The diagnostic identifies the authored operation and the runtime
    stage that rejected it.

    Fix: express managed concurrency with an actor, FSM, or supervisor
    declaration.
    """,
    "E108" => """
    E108: Splice Outside Quote

    A scalar `$()` or repeated `$(... ...)` splice was used where no `quote`
    exists to receive generated syntax. The parser-owned range includes the
    splice opener, body, optional ellipsis, and closing parenthesis.

    Fix: move the splice inside `quote ...`, or remove `$()` to evaluate an
    ordinary expression.
    """,
    "E109" => """
    E109: Proof Chain Syntax Error

    A `proof chain` is empty or one of its equality steps is missing `==`, a
    right-hand endpoint, or `because` evidence. The structured payload retains
    the construct, step, observed token, expected continuation, and insertion
    position when a machine-applicable repair is available.

    Write an explicit first expression, then one or more `_ == endpoint`
    steps, each followed by `because` and checked evidence.
    """,
    "E110" => """
    E110: Proof Chain Mismatch

    A chain endpoint has the wrong carrier or a `because` expression does not
    prove the equality required by its authored step. The diagnostic identifies
    the one-based displayed step and labels authored endpoints and evidence;
    generated transitivity applications are never blamed.

    Supply evidence of exactly the proposition displayed for that step, or
    correct the adjacent endpoint.
    """,
    "E111" => """
    E111: Directed Rewrite Failed

    A `rewrite using` command could not apply its equality to the selected goal
    or local hypothesis. The diagnostic distinguishes missing, ambiguous, and
    invalid occurrences, unavailable targets, and an equality that only matches
    in the opposite direction.

    Use the displayed `at n` occurrence, correct the target, or switch between
    forward and `backwards` rewriting.
    """,
    "E112" => """
    E112: Simplification Failed

    Proof-producing simplification rejected a rule, left a residual goal, could
    not adapt supplied evidence, or reached its explicit resource guard. The
    structured payload retains the before/after goals and rewrite trace IDs.

    Supply a decreasing equality rule, add the missing defining equation, or
    continue the proof from the displayed residual proposition.
    """,
    "E113" => """
    E113: Induction Failed

    Structured induction could not be lowered to ordinary total recursion.
    The diagnostic distinguishes a non-inductive subject, missing or duplicate
    constructors, a constructor from another datatype, malformed field and
    induction-hypothesis bindings, and a local subject that cannot be lifted.

    Select an inductive value and bind each constructor's ordinary fields,
    followed by one hypothesis for every structurally recursive field.
    """,
    "E114" => """
    E114: Defining Equation Unavailable

    A friendly generated equation name did not identify one accessible,
    certified function branch. The diagnostic relates the use to the defining
    function and any colliding equation candidates.

    Choose an available constructor member or its structural pattern key.
    """,
    "E115" => """
    E115: Named Argument Mismatch

    A call contains an unknown or duplicate argument name, places a positional
    argument after a named one, leaves a required labelled slot unfilled, or
    does not identify one overload unambiguously. Authored argument-label,
    value, call, and parameter-declaration ranges are retained when available.

    Put positional arguments first, then use each declared parameter label at
    most once; named arguments may otherwise appear in any order.
    """,
    "E116" => """
    E116: Invalid Implementation Scope

    An implementation has no nested members, usually because an intended member
    is aligned with the `implementation` declaration instead of indented beneath
    it. The diagnostic labels both declarations and offers an indentation edit
    when the following function is the likely member.

    Indent every implementation member beneath its `implementation` declaration.
    """,
    "E117" => """
    E117: Resource Usage Violation

    A linear value is not consumed exactly once, or an affine value may be
    consumed more than once. The diagnostic identifies the authored binding and
    every unambiguous use that contributes to the violation.

    Keep linear ownership on exactly one path and affine ownership on at most
    one path. Pass restricted values only to parameters with compatible grades.
    """,
    "E118" => """
    E118: Pattern Coverage

    A pattern match omits a reachable constructor, repeats a constructor, or
    marks a reachable constructor as impossible. Coverage is checked against the
    matched type and its refined indices.

    Add every reachable constructor exactly once. Use `impossible` only when the
    constructor is ruled out by the matched indices.
    """,
    "E119" => """
    E119: Pattern Structure

    A pattern binds one name more than once, contains more than one catch-all,
    marks a catch-all impossible, or leaves an open binary/map match without a
    fallback.

    Bind each name once and keep one final catch-all for open pattern families.
    Use explicit comparisons when two bound values must be equal.
    """,
    "E120" => """
    E120: Invalid Primitive Declaration

    A primitive declaration is missing its `@builtin` marker, names an unknown
    primitive representation, contradicts the compiler's seeded primitive
    floor, or otherwise has an unsupported declaration shape. The diagnostic
    points at the primitive name or exact marker argument responsible.

    Use only the supported `:float`, `:binary`, and `:atom` builtin tags, and
    keep seeded primitive names paired with their established representation.
    """,
    "W000" => """
    W000: Compiler Warning

    Compatibility code for a compiler warning awaiting a more specific public
    category. New producers must allocate a specific warning code.
    """,
    "W001" => """
    W001: Migration Warning

    Authored syntax is accepted for compatibility but has a modern form.
    """,
    "W002" => """
    W002: Invalid Configuration

    A configuration value was ignored because it is not valid in its setting.
    """,
    "W003" => """
    W003: Formatting May Discard Source Details

    An explicitly requested formatting mode reconstructs source from the AST,
    so comments or non-canonical layout that are not represented there may be
    discarded. Commit or copy the source before continuing.
    """,
    "W088" => """
    W088: Unresolved Import

    Retired. The classic code generator used to emit a plain local call when
    an unqualified call matched no export of any `use`-imported module. The
    dependent-only pipeline now rejects that name as E091 before codegen, so
    this fallback warning is no longer reachable.

    It most often fires inside an import cycle (W086), where the callee
    module has not been loaded yet when the caller is compiled, so its
    exports are invisible to the beam-probing resolver.

    Example:
      mod UserB
        use LibA
        fn start() -> Int = ping()   # warning: ping/0 not found in LibA

    Fix: make sure the imported module is compiled and loaded before
    this file (DepGraph ordering normally guarantees this outside a
    cycle), or qualify the call (`LibA.ping()`).
    """
  }

  defp catalog_entries_data do
    @catalog
    |> Enum.map(fn {code, text} ->
      lines = text |> String.trim() |> String.split("\n") |> Enum.map(&String.trim/1)

      title =
        case lines do
          [first | _] ->
            case String.split(first, ":", parts: 2) do
              [_, name] -> String.trim(name)
              _ -> first
            end

          _ ->
            code
        end

      brief = Enum.drop(lines, 1) |> Enum.find("", &(&1 != ""))
      {code, title, brief}
    end)
    |> Enum.sort_by(fn {code, _, _} -> code end)
  end

  defp catalog_explanation_data!(code) do
    case Map.fetch(@catalog, String.upcase(code)) do
      {:ok, text} -> String.trim(text)
      :error -> raise ArgumentError, "unregistered diagnostic code: #{inspect(code)}"
    end
  end

  @spec entries() :: [Entry.t()]
  def entries do
    catalog_entries_data()
    |> Enum.map(fn {code, title, brief} ->
      %Entry{
        code: code,
        key: stable_key(code, title),
        severity: severity(code),
        title: title,
        status: if(code in @retired, do: :retired, else: :reachable),
        subsystem: subsystem(code),
        payload_schema: 1,
        schema_version: 1,
        producers: producers(code),
        producer_fixtures: producer_fixtures(code),
        producer_converters: producer_converters(code),
        converter: converter(code),
        converter_function: converter_function(code),
        catalog_case: Map.get(@catalog_cases, code),
        fixture_id: Map.get(@catalog_cases, code),
        retirement_reason: Map.get(@retirement_reasons, code),
        brief: brief,
        explanation: catalog_explanation_data!(code)
      }
    end)
  end

  @spec fetch(String.t()) :: {:ok, Entry.t()} | :error
  def fetch(code) when is_binary(code) do
    normalized = String.upcase(code)

    case Enum.find(entries(), &(&1.code == normalized)) do
      nil -> :error
      entry -> {:ok, entry}
    end
  end

  @spec fetch!(String.t()) :: Entry.t()
  def fetch!(code) do
    case fetch(code) do
      {:ok, entry} -> entry
      :error -> raise ArgumentError, "unregistered diagnostic code: #{inspect(code)}"
    end
  end

  @spec reachable() :: [Entry.t()]
  def reachable, do: Enum.filter(entries(), &(&1.status == :reachable))

  @spec retired() :: [Entry.t()]
  def retired, do: Enum.filter(entries(), &(&1.status == :retired))

  @doc "Return the checked code-to-producer inventory used by CI and catalog tooling."
  @spec producer_inventory() :: %{String.t() => [atom()]}
  def producer_inventory do
    Map.new(entries(), &{&1.code, &1.producers})
  end

  @doc "Return the legacy explain-list shape derived from typed registry entries."
  @spec list_all() :: [{String.t(), String.t(), String.t()}]
  def list_all do
    entries()
    |> Enum.map(&{&1.code, &1.title, &1.brief})
    |> Enum.sort_by(&elem(&1, 0))
  end

  @doc "Look up the complete explanation for a registered diagnostic code."
  @spec explain(String.t()) :: {:ok, String.t()} | :error
  def explain(code) when is_binary(code) do
    case fetch(code) do
      {:ok, entry} -> {:ok, entry.explanation}
      :error -> :error
    end
  end

  @doc "Return the complete catalog projection owned by the registry."
  @spec catalog_entries() :: [{String.t(), String.t(), String.t()}]
  def catalog_entries, do: list_all()

  @doc "Return a complete explanation for a registered code or raise for unknown codes."
  @spec catalog_explanation!(String.t()) :: String.t()
  def catalog_explanation!(code) do
    case explain(code) do
      {:ok, explanation} -> explanation
      :error -> raise ArgumentError, "unregistered diagnostic code: #{inspect(code)}"
    end
  end

  @doc "Validate registry invariants used by the diagnostic catalog and CI."
  @spec validate([Entry.t()]) :: :ok | {:error, term()}
  def validate(entries \\ entries()) when is_list(entries) do
    with :ok <- unique_codes(entries),
         :ok <- unique_catalog_metadata(entries),
         :ok <- valid_entries(entries),
         :ok <- validate_producer_catalog(entries) do
      :ok
    end
  end

  @doc "Verify that reachable codes and declared producers have first-party source evidence."
  @spec validate_reachability([Path.t()]) :: :ok | {:error, term()}
  def validate_reachability(paths \\ default_producer_paths()) when is_list(paths) do
    referenced =
      paths
      |> Enum.flat_map(&source_codes/1)
      |> MapSet.new()

    missing_codes =
      reachable()
      |> Enum.reject(&MapSet.member?(referenced, &1.code))
      |> Enum.map(& &1.code)
      |> Enum.sort()

    with :ok <- if(missing_codes == [], do: :ok, else: {:error, {:unreachable_code, missing_codes}}),
         :ok <- validate_producer_coverage(),
         :ok <- validate_producer_catalog() do
      :ok
    end
  end

  @doc "Ensure every known producer owns a reachable registry entry."
  @spec validate_producer_coverage() :: :ok | {:error, term()}
  def validate_producer_coverage do
    owned =
      reachable()
      |> Enum.flat_map(& &1.producers)
      |> MapSet.new()

    missing = @known_producers |> Enum.reject(&MapSet.member?(owned, &1)) |> Enum.sort()
    if missing == [], do: :ok, else: {:error, {:producer_without_reachable_code, missing}}
  end

  @doc "Ensure every reachable code/producer branch has its own catalog fixture identity."
  @spec validate_producer_catalog([Entry.t()]) :: :ok | {:error, term()}
  def validate_producer_catalog(entries \\ reachable()) do
    entries = Enum.filter(entries, &(&1.status == :reachable))

    expected =
      entries
      |> Enum.flat_map(fn entry -> Enum.map(entry.producers, &{entry.code, &1}) end)
      |> MapSet.new()

    actual =
      entries
      |> Enum.flat_map(fn entry ->
        Enum.map(entry.producer_fixtures || %{}, fn {producer, _id} -> {entry.code, producer} end)
      end)
      |> MapSet.new()

    missing = expected |> MapSet.difference(actual) |> Enum.sort()
    unexpected = actual |> MapSet.difference(expected) |> Enum.sort()

    fixture_ids =
      entries
      |> Enum.flat_map(fn entry -> Map.values(entry.producer_fixtures || %{}) end)

    duplicate_ids = fixture_ids -- Enum.uniq(fixture_ids)

    cond do
      missing != [] -> {:error, {:producer_branches_without_catalog_fixture, missing}}
      unexpected != [] -> {:error, {:catalog_fixtures_without_producer_branch, unexpected}}
      duplicate_ids != [] -> {:error, {:duplicate_producer_fixture_id, Enum.uniq(duplicate_ids) |> Enum.sort()}}
      true -> :ok
    end
  end

  @doc "Return fixture identity mapped to its owning diagnostic code and producer."
  @spec producer_fixture_inventory([Entry.t()]) :: %{atom() => {String.t(), atom()}}
  def producer_fixture_inventory(entries \\ reachable()) do
    entries
    |> Enum.filter(&(&1.status == :reachable))
    |> Enum.flat_map(fn entry ->
      Enum.map(entry.producer_fixtures || %{}, fn {producer, fixture_id} ->
        {fixture_id, {entry.code, producer}}
      end)
    end)
    |> Map.new()
  end

  @doc "Validate that catalog execution reached every fixture in the requested producer scope."
  @spec validate_exercised_producer_fixtures([atom()], keyword()) :: :ok | {:error, term()}
  def validate_exercised_producer_fixtures(fixture_ids, opts \\ []) when is_list(fixture_ids) do
    inventory = producer_fixture_inventory(Keyword.get(opts, :entries, reachable()))
    producer_scope = Keyword.get(opts, :only_producers)

    expected =
      inventory
      |> Enum.filter(fn {_id, {_code, producer}} ->
        is_nil(producer_scope) or producer in producer_scope
      end)
      |> Map.new()

    duplicates = fixture_ids -- Enum.uniq(fixture_ids)
    supplied = MapSet.new(fixture_ids)
    known = inventory |> Map.keys() |> MapSet.new()
    expected_ids = expected |> Map.keys() |> MapSet.new()
    unknown = supplied |> MapSet.difference(known) |> Enum.sort()
    missing = expected_ids |> MapSet.difference(supplied) |> Enum.sort()

    cond do
      duplicates != [] ->
        {:error, {:duplicate_exercised_producer_fixture, duplicates |> Enum.uniq() |> Enum.sort()}}

      unknown != [] ->
        {:error, {:unknown_exercised_producer_fixture, unknown}}

      missing != [] ->
        {:error, {:unexercised_producer_fixtures, missing}}

      true ->
        :ok
    end
  end

  @doc "Validate stable diagnostic codes referenced by first-party source files."
  @spec validate_sources([Path.t()]) :: :ok | {:error, {:unregistered_source_codes, [String.t()]}}
  def validate_sources(paths \\ default_source_paths()) when is_list(paths) do
    referenced =
      paths
      |> Enum.flat_map(&source_codes/1)
      |> MapSet.new()

    registered = entries() |> Enum.map(& &1.code) |> MapSet.new()
    missing = referenced |> MapSet.difference(registered) |> Enum.sort()

    if missing == [], do: :ok, else: {:error, {:unregistered_source_codes, missing}}
  end

  @doc false
  @spec source_codes(Path.t()) :: [String.t()]
  def source_codes(path) do
    case File.read(path) do
      {:ok, source} ->
        Regex.scan(~r/[\"']((?:E|W|I|H)\d{3})[\"']/, source, capture: :all_but_first)
        |> List.flatten()
        |> Enum.uniq()

      {:error, _reason} ->
        []
    end
  end

  defp severity("E" <> _), do: :error
  defp severity("W" <> _), do: :warning
  defp severity("I" <> _), do: :information
  defp severity("H" <> _), do: :hint

  defp stable_key("E091", _title), do: :unknown_name
  defp stable_key("E092", _title), do: :macro_expansion_failed
  defp stable_key("E093", _title), do: :type_mismatch
  defp stable_key("E094", _title), do: :syntax_error
  defp stable_key("E101", _title), do: :internal_compiler_error
  defp stable_key("E102", _title), do: :erasure_violation
  defp stable_key("E103", _title), do: :non_strictly_positive_type
  defp stable_key("E104", _title), do: :erased_value_used_relevantly
  defp stable_key("E105", _title), do: :declaration_conflict
  defp stable_key("E106", _title), do: :operator_declaration_conflict
  defp stable_key("E107", _title), do: :unsupported_async
  defp stable_key("E108", _title), do: :splice_outside_quote
  defp stable_key("E109", _title), do: :proof_chain_syntax
  defp stable_key("E110", _title), do: :proof_chain_mismatch
  defp stable_key("E111", _title), do: :rewrite_failed
  defp stable_key("E112", _title), do: :simplification_failed
  defp stable_key("E113", _title), do: :induction_failed
  defp stable_key("E114", _title), do: :defining_equation_unavailable
  defp stable_key("E115", _title), do: :named_argument_mismatch
  defp stable_key("E116", _title), do: :implementation_scope
  defp stable_key("E117", _title), do: :resource_usage_violation
  defp stable_key("E118", _title), do: :pattern_coverage
  defp stable_key("E119", _title), do: :pattern_structure
  defp stable_key("E120", _title), do: :primitive_declaration

  defp stable_key(_code, title) do
    title
    |> String.downcase()
    |> String.replace(~r/[^a-z0-9]+/, "_")
    |> String.trim("_")
    |> String.to_atom()
  end

  defp converter(code) when code in @operational, do: Cure.Diagnostic.Adapter.Operational
  defp converter("E091"), do: Cure.Diagnostic.Adapter.Name
  defp converter("E013"), do: Cure.Diagnostic.Adapter.StaticAnalysis
  defp converter("E102"), do: Cure.Diagnostic.Adapter.StaticAnalysis
  defp converter("E103"), do: Cure.Diagnostic.Adapter.Kernel
  defp converter("E104"), do: Cure.Diagnostic.Adapter.StaticAnalysis
  defp converter("E117"), do: Cure.Diagnostic.Adapter.StaticAnalysis
  defp converter("E118"), do: Cure.Diagnostic.Adapter.StaticAnalysis
  defp converter("E119"), do: Cure.Diagnostic.Adapter.StaticAnalysis
  defp converter(code) when code in @structured, do: Cure.Diagnostic.Adapter
  defp converter(_code), do: Cure.Compiler.Errors

  defp converter_function(code) when code in @operational, do: :from_error
  defp converter_function(code) when code in @structured, do: :from_error
  defp converter_function(_code), do: :format_error

  defp producer_converters(code) do
    Map.new(producers(code), fn producer ->
      {producer, producer_converter(code, producer)}
    end)
  end

  defp producer_converter("E101", :beam_writer),
    do: {Cure.Diagnostic.Adapter.Codegen, :from_error}

  defp producer_converter("E101", :macro_expansion),
    do: {Cure.Diagnostic.Adapter, :from_error}

  defp producer_converter("E091", producer)
       when producer in [:name_resolution, :pattern_checker],
       do: {Cure.Diagnostic.Adapter.Name, :from_error}

  defp producer_converter("E013", :totality_checker),
    do: {Cure.Diagnostic.Adapter.StaticAnalysis, :from_error}

  defp producer_converter("E102", :elaboration),
    do: {Cure.Diagnostic.Adapter.StaticAnalysis, :from_error}

  defp producer_converter("E103", :kernel),
    do: {Cure.Diagnostic.Adapter.Kernel, :from_error}

  defp producer_converter("E093", :kernel),
    do: {Cure.Diagnostic.Adapter.Type, :from_error}

  defp producer_converter("E104", :elaboration),
    do: {Cure.Diagnostic.Adapter.StaticAnalysis, :from_error}

  defp producer_converter("E117", :elaboration),
    do: {Cure.Diagnostic.Adapter.StaticAnalysis, :from_error}

  defp producer_converter("E118", :elaboration),
    do: {Cure.Diagnostic.Adapter.StaticAnalysis, :from_error}

  defp producer_converter("E119", :elaboration),
    do: {Cure.Diagnostic.Adapter.StaticAnalysis, :from_error}

  defp producer_converter(_code, :operational),
    do: {Cure.Diagnostic.Adapter.Operational, :from_error}

  defp producer_converter(code, _producer) when code in @structured,
    do: {Cure.Diagnostic.Adapter, :from_error}

  defp producer_converter(_code, _producer),
    do: {Cure.Compiler.Errors, :format_error}

  defp producers(code) when code in @retired, do: []

  defp producers(code)
       when code in ~w[E030 E038 E039 E040 E041 E042 E065 E066 E067 E068 E069 E070 E095 E096 E097 E098 E099 E100 W000 W001 W002 W003],
       do: [:operational]

  defp producers(code) when code in ~w[E011 E014], do: [:elaboration]
  defp producers("E013"), do: [:totality_checker]
  defp producers(code) when code in ~w[E021 E022], do: [:elaboration]
  defp producers("E026"), do: [:proof_checker]
  defp producers("E003"), do: [:elaboration]
  defp producers("E035"), do: [:parser]
  defp producers(code) when code in ~w[E056 E057], do: [:elaboration]
  defp producers(code) when code in ~w[E076 E077 E078], do: [:parser]
  defp producers("E063"), do: [:parser]
  defp producers("E087"), do: [:dependency_graph]
  defp producers("E089"), do: [:name_resolution]
  defp producers("E090"), do: [:elaboration]
  defp producers("E091"), do: [:name_resolution, :pattern_checker]
  defp producers("E092"), do: [:macro_expansion, :parser]
  # `Cure.Elab.TypeConv.convertible?/3` is a boolean query over `Core.Conv`; it
  # cannot emit a diagnostic. Conversion failures reported as E093 are produced
  # either by the surface elaborator or directly by `Cure.Core.Kernel`, so do not
  # advertise an unreachable `:kernel_conversion` producer branch.
  defp producers("E093"), do: [:elaboration, :kernel]
  defp producers("E094"), do: [:lexer, :parser]
  # The kernel is pure and returns domain errors; it does not construct internal
  # compiler diagnostics. E101 is owned by the BEAM boundary and the host crash
  # boundary, which are the two places that add stage/reason fingerprints.
  defp producers("E101"), do: [:beam_writer, :macro_expansion, :operational]
  defp producers("E102"), do: [:elaboration]
  defp producers("E103"), do: [:kernel]
  defp producers("E104"), do: [:elaboration]
  defp producers("E105"), do: [:elaboration, :name_resolution]
  # Fixity resolution rejects conflicts and cycles while parsing. Program keeps
  # a defensive cycle check for externally supplied/generated ASTs, but no
  # first-party source path reaches it, so parser is the sole reachable producer.
  defp producers("E106"), do: [:parser]
  defp producers("E107"), do: [:elaboration]
  defp producers("E108"), do: [:elaboration]
  defp producers("E109"), do: [:parser]
  defp producers("E110"), do: [:elaboration]
  defp producers("E111"), do: [:elaboration]
  defp producers("E114"), do: [:elaboration]
  defp producers("E112"), do: [:elaboration]
  defp producers("E113"), do: [:elaboration]
  defp producers("E115"), do: [:elaboration]
  defp producers("E116"), do: [:elaboration]
  defp producers("E117"), do: [:elaboration]
  defp producers("E118"), do: [:elaboration]
  defp producers("E119"), do: [:elaboration]
  defp producers("E120"), do: [:elaboration]
  defp producers("E008"), do: [:operational]
  defp producers("W086"), do: [:dependency_graph]
  defp producers("W088"), do: [:name_resolution]
  defp producers(_code), do: [:compiler_errors]

  defp producer_fixtures(code) when code in @retired, do: %{}

  defp producer_fixtures("E003"),
    do: %{elaboration: :arity_mismatch_elaboration}

  defp producer_fixtures("E090"),
    do: %{elaboration: :unrecognized_pattern_elaboration}

  defp producer_fixtures("E091"),
    do: %{name_resolution: :unknown_name_resolution, pattern_checker: :unknown_pattern_name}

  defp producer_fixtures("E092"),
    do: %{macro_expansion: :macro_expansion_failure, parser: :parser_macro_failure}

  defp producer_fixtures("E093"),
    do: %{
      elaboration: :type_mismatch_elaboration,
      kernel: :type_mismatch_kernel
    }

  defp producer_fixtures("E094"),
    do: %{lexer: :syntax_error_lexer, parser: :syntax_error_parser}

  defp producer_fixtures("E101"),
    do: %{
      beam_writer: :internal_failure_beam_writer,
      macro_expansion: :internal_failure_macro_expansion,
      operational: :internal_failure_operational
    }

  defp producer_fixtures("E105"),
    do: %{elaboration: :declaration_conflict_elaboration, name_resolution: :declaration_conflict_name_resolution}

  defp producer_fixtures("E106"), do: %{parser: :operator_conflict_parser}

  defp producer_fixtures(code) do
    case {producers(code), Map.get(@catalog_cases, code)} do
      {[producer], fixture_id} when is_atom(fixture_id) -> %{producer => fixture_id}
      _ -> %{}
    end
  end

  defp subsystem("E101"), do: :compiler
  defp subsystem("E102"), do: :elaboration
  defp subsystem("E103"), do: :kernel
  defp subsystem("E104"), do: :elaboration
  defp subsystem("E105"), do: :elaboration
  defp subsystem("E106"), do: :elaboration
  defp subsystem("E107"), do: :elaboration
  defp subsystem("E108"), do: :elaboration
  defp subsystem("E109"), do: :parser
  defp subsystem("E110"), do: :elaboration
  defp subsystem("E111"), do: :elaboration
  defp subsystem("E114"), do: :elaboration
  defp subsystem("E112"), do: :elaboration
  defp subsystem("E113"), do: :elaboration
  defp subsystem("E115"), do: :elaboration
  defp subsystem("E116"), do: :elaboration
  defp subsystem("E117"), do: :elaboration
  defp subsystem("E118"), do: :elaboration
  defp subsystem("E119"), do: :elaboration
  defp subsystem("E120"), do: :elaboration
  defp subsystem("E091"), do: :resolution
  defp subsystem("E092"), do: :macros
  defp subsystem("E093"), do: :elaboration
  defp subsystem("E094"), do: :parser
  defp subsystem(code) when code in ~w[E095 E096 E097 E098 E099 E100], do: :operations
  defp subsystem("W" <> _), do: :analysis
  defp subsystem(_code), do: :compiler

  defp unique_codes(entries) do
    entries
    |> Enum.map(& &1.code)
    |> Enum.frequencies()
    |> Enum.find_value(:ok, fn
      {code, count} when count > 1 -> {:error, {:duplicate_code, code}}
      _ -> nil
    end)
  end

  defp unique_catalog_metadata(entries) do
    reachable = Enum.filter(entries, &(&1.status == :reachable))

    with :ok <- unique_field(reachable, :catalog_case, :duplicate_catalog_case),
         :ok <- unique_field(reachable, :fixture_id, :duplicate_fixture_id) do
      :ok
    end
  end

  defp unique_field(entries, field, error_tag) do
    case entries |> Enum.group_by(&Map.fetch!(&1, field)) |> Enum.find(fn {_value, owners} -> length(owners) > 1 end) do
      {value, _owners} -> {:error, {error_tag, value}}
      nil -> :ok
    end
  end

  defp valid_entries(entries) do
    Enum.find_value(entries, :ok, &validate_entry/1)
  end

  defp default_source_paths do
    Path.wildcard("lib/**/*.ex")
  end

  defp default_producer_paths do
    default_source_paths()
    |> Enum.reject(&String.contains?(&1, "lib/cure/diagnostic/registry"))
  end

  defp validate_entry(%Entry{} = entry) do
    cond do
      entry.status == :reachable and entry.producers == [] ->
        {:error, {:missing_producer, entry.code}}

      entry.status == :retired and entry.producers != [] ->
        {:error, {:retired_with_producer, entry.code}}

      entry.status == :reachable and
          Enum.any?(entry.producers, &(&1 not in @known_producers)) ->
        {:error, {:unowned_producer, entry.code}}

      entry.status == :reachable and
          Enum.any?(entry.producers, &(not producer_loaded?(&1))) ->
        {:error, {:unreachable_producer, entry.code}}

      entry.status == :reachable and
          MapSet.new(Map.keys(entry.producer_converters)) != MapSet.new(entry.producers) ->
        {:error, {:missing_producer_converter, entry.code}}

      entry.status == :reachable and
          Enum.any?(entry.producer_converters, fn {_producer, {module, function}} ->
            not is_atom(module) or not is_atom(function) or
              not Code.ensure_loaded?(module) or not function_exported?(module, function, 2)
          end) ->
        {:error, {:missing_producer_converter_function, entry.code}}

      entry.status == :reachable and entry.converter == Cure.Compiler.Errors ->
        {:error, {:legacy_converter, entry.code}}

      not is_atom(entry.converter) ->
        {:error, {:missing_converter, entry.code}}

      not is_atom(entry.converter_function) ->
        {:error, {:missing_converter_function, entry.code}}

      not Code.ensure_loaded?(entry.converter) or
          not function_exported?(entry.converter, entry.converter_function, 2) ->
        {:error, {:missing_converter_function, entry.code}}

      not is_integer(entry.schema_version) or entry.schema_version < 1 ->
        {:error, {:invalid_schema_version, entry.code}}

      entry.status == :retired and (not is_binary(entry.retirement_reason) or entry.retirement_reason == "") ->
        {:error, {:retired_without_reason, entry.code}}

      entry.status == :reachable and not is_nil(entry.retirement_reason) ->
        {:error, {:reachable_with_retirement_reason, entry.code}}

      entry.status == :reachable and is_nil(entry.catalog_case) ->
        {:error, {:reachable_without_catalog_case, entry.code}}

      entry.status == :reachable and is_nil(entry.fixture_id) ->
        {:error, {:reachable_without_fixture, entry.code}}

      true ->
        :ok
    end
  end

  defp producer_loaded?(producer) do
    case Map.fetch(@producer_modules, producer) do
      {:ok, module} -> Code.ensure_loaded?(module)
      :error -> false
    end
  end
end

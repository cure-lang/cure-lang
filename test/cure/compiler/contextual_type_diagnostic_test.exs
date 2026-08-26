defmodule Cure.Compiler.ContextualTypeDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Span
  alias Cure.Diagnostic.Renderer

  test "an annotated local fact mismatch names the fact" do
    source = """
    mod HaveError
      use Std.Equivalent
      fn answer() -> Equivalent(Int, 1, 1) =
        have useful: Int = 1.0
        reflexive(1)
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "have_error.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "have_error.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.title == "Local fact does not match"
    assert diagnostic.payload.origin.kind == :local_fact
    assert diagnostic.payload.origin.owner == "useful"
    assert rendered =~ "local fact `useful`"
  end

  test "a declared return mismatch retains its authored checking context" do
    source = "fn answer() -> Int = 1.0\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "answer.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "answer.cure", source)

    assert diagnostic.code == "E093"
    assert diagnostic.title == "Annotation does not match"
    assert diagnostic.payload.origin.owner == :answer
    assert diagnostic.payload.expression_category == :literal
    assert diagnostic.primary.span.start_column == 22
    assert [%{span: annotation, message: "the expectation comes from here"}] = diagnostic.secondary
    assert annotation.start_column == 16
    assert annotation.end_column == 19

    rendered = Renderer.plain(diagnostic, registry)
    assert rendered =~ "type written in its annotation"
    assert rendered =~ "the expectation comes from here"
    assert rendered =~ "this expression has the wrong type"

    [related] = Renderer.lsp(diagnostic, registry)["relatedInformation"]
    assert related["message"] == "the expectation comes from here"
    assert related["location"]["range"]["start"]["character"] == 15
  end

  test "a duplicate parameter labels both authored binders" do
    source = "mod DupParam\n  fn f(x: Int, x: Int) -> Int = x\nend\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "duplicate_parameter.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "duplicate_parameter.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E105"
    assert diagnostic.title == "Duplicate parameter"
    assert diagnostic.payload.name == :x
    assert diagnostic.primary.span.start_column == 16
    assert diagnostic.primary.message == "this parameter repeats an earlier name"

    assert [%{span: first, message: "the name was first declared here", style: :secondary}] =
             diagnostic.secondary

    assert first.start_column == 8
    assert rendered =~ "2 |   fn f(x: Int, x: Int) -> Int = x"
    assert rendered =~ "this parameter repeats an earlier name"
    assert rendered =~ "the name was first declared here"
    assert rendered =~ "Rename or remove one occurrence"

    [related] = Renderer.lsp(diagnostic, registry)["relatedInformation"]
    assert related["message"] == "the name was first declared here"
    assert related["location"]["range"]["start"]["character"] == 7
  end

  test "a sibling-module collision survives codegen wrapping and labels both declarations" do
    source = "mod A\n  fn helper(x: Int) -> Int = x\nend\nmod B\n  fn helper(x: Int) -> Int = x\nend\n"

    assert {:error, {:codegen_error, {:sibling_module_collision, details}} = reason} =
             Cure.Compiler.compile_string(source,
               file: "siblings.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "siblings.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E105"
    assert diagnostic.title == "Name repeated across sibling modules"
    assert details.name == :helper
    assert details.owners == [:A, :B]
    assert diagnostic.primary.span.start_line == 5
    assert diagnostic.primary.span.start_column == 6
    assert diagnostic.primary.message == "this name is already declared in another sibling module"

    assert [%{span: first, message: "the name was first declared here", style: :secondary}] =
             diagnostic.secondary

    assert {first.start_line, first.start_column} == {2, 6}

    assert rendered ==
             String.trim_trailing("""
             -- NAME REPEATED ACROSS SIBLING MODULES [E105] ------------------- siblings.cure

             The name `helper` is declared across modules A, B. Sibling modules in one source
             file currently share an elaboration namespace, so one declaration would
             overwrite the other. Rename one declaration or move the modules into separate
             source files.

             at siblings.cure:5:6
             2 |   fn helper(x: Int) -> Int = x
               |      ------ the name was first declared here
             3 | end
             4 | mod B
             5 |   fn helper(x: Int) -> Int = x
               |      ^^^^^^ this name is already declared in another sibling module
             """)

    assert [related] = Renderer.lsp(diagnostic, registry)["relatedInformation"]
    assert related["message"] == "the name was first declared here"
    assert related["location"]["range"]["start"] == %{"line" => 1, "character" => 5}
  end

  test "a duplicate record field labels both authored declarations" do
    source = "mod DupField\n  rec Point\n    x: Int\n    x: Bool\nend\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "duplicate_field.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "duplicate_field.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E105"
    assert diagnostic.title == "Duplicate field"
    assert diagnostic.primary.span.start_line == 4
    assert diagnostic.primary.message == "this field repeats an earlier name"
    assert [%{span: first, message: "the name was first declared here"}] = diagnostic.secondary
    assert first.start_line == 3
    assert rendered =~ "3 |     x: Int"
    assert rendered =~ "4 |     x: Bool"
    assert rendered =~ "this field repeats an earlier name"
    assert rendered =~ "the name was first declared here"
    assert rendered =~ "every record field has a unique name"
  end

  test "a duplicate type labels both declaration names" do
    source = "mod DupType\n  type Foo = A\n  type Foo = B\nend\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "duplicate_type.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "duplicate_type.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E105"
    assert diagnostic.title == "Duplicate type declaration"
    assert diagnostic.primary.span.start_line == 3
    assert diagnostic.primary.span.start_column == 8
    assert diagnostic.primary.message == "this type repeats an earlier declaration"
    assert [%{span: first, message: "the name was first declared here"}] = diagnostic.secondary
    assert {first.start_line, first.start_column} == {2, 8}
    assert rendered =~ "2 |   type Foo = A"
    assert rendered =~ "3 |   type Foo = B"
    assert rendered =~ "this type repeats an earlier declaration"
    assert rendered =~ "the name was first declared here"
    assert rendered =~ "type has a unique identity"
  end

  test "a duplicate constructor labels both authored variants" do
    source = "mod DupCtor\n  type First = Shared | Other\n  type Second = Shared | Last\nend\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "duplicate_constructor.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "duplicate_constructor.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E105"
    assert diagnostic.title == "Duplicate constructor"
    assert diagnostic.primary.span.start_line == 3
    assert diagnostic.primary.span.start_column == 17
    assert diagnostic.primary.message == "this constructor repeats an earlier declaration"
    assert [%{span: first, message: "the name was first declared here"}] = diagnostic.secondary
    assert {first.start_line, first.start_column} == {2, 16}
    assert rendered =~ "2 |   type First = Shared | Other"
    assert rendered =~ "3 |   type Second = Shared | Last"
    assert rendered =~ "this constructor repeats an earlier declaration"
    assert rendered =~ "the name was first declared here"
    assert rendered =~ "pattern matching stays unambiguous"
  end

  test "conflicting operator declarations label both authored operators" do
    source = """
    mod FixityConflict
      precedencegroup Loose
      precedencegroup Tight
      infix `<?>` : Loose
      infix `<?>` : Tight
    end
    """

    assert {:error, {:parse_error, [reason]}} =
             Cure.Compiler.compile_string(source,
               file: "fixity_conflict.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "fixity_conflict.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E106"
    assert diagnostic.title == "Conflicting operator fixity"
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {5, 9}
    assert [%{span: first, message: "the conflicting assignment is here"}] = diagnostic.secondary
    assert {first.start_line, first.start_column} == {4, 9}
    assert rendered =~ "4 |   infix `<?>` : Loose"
    assert rendered =~ "5 |   infix `<?>` : Tight"
    assert rendered =~ "assigned to both `Loose` and `Tight`"

    [related] = Renderer.lsp(diagnostic, registry)["relatedInformation"]
    assert related["message"] == "the conflicting assignment is here"
  end

  test "precedence cycles label every authored participating group" do
    source = """
    mod PrecedenceCycle
      precedencegroup Ring
        higher_than: Loop
      precedencegroup Loop
        higher_than: Ring
    end
    """

    assert {:error, {:parse_error, [reason]}} =
             Cure.Compiler.compile_string(source,
               file: "precedence_cycle.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "precedence_cycle.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E106"
    assert diagnostic.title == "Cyclic operator precedence"
    assert diagnostic.primary.span.start_line == 4

    assert [%{span: first, message: "this precedence group also participates in the cycle"}] =
             diagnostic.secondary

    assert first.start_line == 2
    assert rendered =~ "2 |   precedencegroup Ring"
    assert rendered =~ "4 |   precedencegroup Loop"
    assert rendered =~ "Remove or reverse one `higher_than`/`lower_than`"
    assert rendered =~ "relation to break the cycle"
  end

  test "incompatible precedence group bodies label both group names" do
    source = """
    mod GroupConflict
      precedencegroup CustomBinding
        associativity: left
      precedencegroup CustomBinding
        associativity: none
    end
    """

    assert {:error, {:parse_error, [reason]}} =
             Cure.Compiler.compile_string(source,
               file: "group_conflict.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "group_conflict.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E106"
    assert diagnostic.title == "Conflicting precedence group"
    assert diagnostic.payload.existing.assoc == :left
    assert diagnostic.payload.new.assoc == :none
    assert diagnostic.primary.span.start_line == 4

    assert [%{span: first, message: "the incompatible group declaration is here"}] =
             diagnostic.secondary

    assert first.start_line == 2
    assert rendered =~ "2 |   precedencegroup CustomBinding"
    assert rendered =~ "4 |   precedencegroup CustomBinding"
    assert rendered =~ "incompatible associativity"
    assert rendered =~ "or ordering rules"
  end

  test "constructor calls report missing arguments at the authored call" do
    source = """
    mod ConstructorArity
      type Maybe = None | Some(Int)
      fn bad() -> Maybe = Some()
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "constructor_arity.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "constructor_arity.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E003"
    assert diagnostic.title == "Constructor arity mismatch"
    assert diagnostic.payload.constructor == "Some"
    assert diagnostic.payload.expected == 1
    assert diagnostic.payload.actual == 0
    assert diagnostic.primary.span.start_line == 3
    assert diagnostic.primary.message == "add 1 argument to this constructor call"
    assert rendered =~ "3 |   fn bad() -> Maybe = Some()"
    assert rendered =~ "requires 1 argument, but this call supplies 0 arguments"

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"]["start"]["line"] == 2
    assert lsp["message"] =~ "requires 1 argument"
  end

  test "constructor calls report excess arguments and a removal hint" do
    source = """
    mod ConstructorArity
      type Maybe = None | Some(Int)
      fn bad() -> Maybe = Some(1, 2)
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "constructor_arity_extra.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "constructor_arity_extra.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.payload.expected == 1
    assert diagnostic.payload.actual == 2
    assert diagnostic.primary.message == "remove 1 argument from this constructor call"
    assert rendered =~ "3 |   fn bad() -> Maybe = Some(1, 2)"
    assert rendered =~ "requires 1 argument, but this call supplies"
    assert rendered =~ "2 arguments"
  end

  test "extern arity errors point at the target arity literal" do
    source = """
    mod ExternArity
      @extern(:erlang, :hd, 2)
      fn head({T: Type}, xs: List(T)) -> T
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "extern_arity.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "extern_arity.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E003"
    assert diagnostic.payload.declared == 2
    assert diagnostic.payload.present == 1
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {2, 25}
    assert diagnostic.primary.message =~ "change this target arity to 1"
    assert rendered =~ "2 |   @extern(:erlang, :hd, 2)"
    assert rendered =~ "^ change this target arity to 1"
    assert rendered =~ "erased parameters do not cross the FFI boundary"

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"]["start"] == %{"line" => 1, "character" => 24}
  end

  test "an extern without a fully typed head points at the missing annotation" do
    source = "mod ExternUntyped\n  @extern(:erlang, :hd, 1)\n  fn head(xs) -> Int\nend\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "extern_untyped.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "extern_untyped.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E056"
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {3, 11}
    assert rendered =~ "3 |   fn head(xs) -> Int"
    assert rendered =~ "Every `@extern` parameter needs an explicit type"

    missing_result = "mod ExternResult\n  @extern(:erlang, :self, 0)\n  fn me()\nend\n"

    assert {:error, {:codegen_error, result_reason}} =
             Cure.Compiler.compile_string(missing_result,
               file: "extern_result.cure",
               emit_events: false
             )

    {result_diagnostic, result_registry} =
      Errors.to_diagnostic(result_reason, "extern_result.cure", missing_result)

    assert result_diagnostic.code == "E056"
    assert {result_diagnostic.primary.span.start_line, result_diagnostic.primary.span.start_column} == {3, 6}

    assert Renderer.plain(result_diagnostic, result_registry) =~
             "Every `@extern` function needs an explicit result type"
  end

  test "an extern with a Cure body points at that body" do
    source = "mod ExternBody\n  @extern(:erlang, :self, 0)\n  fn me() -> Atom = :oops\nend\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "extern_body.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "extern_body.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E057"
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {3, 21}
    assert rendered =~ "3 |   fn me() -> Atom = :oops"
    assert rendered =~ "cannot also"
    assert rendered =~ "define a Cure body"
  end

  test "unsupported spawn points at the complete authored operation" do
    source = "mod SpawnUnsupported\n  fn bad() -> Int = spawn 1\nend\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "spawn.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "spawn.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E107"
    assert {diagnostic.primary.span.start_line, diagnostic.primary.span.start_column} == {2, 21}
    assert diagnostic.primary.span.end_column == 28
    assert rendered =~ "2 |   fn bad() -> Int = spawn 1"
    assert rendered =~ "^^^^^^^ this asynchronous operation has no dependent-runtime lowering"
    assert rendered =~ "The dependent runtime cannot lower `spawn`"
  end

  test "under-saturated calls report the callee arity without rejecting valid partial application" do
    source = """
    mod CallArity
      fn id(x: Int) -> Int = x
      fn bad() -> Int = id()
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "call_arity_few.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "call_arity_few.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E003"
    assert diagnostic.title == "Function arity mismatch"
    assert diagnostic.payload == %{kind: :function, name: "id", expected: 1, actual: 0, direction: :too_few}
    assert diagnostic.primary.message == "add 1 argument to this call"
    assert rendered =~ "3 |   fn bad() -> Int = id()"
    assert rendered =~ "`id` accepts 1 argument, but this call supplies 0 arguments"
    assert rendered =~ "use this partial application where a function is expected"
  end

  test "over-saturated calls report excess arguments but permit callable results" do
    source = """
    mod CallArity
      fn id(x: Int) -> Int = x
      fn bad() -> Int = id(1, 2)
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "call_arity_many.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "call_arity_many.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.payload.expected == 1
    assert diagnostic.payload.actual == 2
    assert diagnostic.payload.direction == :too_many
    assert diagnostic.primary.message == "remove 1 argument from this call"
    assert rendered =~ "3 |   fn bad() -> Int = id(1, 2)"
    assert rendered =~ "call the returned function separately"

    callable_result = """
    mod CallableResult
      fn add_from(x: Int) -> (Int) -> Int = fn(y) -> x + y
      fn good() -> Int = add_from(1, 2)
    end
    """

    assert {:ok, _env} = Cure.Elab.Program.elaborate(callable_result)
  end

  test "constructor patterns with missing fields report E003 instead of crashing" do
    source = """
    mod PatternArity
      type Pair = MkPair(Int, Int)
      fn first(pair: Pair) -> Int = match pair
        MkPair(x) -> x
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "pattern_arity_few.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "pattern_arity_few.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E003"
    assert diagnostic.title == "Pattern arity mismatch"
    assert diagnostic.payload.display_name == "MkPair"
    assert diagnostic.payload.expected == 2
    assert diagnostic.payload.actual == 1
    assert diagnostic.primary.span.start_line == 4
    assert diagnostic.primary.message == "add 1 argument to this pattern"
    assert rendered =~ "4 |     MkPair(x) -> x"
    assert rendered =~ "use `_` for fields you do not need"

    assert Renderer.lsp(diagnostic, registry)["range"]["start"]["line"] == 3
  end

  test "constructor patterns with excess fields identify the exact pattern" do
    source = """
    mod PatternArity
      type Pair = MkPair(Int, Int)
      fn first(pair: Pair) -> Int = match pair
        MkPair(x, y, z) -> x
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "pattern_arity_many.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "pattern_arity_many.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.payload.expected == 2
    assert diagnostic.payload.actual == 3
    assert diagnostic.payload.direction == :too_many
    assert diagnostic.primary.message == "remove 1 argument from this pattern"
    assert rendered =~ "4 |     MkPair(x, y, z) -> x"
    assert rendered =~ "this constructor does not contain them"
  end

  test "tuple pattern arity reports the expected and authored sizes with a pattern caret" do
    source = """
    mod TuplePatternArity
      fn first(pair: Tuple(Int, Int)) -> Int = match pair
        %[x, y, ignored] -> x
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "tuple_pattern_arity.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "tuple_pattern_arity.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E003"
    assert diagnostic.title == "Tuple pattern has the wrong size"
    assert diagnostic.payload == %{kind: :tuple_pattern, expected: 2, actual: 3}
    assert diagnostic.primary.span.start_line == 3
    assert diagnostic.primary.message == "remove 1 argument from this tuple pattern"
    assert rendered =~ "3 |     %[x, y, ignored] -> x"
    assert rendered =~ "^^^^^^^^^^^^^^^^ remove 1 argument from this tuple pattern"
    assert rendered =~ "this value has only 2 arguments"

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"]["start"] == %{"line" => 2, "character" => 4}
  end

  test "an unsupported range pattern points only at its operator" do
    source = """
    mod RangePattern
      fn bad(x: Int) -> Int = match x
        1..10 -> 1
        _ -> 0
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "range_pattern.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "range_pattern.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E090"
    assert diagnostic.primary.span.start_line == 3
    assert diagnostic.primary.span.start_column == 6
    assert diagnostic.primary.span.end_column == 8
    assert rendered =~ "3 |     1..10 -> 1"
    assert rendered =~ "^^ a range operator cannot be used in a pattern"
    assert rendered =~ "test the range in a guard instead"
    refute rendered =~ "2 |   fn bad"

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 2, "character" => 5},
             "end" => %{"line" => 2, "character" => 7}
           }
  end

  test "an unknown pattern constructor points at its name and suggests constructors from the matched type" do
    source = """
    mod PatternName
      type Maybe = None | Some(Int)
      fn value(maybe: Maybe) -> Int = match maybe
        Smoe(value) -> value
        None() -> 0
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "pattern_name.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "pattern_name.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E091"
    assert diagnostic.primary.span.start_line == 4
    assert diagnostic.primary.span.start_column == 5
    assert diagnostic.primary.span.end_column == 9
    assert rendered =~ "4 |     Smoe(value) -> value"
    assert rendered =~ "^^^^ `Smoe` was not found"
    assert rendered =~ "Did you mean `Some`?"
    refute rendered =~ "3 |   fn value"

    [suggestion | _] = diagnostic.suggestions
    assert suggestion.applicability == :machine_applicable
    assert [%Cure.Diagnostic.TextEdit{replacement: "Some"}] = suggestion.edits

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 3, "character" => 4},
             "end" => %{"line" => 3, "character" => 8}
           }
  end

  test "declaration context derives its extent from the parser-owned span" do
    source = "fn bad() -> Int = \"é\"\n"

    assert {:error, {:codegen_error, {:source_context, _reason, context}}} =
             Cure.Compiler.compile_string(source,
               file: "extent.cure",
               emit_events: false
             )

    assert context.span.start_column == 19
    assert context.span.end_column == 22
    assert context.length == context.span.end_column - context.span.start_column
  end

  test "an unknown variable points at the variable rather than the whole body" do
    source = "fn run() -> Int = missing_name\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "unknown_variable.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "unknown_variable.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E091"
    assert diagnostic.primary.span.start_column == 19
    assert rendered =~ "1 | fn run() -> Int = missing_name"
    assert rendered =~ "^^^^^^^^^^^^"
  end

  test "an unknown function points at the authored call" do
    source = "fn run() -> Int = missing_fn(1)\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "unknown_call.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "unknown_call.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E091"
    assert diagnostic.primary.span.start_column == 19
    assert rendered =~ "1 | fn run() -> Int = missing_fn(1)"
    assert rendered =~ "^^^^^^^^^^^^^"
  end

  test "an unknown function offers a nearby in-scope call suggestion" do
    source = """
    mod Suggestions
      fn print() -> Int = 1
      fn run() -> Int = prnt()
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "suggestions.cure",
               emit_events: false
             )

    {diagnostic, _registry} = Errors.to_diagnostic(reason, "suggestions.cure", source)

    assert diagnostic.code == "E091"
    assert diagnostic.payload.candidates == ["print"]
    assert [%Cure.Diagnostic.Suggestion{message: message}] = diagnostic.suggestions
    assert message =~ "`print`"
  end

  test "a missing implicit instance retains the authored call context" do
    source = "mod M\n  fn has(x: t, y: t) -> Bool = x == y\nend\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "implicit.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "implicit.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.expectation_origin == :implicit
    assert diagnostic.payload.checking == :==
    assert rendered =~ "implicit"
    assert rendered =~ "2 |   fn has(x: t, y: t) -> Bool = x == y"
  end

  test "a record update fallback points at the authored update" do
    source =
      "rec Point\n  x: Int\n  y: Int\nfn bad(p: Point) -> Point = Point{p | x: \"bad\"}\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "record_update.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "record_update.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :record_update
    assert rendered =~ "4 | fn bad(p: Point) -> Point = Point{p | x: \"bad\"}"
    assert rendered =~ "^"
  end

  test "an effect result mismatch points at the effect expression" do
    source = "fn main() -> Effect(Int) = true\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "effects.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "effects.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :effects
    assert rendered =~ "1 | fn main() -> Effect(Int) = true"
    assert rendered =~ "this expression has an invalid effect"
  end

  test "an extern result mismatch identifies the FFI boundary" do
    source =
      "@extern(:erlang, :abs, 1)\nfn abs(x: Int) -> Int\nfn bad() -> Bool = abs(1)\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "ffi.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "ffi.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :ffi
    assert rendered =~ "3 | fn bad() -> Bool = abs(1)"
    assert rendered =~ "this FFI boundary has the wrong type"
  end

  test "a list element mismatch retains its authored element context" do
    source = "mod M\n  use Std.List\n  fn bad() -> List(Int) = [1, true]\nend\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "list.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "list.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :collection
    assert diagnostic.payload.origin.owner == :list
    assert diagnostic.payload.origin.index == 1
    assert rendered =~ "3 |   fn bad() -> List(Int) = [1, true]"
    assert rendered =~ "this collection element has the wrong type"
  end

  test "a real conditional mismatch reports the authored guard" do
    source = "fn main() -> Int = if 1 then 2 else 3\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "condition.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "condition.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :condition
    assert diagnostic.primary.span.start_column == 23
    assert rendered =~ "CONDITION IS NOT BOOLEAN"
    assert rendered =~ "1 | fn main() -> Int = if 1 then 2 else 3"
    assert rendered =~ "this condition has the wrong type"
  end

  test "an inferred conditional branch mismatch does not leak constructor resolution" do
    source = "fn choose(cond: Bool) = if cond then 1 else \"two\"\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "conditional_branch.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "conditional_branch.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :branch
    assert diagnostic.payload.origin.owner == :if
    assert diagnostic.payload.origin.index == 1
    assert rendered =~ "Expected: Int"
    # `String` is nominal, so it names itself. There is nothing to unfold and
    # therefore nothing to leak: the reader is never shown `List`, `Cons`, or
    # `Bounded(1114112)` for a type they wrote as `String`.
    assert rendered =~ "Found:    String"
    refute rendered =~ "Bounded"
    refute rendered =~ "does not belong"
  end

  test "a pickup branch mismatch does not leak String's List constructors" do
    source = """
    fn choose(cond: Bool) =
      pickup
        cond -> 1
        else -> "two"
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "pickup_branch.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "pickup_branch.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :branch
    assert diagnostic.payload.origin.index == 1
    assert rendered =~ "Expected: Int"
    assert rendered =~ "Found:    String"
    refute rendered =~ "Bounded"
    refute rendered =~ "`Cons`"
    refute rendered =~ "does not belong"
  end

  test "a user typealias is shown with its expanded type in a branch mismatch" do
    source = """
    mod M
      typealias UserId = Int
      fn choose(cond: Bool, id: UserId) -> UserId =
        pickup
          cond -> id
          else -> true
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "aliased_branch.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "aliased_branch.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert rendered =~ "Expected: UserId (Int)"
    assert rendered =~ "Found:    Bool"
  end

  test "a branch failure names the checking function and authored arms" do
    reason =
      {:source_context, :branch_type,
       %{
         line: 8,
         column: 5,
         length: 20,
         checking: :multiply_int_successor_coefficient,
         expression_category: :pattern_match,
         expectation_origin: :annotation,
         branch_patterns: ["FromNat", "NegativeSuccessor"]
       }}

    source = "\n\n\n\n\n\n\n    match coefficient\n"
    {diagnostic, registry} = Errors.to_diagnostic(reason, "proof_int_order.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.branches == ["FromNat", "NegativeSuccessor"]
    assert rendered =~ "MULTIPLY_INT_SUCCESSOR_COEFFICIENT"
    assert rendered =~ "FromNat"
    assert rendered =~ "NegativeSuccessor"
    assert rendered =~ "proof_int_order.cure:8:5"
    assert rendered =~ "8 |     match coefficient"
    assert rendered =~ "|     ^"
  end

  test "an enriched branch failure labels every arm and singles out the outlier" do
    source = "match coefficient\n  FromNat(n) -> first\n  NegativeSuccessor(n) -> second\n"

    first = raw_span(source, "FromNat(n) -> first", 2, 3)
    second = raw_span(source, "NegativeSuccessor(n) -> second", 3, 3)

    reason =
      {:source_context,
       {:branch_type,
        %{
          constructor: :"Std.Int#NegativeSuccessor",
          actual: {:data, :Actual, [], []},
          expected: {:data, :Expected, [], []}
        }},
       %{
         line: 2,
         column: 3,
         checking: :multiply_int_successor_coefficient,
         expression_category: :pattern_match,
         expectation_origin: :annotation,
         branch_patterns: [
           %{name: "FromNat", span: first},
           %{name: "NegativeSuccessor", span: second}
         ]
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "proof_int_order.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.primary.style == :primary
    assert diagnostic.primary.span.start_line == second.start_line
    assert diagnostic.primary.span.start_column == second.start_column
    assert diagnostic.primary.message == "possible outlier: this branch has the incompatible type"
    assert [secondary] = diagnostic.secondary
    assert secondary.style == :secondary
    assert secondary.span.start_line == first.start_line
    assert secondary.span.start_column == first.start_column
    assert secondary.message == "compare this branch with the declared result"
    assert diagnostic.payload.failing_branch == :"Std.Int#NegativeSuccessor"
    assert rendered =~ "Possible outlier"
    assert rendered =~ "FromNat(n) -> first"
    assert rendered =~ "NegativeSuccessor(n) -> second"
    assert rendered =~ "compare this branch with the declared result"
    assert rendered =~ "possible outlier: this branch has the incompatible type"

    lsp = Renderer.lsp(diagnostic, registry)
    assert [related] = lsp["relatedInformation"]
    assert related["message"] == "compare this branch with the declared result"
    assert related["location"]["range"]["start"]["line"] == 1
  end

  test "a singleton branch type is called out when the other arms agree" do
    source = "match value\n  A -> one\n  B -> two\n  C -> odd\n"
    common = {:data, :Common, [], []}
    outlier = {:data, :Outlier, [], []}
    a_span = raw_span(source, "A -> one", 2, 3)
    b_span = raw_span(source, "B -> two", 3, 3)
    c_span = raw_span(source, "C -> odd", 4, 3)

    reason =
      {:source_context,
       {:branch_type,
        %{
          branches: [
            %{constructor: :A, actual: common, expected: common, status: :ok},
            %{constructor: :B, actual: common, expected: common, status: :ok},
            %{constructor: :C, actual: outlier, expected: common, status: {:error, :branch_type}}
          ]
        }},
       %{
         checking: :three_way_match,
         branch_patterns: [
           %{name: "A", span: a_span},
           %{name: "B", span: b_span},
           %{name: "C", span: c_span}
         ]
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "branches.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert rendered =~ "only the `C` branch has type"
    assert rendered =~ "4 |   C -> odd"
    assert diagnostic.primary.span.start_line == c_span.start_line
    assert diagnostic.primary.span.start_column == c_span.start_column
    assert diagnostic.primary.message =~ "possible outlier"

    assert Enum.map(diagnostic.secondary, &{&1.span.start_line, &1.span.start_column}) == [
             {a_span.start_line, a_span.start_column},
             {b_span.start_line, b_span.start_column}
           ]

    assert Enum.all?(diagnostic.secondary, &(&1.style == :secondary))
    assert diagnostic.payload.branch_types |> Enum.map(& &1.branch) == [:A, :B, :C]
  end

  test "a call argument conversion retains its argument origin and caret" do
    source = "fn main() -> Int = use(1, \"bad\")\n"
    argument = raw_span(source, "\"bad\"", 1, 27)

    reason =
      {:source_context, {:conversion_failure, "String", "Int"},
       %{
         line: 1,
         column: 27,
         length: 5,
         span: argument,
         expectation_span: argument,
         checking: :use,
         argument_index: 1,
         expression_category: :literal,
         expectation_origin: :call_argument
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "call.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Argument has the wrong type"
    assert diagnostic.payload.origin.kind == :call_argument
    assert diagnostic.payload.origin.owner == :use
    assert diagnostic.payload.origin.index == 1
    assert diagnostic.primary.span.start_column == 27
    assert rendered =~ "Argument 2 of `use`"
    assert rendered =~ "Expected: Int"
    assert rendered =~ "Found:    String"
    assert rendered =~ "1 | fn main() -> Int = use(1, \"bad\")"
    assert rendered =~ "this argument has the wrong type"
  end

  test "an operator operand conversion retains its operand origin and caret" do
    source = "fn main() -> Bool = \"bad\" == 1\n"
    operand = raw_span(source, "\"bad\"", 1, 21)

    reason =
      {:source_context, {:conversion_failure, "String", "Int"},
       %{
         line: 1,
         column: 21,
         length: 5,
         span: operand,
         expectation_span: operand,
         checking: :==,
         argument_index: 0,
         expression_category: :literal,
         expectation_origin: :operator_operand
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "operator.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Operator cannot use this value"
    assert diagnostic.payload.origin.kind == :operator_operand
    assert diagnostic.payload.origin.owner == :==
    assert diagnostic.payload.origin.index == 0
    assert diagnostic.primary.span.start_column == 21
    assert rendered =~ "The `==` operator cannot use this operand type"
    assert rendered =~ "Expected: Int"
    assert rendered =~ "Found:    String"
    assert rendered =~ "1 | fn main() -> Bool = \"bad\" == 1"
    assert rendered =~ "this operator operand has the wrong type"
  end

  test "a conditional guard conversion retains its condition origin and caret" do
    source = "fn main() -> Int = if 1 then 2 else 3\n"
    condition = raw_span(source, "1", 1, 23)

    reason =
      {:source_context, {:conversion_failure, "Int", "Bool"},
       %{
         line: 1,
         column: 23,
         length: 1,
         span: condition,
         expectation_span: condition,
         checking: :if,
         expression_category: :literal,
         expectation_origin: :condition
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "condition.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Condition is not boolean"
    assert diagnostic.payload.origin.kind == :condition
    assert diagnostic.payload.origin.owner == :if
    assert diagnostic.primary.span.start_column == 23
    assert rendered =~ "A condition must produce `Bool`"
    assert rendered =~ "Expected: Bool"
    assert rendered =~ "Found:    Int"
    assert rendered =~ "1 | fn main() -> Int = if 1 then 2 else 3"
    assert rendered =~ "this condition has the wrong type"
  end

  test "a tuple element conversion retains its element origin and caret" do
    source = "fn main() -> Pair = %[1, \"bad\"]\n"
    element = raw_span(source, "\"bad\"", 1, 26)

    reason =
      {:source_context, {:conversion_failure, "String", "Int"},
       %{
         line: 1,
         column: 26,
         length: 5,
         span: element,
         expectation_span: element,
         checking: :tuple,
         argument_index: 1,
         expression_category: :literal,
         expectation_origin: :element
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "tuple.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Collection element has the wrong type"
    assert diagnostic.payload.origin.kind == :element
    assert diagnostic.payload.origin.owner == :tuple
    assert diagnostic.payload.origin.index == 1
    assert diagnostic.primary.span.start_column == 26
    assert rendered =~ "Element 2 of this collection"
    assert rendered =~ "Expected: Int"
    assert rendered =~ "Found:    String"
    assert rendered =~ "1 | fn main() -> Pair = %[1, \"bad\"]"
    assert rendered =~ "this collection element has the wrong type"
  end

  test "a constructor argument conversion retains its constructor origin and caret" do
    source = "fn main() -> Maybe = Some(\"bad\")\n"
    argument = raw_span(source, "\"bad\"", 1, 27)

    reason =
      {:source_context, {:conversion_failure, "String", "Int"},
       %{
         line: 1,
         column: 27,
         length: 5,
         span: argument,
         expectation_span: argument,
         checking: :Some,
         argument_index: 0,
         expression_category: :literal,
         expectation_origin: :constructor_argument
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "constructor.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Constructor argument has the wrong type"
    assert diagnostic.payload.origin.kind == :constructor_argument
    assert diagnostic.payload.origin.owner == :Some
    assert diagnostic.payload.origin.index == 0
    assert diagnostic.primary.span.start_column == 27
    assert rendered =~ "Argument 1 of constructor `Some`"
    assert rendered =~ "Expected: Int"
    assert rendered =~ "Found:    String"
    assert rendered =~ "1 | fn main() -> Maybe = Some(\"bad\")"
    assert rendered =~ "this constructor argument has the wrong type"
  end

  test "a record field conversion retains the authored field origin and caret" do
    source = "Point{name: \"bad\"}\n"
    value = raw_span(source, "\"bad\"", 1, 13)

    reason =
      {:source_context, {:conversion_failure, "String", "Int"},
       %{
         line: 1,
         column: 13,
         length: 5,
         span: value,
         expectation_span: value,
         checking: :name,
         argument_index: 0,
         expression_category: :literal,
         expectation_origin: :record_field
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "record.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Record field has the wrong type"
    assert diagnostic.payload.origin.kind == :record_field
    assert diagnostic.payload.origin.owner == :name
    assert diagnostic.primary.span.start_column == 13
    assert rendered =~ "Field `name` does not match"
    assert rendered =~ "Expected: Int"
    assert rendered =~ "Found:    String"
    assert rendered =~ "1 | Point{name: \"bad\"}"
    assert rendered =~ "this record field has the wrong type"
  end

  test "a real one-field record mismatch points at the field value" do
    source =
      "mod M\n" <>
        "  rec Point\n" <>
        "    x: Int\n" <>
        "  fn bad() -> Point = Point{x: \"bad\"}\n" <>
        "end\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "record.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "record.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :record_field
    assert diagnostic.payload.origin.owner == :x
    assert diagnostic.primary.span.start_line == 4
    assert rendered =~ "Field `x` does not match"
    assert rendered =~ "4 |   fn bad() -> Point = Point{x: \"bad\"}"
    assert rendered =~ "this record field has the wrong type"
  end

  test "an unknown record field points at its name and suggests from the declared shape" do
    source =
      "mod M\n" <>
        "  rec Point\n" <>
        "    x: Int\n" <>
        "    y: Int\n" <>
        "  fn bad() -> Point = Point{xx: 1, y: 2}\n" <>
        "end\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "record_typo.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "record_typo.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E022"
    assert diagnostic.title == "Unknown record field"
    assert diagnostic.payload.record == :Point
    assert diagnostic.payload.declared == [:x, :y]
    assert diagnostic.payload.unknown == [:xx]
    assert Enum.map(diagnostic.payload.candidates, & &1.name) == ["x", "y"]
    assert diagnostic.primary.span.start_line == 5
    assert diagnostic.primary.span.start_column == 29
    assert rendered =~ "5 |   fn bad() -> Point = Point{xx: 1, y: 2}"
    assert rendered =~ "----- ^^ this constructs `Point`; this field is not declared by the record"
    assert rendered =~ "Did you mean `x`?"

    assert [suggestion] = diagnostic.suggestions
    assert suggestion.applicability == :machine_applicable
    assert [%{replacement: "x", span: edit_span}] = suggestion.edits
    assert edit_span.start_column == 29

    lsp_diagnostic = Renderer.lsp(diagnostic, registry)
    [action] = Cure.LSP.Server.compute_code_actions("file:///record_typo.cure", [lsp_diagnostic])
    assert action["title"] == "Replace it with `x`"
  end

  test "a missing record field names the field and points at the owned closing brace" do
    source =
      "mod M\n" <>
        "  rec Point\n" <>
        "    x: Int\n" <>
        "    y: Int\n" <>
        "  fn bad() -> Point = Point{x: 1}\n" <>
        "end\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "record_missing.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "record_missing.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E022"
    assert diagnostic.title == "Missing record field"
    assert diagnostic.payload.missing == [:y]
    assert diagnostic.primary.span.start_column == 33
    assert rendered =~ "missing `y`"
    assert rendered =~ "add the missing field `y` before this closing brace"
    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions
  end

  test "a whole-record mismatch retains the authored record boundary" do
    source = "fn bad() -> Point = Point{x: value}\n"
    span = raw_span(source, "Point{x: value}", 1, 19)

    reason =
      {:source_context, {:cannot_unify, :actual_point, :expected_point},
       %{span: span, checking: :bad, expression_category: :function_call, expectation_origin: :record}}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "record_shape.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :record
    assert diagnostic.payload.origin.owner == :bad
    assert rendered =~ "RECORD HAS THE WRONG TYPE"
    assert rendered =~ "this record has the wrong type"
  end

  test "a typed pattern mismatch points at the authored annotation" do
    source = "n: Bool -> 1\n"
    annotation = raw_span(source, "Bool", 1, 4)
    type_ast = {:variable, [source_info: %Cure.MetaAST.SourceInfo{whole: annotation}], "Bool"}

    reason =
      {:source_context, {:typed_pattern_type_mismatch, type_ast},
       %{
         line: 1,
         column: 4,
         length: 4,
         span: annotation,
         expectation_span: annotation,
         checking: :pattern,
         expression_category: :pattern,
         expectation_origin: :pattern,
         argument_index: 0
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "pattern.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Pattern annotation does not match"
    assert diagnostic.primary.span.start_column == 4
    assert rendered =~ "This pattern's annotation is incompatible"
    assert rendered =~ "1 | n: Bool -> 1"
    assert rendered =~ "change the pattern or its type annotation"
  end

  test "a unary operator operand retains its source caret" do
    source = "not 1\n"
    operand = raw_span(source, "1", 1, 5)

    reason =
      {:source_context, {:conversion_failure, "Int", "Bool"},
       %{
         line: 1,
         column: 5,
         length: 1,
         span: operand,
         expectation_span: operand,
         checking: :not,
         expression_category: :literal,
         expectation_origin: :operator_operand,
         argument_index: 0
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "unary.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.title == "Operator cannot use this value"
    assert diagnostic.payload.origin.owner == :not
    assert diagnostic.primary.span.start_column == 5
    assert rendered =~ "The `not` operator cannot use this operand type"
    assert rendered =~ "1 | not 1"
    assert rendered =~ "this operator operand has the wrong type"
  end

  test "a real call result mismatch names and highlights the call" do
    source =
      "fn id(x: Int) -> Int = x\n" <>
        "fn main() -> Bool = id(1)\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "call_result.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "call_result.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :call_result
    assert diagnostic.payload.origin.owner == "id"
    assert diagnostic.primary.span.start_line == 2
    assert rendered =~ "CALL RESULT HAS THE WRONG TYPE"
    assert rendered =~ "The result of `id` does not match"
    assert rendered =~ "2 | fn main() -> Bool = id(1)"
    assert rendered =~ "this call result has the wrong type"
  end

  test "a real chained application reports an application result" do
    source =
      "fn mk() -> (Nat) -> Nat = fn(y) -> y\n" <>
        "fn main() -> Bool = mk()(Z())\n"

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source,
               file: "application.cure",
               emit_events: false
             )

    {diagnostic, registry} = Errors.to_diagnostic(reason, "application.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :application
    assert diagnostic.primary.span.start_line == 2
    assert rendered =~ "APPLICATION HAS THE WRONG TYPE"
    assert rendered =~ "This application"
    assert rendered =~ "2 | fn main() -> Bool = mk()(Z())"
    assert rendered =~ "this application has the wrong type"
  end

  test "typed actor family failures retain a family-specific type origin" do
    source = "actor Cure.Generated.BadActor\n"
    span = raw_span(source, "actor", 1, 1)

    reason =
      {:lift_module_error,
       %{
         module: "Cure.Generated.BadActor",
         behaviour: :gen_server,
         source_provenance: %{macro: "actor"},
         expansion_provenance: [],
         cause:
           {:source_context, {:cannot_unify, :bool, :int},
            %{checking: :handle_cast, expression_category: :literal, span: span}}
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "actor.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :actor
    assert diagnostic.payload.origin.owner == "Cure.Generated.BadActor"
    assert diagnostic.primary.span.start_column == 1
    assert rendered =~ "ACTOR MESSAGE HAS THE WRONG TYPE"
    assert rendered =~ "this actor message has the wrong type"
  end

  test "a real actor family callback failure renders at its authored invocation" do
    source = """
    mod BadActorDefinition
      use Std.Actor
      actor Cure.Generated.BadActor
        state Int
        on_cast
          Inc -> true
    """

    assert {:error, reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {diagnostic, registry} = Errors.to_diagnostic(reason, "actor_real.cure", source)
    rendered = Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.origin.kind == :actor
    assert diagnostic.primary.span.start_line == 3
    assert rendered =~ "ACTOR CALLBACK HAS THE WRONG TYPE"
    assert rendered =~ "3 |   actor Cure.Generated.BadActor"
  end

  test "typed FSM and supervisor family failures retain their family origins" do
    source = "family declaration\n"
    span = raw_span(source, "family", 1, 1)

    for {behaviour, macro, origin} <- [
          {:gen_statem, "fsm", :fsm},
          {:supervisor, "sup", :supervisor}
        ] do
      reason =
        {:lift_module_error,
         %{
           module: "Cure.Generated.Family",
           behaviour: behaviour,
           source_provenance: %{macro: macro},
           expansion_provenance: [],
           cause:
             {:source_context, {:cannot_unify, :bool, :int},
              %{checking: :generated_callback, expression_category: :literal, span: span}}
         }}

      {diagnostic, _registry} = Errors.to_diagnostic(reason, "family.cure", source)

      assert diagnostic.code == "E093"
      assert diagnostic.payload.origin.kind == origin
    end
  end

  defp raw_span(source, needle, line, column) do
    {start_byte, byte_length} = :binary.match(source, needle)

    %Span{
      source_id: "nofile",
      path: "nofile",
      start_byte: start_byte,
      end_byte: start_byte + byte_length,
      start_line: line,
      start_column: column,
      end_line: line,
      end_column: column + String.length(needle)
    }
  end
end

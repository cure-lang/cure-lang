defmodule Cure.Compiler.DeclarationSeparatorDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp diagnostic(source, file) do
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error =
      Enum.find(errors, fn
        {:declaration_separator_missing, _} -> true
        {:container_elements_syntax, _} -> true
        _ -> false
      end)

    assert {tag, _} = error
    assert tag in [:declaration_separator_missing, :container_elements_syntax]
    {error, Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)}
  end

  test "a GADT constructor signature gets an exact colon insertion" do
    source = "mod M\n  type A = MkA\n  type Box indices ()\n    Mk A -> Box\n"
    {error, {diagnostic, registry}} = diagnostic(source, "ctor_colon.cure")

    assert {:declaration_separator_missing,
            %{
              kind: :gadt_constructor_colon_missing,
              family: "Box",
              declaration: "Mk"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CONSTRUCTOR SIGNATURE NEEDS A COLON [E094] ------------------ ctor_colon.cure

             The constructor `Mk` in `Box` needs `:` between its name and type signature.

             A valid continuation here starts with ':'.

             at ctor_colon.cure:4:8
             4 |     Mk A -> Box
               |     -- ^ this is the constructor name; insert `:` before this constructor signature

             Hint: Insert `:` before the constructor signature
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ": ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {4, 8}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => ": ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 3, "character" => 7},
             "end" => %{"line" => 3, "character" => 7}
           }
  end

  test "a record field declaration gets an exact colon insertion" do
    source = "rec Person\n  name String\n"
    {error, {diagnostic, registry}} = diagnostic(source, "record_colon.cure")

    assert {:declaration_separator_missing,
            %{
              kind: :record_field_colon_missing,
              family: "Person",
              declaration: "name"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- RECORD FIELD NEEDS A COLON [E094] ------------------------- record_colon.cure

             The field `name` in record `Person` needs `:` between its name and declared
             type.

             A valid continuation here starts with ':'.

             at record_colon.cure:2:8
             2 |   name String
               |   ---- ^ this is the record field name; insert `:` before this field type

             Hint: Insert `:` before the field type
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ": ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {2, 8}
    assert insertion.start_byte == insertion.end_byte
  end

  test "a fixity declaration gets an exact colon insertion without stealing ordinary prefix expressions" do
    source = "precedencegroup Custom\n  associativity: left\ninfix `<?>` Custom\n"
    {error, {diagnostic, registry}} = diagnostic(source, "fixity_colon.cure")

    assert {:declaration_separator_missing,
            %{
              kind: :fixity_colon_missing,
              family: :infix,
              declaration: "<?>"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- FIXITY DECLARATION NEEDS A COLON [E094] ------------------- fixity_colon.cure

             The `infix` declaration for `<?>` needs `:` between the operator and its
             precedence group.

             A valid continuation here starts with ':'.

             at fixity_colon.cure:3:13
             3 | infix `<?>` Custom
               | ----- ----- ^ this starts the fixity declaration; this is the operator being declared; insert `:` before this precedence group

             Hint: Insert `:` before the precedence group
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ": ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {3, 13}
    assert insertion.start_byte == insertion.end_byte

    ordinary = "fn keep(prefix: Int) -> Int = prefix + 1\n"
    {:ok, tokens} = Lexer.tokenize(ordinary, emit_events: false)
    assert {:ok, _ast} = Parser.parse(tokens, emit_events: false)
  end

  test "a precedence-group setting labels both its group and field name" do
    source = "precedencegroup Custom\n  associativity left\n"
    {error, {diagnostic, registry}} = diagnostic(source, "group_colon.cure")

    assert {:declaration_separator_missing,
            %{
              kind: :precedencegroup_field_colon_missing,
              family: :Custom,
              declaration: "associativity"
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- PRECEDENCE GROUP FIELD NEEDS A COLON [E094] ---------------- group_colon.cure

             The `associativity` setting in precedence group `Custom` needs `:` before its
             value.

             A valid continuation here starts with ':'.

             at group_colon.cure:2:17
             1 | precedencegroup Custom
               |                 ------ this is the precedence group
             2 |   associativity left
               |   ------------- ^ this is the setting name; insert `:` before this setting value

             Hint: Insert `:` before the setting value
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ": ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {2, 17}
    assert insertion.start_byte == insertion.end_byte
  end

  test "a type alias gets an exact equals-sign insertion" do
    source = "typealias P Int"
    {error, {diagnostic, registry}} = diagnostic(source, "alias_assign.cure")

    assert {:declaration_separator_missing,
            %{kind: :type_declaration_assign_missing, family: :typealias, declaration: "P"}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE ALIAS NEEDS AN EQUALS SIGN [E094] -------------------- alias_assign.cure

             The type alias `P` needs `=` between its name and the type it expands to.

             A valid continuation here starts with '='.

             at alias_assign.cure:1:13
             1 | typealias P Int
               | --------- - ^ this starts the type declaration; the declaration head ends here; insert `=` before this type body

             Hint: Insert `=` before the type body
             """)

    assert [%{edits: [%{replacement: "= ", span: insertion}]}] = diagnostic.suggestions
    assert {insertion.start_line, insertion.start_column} == {1, 13}
  end

  test "an algebraic type declaration gets an exact equals-sign insertion" do
    source = "type Color Red | Blue"
    {error, {diagnostic, registry}} = diagnostic(source, "type_assign.cure")

    assert {:declaration_separator_missing,
            %{kind: :type_declaration_assign_missing, family: :type, declaration: "Color"}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE DECLARATION NEEDS AN EQUALS SIGN [E094] --------------- type_assign.cure

             The type `Color` needs `=` between its declaration head and its constructors or
             aliased type.

             A valid continuation here starts with '='.

             at type_assign.cure:1:12
             1 | type Color Red | Blue
               | ---- ----- ^ this starts the type declaration; the declaration head ends here; insert `=` before this type body

             Hint: Insert `=` before the type body
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "= ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 11
    assert insertion.end_byte == 11
  end

  test "an unclosed type parameter list owns its opener and final parameter" do
    source = "typealias Pair(a: Type = Int"
    {error, {diagnostic, registry}} = diagnostic(source, "type_params_close.cure")

    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :type_parameters, declaration: "Pair"}} =
             error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE PARAMETER LIST IS NOT CLOSED [E094] ------------- type_params_close.cure

             The declaration of `Pair` reaches the end of its type parameter list without the
             closing ')'.

             at type_params_close.cure:1:29
             1 | typealias Pair(a: Type = Int
               |               --------------^ these type parameters start here; the previous type parameter ends here; close these type parameters with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{edits: [%{replacement: ")", span: insertion}]}] = diagnostic.suggestions
    assert insertion.start_byte == byte_size(source)
    assert insertion.end_byte == byte_size(source)
  end

  test "adjacent type parameters get a zero-width comma insertion" do
    source = "type Pair(a: Type b: Type) = Mk"
    {error, {diagnostic, registry}} = diagnostic(source, "type_params_comma.cure")

    assert {:container_elements_syntax,
            %{kind: :container_separator_missing, container: :type_parameters, declaration: "Pair"}} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE PARAMETERS NEED A COMMA [E094] ------------------ type_params_comma.cure

             The declaration of `Pair` has another type parameter here, but consecutive
             parameters must be separated by a comma.

             at type_params_comma.cure:1:19
             1 | type Pair(a: Type b: Type) = Mk
               |          -------- ^ these type parameters start here; the previous type parameter ends here; insert a comma before this type parameter

             Hint: Insert `,` between these type parameters
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 19}
    assert insertion.start_byte == insertion.end_byte
  end

  test "record type parameters use the same contextual comma diagnostic" do
    source = "rec Pair(A B)\n  first: A\n"
    {error, {diagnostic, registry}} = diagnostic(source, "record_params.cure")

    assert {:container_elements_syntax,
            %{
              kind: :container_separator_missing,
              container: :type_parameters,
              declaration: "Pair",
              declaration_kind: :record
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE PARAMETERS NEED A COMMA [E094] ---------------------- record_params.cure

             The declaration of `Pair` has another type parameter here, but consecutive
             parameters must be separated by a comma.

             at record_params.cure:1:12
             1 | rec Pair(A B)
               |         -- ^ these type parameters start here; the previous type parameter ends here; insert a comma before this type parameter

             Hint: Insert `,` between these type parameters
             """)

    assert [%{edits: [%{replacement: ", ", span: insertion}]}] = diagnostic.suggestions
    assert {insertion.start_line, insertion.start_column} == {1, 12}
    assert insertion.start_byte == insertion.end_byte
  end

  test "adjacent protocol type parameters retain protocol ownership" do
    source = "proto Mapper(A B)\n"
    {error, {diagnostic, registry}} = diagnostic(source, "proto_params.cure")

    assert {:container_elements_syntax,
            %{
              kind: :container_separator_missing,
              container: :type_parameters,
              declaration: "Mapper",
              declaration_kind: :protocol
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE PARAMETERS NEED A COMMA [E094] ----------------------- proto_params.cure

             The declaration of `Mapper` has another type parameter here, but consecutive
             parameters must be separated by a comma.

             at proto_params.cure:1:16
             1 | proto Mapper(A B)
               |             -- ^ these type parameters start here; the previous type parameter ends here; insert a comma before this type parameter

             Hint: Insert `,` between these type parameters
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 16}
    assert insertion.start_byte == insertion.end_byte
  end

  test "adjacent interface type parameters retain interface ownership" do
    source = "interface Functor(f a)\n"
    {error, {diagnostic, registry}} = diagnostic(source, "interface_params.cure")

    assert {:container_elements_syntax,
            %{
              kind: :container_separator_missing,
              container: :type_parameters,
              declaration: "Functor",
              declaration_kind: :interface
            }} = error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE PARAMETERS NEED A COMMA [E094] ------------------- interface_params.cure

             The declaration of `Functor` has another type parameter here, but consecutive
             parameters must be separated by a comma.

             at interface_params.cure:1:21
             1 | interface Functor(f a)
               |                  -- ^ these type parameters start here; the previous type parameter ends here; insert a comma before this type parameter

             Hint: Insert `,` between these type parameters
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 21}
    assert insertion.start_byte == insertion.end_byte
  end

  test "assert_type gets an exact colon insertion between its expression and type" do
    source = "fn checked() -> Int = assert_type 42 Int"
    {error, {diagnostic, registry}} = diagnostic(source, "assert_type_colon.cure")

    assert {:declaration_separator_missing, %{kind: :assert_type_colon_missing, expected: :colon, observed: "Int"}} =
             error

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TYPE ASSERTION NEEDS A COLON [E094] ------------------ assert_type_colon.cure

             The `assert_type` expression needs `:` between the asserted value and its
             expected type.

             A valid continuation here starts with ':'.

             at assert_type_colon.cure:1:38
             1 | fn checked() -> Int = assert_type 42 Int
               |                       ----------- -- ^ this type assertion starts here; the asserted expression ends here; insert `:` before this expected type

             Hint: Insert `:` before the expected type
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ": ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {1, 38}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => ": ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 37},
             "end" => %{"line" => 0, "character" => 37}
           }
  end

  test "assert_type does not offer a partial machine edit when the expected type is absent" do
    source = "fn checked() -> Int = assert_type 42"
    {error, {diagnostic, _registry}} = diagnostic(source, "assert_type_eof.cure")

    assert {:declaration_separator_missing, %{kind: :assert_type_colon_missing, observed: :eof, token_type: :eof}} =
             error

    assert diagnostic.suggestions == []
  end
end

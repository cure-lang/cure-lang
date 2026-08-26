defmodule Cure.Compiler.ImplementationScopeDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.{Renderer, Sink}

  @misindented """
  mod MisindentedImplementation
    interface Equal(t)
      fn equal(a: t, b: t) -> Bool
    implementation Equal for Int
    fn equal(a: Int, b: Int) -> Bool = true
  end
  """

  test "a sibling function after an empty implementation is E116 with both ranges and an indentation edit" do
    assert {:error, {:codegen_error, {:implementation_scope, details}} = reason} =
             Cure.Compiler.compile_string(@misindented,
               file: "misindented_implementation.cure",
               emit_events: false
             )

    assert details.kind == :member_outside
    assert details.interface == "Equal"
    assert details.for == "Int"
    assert details.member == "equal"
    assert source_slice(@misindented, details.implementation_span) == "implementation Equal for Int"
    assert source_slice(@misindented, details.member_span) == "fn equal(a: Int, b: Int) -> Bool = true"

    {diagnostic, registry} =
      Errors.to_diagnostic(reason, "misindented_implementation.cure", @misindented)

    assert diagnostic.code == "E116"
    assert diagnostic.primary.span == details.member_span
    assert [%{span: implementation_span}] = diagnostic.secondary
    assert implementation_span == details.implementation_span

    assert [%{applicability: :machine_applicable, edits: [edit]}] = diagnostic.suggestions
    assert edit.replacement == "  "
    assert edit.span.start_byte == details.member_span.start_byte
    assert edit.span.end_byte == edit.span.start_byte

    rendered = Renderer.plain(diagnostic, registry, width: 90)
    assert rendered =~ "-- IMPLEMENTATION MEMBER IS OUTSIDE ITS IMPLEMENTATION SCOPE [E116]"
    assert rendered =~ "4 |   implementation Equal for Int"
    assert rendered =~ "5 |   fn equal(a: Int, b: Int) -> Bool = true"
    assert rendered =~ "indent this member so it belongs to the implementation"
    assert rendered =~ "Hint: Indent `equal` beneath the implementation"

    lsp = Sink.render(Sink.new(format: :lsp, registry: registry), diagnostic)
    assert lsp["code"] == "E116"
    assert lsp["range"]["start"] == %{"line" => 4, "character" => 2}
    assert length(lsp["relatedInformation"]) == 1
    assert hd(lsp["data"]["suggestions"])["applicability"] == "machine_applicable"

    fixed = apply_edit(@misindented, edit)

    assert {:ok, _module, _warnings} =
             Cure.Compiler.compile_string(fixed,
               file: "fixed_implementation.cure",
               emit_events: false
             )
  end

  test "an implementation with no following member reports the empty form honestly" do
    source = """
    mod EmptyImplementation
      interface Marker(t)
        fn mark(value: t) -> Bool
      implementation Marker for Int
    end
    """

    assert {:error, {:implementation_scope, details}} = Cure.Elab.Program.elaborate(source)
    assert details.kind == :empty
    assert details.interface == "Marker"
    assert details.for == "Int"

    {diagnostic, registry} = Errors.to_diagnostic({:implementation_scope, details}, "empty.cure", source)
    rendered = Renderer.plain(diagnostic, registry, width: 100)

    assert diagnostic.code == "E116"
    assert rendered =~ "-- IMPLEMENTATION HAS NO MEMBERS [E116]"
    assert rendered =~ "Every implementation must contain at least one"
    assert rendered =~ "nested member."
    assert rendered =~ "add the implementation's members beneath this declaration"
  end

  test "properly nested multiple members preserve implementation scope" do
    source = """
    mod MultipleImplementationMembers
      interface PairOps(t)
        fn first(value: t) -> Int
        fn second(value: t) -> Int
      implementation PairOps for Int
        fn first(value: Int) -> Int = value
        fn second(value: Int) -> Int = value
    end
    """

    assert {:ok, _module, _warnings} =
             Cure.Compiler.compile_string(source,
               file: "multiple_implementation_members.cure",
               emit_events: false
             )
  end

  test "an unrelated sibling is not guessed to be an implementation member" do
    source = """
    mod UnrelatedSibling
      interface Marker(t)
        fn mark(value: t) -> Bool
      implementation Marker for Int
      fn helper(value: Int) -> Int = value
    end
    """

    assert {:error, {:implementation_scope, details}} = Cure.Elab.Program.elaborate(source)
    assert details.kind == :empty
    refute Map.has_key?(details, :member)

    {diagnostic, _registry} = Errors.to_diagnostic({:implementation_scope, details}, "unrelated.cure", source)
    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions
  end

  defp source_slice(source, span),
    do: binary_part(source, span.start_byte, span.end_byte - span.start_byte)

  defp apply_edit(source, edit) do
    prefix = binary_part(source, 0, edit.span.start_byte)
    suffix = binary_part(source, edit.span.end_byte, byte_size(source) - edit.span.end_byte)
    prefix <> edit.replacement <> suffix
  end
end

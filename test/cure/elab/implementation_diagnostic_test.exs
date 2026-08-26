defmodule Cure.Elab.ImplementationDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "a mismatched method signature shows the required and provided types at the method" do
    source =
      "mod M\n  interface Eqs(a)\n    fn eqs(x: a, y: a) -> Bool\n  implementation Eqs for Int\n    fn eqs(x: Int, y: Int) -> Int = 42\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "method_return.cure")

    assert {:method_signature_mismatch, %{interface: :Eqs, method: :eqs, expected: expected, actual: actual}} =
             Program.semantic_error(error)

    refute expected == actual

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- IMPLEMENTATION METHOD HAS THE WRONG SIGNATURE [E105] ----- method_return.cure

             `eqs` in this `Eqs` implementation has a different signature from the method
             declared by the interface. Every parameter and the result must agree after
             substituting the implementation type.

             Expected: Int -> Int -> Bool
             Found:    Int -> Int -> Int

             at method_return.cure:5:5
             5 |     fn eqs(x: Int, y: Int) -> Int = 42
               |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ this implementation provides the incompatible signature

             Hint: Change `eqs` to use the parameter and result types required by `Eqs`
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 4, 38)
    assert lsp["relatedInformation"] == []

    assert lsp["data"]["payload"] == %{
             "actual_surface" => "Int -> Int -> Int",
             "expected_surface" => "Int -> Int -> Bool",
             "interface" => "Eqs",
             "kind" => "method_signature_mismatch",
             "method" => "eqs"
           }

    fixed = String.replace(source, "-> Int = 42", "-> Bool = true")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "method_return_fixed.cure")
  end

  test "a stray implementation method shows its full declaration and interface candidates" do
    source =
      "mod M\n  interface Eqs(a)\n    fn eqs(x: a, y: a) -> Bool = true\n    fn nes(x: a, y: a) -> Bool = true\n  implementation Eqs for Int\n    fn eqz(x: Int, y: Int) -> Bool = int_eq(x, y)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "unknown_method.cure")

    assert {:unknown_interface_method, %{interface: :Eqs, method: :eqz, candidates: [:eqs, :nes]}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- UNKNOWN MODULE MEMBER [E091] ---------------------------- unknown_method.cure

             `eqz` is not available in this member namespace.

             at unknown_method.cure:6:5
             6 |     fn eqz(x: Int, y: Int) -> Bool = int_eq(x, y)
               |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ `eqz` was not found

             Hint: Did you mean `eqs`?
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(5, 4, 49)
    assert lsp["relatedInformation"] == []
    assert lsp["data"]["payload"]["candidates"] == ["eqs", "nes"]
    refute inspect(lsp["data"]["payload"]) =~ "source_info"
  end

  test "a missing required method points at the implementation that needs it" do
    source =
      "mod M\n  interface Eqs(a)\n    fn eqs(x: a, y: a) -> Bool\n    fn nes(x: a, y: a) -> Bool\n  implementation Eqs for Int\n    fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "missing_method.cure")

    assert {:missing_method, %{interface: :Eqs, method: :nes, head: head, for: "Int", span: %Cure.Diagnostic.Span{}}} =
             Program.semantic_error(error)

    assert Cure.Elab.Name.base(head) == "Int"

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- IMPLEMENTATION IS MISSING `NES` [E105] ------------------ missing_method.cure

             `Eqs` requires a method named `nes`, but this implementation for `Int` does not
             provide it and the interface has no default implementation.

             at missing_method.cure:5:3
             5 |   implementation Eqs for Int
               |   ^^^^^^^^^^^^^^^^^^^^^^^^^^ add `nes` beneath this implementation

             Hint: Implement `nes` with the signature required by `Eqs`
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 2, 28)
    assert lsp["relatedInformation"] == []

    assert lsp["data"]["payload"] == %{
             "head" => "Int",
             "head_id" => "Std.Int#Int",
             "interface" => "Eqs",
             "kind" => "missing_method",
             "method" => "nes"
           }

    fixed =
      String.replace(
        source,
        "    fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)\nend",
        "    fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)\n    fn nes(x: Int, y: Int) -> Bool = true\nend"
      )

    assert {:ok, _environment} = Program.elaborate(fixed, file: "missing_method_fixed.cure")
  end

  test "a value used as an implementation head points at the value after `for`" do
    source =
      "mod M\n  interface Eqs(a)\n    fn eqs(x: a, y: a) -> Bool = true\n  implementation Eqs for 1\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "value_head.cure")

    assert {:instance_head_ill_formed, %{reason: :not_type_head, interface: :Eqs, span: %Cure.Diagnostic.Span{}}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- IMPLEMENTATION HEAD IS NOT A TYPE [E105] -------------------- value_head.cure

             `1` is a value, but an implementation can only be declared for a type. Cure
             needs a type constructor here so it can select this implementation consistently.

             at value_head.cure:4:26
             4 |   implementation Eqs for 1
               |                          ^ this is a value, not an implementation type

             Hint: Replace `1` with the name of a type that implements `Eqs`
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 25, 26)
    assert lsp["relatedInformation"] == []

    assert lsp["data"]["payload"] == %{
             "authored_head" => "1",
             "interface" => "Eqs",
             "kind" => "instance_head_ill_formed",
             "reason" => "not_type_head"
           }

    fixed = String.replace(source, "for 1", "for Int")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "value_head_fixed.cure")
  end

  test "overlapping anonymous implementations label both declarations" do
    source =
      "mod M\n  interface Eqs(a)\n    fn eqs(x: a, y: a) -> Bool = true\n  implementation Eqs for Int\n  implementation Eqs for Int\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "overlap.cure")

    assert {:overlapping_instance,
            %{
              interface: :Eqs,
              head: head,
              first_span: %Cure.Diagnostic.Span{},
              second_span: %Cure.Diagnostic.Span{}
            }} = Program.semantic_error(error)

    assert Cure.Elab.Name.base(head) == "Int"

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- IMPLEMENTATIONS OVERLAP [E105] --------------------------------- overlap.cure

             There are two anonymous implementations of `Eqs` for `Int`. Cure requires one
             globally coherent implementation so every call selects the same behavior.

             at overlap.cure:5:3
             4 |   implementation Eqs for Int
               |   -------------------------- the first `Eqs` implementation for `Int` is here
             5 |   implementation Eqs for Int
               |   ^^^^^^^^^^^^^^^^^^^^^^^^^^ this second implementation conflicts with the first

             Hint: Remove one implementation, or give one an `as` name and select it explicitly
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 2, 28)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(3, 2, 28)
           ]

    assert lsp["data"]["payload"] == %{
             "head" => "Int",
             "head_id" => "Std.Int#Int",
             "interface" => "Eqs",
             "kind" => "overlapping_instance"
           }

    fixed = String.replace(source, "  implementation Eqs for Int\nend", "end")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "overlap_fixed.cure")
  end

  test "duplicate named implementations label both uses of the name" do
    source =
      "mod M\n  interface Eqs(a)\n    fn eqs(x: a, y: a) -> Bool = true\n  implementation Eqs for Int as fast\n  implementation Eqs for Bool as fast\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "named_overlap.cure")

    assert {:overlapping_named_instance,
            %{
              name: :fast,
              first_interface: :Eqs,
              first_for: "Int",
              second_for: "Bool",
              first_span: %Cure.Diagnostic.Span{},
              second_span: %Cure.Diagnostic.Span{}
            }} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- IMPLEMENTATION NAME IS ALREADY USED [E105] --------------- named_overlap.cure

             The name `fast` already selects `Eqs` for `Int`, so it cannot also select `Eqs`
             for `Bool`. Named implementations must have distinct names wherever they are in
             scope.

             at named_overlap.cure:5:3
             4 |   implementation Eqs for Int as fast
               |   ---------------------------------- `fast` first names `Eqs` for `Int` here
             5 |   implementation Eqs for Bool as fast
               |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ this second `fast` conflicts with the first

             Hint: Choose a different name after `as` for one implementation
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(4, 2, 37)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(3, 2, 36)
           ]

    assert lsp["data"]["payload"] == %{
             "first_head" => "Int",
             "first_interface" => "Eqs",
             "kind" => "overlapping_named_instance",
             "name" => "fast",
             "second_head" => "Bool",
             "second_interface" => "Eqs"
           }

    fixed = String.replace(source, "for Bool as fast", "for Bool as booleanEqs")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "named_overlap_fixed.cure")
  end

  test "an unknown interface labels its authored name and suggests an in-scope interface" do
    source =
      "mod M\n  interface Equatable(a)\n    fn eqs(x: a, y: a) -> Bool\n  implementation Equatble for Int\n    fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "unknown_interface.cure")

    assert {:no_such_interface, %{interface: :Equatble, span: %Cure.Diagnostic.Span{}, candidates: candidates}} =
             Program.semantic_error(error)

    assert :Equatable in candidates

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- UNKNOWN INTERFACE [E091] ----------------------------- unknown_interface.cure

             `Equatble` is not available in this interface namespace.

             at unknown_interface.cure:4:18
             4 |   implementation Equatble for Int
               |                  ^^^^^^^^ `Equatble` was not found

             Hint: Did you mean `Equatable`?
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(3, 17, 25)
    assert lsp["relatedInformation"] == []
    assert "Equatable" in lsp["data"]["payload"]["candidates"]

    fixed = String.replace(source, "Equatble", "Equatable")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "unknown_interface_fixed.cure")
  end

  defp diagnostic(source, file) do
    assert {:error, error} = Program.elaborate(source, file: file)
    {diagnostic, registry} = Errors.to_diagnostic(error, file, source)
    {diagnostic, registry, error}
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end

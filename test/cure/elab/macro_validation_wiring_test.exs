defmodule Cure.Elab.MacroValidationWiringTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "compilation rejects a macro with an uncovered diagnosis point" do
    source = """
    mod M
      macro Every
        syntax every <t: Duration> becomes t
        explain
          keyword "every" =>
            "starts with every"
    """

    assert {:error, {:source_context, {:missing_diagnosis, points}, %{span: %Cure.Diagnostic.Span{}}}} =
             Program.elaborate(source)

    assert {:hole_kind, "Duration"} in points
  end

  test "compilation rejects an unpinned syntax rule" do
    source = """
    mod M
      macro Now
        syntax now becomes 0
        explain
          keyword "now" =>
            "starts with now"
    """

    assert {:error, {:source_context, {:rule_unpinned, ["now"]}, %{span: %Cure.Diagnostic.Span{}}}} =
             Program.elaborate(source)
  end

  test "compilation points at a computed hole that claims the reserved context field" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        syntax mk <context: Code> contextual computed by build_it

      fn build_it(input: MkSyntax) -> Syntax = input.context
    """

    assert {:error,
            {:source_context, {:reserved_syntax_field, "context", ["mk"]},
             %{
               span: %Cure.Diagnostic.Span{start_line: 5, start_column: 15},
               rule_spans: [%Cure.Diagnostic.Span{}]
             }} = reason} = Program.elaborate(source)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "reserved_context.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO HOLE USES A RESERVED NAME [E092] ---------------- reserved_context.cure

             The hole `context` in the `mk` rule conflicts with the reflected expansion
             context supplied to computed rules.

             at reserved_context.cure:5:15
             5 |     syntax mk <context: Code> contextual computed by build_it
               |               ^^^^^^^^^^^^^^^ this hole name is reserved for expansion context

             Hint: Rename this hole; `context` is supplied automatically
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 4, "character" => 14},
             "end" => %{"line" => 4, "character" => 29}
           }
  end

  test "compilation rejects a mismatched syntax expansion pin" do
    source = """
    mod M
      macro Now
        syntax now becomes 0
          example now expands 1
        explain
          keyword "now" =>
            "starts with now"
    """

    assert {:error,
            {:source_context, {:example_mismatch, [%{keyword: "now", source_span: %Cure.Diagnostic.Span{}}]},
             %{span: %Cure.Diagnostic.Span{}, rule_spans: [%Cure.Diagnostic.Span{}]}} = reason} =
             Program.elaborate(source)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "example_pin.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO EXAMPLE HAS THE WRONG EXPANSION [E092] --------------- example_pin.cure

             Macro example(s) do not match their actual expansions: now.

             at example_pin.cure:4:7
             3 |     syntax now becomes 0
               |     -------------------- this rule owns the failing example
             4 |       example now expands 1
               |       ^^^^^^^^^^^^^^^^^^^^^ this pin does not match the actual expansion

             Hint: Update the pinned expansion or fix the macro rule
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 3, "character" => 6},
             "end" => %{"line" => 3, "character" => 27}
           }
  end

  test "compilation accepts a fully pinned computed rule" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        syntax mk <x: Code> computed by build_it
          example mk 1 expands 1
        explain
          Code =>
            "expects code"
          keyword "mk" =>
            "starts with mk"

      fn build_it(a: MkSyntax) -> Syntax = a.x
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "compilation accepts a type-only syntax example pin" do
    source = """
    mod M
      macro One
        syntax one becomes 1
          example one expands : Int
        explain
          keyword "one" =>
            "starts with one"
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "compilation rejects a type-only syntax example pin with the wrong type" do
    source = """
    mod M
      macro One
        syntax one becomes 1
          example one expands : String
        explain
          keyword "one" =>
            "starts with one"
    """

    assert {:error,
            {:source_context, {:example_type_mismatch, [%{keyword: "one", source_span: %Cure.Diagnostic.Span{}}]},
             %{span: %Cure.Diagnostic.Span{}, rule_spans: [%Cure.Diagnostic.Span{}]}} = reason} =
             Program.elaborate(source)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "example_type.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO EXAMPLE HAS THE WRONG TYPE [E092] ------------------- example_type.cure

             Macro example(s) have the wrong type: one.

             at example_type.cure:4:7
             3 |     syntax one becomes 1
               |     -------------------- this rule owns the failing example
             4 |       example one expands : String
               |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ this pinned type does not accept the expansion

             Hint: Use the expansion's actual type or fix the macro rule
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 3, "character" => 6},
             "end" => %{"line" => 3, "character" => 34}
           }
  end

  test "compilation rejects a macro whose generated expansion is ill-typed" do
    source = """
    mod M
      macro Bad
        syntax bad <n: Code> becomes n + true
          example bad 0 expands 0 + true
        explain
          Code =>
            "expects code"
          keyword "bad" =>
            "starts with bad"
    """

    assert {:error,
            {:source_context, {:expansion_ill_typed, %{keyword: "bad"}},
             %{
               span: %Cure.Diagnostic.Span{start_line: 3, start_column: 34},
               rule_kind: :syntax
             }} = reason} = Program.elaborate(source)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "expansion_proof.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO RULE CAN GENERATE ILL-TYPED CODE [E092] ---------- expansion_proof.cure

             The `bad` rule has a generated counterexample that the dependent elaborator
             rejects.

             at expansion_proof.cure:3:34
             3 |     syntax bad <n: Code> becomes n + true
               |                                  ^^^^^^^^ this expansion template produces the invalid expansion

             Note: The generated counterexample and internal elaboration reason are available
                   in debug output.

             Hint: Fix the `bad` rule so every accepted input produces well-typed Cure code
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 2, "character" => 33},
             "end" => %{"line" => 2, "character" => 41}
           }

    refute Map.has_key?(diagnostic.payload, :internal_reason)
    {debug_diagnostic, _registry} = Errors.to_diagnostic(reason, "expansion_proof.cure", source, debug: true)
    assert Map.has_key?(debug_diagnostic.payload, :internal_reason)
    assert Map.has_key?(debug_diagnostic.payload, :expansion)
  end

  test "compilation points at a hole category the proof generator cannot inhabit" do
    source = """
    mod M
      macro Mystery
        syntax inspect <value: OpaqueThing> becomes 0
    """

    assert {:error,
            {:source_context, {:unsupported_hole_type, "OpaqueThing"},
             %{
               span: %Cure.Diagnostic.Span{start_line: 3, start_column: 20},
               category: "OpaqueThing"
             }} = reason} = Program.elaborate(source)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "unsupported_hole.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO HOLE CANNOT BE GENERATED FOR PROOFS [E092] ------ unsupported_hole.cure

             The generative expansion proof has no safe value generator for the `OpaqueThing`
             hole category.

             at unsupported_hole.cure:3:20
             3 |     syntax inspect <value: OpaqueThing> becomes 0
               |                    ^^^^^^^^^^^^^^^^^^^^ the proof generator cannot construct this category

             Hint: Use a generatable category, or mark the rule `contextual` when proof needs its call site
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 2, "character" => 19},
             "end" => %{"line" => 2, "character" => 39}
           }
  end

  test "unsupported proof categories label every affected hole" do
    source = """
    mod M
      macro Mystery
        syntax first <a: OpaqueThing> becomes 0
        syntax second <b: OpaqueThing> becomes 1
    """

    assert {:error,
            {:source_context, {:unsupported_hole_type, "OpaqueThing"},
             %{hole_spans: [%Cure.Diagnostic.Span{}, %Cure.Diagnostic.Span{}]}} = reason} = Program.elaborate(source)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "unsupported_holes.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO HOLE CANNOT BE GENERATED FOR PROOFS [E092] ----- unsupported_holes.cure

             The generative expansion proof has no safe value generator for the `OpaqueThing`
             hole category.

             at unsupported_holes.cure:3:18
             3 |     syntax first <a: OpaqueThing> becomes 0
               |                  ^^^^^^^^^^^^^^^^ the proof generator cannot construct this category
             4 |     syntax second <b: OpaqueThing> becomes 1
               |                   ---------------- this hole uses the same unsupported category

             Hint: Use a generatable category, or mark the rule `contextual` when proof needs its call site
             """)
  end

  test "a defensive generated-hole invariant failure blames the hole, not the author" do
    source = """
    mod M
      macro Broken
        syntax bad <n: Nat> becomes n
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    {:macro_def, _, [rule]} = Enum.find(children, &match?({:macro_def, _, _}, &1))
    [span] = get_in(rule, [:field_spans, "n"])

    reason =
      {:source_context,
       {:generated_hole_not_well_typed,
        %{term: {:ctor, :Bad, []}, category: "Nat", hole: "n", generator_invariant: true}},
       %{
         span: span,
         hole_spans: [span],
         macro: "Broken",
         category: "Nat",
         hole: "n",
         expression_category: :macro_proof_generator_invariant
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "generator_invariant.cure", source)
    fingerprint = diagnostic.payload.fingerprint

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- MACRO PROOF GENERATOR PRODUCED AN INVALID VALUE [E092] -- generator_invariant.cure

             The compiler's `Nat` proof generator produced a value that failed its own type
             check. This is not an error in the macro declaration.

             at generator_invariant.cure:3:16
             3 |     syntax bad <n: Nat> becomes n
               |                ^^^^^^^^ proof generation failed while checking this hole

             Note: Internal diagnostic fingerprint: #{fingerprint}.

             Hint: Report this compiler defect with fingerprint `#{fingerprint}`
             """)

    refute Map.has_key?(diagnostic.payload, :generated_term)
    {debug_diagnostic, _registry} = Errors.to_diagnostic(reason, "generator_invariant.cure", source, debug: true)
    assert debug_diagnostic.payload.generated_term == {:ctor, :Bad, []}
  end
end

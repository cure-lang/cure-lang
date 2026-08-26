defmodule Cure.Diagnostic.ProofChainDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.{Renderer, Sink}

  test "E109 preserves authored ranges and projects through every renderer" do
    source = "proof chain\n  first\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "chain_syntax.cure", emit_events: false)
    assert {:error, [reason | _]} = Parser.parse(tokens, file: "chain_syntax.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "chain_syntax.cure", source)
    assert diagnostic.code == "E109"
    assert diagnostic.key == :proof_chain_syntax
    assert diagnostic.payload.kind == :missing_relation

    plain = Renderer.plain(diagnostic, registry)
    terminal = Renderer.terminal(diagnostic, registry, color: :always, width: 80)
    json = diagnostic |> Renderer.json() |> Jason.decode!()
    lsp = Sink.render(Sink.new(format: :lsp, registry: registry, position_encoding: :utf16), diagnostic)

    assert plain =~ "PROOF CHAIN STEP IS MISSING `==`"
    assert terminal =~ "\e["
    assert json["code"] == "E109"
    assert lsp["code"] == "E109"
    assert lsp["range"]["start"]["line"] == 1
  end

  test "E109 owns every inline chain structure failure" do
    fixtures = [
      {:empty_chain, "proof chain\n"},
      {:missing_relation, "proof chain\n  first\n"},
      {:missing_right_side, "proof chain\n  first\n    == because evidence\n"},
      {:missing_because, "proof chain\n  first\n    == second\n"},
      {:first_step_previous, "proof chain\n  _\n    == second\n    because evidence\n"}
    ]

    for {variant, source} <- fixtures do
      assert {:ok, tokens} = Lexer.tokenize(source, file: "#{variant}.cure", emit_events: false)
      assert {:error, reasons} = Parser.parse(tokens, file: "#{variant}.cure", emit_events: false)

      assert Enum.any?(reasons, fn reason ->
               {diagnostic, _registry} = Errors.to_diagnostic(reason, "#{variant}.cure", source)
               diagnostic.code == "E109" and diagnostic.payload.kind == variant
             end)
    end
  end

  test "E110 blames because evidence rather than generated transitivity" do
    source = """
    mod BadChainDiagnostic
      use Std.Equivalent
      fn proof(x: Int) -> Equivalent(Int, x, x) = proof chain
        x
          == 1
          because reflexive(x)
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "chain_type.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "chain_type.cure", source)
    assert diagnostic.code == "E110"
    assert diagnostic.payload.kind == :wrong_justification
    assert diagnostic.payload.step_index == 0

    plain = Renderer.plain(diagnostic, registry)
    json = diagnostic |> Renderer.json() |> Jason.decode!()
    lsp = Renderer.lsp(diagnostic, registry, :utf16)

    assert plain =~ "because reflexive(x)"
    assert plain =~ "this evidence proves a different proposition"
    refute plain =~ "generated trans"
    assert json["payload"]["step_index"] == 0
    assert lsp["code"] == "E110"
    assert lsp["range"]["start"]["line"] == 5
  end

  test "E110 labels adjacent endpoints with different carriers" do
    source = """
    mod CarrierMismatch
      use Std.Equivalent
      fn proof(x: Int) -> Equivalent(Int, x, x) = proof chain
        x
          == 1.0
          because reflexive(x)
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "chain_carrier.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "chain_carrier.cure", source)
    assert diagnostic.code == "E110"
    assert diagnostic.payload.kind == :adjacent_endpoints
    assert diagnostic.payload.step_index == 0
    assert length(diagnostic.secondary) >= 1
    assert Renderer.plain(diagnostic, registry) =~ "previous endpoint"
  end

  test "unfinished because blocks expose their residual goal and local facts" do
    source = """
    mod OpenBecause
      use Std.Equivalent
      fn proof(x: Int) -> Equivalent(Int, x, x) = proof chain
        x
          == x
          because
            have fact: Equivalent(Int, x, x) = reflexive(x)
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "open_because.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "open_because.cure", source)
    assert diagnostic.code == "E110"
    assert diagnostic.payload.kind == :unfinished_justification
    assert diagnostic.payload.cause == {:open_goal, ["fact"]}
    assert diagnostic.payload.residual_goal
    assert Renderer.plain(diagnostic, registry) =~ "still open"
    assert Renderer.lsp(diagnostic, registry, :utf16)["range"]["start"]["line"] == 5
  end

  test "statements after closure use E109 and label both statements" do
    source = """
    mod ClosedBecause
      use Std.Equivalent
      fn proof(x: Int) -> Equivalent(Int, x, x) = proof chain
        x
          == x
          because
            reflexive(x)
            reflexive(x)
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "closed_because.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "closed_because.cure", source)
    assert diagnostic.code == "E109"
    assert diagnostic.payload.kind == :unreachable_proof_statement
    assert length(diagnostic.secondary) == 1
    plain = Renderer.plain(diagnostic, registry)
    assert plain =~ "already closed here"
    assert plain =~ "statement is unreachable"
    assert Renderer.lsp(diagnostic, registry, :utf16)["relatedInformation"] != []
  end

  test "E111 preserves directed rewrite failures through plain, JSON, and LSP renderers" do
    source = """
    mod AmbiguousRewrite
      use Std.Equivalent
      fn proof(x: Int, y: Int, equality: Equivalent(Int, x, y)) -> Equivalent(Int, x, x) = proof chain
        x
          == x
          because
            rewrite using equality
            equality
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "ambiguous_rewrite.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "ambiguous_rewrite.cure", source)
    assert diagnostic.code == "E111"
    assert diagnostic.key == :rewrite_failed
    assert diagnostic.payload.kind == :ambiguous_occurrence
    assert Enum.map(diagnostic.payload.occurrences, & &1.number) == [1, 2]
    assert Enum.map(diagnostic.suggestions, &(&1.edits |> hd() |> Map.fetch!(:replacement))) == [" at 1", " at 2"]
    assert Renderer.plain(diagnostic, registry) =~ "at n"
    assert (diagnostic |> Renderer.json() |> Jason.decode!())["code"] == "E111"
    assert Renderer.lsp(diagnostic, registry, :utf16)["code"] == "E111"
  end

  test "E111 assigns stable variants to every directed rewrite selection failure" do
    fixtures = [
      {:no_occurrence, "z", "z", "rewrite using equality"},
      {:reverse_only, "y", "z", "rewrite using equality"},
      {:invalid_occurrence, "x", "x", "rewrite using equality at 3"},
      {:bad_target, "x", "y", "rewrite using equality in missing"}
    ]

    for {kind, left, right, command} <- fixtures do
      source = """
      mod Rewrite#{kind}
        use Std.Equivalent
        fn proof(x: Int, y: Int, z: Int, equality: Equivalent(Int, x, y)) -> Equivalent(Int, #{left}, #{right}) = proof chain
          #{left}
            == #{right}
            because
              #{command}
              equality
      end
      """

      assert {:error, {:codegen_error, reason}} =
               Cure.Compiler.compile_string(source, file: "#{kind}.cure", emit_events: false)

      {diagnostic, _registry} = Errors.to_diagnostic(reason, "#{kind}.cure", source)
      assert diagnostic.code == "E111"
      assert diagnostic.payload.kind == kind
      assert diagnostic.payload.command
      assert diagnostic.payload.theorem
      assert diagnostic.payload.goal

      if kind == :reverse_only do
        assert [
                 %{
                   applicability: :machine_applicable,
                   edits: [%{replacement: " backwards", span: insertion}]
                 }
               ] = diagnostic.suggestions

        assert insertion.start_byte == insertion.end_byte
        assert binary_part(source, insertion.start_byte - 7, 7) == "rewrite"
        assert binary_part(source, insertion.start_byte, 6) == " using"
      end
    end
  end

  test "E112 preserves residual simplification data through plain, JSON, and LSP" do
    source = """
    mod ResidualSimplification
      type Nat = Z | S(Nat)
      fn bad(x: Nat) -> Equivalent(Nat, x, S(x)) = proof chain
        x == S(x)
        because simplify
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "residual_simplify.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "residual_simplify.cure", source)
    assert diagnostic.code == "E112"
    assert diagnostic.key == :simplification_failed
    assert diagnostic.payload.kind == :residual_goal
    assert diagnostic.payload.before_goal
    assert diagnostic.payload.after_goal
    assert diagnostic.payload.before_surface =~ "Equivalent"
    assert diagnostic.payload.after_surface =~ "Equivalent"
    plain = Renderer.plain(diagnostic, registry)
    assert plain =~ "RESIDUAL GOAL"
    assert plain =~ ~r/Before:\s+Equivalent/
    assert plain =~ "After:"
    assert (diagnostic |> Renderer.json() |> Jason.decode!())["code"] == "E112"
    assert Renderer.lsp(diagnostic, registry, :utf16)["code"] == "E112"
  end

  test "E112 keeps the default compact and renders structured trace IDs only on request" do
    problem = %Cure.Diagnostic.SimplificationProblem{
      kind: :residual_goal,
      before_goal: :before,
      after_goal: :after,
      trace_ids: ["equation-1", "explicit-2"]
    }

    compact = Cure.Diagnostic.Adapter.from_error({:simplification_failed, problem})
    expanded = Cure.Diagnostic.Adapter.from_error({:simplification_failed, problem}, trace: :expanded)
    compact_text = compact.body |> Cure.Diagnostic.Doc.to_map() |> Jason.encode!()
    expanded_text = expanded.body |> Cure.Diagnostic.Doc.to_map() |> Jason.encode!()

    refute compact_text =~ "equation-1"
    assert expanded_text =~ "equation-1"
    assert expanded_text =~ "explicit-2"
  end

  test "E112 proof adaptation renders the supplied and required simplified propositions" do
    source = """
    mod AdaptDiagnostic
      type Nat = Z | S(Nat)
      fn bad(x: Nat, y: Nat, equality: Equivalent(Nat, x, y)) -> Equivalent(Nat, x, S(y)) = proof chain
        x == S(y)
        because simplify using equality
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "adapt_mismatch.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "adapt_mismatch.cure", source)
    assert diagnostic.code == "E112"
    assert diagnostic.payload.kind == :proof_mismatch
    assert diagnostic.payload.simplified_supplied
    assert diagnostic.payload.simplified_goal
    plain = Renderer.plain(diagnostic, registry)
    assert plain =~ ~r/Supplied proof\s+simplifies to:/
    assert plain =~ ~r/Before:\s+Equivalent/
    assert (diagnostic |> Renderer.json() |> Jason.decode!())["payload"]["simplified_supplied"]
    assert Renderer.lsp(diagnostic, registry, :utf16)["code"] == "E112"
  end

  test "E113 preserves induction subject and constructor-shape data through every renderer" do
    source = """
    mod BadInductionFields
      type Nat = Z | S(Nat)
      fn bad(value: Nat) -> Equivalent(Nat, value, value) = induction value
        case Z => reflexive(Z)
        case S() => reflexive(Z)
    end
    """

    assert {:error, {:codegen_error, _reason} = wrapped_reason} =
             Cure.Compiler.compile_string(source, file: "bad_induction_fields.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(wrapped_reason, "bad_induction_fields.cure", source)
    assert diagnostic.code == "E113"
    refute Renderer.plain(diagnostic, registry) =~ "CODE GENERATION FAILED"
    assert diagnostic.key == :induction_failed
    assert diagnostic.payload.kind == :wrong_case_fields
    assert diagnostic.payload.expected_fields == 2
    assert diagnostic.payload.observed_fields == 0
    assert diagnostic.payload.recursive_fields == [0]
    assert diagnostic.payload.constructor_range

    plain = Renderer.plain(diagnostic, registry)
    terminal = Renderer.terminal(diagnostic, registry, color: :always, width: 80)
    json = diagnostic |> Renderer.json() |> Jason.decode!()
    lsp = Renderer.lsp(diagnostic, registry, :utf16)

    assert plain =~ "INDUCTION CASE HAS THE WRONG FIELDS"
    assert plain =~ "Expected 2 bindings but found 0"
    assert terminal =~ "\e["
    assert json["code"] == "E113"
    assert json["payload"]["kind"] == "wrong_case_fields"
    assert lsp["code"] == "E113"
  end

  test "E113 distinguishes non-inductive, missing, duplicate, and unknown cases" do
    fixtures = [
      {:non_inductive_subject,
       """
       mod NonInductive
         fn bad(value: Float) -> Float = induction value
           case Nope => value
       end
       """},
      {:missing_case,
       """
       mod MissingInduction
         type Nat = Z | S(Nat)
         fn bad(value: Nat) -> Equivalent(Nat, value, value) = induction value
           case Z => reflexive(Z)
       end
       """},
      {:duplicate_case,
       """
       mod DuplicateInduction
         type Nat = Z | S(Nat)
         fn bad(value: Nat) -> Equivalent(Nat, value, value) = induction value
           case Z => reflexive(Z)
           case Z => reflexive(Z)
           case S(previous, induction_hypothesis) => reflexive(S(previous))
       end
       """},
      {:unknown_case,
       """
       mod UnknownInduction
         type Nat = Z | S(Nat)
         type Bit = Off | On
         fn bad(value: Nat) -> Equivalent(Nat, value, value) = induction value
           case Z => reflexive(Z)
           case On => reflexive(Z)
       end
       """}
    ]

    for {kind, source} <- fixtures do
      assert {:error, {:codegen_error, reason}} = Cure.Compiler.compile_string(source, emit_events: false)
      {diagnostic, _registry} = Errors.to_diagnostic(reason, "induction.cure", source)
      assert diagnostic.code == "E113"
      assert diagnostic.payload.kind == kind
      assert diagnostic.primary

      if kind == :missing_case do
        assert diagnostic.payload.constructor_range
        assert Enum.any?(diagnostic.secondary, &(&1.message == "constructor declared here"))
      end
    end
  end

  test "E113 rejects an impossible marker on a reachable constructor" do
    source = """
    mod ReachableInductionCase
      type Nat = Z | S(Nat)
      fn bad(value: Nat) -> Equivalent(Nat, value, value) = induction value
        case Z => impossible
        case S(previous, induction_hypothesis) => reflexive(S(previous))
    end
    """

    assert {:error, {:codegen_error, reason}} = Cure.Compiler.compile_string(source, emit_events: false)
    {diagnostic, _registry} = Errors.to_diagnostic(reason, "reachable_induction.cure", source)
    assert diagnostic.code == "E113"
    assert diagnostic.payload.kind == :impossible_case
    assert diagnostic.primary
  end

  test "E113 names an omitted recursive induction hypothesis" do
    source = """
    mod MissingInductionHypothesis
      type Nat = Z | S(Nat)
      fn bad(value: Nat) -> Equivalent(Nat, value, value) = induction value
        case Z => reflexive(Z)
        case S(previous) => reflexive(S(previous))
    end
    """

    assert {:error, {:codegen_error, reason}} = Cure.Compiler.compile_string(source, emit_events: false)
    {diagnostic, _registry} = Errors.to_diagnostic(reason, "missing_hypothesis.cure", source)
    assert diagnostic.code == "E113"
    assert diagnostic.payload.kind == :unavailable_hypothesis
    assert diagnostic.payload.recursive_fields == [0]
  end

  test "E113 explains a hypothesis used at the wrong specialized proposition" do
    source = """
    mod MistypedInductionHypothesis
      type Nat = Z | S(Nat)
      fn bad(value: Nat) -> Equivalent(Nat, value, value) = induction value
        case Z => reflexive(Z)
        case S(previous, induction_hypothesis) => induction_hypothesis
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "mistyped_hypothesis.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "mistyped_hypothesis.cure", source)
    assert diagnostic.code == "E113"
    assert diagnostic.payload.kind == :mistyped_hypothesis
    assert diagnostic.payload.hypothesis == "induction_hypothesis"
    assert diagnostic.payload.hypothesis_range
    assert diagnostic.payload.available
    assert diagnostic.payload.required
    assert Renderer.plain(diagnostic, registry) =~ "Available:"
    assert Renderer.lsp(diagnostic, registry, :utf16)["code"] == "E113"
  end

  test "E114 relates an unavailable equation member to its defining function" do
    source = """
    mod MissingEquation
      type Nat = Z | S(Nat)
      fn identity(n: Nat) -> Nat = match n
        Z -> Z
        S(previous) -> S(previous)
      fn bad() = identity.Missing
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "missing_equation.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "missing_equation.cure", source)
    assert diagnostic.code == "E114"
    assert diagnostic.payload.kind == :unknown_equation
    assert diagnostic.payload.equation_use
    assert diagnostic.payload.function_definition
    assert Renderer.plain(diagnostic, registry) =~ "function is defined here"
    assert (diagnostic |> Renderer.json() |> Jason.decode!())["code"] == "E114"
    assert Renderer.lsp(diagnostic, registry, :utf16)["code"] == "E114"
  end
end

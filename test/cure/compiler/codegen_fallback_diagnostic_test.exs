defmodule Cure.Compiler.CodegenFallbackDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{BeamWriter, Errors}
  alias Cure.Diagnostic.{ProvenanceFrame, Span}
  alias Cure.Diagnostic.Adapter.Codegen
  alias Cure.Diagnostic.Renderer

  test "an injected BEAM rejection keeps stage, module, source, reason, and fingerprint" do
    module = :"Cure.InjectedBrokenBeam"

    forms = [
      {:attribute, 1, :module, module},
      {:attribute, 1, :export, [missing: 0]}
    ]

    assert {:error, errors, warnings} = BeamWriter.compile_forms(forms)
    assert errors != []

    reason =
      {:codegen_failure,
       %{
         stage: :beam_writer,
         module: module,
         file: "injected_failure.cure",
         reason: {:beam_lint, errors, warnings}
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "injected_failure.cure", "mod InjectedFailure\nend\n")
    rendered = Renderer.plain(diagnostic, registry, width: 100)

    assert diagnostic.code == "E101"
    assert diagnostic.payload.stage == :beam_writer
    assert diagnostic.payload.module == module
    assert diagnostic.payload.file == "injected_failure.cure"
    assert diagnostic.payload.reason != ""
    assert diagnostic.payload.fingerprint =~ ~r/^[0-9a-f]{12}$/

    assert rendered =~ "Stage: `beam_writer`."
    assert rendered =~ "Module: `Cure.InjectedBrokenBeam`."
    assert rendered =~ "Source: `injected_failure.cure`."
    assert rendered =~ "Underlying"
    assert rendered =~ "reason: #{diagnostic.payload.reason}."
    assert rendered =~ "Diagnostic fingerprint: `#{diagnostic.payload.fingerprint}`."
    refute rendered =~ "The compiler could not produce a valid BEAM artifact for this source.\n\nNote:"

    assert :ok =
             Cure.Diagnostic.Registry.validate_exercised_producer_fixtures([:internal_failure_beam_writer],
               only_producers: [:beam_writer]
             )

    direct =
      Codegen.from_error(reason,
        codegen_stage: :ignored,
        source_file: "also-ignored.cure"
      )

    assert direct.code == diagnostic.code
    assert direct.title == diagnostic.title
    assert direct.body == diagnostic.body
    assert direct.payload == diagnostic.payload
  end

  test "fallback fingerprints are stable for the same failure and differ with stage" do
    base = %{
      stage: :beam_writer,
      module: :"Cure.StableFailure",
      file: "stable_failure.cure",
      reason: {:beam_lint, [:deliberate_failure]}
    }

    {first, _registry} = Errors.to_diagnostic({:codegen_failure, base}, base.file, "")
    {second, _registry} = Errors.to_diagnostic({:codegen_failure, base}, base.file, "")

    {other_stage, _registry} =
      Errors.to_diagnostic({:codegen_failure, %{base | stage: :beam_loader}}, base.file, "")

    assert first.payload.fingerprint == second.payload.fingerprint
    refute first.payload.fingerprint == other_stage.payload.fingerprint
  end

  test "E101 preserves the complete structured compiler-failure context" do
    span =
      Span.new(
        source_id: "contextual_failure.cure",
        path: "contextual_failure.cure",
        start_byte: 20,
        end_byte: 31,
        start_line: 2,
        start_column: 3,
        end_line: 2,
        end_column: 14
      )

    provenance = [
      %ProvenanceFrame{kind: :macro_expansion, name: :derive, invocation: span, generated: span}
    ]

    details = %{
      stage: :final_core_validation,
      module: :ContextualFailure,
      file: span.path,
      reason: :type_mismatch,
      declaration: :"ContextualFailure#run",
      span: span,
      core_term: {:app, {:global, :"ContextualFailure#helper"}, Enum.to_list(1..100)},
      core_trace: [
        %{term: {:global, :"ContextualFailure#run"}, phase: :elaboration},
        %{term: {:global, :"ContextualFailure#helper"}, phase: :emission}
      ],
      expected_type: {:global, :Nat},
      inferred_type: {:global, :String},
      unresolved_global: :"ContextualFailure#helper",
      closure_path: [:"ContextualFailure#run", :"ContextualFailure#helper"],
      provenance: provenance
    }

    diagnostic = Codegen.from_error({:codegen_failure, details}, [])

    assert diagnostic.primary.span == span
    assert diagnostic.provenance == provenance
    assert diagnostic.payload.declaration == :"ContextualFailure#run"
    assert diagnostic.payload.span == span
    assert diagnostic.payload.core_term =~ "ContextualFailure#helper"
    assert byte_size(diagnostic.payload.core_term) < 1_000
    assert diagnostic.payload.core_trace == details.core_trace
    assert diagnostic.payload.expected_type == "{:global, :Nat}"
    assert diagnostic.payload.inferred_type == "{:global, :String}"
    assert diagnostic.payload.unresolved_global == :"ContextualFailure#helper"
    assert diagnostic.payload.closure_path == details.closure_path

    changed =
      Codegen.from_error(
        {:codegen_failure, %{details | declaration: :"ContextualFailure#other"}},
        []
      )

    refute changed.payload.fingerprint == diagnostic.payload.fingerprint
  end

  test "emission closure failures name the missing Core reference and its closure path" do
    diagnostic =
      Codegen.from_error(
        {:codegen_error,
         {:emission_closure_missing,
          %{
            definition: :same,
            referenced_by: :"Fixture#run",
            module: "Fixture",
            closure_path: [:"Fixture#run", :same]
          }}},
        source_file: "fixture.cure"
      )

    assert diagnostic.code == "E101"
    assert diagnostic.payload.kind == :emission_closure_missing
    assert diagnostic.payload.declaration == :"Fixture#run"
    assert diagnostic.payload.unresolved_global == :same
    assert diagnostic.payload.closure_path == [:"Fixture#run", :same]
  end

  test "final-Core E101 identifies the declaration and rejected Core nodes" do
    rejected = {:app, {:global, :missing}, {:int_lit, 1}}

    diagnostic =
      Codegen.from_error(
        {:final_core_violation, :"Fixture#run", [%{clause: :known_globals, message: "unknown global", node: rejected}]},
        codegen_stage: :final_core_validation,
        codegen_module: :Fixture
      )

    assert diagnostic.payload.declaration == :"Fixture#run"
    assert diagnostic.payload.core_term =~ ":missing"
    assert diagnostic.payload.core_trace == [rejected]
    assert diagnostic.payload.unresolved_global == :missing
  end
end
